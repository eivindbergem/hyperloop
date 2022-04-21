//! Async task with priority
use core::{
    pin::Pin,
    task::{Context, Poll, Waker},
};

use futures::Future;

/// Task priority
pub type Priority = u8;

/// Async task with priority
///
/// # Example
///```
/// use hyperloop::task::Task;
///
/// async fn task_fn() {
/// }
///
/// let task = Task::new(task_fn(), 1);
/// ```
pub struct Task<F>
where
    F: Future<Output = ()> + 'static,
{
    future: F,
    priority: Priority,
}

impl<F> Task<F>
where
    F: Future<Output = ()> + 'static,
{
    /// Create new task from future with given priority
    pub fn new(future: F, priority: Priority) -> Self {
        Self { future, priority }
    }

    /// Return handle to pinned task
    pub fn get_handle(self: Pin<&mut Self>) -> TaskHandle {
        TaskHandle::new(self)
    }
}

/// Type erased handle for `Task`
pub struct TaskHandle {
    future: *mut (),
    poll: fn(*mut (), &mut Context<'_>) -> Poll<()>,
    pub priority: Priority,
}

impl TaskHandle {
    fn new<F: Future<Output = ()>>(task: Pin<&mut Task<F>>) -> Self {
        unsafe {
            let task = Pin::get_unchecked_mut(task);

            Self {
                future: &mut task.future as *mut F as *mut (),
                poll: core::mem::transmute::<
                    fn(Pin<&mut F>, &mut Context<'_>) -> Poll<F::Output>,
                    fn(*mut (), &mut Context<'_>) -> Poll<()>,
                >(F::poll),
                priority: task.priority,
            }
        }
    }

    /// Poll task with given waker
    pub fn poll(&mut self, waker: Waker) -> Poll<()> {
        let mut cx = Context::from_waker(&waker);

        let poll = self.poll;

        poll(self.future, &mut cx)
    }
}

#[derive(Debug)]
struct YieldFuture {
    done: bool,
}

impl YieldFuture {
    fn new() -> Self {
        Self { done: false }
    }
}

impl Future for YieldFuture {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if !self.done {
            self.done = true;
            cx.waker().wake_by_ref();

            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}

/// Yield task
pub fn yield_now() -> impl Future<Output = ()> {
    YieldFuture::new()
}

#[cfg(test)]
mod tests {
    use crossbeam_queue::ArrayQueue;
    use std::sync::Arc;

    use crate::common::tests::MockWaker;

    use super::*;

    #[test]
    fn task() {
        let queue = Arc::new(ArrayQueue::new(10));

        let test_future = |queue| {
            async fn future(queue: Arc<ArrayQueue<u32>>) {
                for i in 0.. {
                    queue.push(i).unwrap();
                    yield_now().await;
                }
            }

            future(queue)
        };

        let mut task = Task::new(test_future(queue.clone()), 1);
        let mut handle = unsafe { Pin::new_unchecked(&mut task).get_handle() };
        let waker: Waker = Arc::new(MockWaker::new()).into();

        assert_eq!(handle.poll(waker.clone()), Poll::Pending);

        assert_eq!(queue.pop().unwrap(), 0);
        assert!(queue.pop().is_none());

        assert_eq!(handle.poll(waker.clone()), Poll::Pending);

        assert_eq!(queue.pop().unwrap(), 1);
        assert!(queue.pop().is_none());
    }
}
