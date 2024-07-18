//! Async executor
//!
//! # Example
//!```
//! # use core::sync::atomic::{AtomicBool, Ordering};
//! # use core::pin::pin;
//! # use hyperloop::task::Task;
//! # use hyperloop::executor::Executor;
//! async fn task_fn(flag: &AtomicBool) {
//!     flag.store(true, Ordering::Relaxed);
//! }
//!
//! static FLAG: AtomicBool = AtomicBool::new(false);
//!
//! let mut task = pin!(Task::new(task_fn(&FLAG), 1));
//! let mut executor = pin!(Executor::new([task.as_mut().get_handle()]));
//! let mut handle = executor.as_mut().get_handle();
//!
//! assert!(!FLAG.load(Ordering::Relaxed));
//!
//! handle.poll_tasks();
//! assert!(FLAG.load(Ordering::Relaxed));
//! ```

use core::cell::UnsafeCell;
use core::cmp::Ordering;
use core::pin::Pin;
use core::sync::atomic::{self, AtomicBool};
use core::task::{Poll, RawWaker, RawWakerVTable, Waker};

use priority_queue::{Max, PriorityQueue, PrioritySender};

use crate::task::{Priority, TaskHandle};

mod priority_queue;

type TaskId = u16;

struct Ticket {
    task: TaskId,
    priority: Priority,
}

impl Ticket {
    pub(crate) fn new(task: TaskId, priority: Priority) -> Self {
        Self { task, priority }
    }
}

impl PartialEq for Ticket {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}

impl Eq for Ticket {}

impl PartialOrd for Ticket {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Ticket {
    fn cmp(&self, other: &Self) -> Ordering {
        self.priority.cmp(&other.priority)
    }
}

type TaskSender = PrioritySender<Ticket>;

const VTABLE: RawWakerVTable = RawWakerVTable::new(clone, wake, wake, drop);

unsafe fn clone(ptr: *const ()) -> RawWaker {
    RawWaker::new(ptr, &VTABLE)
}

unsafe fn wake(ptr: *const ()) {
    let task = &*(ptr as *const ExecutorTask);
    task.wake();
}

unsafe fn drop(_ptr: *const ()) {}

struct ExecutorTask {
    task: TaskHandle,
    task_id: TaskId,
    priority: Priority,
    sender: Option<TaskSender>,
    pending_wake: AtomicBool,
}

impl ExecutorTask {
    fn new(
        task: TaskHandle,
        task_id: TaskId,
        priority: Priority,
        sender: Option<TaskSender>,
    ) -> Self {
        Self {
            task,
            task_id,
            priority,
            sender,
            pending_wake: AtomicBool::new(false),
        }
    }

    fn set_sender(&mut self, sender: TaskSender) {
        self.sender = Some(sender);
    }

    fn get_waker(task: *const ExecutorTask) -> Waker {
        let ptr: *const () = task.cast();
        let vtable = &VTABLE;

        unsafe { Waker::from_raw(RawWaker::new(ptr, vtable)) }
    }

    fn send_ticket(&self, ticket: Ticket) -> Result<(), ()> {
        let sender = unsafe { self.sender.as_ref().unwrap_unchecked() };

        sender.send(ticket).map_err(|_| ())
    }

    fn wake(&self) {
        if self
            .pending_wake
            .compare_exchange(
                false,
                true,
                atomic::Ordering::Acquire,
                atomic::Ordering::Acquire,
            )
            .is_ok()
        {
            let ticket = Ticket::new(self.task_id, self.priority);

            self.send_ticket(ticket).unwrap_or_else(|_| unreachable!());
        }
    }

    fn clear_pending_wake_flag(&self) {
        let _ = self.pending_wake.compare_exchange(
            true,
            false,
            atomic::Ordering::Acquire,
            atomic::Ordering::Acquire,
        );
    }

    fn poll(&mut self, waker: Waker) -> Poll<()> {
        self.task.poll(waker)
    }
}

/// Async executor
///
/// # Example
///```
/// # use core::sync::atomic::{AtomicBool, Ordering};
/// # use core::pin::pin;
/// # use hyperloop::task::Task;
/// # use hyperloop::executor::Executor;
/// async fn task_fn(flag: &AtomicBool) {
///     flag.store(true, Ordering::Relaxed);
/// }
///
/// static FLAG: AtomicBool = AtomicBool::new(false);
///
/// let mut task = pin!(Task::new(task_fn(&FLAG), 1));
/// let mut executor = pin!(Executor::new([task.as_mut().get_handle()]));
/// let mut handle = executor.as_mut().get_handle();
///
/// assert!(!FLAG.load(Ordering::Relaxed));
///
/// handle.poll_tasks();
/// assert!(FLAG.load(Ordering::Relaxed));
/// ```
pub struct Executor<const N: usize> {
    tasks: [UnsafeCell<ExecutorTask>; N],
    queue: PriorityQueue<Ticket, Max, N>,
}

impl<const N: usize> Executor<N> {
    /// Create new executor with tasks
    pub fn new(tasks: [TaskHandle; N]) -> Self {
        let mut i = 0;
        let tasks = tasks.map(|task| {
            let priority = task.priority;
            let task = UnsafeCell::new(ExecutorTask::new(task, i, priority, None));
            i += 1;
            task
        });

        Self {
            tasks,
            queue: PriorityQueue::new(),
        }
    }

    fn get_task(&mut self, task_id: TaskId) -> *mut ExecutorTask {
        self.tasks[task_id as usize].get()
    }

    fn init(self: Pin<&mut Self>) {
        let this = unsafe { self.get_unchecked_mut() };

        for i in 0..N {
            let sender = unsafe { this.queue.get_sender() };
            let task = unsafe { &mut *this.get_task(i as u16) };

            task.set_sender(sender);
            task.wake();
        }
    }

    fn poll_task(&mut self, task_id: TaskId) {
        let task = self.get_task(task_id);
        let waker = ExecutorTask::get_waker(task);
        let task = unsafe { &mut *task };

        task.clear_pending_wake_flag();

        let _ = task.poll(waker);
    }

    /// Poll all tasks in the queue
    fn poll_tasks(self: Pin<&mut Self>) {
        let this = unsafe { self.get_unchecked_mut() };

        while let Some(ticket) = this.queue.pop() {
            this.poll_task(ticket.task);
        }
    }

    /// Initialize and return handle to pinned `Executor`
    pub fn get_handle(mut self: Pin<&mut Self>) -> ExecutorHandle<N> {
        self.as_mut().init();

        ExecutorHandle { executor: self }
    }
}

/// Handle to pinned [`Executor`]
///
/// Use this to ensure pinned and initalized [`Executor`]. Use
/// [`Executor::get_handle`] to create handle.
pub struct ExecutorHandle<'a, const N: usize> {
    executor: Pin<&'a mut Executor<N>>,
}

impl<'a, const N: usize> ExecutorHandle<'a, N> {
    /// Poll all tasks in the queue
    pub fn poll_tasks(&mut self) {
        self.executor.as_mut().poll_tasks()
    }
}

#[cfg(test)]
mod tests {
    use core::task::Context;
    use crossbeam_queue::ArrayQueue;
    use futures::{task::AtomicWaker, Future};
    use std::sync::Arc;

    use super::*;
    use crate::task::Task;

    #[derive(Debug)]
    pub struct Notification {
        ready: AtomicBool,
        waker: AtomicWaker,
    }

    impl Notification {
        pub const fn new() -> Self {
            Self {
                ready: AtomicBool::new(false),
                waker: AtomicWaker::new(),
            }
        }

        pub fn notify(&self) {
            self.ready.store(true, atomic::Ordering::Relaxed);
            self.waker.wake();
        }

        pub fn wait(&self) -> NotificationFuture<'_> {
            self.ready.store(false, atomic::Ordering::Relaxed);
            NotificationFuture::new(&self)
        }
    }

    pub struct NotificationFuture<'a> {
        notification: &'a Notification,
    }

    impl<'a> NotificationFuture<'a> {
        fn new(shared: &'a Notification) -> Self {
            Self {
                notification: shared,
            }
        }
    }

    impl<'a> Future for NotificationFuture<'a> {
        type Output = ();

        fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            if self.notification.ready.load(atomic::Ordering::Relaxed) {
                Poll::Ready(())
            } else {
                self.notification.waker.register(cx.waker());
                Poll::Pending
            }
        }
    }

    #[test]
    fn test_executor() {
        let queue = Arc::new(ArrayQueue::new(10));

        let test_future = move |queue, value| {
            async fn future(queue: Arc<ArrayQueue<u32>>, value: u32) {
                queue.push(value).unwrap();
            }

            future(queue, value)
        };

        let mut task1 = Task::new(test_future(queue.clone(), 1), 1);
        let mut task2 = Task::new(test_future(queue.clone(), 2), 3);
        let mut task3 = Task::new(test_future(queue.clone(), 3), 2);
        let mut task4 = Task::new(test_future(queue.clone(), 4), 4);

        let mut executor = Executor::new([
            unsafe { Pin::new_unchecked(&mut task1) }.get_handle(),
            unsafe { Pin::new_unchecked(&mut task2) }.get_handle(),
            unsafe { Pin::new_unchecked(&mut task3) }.get_handle(),
            unsafe { Pin::new_unchecked(&mut task4) }.get_handle(),
        ]);
        let mut handle = unsafe { Pin::new_unchecked(&mut executor).get_handle() };

        handle.poll_tasks();

        assert_eq!(queue.pop().unwrap(), 4);
        assert_eq!(queue.pop().unwrap(), 2);
        assert_eq!(queue.pop().unwrap(), 3);
        assert_eq!(queue.pop().unwrap(), 1);
    }

    #[test]
    fn test_pending_wake() {
        let queue = Arc::new(ArrayQueue::new(10));
        let notify = Arc::new(Notification::new());

        let test_future = |queue, notify| {
            async fn future(queue: Arc<ArrayQueue<u32>>, notify: Arc<Notification>) {
                for i in 0..10 {
                    queue.push(i).unwrap();
                    notify.wait().await;
                }
            }

            future(queue, notify)
        };

        let mut task = Task::new(test_future(queue.clone(), notify.clone()), 1);

        let mut executor = Executor::new([unsafe { Pin::new_unchecked(&mut task).get_handle() }]);
        let mut handle = unsafe { Pin::new_unchecked(&mut executor).get_handle() };

        handle.poll_tasks();

        assert_eq!(queue.pop().unwrap(), 0);
        assert!(queue.pop().is_none());

        notify.notify();

        handle.poll_tasks();

        assert_eq!(queue.pop().unwrap(), 1);
        assert!(queue.pop().is_none());

        handle.poll_tasks();
        assert!(queue.pop().is_none());

        notify.notify();
        handle.poll_tasks();

        assert_eq!(queue.pop().unwrap(), 2);
        assert!(queue.pop().is_none());
    }
}
