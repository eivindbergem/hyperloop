//! Timer for delaying tasks and getting timestamp
//!
//! [`TimerQueue`] requires a hardware timer that implements
//! [`HardwareTimer`]. Two reference implementations are provided:
//! - [`cortex_m::SysTickTimer`] - A systick-based timer for Cortex-M systems
//! - [`std::StdTimer`] - A standard library based timer for testing in software

use core::{
    cell::UnsafeCell,
    ops::{Add, AddAssign},
    pin::Pin,
    task::{Context, Poll, Waker},
};

use core::future::Future;
use pinned_aliasable::Aliasable;

use self::list::{List, Node};

mod list;

#[cfg(feature = "cortex-m")]
#[doc(cfg(feature = "cortex-m"))]
pub mod cortex_m;

#[cfg(feature = "std")]
#[doc(cfg(feature = "std"))]
pub mod std;

/// Trait for interfacing with hardware timers.
///
/// Should provide monotonic time and the ability to set alarms. Check
/// out `systick::SysTickTimer` for a reference implementation.
pub trait HardwareTimer {
    type Instant: Ord
        + Eq
        + Copy
        + AddAssign<Self::Duration>
        + Add<Self::Duration, Output = Self::Instant>;
    type Duration: Copy;

    /// Start timer
    fn start(&self);

    /// Return current time
    fn now(&self) -> Self::Instant;

    /// Set alarm expiring at given instant. If None is provided, the
    /// alarm should be set to the maximum delay
    fn set_alarm(&self, expires: Option<Self::Instant>);

    /// Block until alarm expires
    fn wait_for_alarm(&self);
}

/// Timer queue for delayed tasks
pub struct TimerQueue<HW>
where
    HW: HardwareTimer,
{
    hw: UnsafeCell<HW>,
    queue: UnsafeCell<List<Ticket<HW::Instant>>>,
}

unsafe impl<HW> Sync for TimerQueue<HW> where HW: HardwareTimer {}
unsafe impl<HW> Send for TimerQueue<HW> where HW: HardwareTimer {}

impl<HW> TimerQueue<HW>
where
    HW: HardwareTimer,
{
    /// Create new timer queue
    pub fn new(hw: HW) -> Self {
        hw.start();

        Self {
            hw: UnsafeCell::new(hw),
            queue: UnsafeCell::new(List::new()),
        }
    }

    /// Return next exired waker, if any
    fn next_waker(&self) -> Option<Waker> {
        let queue = unsafe { &mut *self.queue.get() };
        let hw = unsafe { &*self.hw.get() };

        if let Some(peek) = queue.peek_mut() {
            let ticket = peek.get();

            if hw.now() > ticket.expires {
                let waker = ticket.waker.clone();
                unsafe { peek.pop() };
                return Some(waker);
            }
        }

        None
    }

    /// Get time of next expiring waker
    fn next_expiration(&self) -> Option<HW::Instant> {
        let queue = unsafe { &mut *self.queue.get() };

        if let Some(peek) = queue.peek_mut() {
            let ticket = peek.get();

            Some(ticket.expires)
        } else {
            None
        }
    }

    /// Set alarm at given instant. If none provided, sets the alarm
    /// to the maximum supported delay
    fn set_alarm(&self, expires: Option<HW::Instant>) {
        self.get_hw_timer().set_alarm(expires);
    }

    /// Block until alarm expires
    pub fn wait_for_alarm(&self) {
        self.get_hw_timer().wait_for_alarm()
    }

    /// Wake expired tasks, if any
    pub fn wake_tasks(&self) {
        while let Some(waker) = self.next_waker() {
            waker.wake();
        }
    }

    /// Return timer for use in tasks
    pub fn get_timer(self: Pin<&Self>) -> Timer<HW> {
        let hw = self.hw.get();
        let sender = self.queue.get();

        Timer::new(hw, sender)
    }

    /// Run interrupt handler
    pub fn interrupt_handler(&self) {
        self.set_alarm(self.next_expiration());
    }

    /// Return reference to hardware timer
    pub fn get_hw_timer(&self) -> &HW {
        unsafe { &*self.hw.get() }
    }

    #[cfg(test)]
    #[allow(clippy::mut_from_ref)]
    fn get_hw_timer_mut(&self) -> &mut HW {
        unsafe { &mut *self.hw.get() }
    }
}

/// Ticket used in timer queue
///
/// Contains expiration time and a waker
#[derive(Clone)]
struct Ticket<I> {
    expires: I,
    waker: Waker,
}

impl<I> Ticket<I> {
    fn new(expires: I, waker: Waker) -> Self {
        Self { expires, waker }
    }
}

impl<I> PartialEq for Ticket<I>
where
    I: Eq,
{
    fn eq(&self, other: &Self) -> bool {
        self.expires == other.expires
    }
}

impl<I> Eq for Ticket<I> where I: Eq + Ord {}

impl<I> PartialOrd for Ticket<I>
where
    I: Ord,
{
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<I> Ord for Ticket<I>
where
    I: Ord,
{
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.expires.cmp(&other.expires)
    }
}

/// Future for delaying a task until a given expiration time
struct DelayFuture<HW>
where
    HW: HardwareTimer,
{
    queue: *mut List<Ticket<HW::Instant>>,
    hw: *const HW,
    expires: HW::Instant,
    node: Option<Aliasable<UnsafeCell<Node<Ticket<HW::Instant>>>>>,
}

impl<C> Drop for DelayFuture<C>
where
    C: HardwareTimer,
{
    fn drop(&mut self) {
        // Make sure to unlink node if dropped before it's popped from
        // the queue
        if let Some(node) = &self.node {
            let node = unsafe { Pin::new_unchecked(node) };
            let node = node.get().get();

            unsafe { Node::unlink(node) };
        }
    }
}

impl<HW> DelayFuture<HW>
where
    HW: HardwareTimer,
{
    fn new(queue: *mut List<Ticket<HW::Instant>>, hw: *const HW, expires: HW::Instant) -> Self {
        Self {
            queue,
            hw,
            expires,
            node: None,
        }
    }

    unsafe fn get_queue_and_node(
        &mut self,
        cx: &mut Context<'_>,
    ) -> (
        &mut List<Ticket<HW::Instant>>,
        &mut Node<Ticket<HW::Instant>>,
    ) {
        let queue = unsafe { &mut *self.queue };
        self.node = Some(Aliasable::new(UnsafeCell::new(Node::new(Ticket::new(
            self.expires,
            cx.waker().clone(),
        )))));

        let node = &mut *Aliasable::get(Pin::new_unchecked(self.node.as_ref().unwrap())).get();

        (queue, node)
    }
}

impl<HW> Future for DelayFuture<HW>
where
    HW: HardwareTimer,
{
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = unsafe { Pin::get_unchecked_mut(self) };
        let hw = unsafe { &*this.hw };

        // Check if future has been added to the queue yet
        if this.node.is_none() {
            // Add node to queue and set alarm. Always return pending
            // on first await, even if time has already expired
            let (queue, node) = unsafe { this.get_queue_and_node(cx) };
            unsafe { queue.insert(node) };

            hw.set_alarm(Some(this.expires));
            Poll::Pending
        } else {
            // Delay until tick count is greater than the
            // expiration. This ensures that we wait for no less than
            // the specified duration, and possibly one tick longer
            // than desired.

            if this.expires > hw.now() {
                hw.set_alarm(Some(this.expires));
                Poll::Pending
            } else {
                Poll::Ready(())
            }
        }
    }
}

#[derive(Eq, PartialEq, Debug)]
pub struct TimeoutError {}

/// Future that wraps around another future, cancelling if awaiting
/// doesn't finish before the expiration time. Uses `DelayFuture`
/// under the hood.
struct TimeoutFuture<F, HW>
where
    F: Future,
    HW: HardwareTimer,
{
    future: F,
    delay: DelayFuture<HW>,
}

impl<F, HW> TimeoutFuture<F, HW>
where
    F: Future,
    HW: HardwareTimer,
{
    fn new(
        future: F,
        sender: *mut List<Ticket<HW::Instant>>,
        hw: *const HW,
        expires: HW::Instant,
    ) -> Self {
        Self {
            future,
            delay: DelayFuture::new(sender, hw, expires),
        }
    }
}

impl<F, HW> Future for TimeoutFuture<F, HW>
where
    F: Future,
    HW: HardwareTimer,
{
    type Output = Result<F::Output, TimeoutError>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let (future, delay) = unsafe {
            let this = self.get_unchecked_mut();
            (
                Pin::new_unchecked(&mut this.future),
                Pin::new_unchecked(&mut this.delay),
            )
        };

        // Poll the inner future first, then if it not ready, check
        // to see if the delay has expired
        if let Poll::Ready(ret) = future.poll(cx) {
            Poll::Ready(Ok(ret))
        } else if let Poll::Ready(()) = delay.poll(cx) {
            // If the delay has expired, return a timeout error
            Poll::Ready(Err(TimeoutError {}))
        } else {
            Poll::Pending
        }
    }
}

/// Periodic delay maintaing a constant frequency.
///
/// Create with [`Timer::periodic`].
pub struct Periodic<HW>
where
    HW: HardwareTimer,
{
    queue: *mut List<Ticket<HW::Instant>>,
    hw: *const HW,
    period: HW::Duration,
    previous: HW::Instant,
}

impl<HW> Periodic<HW>
where
    HW: HardwareTimer,
{
    fn new(queue: *mut List<Ticket<HW::Instant>>, hw: *const HW, period: HW::Duration) -> Self {
        let previous = unsafe { (*hw).now() };

        Self {
            queue,
            hw,
            period,
            previous,
        }
    }

    /// Wait till next period
    pub fn wait(&mut self) -> impl Future<Output = ()> {
        self.previous += self.period;

        DelayFuture::new(self.queue, self.hw, self.previous)
    }
}

/// Handle for timer
#[derive(Clone)]
pub struct Timer<HW>
where
    HW: HardwareTimer,
{
    hw: *const HW,
    sender: *mut List<Ticket<HW::Instant>>,
}

impl<HW> Timer<HW>
where
    HW: HardwareTimer,
{
    fn new(hw: *const HW, sender: *mut List<Ticket<HW::Instant>>) -> Self {
        Self { hw, sender }
    }

    /// Get expiration time from duration
    fn expiration(&self, duration: HW::Duration) -> HW::Instant {
        (unsafe { (*self.hw).now() }) + duration
    }

    /// Delay for duration
    ///
    /// # Example
    /// ```
    /// # use hyperloop::timer::TimerQueue;
    /// # use hyperloop::timer::std::StdTimer;
    /// # use std::time::Duration;
    /// # use std::pin::pin;
    /// # let mut queue = pin!(TimerQueue::new(StdTimer::new()));
    /// # let timer = queue.as_ref().get_timer();
    /// timer.delay(Duration::from_millis(1));
    /// ```
    pub fn delay(&self, duration: HW::Duration) -> impl Future<Output = ()> {
        self.delay_until(self.expiration(duration))
    }

    /// Delay until deadline
    ///
    /// # Example
    /// ```
    /// # use hyperloop::timer::TimerQueue;
    /// # use hyperloop::timer::std::StdTimer;
    /// # use std::time::Duration;
    /// # use std::pin::pin;
    /// # let mut queue = pin!(TimerQueue::new(StdTimer::new()));
    /// # let timer = queue.as_ref().get_timer();
    /// timer.delay_until(timer.now() + Duration::from_millis(10));
    /// ```
    pub fn delay_until(&self, deadline: HW::Instant) -> impl Future<Output = ()> {
        DelayFuture::new(self.sender, self.hw, deadline)
    }

    /// Drop future if not ready by expiration
    ///
    /// # Example
    /// ```
    /// # use hyperloop::timer::TimerQueue;
    /// # use hyperloop::timer::std::StdTimer;
    /// # use hyperloop::task::yield_now;
    /// # use std::time::Duration;
    /// # use std::pin::pin;
    /// # let mut queue = pin!(TimerQueue::new(StdTimer::new()));
    /// # let timer = queue.as_ref().get_timer();
    /// async fn never_ends() {
    ///     loop {
    ///         yield_now().await;
    ///     }
    /// }
    ///
    /// timer.timeout(never_ends(), Duration::from_millis(100));
    /// ```
    pub fn timeout<F: Future>(
        &self,
        future: F,
        duration: HW::Duration,
    ) -> impl Future<Output = Result<F::Output, TimeoutError>> {
        TimeoutFuture::new(future, self.sender, self.hw, self.expiration(duration))
    }

    /// Consistent periodic delay without drift
    ///
    /// # Example
    /// ```
    /// # use hyperloop::timer::{Timer, HardwareTimer};
    /// # async fn periodic_task<HW: HardwareTimer>(timer: Timer<HW>, period: HW::Duration) {
    /// let mut periodic = timer.periodic(period);
    ///
    /// loop {
    ///     // Do some periodic work here
    ///
    ///     // Wait until next period
    ///     periodic.wait().await;
    /// }
    /// # }
    /// ```

    pub fn periodic(&self, duration: HW::Duration) -> Periodic<HW> {
        Periodic::new(self.sender, self.hw, duration)
    }

    /// Return current time
    pub fn now(&self) -> HW::Instant {
        unsafe { (*self.hw).now() }
    }
}

#[cfg(test)]
mod tests {
    use ::std::pin::pin;
    use core::sync::atomic::{AtomicBool, Ordering};
    use core::time::Duration;

    use crate::common::tests::MockWaker;
    use crate::executor::Executor;
    use crate::task::Task;

    use super::*;

    use ::std::sync::Arc;
    use crossbeam_queue::ArrayQueue;

    const TICK: Duration = Duration::from_millis(1);

    #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
    struct MockInstant {
        instant: Duration,
    }

    impl MockInstant {
        fn from_ticks(ticks: u32) -> Self {
            Self {
                instant: TICK * ticks,
            }
        }

        fn ticks(&self) -> u128 {
            self.instant.as_millis()
        }
    }

    impl Add<Duration> for MockInstant {
        type Output = Self;

        fn add(self, rhs: Duration) -> Self::Output {
            let instant = self.instant + rhs;

            Self { instant }
        }
    }

    impl AddAssign<Duration> for MockInstant {
        fn add_assign(&mut self, rhs: Duration) {
            self.instant += rhs;
        }
    }

    #[derive(Clone)]
    struct MockHardwareTimer {
        time: Duration,
    }

    impl MockHardwareTimer {
        fn new() -> Self {
            Self {
                time: Duration::ZERO,
            }
        }

        fn add(&mut self, duration: Duration) {
            self.time = self.time.checked_add(duration).unwrap();
        }

        fn tick(&mut self) {
            self.add(TICK);
        }

        fn ticks(&self) -> u128 {
            self.time.as_millis()
        }
    }

    impl HardwareTimer for MockHardwareTimer {
        type Instant = MockInstant;
        type Duration = Duration;

        fn now(&self) -> Self::Instant {
            MockInstant { instant: self.time }
        }

        fn set_alarm(&self, _duration: Option<Self::Instant>) {}

        fn start(&self) {}

        fn wait_for_alarm(&self) {}
    }

    #[test]
    fn state() {
        let queue = TimerQueue::new(MockHardwareTimer::new());

        assert_eq!(unsafe { (*queue.hw.get()).ticks() }, 0);
        assert_eq!(unsafe { (*queue.hw.get()).ticks() }, 0);

        unsafe {
            (*queue.hw.get()).tick();
        }

        assert_eq!(unsafe { (*queue.hw.get()).ticks() }, 1);

        unsafe {
            (*queue.hw.get()).tick();
        }

        assert_eq!(unsafe { (*queue.hw.get()).ticks() }, 2);
    }

    #[test]
    fn delay() {
        let queue = pin!(TimerQueue::new(MockHardwareTimer::new()));
        let timer = queue.as_ref().get_timer();

        let mockwaker = Arc::new(MockWaker::new());
        let waker: Waker = mockwaker.clone().into();
        let mut cx = Context::from_waker(&waker);

        let mut future1 = DelayFuture::new(timer.sender, timer.hw, MockInstant::from_ticks(1));

        assert_eq!(
            unsafe { Pin::new_unchecked(&mut future1).poll(&mut cx) },
            Poll::Pending
        );
        assert_eq!(
            unsafe { Pin::new_unchecked(&mut future1).poll(&mut cx) },
            Poll::Pending
        );
        assert_eq!(
            unsafe { Pin::new_unchecked(&mut future1).poll(&mut cx) },
            Poll::Pending
        );

        assert!(queue.next_waker().is_none());

        unsafe {
            (*queue.hw.get()).tick();
        }
        unsafe {
            (*queue.hw.get()).tick();
        }

        let waker = queue.next_waker().unwrap();

        waker.wake();
        assert!(mockwaker.woke.load(Ordering::Relaxed));
        assert_eq!(
            unsafe { Pin::new_unchecked(&mut future1).poll(&mut cx) },
            Poll::Ready(())
        );
    }

    #[test]
    fn delay2() {
        let queue = pin!(TimerQueue::new(MockHardwareTimer::new()));
        let timer = queue.as_ref().get_timer();

        let mockwaker = Arc::new(MockWaker::new());
        let waker: Waker = mockwaker.clone().into();
        let mut cx = Context::from_waker(&waker);

        let mut future1 = DelayFuture::new(timer.sender, timer.hw, MockInstant::from_ticks(1));

        assert_eq!(
            unsafe { Pin::new_unchecked(&mut future1).poll(&mut cx) },
            Poll::Pending
        );
        assert_eq!(
            unsafe { Pin::new_unchecked(&mut future1).poll(&mut cx) },
            Poll::Pending
        );
        assert_eq!(
            unsafe { Pin::new_unchecked(&mut future1).poll(&mut cx) },
            Poll::Pending
        );

        unsafe {
            (*queue.hw.get()).tick();
        }
        unsafe {
            (*queue.hw.get()).tick();
        }

        assert_eq!(
            unsafe { Pin::new_unchecked(&mut future1).poll(&mut cx) },
            Poll::Ready(())
        );

        let mut future2 = DelayFuture::new(timer.sender, timer.hw, MockInstant::from_ticks(20));

        assert_eq!(
            unsafe { Pin::new_unchecked(&mut future2).poll(&mut cx) },
            Poll::Pending
        );

        let mut future3 = DelayFuture::new(timer.sender, timer.hw, MockInstant::from_ticks(15));

        assert_eq!(
            unsafe { Pin::new_unchecked(&mut future3).poll(&mut cx) },
            Poll::Pending
        );

        if let Some(ticket) = unsafe { (*queue.queue.get()).pop() } {
            let ticket = unsafe { &*ticket };
            assert_eq!(ticket.expires.ticks(), 1);
            ticket.waker.wake_by_ref();
            assert!(mockwaker.woke.load(Ordering::Relaxed))
        }

        if let Some(ticket) = unsafe { (*queue.queue.get()).pop() } {
            let ticket = unsafe { &*ticket };
            assert_eq!(ticket.expires.ticks(), 15);
        }

        if let Some(ticket) = unsafe { (*queue.queue.get()).pop() } {
            let ticket = unsafe { &*ticket };
            assert_eq!(ticket.expires.ticks(), 20);
        }
    }

    #[test]
    fn delay_until() {
        let queue = pin!(TimerQueue::new(MockHardwareTimer::new()));
        let timer = queue.as_ref().get_timer();

        let mockwaker = Arc::new(MockWaker::new());
        let waker: Waker = mockwaker.clone().into();
        let mut cx = Context::from_waker(&waker);

        unsafe {
            (*queue.hw.get()).tick();
        }

        let mut future1 = timer.delay_until(MockInstant::from_ticks(0));

        assert_eq!(
            unsafe { Pin::new_unchecked(&mut future1).poll(&mut cx) },
            Poll::Pending
        );

        assert_eq!(
            unsafe { Pin::new_unchecked(&mut future1).poll(&mut cx) },
            Poll::Ready(())
        );

        let mut future1 = timer.delay_until(MockInstant::from_ticks(2));

        for _ in 0..3 {
            assert_eq!(
                unsafe { Pin::new_unchecked(&mut future1).poll(&mut cx) },
                Poll::Pending
            );
        }

        unsafe {
            (*queue.hw.get()).tick();
            (*queue.hw.get()).tick();
        }

        assert_eq!(
            unsafe { Pin::new_unchecked(&mut future1).poll(&mut cx) },
            Poll::Ready(())
        );
    }

    #[test]
    fn timer() {
        let queue = pin!(TimerQueue::new(MockHardwareTimer::new()));
        let timer = queue.as_ref().get_timer();

        let test_future = |queue, timer| {
            async fn future(queue: Arc<ArrayQueue<u32>>, timer: Timer<MockHardwareTimer>) {
                queue.push(1).unwrap();

                timer.delay(Duration::ZERO).await;

                queue.push(2).unwrap();

                timer.delay(TICK).await;

                queue.push(3).unwrap();

                timer.delay(TICK).await;

                queue.push(4).unwrap();

                timer.delay(TICK).await;

                queue.push(5).unwrap();

                timer.delay(TICK * 10).await;

                queue.push(6).unwrap();
            }

            future(queue, timer)
        };

        let array_queue = Arc::new(ArrayQueue::new(10));

        let mut task = Task::new(test_future(array_queue.clone(), timer.clone()), 1);

        let mut executor = Executor::new([unsafe { Pin::new_unchecked(&mut task).get_handle() }]);
        let mut executor_handle = unsafe { Pin::new_unchecked(&mut executor).get_handle() };

        executor_handle.poll_tasks();

        assert_eq!(array_queue.pop(), Some(1));
        assert_eq!(array_queue.pop(), None);

        unsafe {
            (*queue.hw.get()).tick();
        }
        queue.wake_tasks();
        executor_handle.poll_tasks();

        assert_eq!(array_queue.pop(), Some(2));
        assert_eq!(array_queue.pop(), None);

        queue.wake_tasks();
        executor_handle.poll_tasks();

        assert_eq!(array_queue.pop(), None);

        unsafe {
            (*queue.hw.get()).tick();
        }
        unsafe {
            (*queue.hw.get()).tick();
        }
        queue.wake_tasks();
        executor_handle.poll_tasks();

        assert_eq!(array_queue.pop(), Some(3));
        assert_eq!(array_queue.pop(), None);

        unsafe {
            (*queue.hw.get()).tick();
        }
        unsafe {
            (*queue.hw.get()).tick();
        }
        queue.wake_tasks();
        executor_handle.poll_tasks();

        assert_eq!(array_queue.pop(), Some(4));
        assert_eq!(array_queue.pop(), None);

        unsafe {
            (*queue.hw.get()).tick();
        }
        unsafe {
            (*queue.hw.get()).tick();
        }
        queue.wake_tasks();
        executor_handle.poll_tasks();

        assert_eq!(array_queue.pop(), Some(5));
        assert_eq!(array_queue.pop(), None);

        for _ in 0..10 {
            unsafe {
                (*queue.hw.get()).tick();
            }
            queue.wake_tasks();
            executor_handle.poll_tasks();

            assert_eq!(array_queue.pop(), None);
        }

        unsafe {
            (*queue.hw.get()).tick();
        }
        queue.wake_tasks();
        executor_handle.poll_tasks();

        assert_eq!(array_queue.pop(), Some(6));
        assert_eq!(array_queue.pop(), None);
    }

    #[test]
    fn nested() {
        let queue = pin!(TimerQueue::new(MockHardwareTimer::new()));
        let timer = queue.as_ref().get_timer();
        let flag = Arc::new(AtomicBool::new(false));

        async fn inner(timer: Timer<MockHardwareTimer>) {
            timer.delay(Duration::from_millis(100)).await;
        }

        async fn outer(timer: Timer<MockHardwareTimer>, flag: Arc<AtomicBool>) {
            assert_eq!(
                timer
                    .timeout(inner(timer.clone()), Duration::from_millis(50))
                    .await,
                Err(TimeoutError {})
            );

            assert_eq!(
                timer
                    .timeout(inner(timer.clone()), Duration::from_millis(200))
                    .await,
                Ok(())
            );

            flag.store(true, Ordering::Relaxed);
        }

        let mut task = Task::new(outer(timer.clone(), flag.clone()), 1);

        let mut executor = Executor::new([unsafe { Pin::new_unchecked(&mut task).get_handle() }]);
        let mut handle = unsafe { Pin::new_unchecked(&mut executor).get_handle() };

        handle.poll_tasks();

        unsafe {
            (*queue.hw.get()).add(Duration::from_millis(51));
        }

        queue.wake_tasks();
        handle.poll_tasks();

        unsafe {
            (*queue.hw.get()).add(Duration::from_millis(101));
        }

        queue.wake_tasks();
        handle.poll_tasks();

        assert!(flag.load(Ordering::Relaxed));

        unsafe {
            (*queue.hw.get()).add(Duration::from_millis(50));
        }

        assert!(queue.next_waker().is_none());
    }

    #[test]
    fn periodic() {
        let queue = pin!(TimerQueue::new(MockHardwareTimer::new()));
        let timer = queue.as_ref().get_timer();
        let array_queue = Arc::new(ArrayQueue::new(10));

        async fn task(timer: Timer<MockHardwareTimer>, queue: Arc<ArrayQueue<i32>>) {
            let mut periodic = timer.periodic(Duration::from_millis(100));

            for i in 0..4 {
                queue.push(i).unwrap();
                periodic.wait().await;
            }
        }

        let mut task = Task::new(task(timer, array_queue.clone()), 1);

        let mut executor = Executor::new([unsafe { Pin::new_unchecked(&mut task).get_handle() }]);
        let mut handle = unsafe { Pin::new_unchecked(&mut executor).get_handle() };

        queue.wake_tasks();
        handle.poll_tasks();

        assert_eq!(array_queue.pop(), Some(0));
        assert_eq!(array_queue.pop(), None);

        queue.wake_tasks();
        handle.poll_tasks();

        assert_eq!(array_queue.pop(), None);

        queue.get_hw_timer_mut().add(Duration::from_millis(50));

        queue.wake_tasks();
        handle.poll_tasks();

        assert_eq!(array_queue.pop(), None);

        queue.get_hw_timer_mut().add(Duration::from_millis(51));

        queue.wake_tasks();
        handle.poll_tasks();

        assert_eq!(array_queue.pop(), Some(1));
        assert_eq!(array_queue.pop(), None);

        queue.get_hw_timer_mut().add(Duration::from_millis(150));

        queue.wake_tasks();
        handle.poll_tasks();

        assert_eq!(array_queue.pop(), Some(2));
        assert_eq!(array_queue.pop(), None);

        queue.get_hw_timer_mut().add(Duration::from_millis(50));

        queue.wake_tasks();
        handle.poll_tasks();

        assert_eq!(array_queue.pop(), Some(3));
        assert_eq!(array_queue.pop(), None);
    }
}
