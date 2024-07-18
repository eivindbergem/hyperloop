#![feature(type_alias_impl_trait)]

use std::{pin::pin, time::Duration};

use hyperloop::{
    executor::Executor,
    task,
    timer::{std::StdTimer, TimerQueue},
};

type Timer = hyperloop::timer::Timer<StdTimer>;

#[task(priority = 1)]
async fn hello(timer: Timer) {
    let mut periodic = timer.periodic(Duration::from_secs(1));
    let start = timer.now();

    loop {
        println!("Hello at {:?}", start.elapsed());
        periodic.wait().await;
    }
}

fn main() {
    let timer_queue = pin!(TimerQueue::new(StdTimer::new()));
    let mut executor = pin!(Executor::new([
        hello(timer_queue.as_ref().get_timer()).unwrap()
    ]));
    let mut handle = executor.as_mut().get_handle();

    loop {
        timer_queue.wake_tasks();
        handle.poll_tasks();

        timer_queue.wait_for_alarm();
    }
}
