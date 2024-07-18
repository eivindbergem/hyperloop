#![feature(type_alias_impl_trait)]

use crossbeam_queue::ArrayQueue;
use hyperloop::{static_executor, task};

use std::sync::Arc;

#[test]
fn macros() {
    #[task(priority = 1)]
    async fn test_task1(queue: Arc<ArrayQueue<u32>>) {
        queue.push(1).unwrap();
    }

    #[task(priority = 2)]
    async fn test_task2(queue: Arc<ArrayQueue<u32>>) {
        queue.push(2).unwrap();
    }

    let queue = Arc::new(ArrayQueue::new(10));

    let task1 = test_task1(queue.clone()).unwrap();
    let task2 = test_task2(queue.clone()).unwrap();

    let mut executor = static_executor!(task1, task2);

    executor.poll_tasks();

    assert_eq!(queue.pop().unwrap(), 2);
    assert_eq!(queue.pop().unwrap(), 1);
}
