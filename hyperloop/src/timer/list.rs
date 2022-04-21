use core::{cell::UnsafeCell, marker::PhantomData, pin::Pin};

use pinned_aliasable::Aliasable;

pub struct PeekMut<'a, T> {
    node: *mut Node<T>,
    _marker: PhantomData<&'a ()>,
}

impl<'a, T> PeekMut<'a, T>
where
    T: Ord,
{
    pub fn get(&self) -> &T {
        let node = unsafe { &*self.node };
        node.get_item()
    }

    pub unsafe fn pop(self) -> *const T {
        Node::unlink(self.node);
        self.get()
    }
}

struct Sentinel<T> {
    next: ForwardLink<T>,
}

impl<T> Sentinel<T> {
    fn new() -> Self {
        Self {
            next: ForwardLink::Empty,
        }
    }
}

pub struct List<T> {
    sentinel: Aliasable<UnsafeCell<Sentinel<T>>>,
}

impl<T: Ord> List<T> {
    pub fn new() -> Self {
        Self {
            sentinel: Aliasable::new(UnsafeCell::new(Sentinel::new())),
        }
    }

    #[allow(clippy::mut_from_ref)]
    unsafe fn get_sentinel(&self) -> &mut Sentinel<T> {
        unsafe { &mut *Aliasable::get(Pin::new_unchecked(&self.sentinel)).get() }
    }

    pub unsafe fn insert(&mut self, new_node: *mut Node<T>) {
        let mut link = self.get_sentinel().next.clone();
        let mut prev: Option<*mut Node<T>> = None; // link.get_node().unwrap();

        loop {
            let backlink = if let Some(node) = prev {
                BackwardLink::Node(node)
            } else {
                BackwardLink::List(self)
            };

            match link {
                ForwardLink::Empty => {
                    (*new_node).link(backlink, ForwardLink::Empty);
                    break;
                }
                ForwardLink::Node(node) => {
                    if (*node).get_item() > (*new_node).get_item() {
                        (*new_node).link(backlink, ForwardLink::Node(node));

                        break;
                    } else {
                        prev = Some(node);
                        link = (*node).next.clone();
                    }
                }
            }
        }
    }

    pub fn peek_mut(&mut self) -> Option<PeekMut<T>> {
        let head = unsafe { self.get_sentinel().next.clone() };

        match head {
            ForwardLink::Empty => None,
            ForwardLink::Node(node) => Some(PeekMut {
                node,
                _marker: PhantomData,
            }),
        }
    }

    #[cfg(test)]
    pub unsafe fn pop(&mut self) -> Option<*const T> {
        self.peek_mut().map(|peek_mut| peek_mut.pop())
    }

    #[cfg(test)]
    fn drain(&mut self) -> Vec<T>
    where
        T: Copy,
    {
        let mut v = Vec::new();

        while let Some(item) = unsafe { self.pop() } {
            let item = unsafe { &*item };
            v.push(*item);
        }

        v
    }
}

impl<T: Ord> Default for List<T> {
    fn default() -> Self {
        Self::new()
    }
}

enum ForwardLink<T> {
    Empty,
    Node(*mut Node<T>),
}

impl<T> Clone for ForwardLink<T> {
    fn clone(&self) -> Self {
        match self {
            Self::Empty => Self::Empty,
            Self::Node(arg0) => Self::Node(*arg0),
        }
    }
}

enum BackwardLink<T> {
    Empty,
    Node(*mut Node<T>),
    List(*mut List<T>),
}

impl<T> Clone for BackwardLink<T> {
    fn clone(&self) -> Self {
        match self {
            Self::Empty => Self::Empty,
            Self::Node(arg0) => Self::Node(*arg0),
            Self::List(arg0) => Self::List(*arg0),
        }
    }
}

pub struct Node<T> {
    item: T,
    next: ForwardLink<T>,
    prev: BackwardLink<T>,
}

impl<T> Node<T>
where
    T: Ord,
{
    pub fn new(item: T) -> Self {
        Self {
            item,
            next: ForwardLink::Empty,
            prev: BackwardLink::Empty,
        }
    }

    unsafe fn link(&mut self, prev: BackwardLink<T>, next: ForwardLink<T>) {
        self.prev = prev;
        self.next = next;

        match self.prev {
            BackwardLink::Node(node) => {
                let node = unsafe { &mut *node };
                node.next = ForwardLink::Node(self);
            }
            BackwardLink::List(list) => {
                let list = unsafe { &mut *list };
                let sentinel = unsafe { list.get_sentinel() };
                sentinel.next = ForwardLink::Node(self);
            }
            BackwardLink::Empty => unreachable!(),
        }

        match self.next {
            ForwardLink::Empty => (),
            ForwardLink::Node(node) => {
                let node = unsafe { &mut *node };
                node.prev = BackwardLink::Node(self);
            }
        }
    }

    fn get_item(&self) -> &T {
        &self.item
    }

    pub unsafe fn unlink(node: *mut Self) {
        let node = unsafe { &mut *node };

        match node.prev {
            BackwardLink::Empty => (),
            BackwardLink::Node(prev) => {
                let prev = unsafe { &mut *prev };
                prev.next = node.next.clone();
            }
            BackwardLink::List(list) => {
                let list = unsafe { &mut *list };
                let sentinel = unsafe { list.get_sentinel() };
                sentinel.next = node.next.clone();
            }
        }

        match node.next {
            ForwardLink::Empty => (),
            ForwardLink::Node(next) => {
                let next = unsafe { &mut *next };
                next.prev = node.prev.clone();
            }
        }

        node.prev = BackwardLink::Empty;
        node.next = ForwardLink::Empty;
    }
}

#[cfg(test)]
mod tests {
    use core::cell::UnsafeCell;

    use super::*;

    #[test]
    fn linked_list() {
        let mut root = List::new();
        let list = &mut root;

        let items = (0..10)
            .map(|i| UnsafeCell::new(Node::new(i)))
            .collect::<Vec<_>>();

        for item in &items {
            let node = item;
            unsafe { list.insert(node.get()) };
        }

        let mut v = Vec::new();

        while let Some(item) = unsafe { list.pop() } {
            let item = unsafe { &*item };
            v.push(*item);
        }

        assert_eq!(v, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn reversed() {
        let mut root = List::new();
        let list = &mut root;

        let items = (0..10)
            .rev()
            .map(|i| UnsafeCell::new(Node::new(i)))
            .collect::<Vec<_>>();

        for item in &items {
            let node = item;
            unsafe { list.insert(node.get()) };
        }

        let mut v = Vec::new();

        while let Some(item) = unsafe { list.pop() } {
            let item = unsafe { &*item };
            v.push(*item);
        }

        assert_eq!(v, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn order() {
        let mut root = List::new();
        let list = &mut root;

        let items = [1, 20, 15]
            .iter()
            .copied()
            .map(|i| UnsafeCell::new(Node::new(i)))
            .collect::<Vec<_>>();

        for item in &items {
            let node = item;
            unsafe { list.insert(node.get()) };
        }

        let mut v = Vec::new();

        while let Some(item) = unsafe { list.pop() } {
            let item = unsafe { &*item };
            v.push(*item);
        }

        assert_eq!(v, [1, 15, 20]);
    }

    #[test]
    fn remove() {
        let root = UnsafeCell::new(List::new());

        for i in 0..3 {
            let nodes = [1, 2, 3]
                .iter()
                .copied()
                .map(|i| UnsafeCell::new(Node::new(i)))
                .collect::<Vec<_>>();

            for node in &nodes {
                let list = unsafe { &mut *root.get() };
                unsafe { list.insert(node.get()) };
            }

            unsafe { Node::unlink(nodes[i].get()) };

            let mut expected = vec![1, 2, 3];
            expected.remove(i);

            let list = unsafe { &mut *root.get() };
            assert_eq!(list.drain(), expected);
        }
    }
}
