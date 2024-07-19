use std::ops::Index;

#[derive(Copy, Clone, Debug)]
pub struct Node<T: Copy + Clone> {
    addr: usize,
    next: Option<usize>,
    prev: Option<usize>,
    symbol: T,
}

impl<T: Copy + Clone> Node<T> {
    fn new(addr: usize, next: Option<usize>, prev: Option<usize>, symbol: T) -> Self {
        Node {
            addr,
            next,
            prev,
            symbol,
        }
    }

    pub fn get_prev(&self) -> Option<usize> {
        self.prev
    }

    pub fn get_next(&self) -> Option<usize> {
        self.next
    }

    pub fn get_addr(&self) -> usize {
        self.addr
    }

    pub fn get_symbol(&self) -> T {
        self.symbol
    }
}

pub struct DLL<T: Copy + Clone> {
    list: Vec<Node<T>>,
    head: Option<usize>,
    tail: Option<usize>,
    free: Vec<usize>,
}

impl<T: Copy + Clone> DLL<T> {
    pub fn new() -> Self {
        DLL {
            list: Vec::new(),
            head: None,
            tail: None,
            free: Vec::new(),
        }
    }

    fn alloc_node(&mut self, next: Option<usize>, prev: Option<usize>, symbol: T) -> usize {
        match self.free.pop() {
            Some(addr) => {
                self.list[addr] = Node::new(addr, next, prev, symbol);
                addr
            }
            None => {
                let addr = self.list.len();
                self.list.push(Node::new(addr, next, prev, symbol));
                addr
            }
        }
    }

    pub fn get_head(&self) -> Option<usize> {
        self.head
    }

    pub fn get_tail(&self) -> Option<usize> {
        self.tail
    }

    pub fn push_after(&mut self, idx: usize, symbol: T) -> usize {
        let node = self.list[idx];
        let new_idx = self.alloc_node(node.next, Some(node.addr), symbol);

        if let Some(next_idx) = node.next {
            self.list[next_idx].prev = Some(new_idx);
        } else {
            self.tail = Some(new_idx);
        }
        self.list[node.addr].next = Some(new_idx);
        new_idx
    }

    pub fn push(&mut self, symbol: T) -> usize {
        match self.tail {
            None => {
                let free_idx = self.alloc_node(None, None, symbol);
                self.head = Some(free_idx);
                self.tail = Some(free_idx);
                free_idx
            }
            Some(tail) => {
                let free_idx = self.alloc_node(None, Some(tail), symbol);
                self.list[tail].next = Some(free_idx);
                self.tail = Some(free_idx);
                free_idx
            }
        }
    }

    pub fn pop(&mut self, idx: usize) -> Node<T> {
        let node = self.list[idx];

        if let Some(prev) = node.prev {
            self.list[prev].next = node.next;
        }

        if let Some(next) = node.next {
            self.list[next].prev = node.prev;
        }

        if let Some(head) = self.head {
            if head == idx {
                self.head = node.next;
            }
        }

        if let Some(tail) = self.tail {
            if tail == idx {
                self.tail = node.prev
            }
        }

        self.free.push(idx);
        node
    }

    pub fn to_vec(&self) -> Vec<T> {
        let mut v = vec![];

        let mut p = self.head;

        while let Some(next) = p {
            let curr = self.list[next];
            v.push(curr.symbol);
            p = curr.next;
        }
        v
    }
}

impl<T: Copy + Clone> Index<usize> for DLL<T> {
    type Output = Node<T>;
    fn index(&self, index: usize) -> &Node<T> {
        &self.list[index]
    }
}

#[cfg(test)]
mod test_dll {
    use super::*;
    #[test]
    fn test_push() {
        let s = "abab";
        let mut dll = DLL::new();

        for c in s.chars() {
            dll.push(c);
        }

        assert_eq!(dll.list.len(), s.chars().count());
        assert_eq!(dll.to_vec(), s.chars().collect::<Vec<char>>());
    }

    #[test]
    fn test_push_after() {
        let mut dll = DLL::new();
        let (a, b, c) = ('a', 'b', 'c');
        let fst = dll.push(a);
        let snd = dll.push(b);
        let trd = dll.push(a);
        let fth = dll.push(b);
        assert_eq!(dll.to_vec(), vec![a, b, a, b]);

        dll.push_after(fst, c);
        assert_eq!(dll.to_vec(), vec![a, c, b, a, b]);

        dll.push_after(snd, c);
        assert_eq!(dll.to_vec(), vec![a, c, b, c, a, b]);

        dll.push_after(trd, c);
        assert_eq!(dll.to_vec(), vec![a, c, b, c, a, c, b]);

        dll.push_after(fth, c);
        assert_eq!(dll.to_vec(), vec![a, c, b, c, a, c, b, c]);
    }

    #[test]
    fn test_push_pop() {
        let mut dll = DLL::new();

        let (a, b, c) = ('a', 'b', 'c');

        let fst = dll.push(a);
        let snd = dll.push(b);
        let trd = dll.push(a);
        let fth = dll.push(b);

        assert_eq!(dll.head, Some(fst));
        assert_eq!(dll.tail, Some(fth));

        dll.pop(fst);
        assert_eq!(dll.head, Some(snd));
        assert_eq!(dll.tail, Some(fth));

        let mid = dll.push_after(snd, c);
        dll.pop(snd);
        assert_eq!(dll.head, Some(mid));

        assert_eq!(dll[trd].prev, Some(mid));
    }

    #[test]
    fn test_append_with_push_after() {
        let mut dll = DLL::new();

        let (a, b) = ('a', 'b');

        let fst = dll.push(a);

        assert_eq!(dll.head, Some(fst));
        assert_eq!(dll.tail, Some(fst));

        let snd = dll.push_after(fst, a);
        assert_eq!(dll.head, Some(fst));
        assert_eq!(dll.tail, Some(snd));

        let trd = dll.push(b);
        assert_eq!(dll.tail, Some(trd));
        assert_eq!(dll[dll.tail.unwrap()].prev, Some(snd));

        let fth = dll.push_after(trd, b);
        assert_eq!(dll.tail, Some(fth));
        assert_eq!(dll.to_vec(), vec![a, a, b, b]);
    }
}
