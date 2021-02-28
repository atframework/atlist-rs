use super::*;

use std::thread;
use std::vec::Vec;

use rand::{thread_rng, RngCore};

fn list_from<T: Clone>(v: &[T]) -> LinkedList<T> {
    v.iter().cloned().collect()
}

pub fn check_links<T>(list: &LinkedList<T>) {
    unsafe {
        let mut len = 0;
        let mut last_ptr: Option<&Node<T>> = None;
        let mut node_ptr: &Node<T>;
        match list.data.head {
            None => {
                // tail node should also be None.
                assert!(list.data.tail.is_none());
                assert_eq!(0, list.data.len);
                return;
            }
            Some(node) => {
                let left_guard = node.as_ref().read();
                let left = left_guard.as_ref().unwrap().container.as_ref();
                let right = &*list.data;
                assert!(ptr::eq(left, right));
                node_ptr = &*node.as_ptr()
            }
        }
        loop {
            match (last_ptr, node_ptr.read().unwrap().prev) {
                (None, None) => {}
                (None, _) => panic!("prev link for head"),
                (Some(p), Some(pptr)) => {
                    assert_eq!(p as *const Node<T>, pptr.as_ptr() as *const Node<T>);
                }
                _ => panic!("prev link is none, not good"),
            }
            match node_ptr.read().unwrap().next {
                Some(next) => {
                    let left_guard = next.as_ref().read();
                    let left = left_guard.as_ref().unwrap().container.as_ref();
                    let right = &*list.data;
                    assert!(ptr::eq(left, right));

                    last_ptr = Some(node_ptr);
                    node_ptr = &*next.as_ptr();
                    len += 1;
                }
                None => {
                    len += 1;
                    break;
                }
            }
        }

        // verify that the tail node points to the last node.
        let tail = list.data.tail.as_ref().expect("some tail node").as_ref();
        assert_eq!(tail as *const Node<T>, node_ptr as *const Node<T>);
        // check that len matches interior links.
        assert_eq!(len, list.data.len);
    }
}

#[test]
fn test_clone_from() {
    // Short cloned from long
    {
        let v = vec![1, 2, 3, 4, 5];
        let u = vec![8, 7, 6, 2, 3, 4, 5];
        let mut m = list_from(&v);
        let n = list_from(&u);
        m.clone_from(&n);
        check_links(&m);
        assert_eq!(m, n);
        for elt in u {
            assert_eq!(*m.pop_front().unwrap().as_ref().read().unwrap(), elt)
        }
    }
    // Long cloned from short
    {
        let v = vec![1, 2, 3, 4, 5];
        let u = vec![6, 7, 8];
        let mut m = list_from(&v);
        let n = list_from(&u);
        m.clone_from(&n);
        check_links(&m);
        assert_eq!(m, n);
        for elt in u {
            assert_eq!(*m.pop_front().unwrap().as_ref().read().unwrap(), elt)
        }
    }
    // Two equal length lists
    {
        let v = vec![1, 2, 3, 4, 5];
        let u = vec![9, 8, 1, 2, 3];
        let mut m = list_from(&v);
        let n = list_from(&u);
        m.clone_from(&n);
        check_links(&m);
        assert_eq!(m, n);
        for elt in u {
            assert_eq!(*m.pop_front().unwrap().as_ref().read().unwrap(), elt)
        }
    }
}

#[test]
fn test_fuzz() {
    for _ in 0..25 {
        fuzz_test(3);
        fuzz_test(16);
        #[cfg(not(miri))] // Miri is too slow
        fuzz_test(189);
    }
}

fn fuzz_test(sz: i32) {
    let mut m: LinkedList<_> = LinkedList::new();
    let mut v = vec![];
    for i in 0..sz {
        check_links(&m);
        let r: u8 = thread_rng().next_u32() as u8;
        match r % 6 {
            0 => {
                let _ = m.pop_back();
                v.pop();
            }
            1 => {
                if !v.is_empty() {
                    let _ = m.pop_front();
                    v.remove(0);
                }
            }
            2 | 4 => {
                let _ = m.push_front(-i);
                v.insert(0, -i);
            }
            3 | 5 | _ => {
                let _ = m.push_back(i);
                v.push(i);
            }
        }
    }

    check_links(&m);

    let mut i = 0;
    for (a, &b) in m.into_iter().zip(&v) {
        i += 1;
        assert_eq!(*a.as_ref().read().unwrap(), b);
    }
    assert_eq!(i, v.len());
}
