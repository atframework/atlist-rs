use super::*;

use std::iter::IntoIterator;
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
        match list.data.get_head() {
            None => {
                // tail node should also be None.
                assert!(list.data.get_tail().is_none());
                assert_eq!(0, list.data.len);
                return;
            }
            Some(node) => {
                let left_guard = node.as_ref().read();
                assert!(left_guard.as_ref().unwrap().prev.is_none());

                let left = left_guard.as_ref().unwrap().end.as_ptr();
                let right = Arc::as_ptr(&list.data.end);
                assert!(ptr::eq(left, right));
                assert!(!ptr::eq(Arc::as_ptr(node.as_ref()), right));
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

            len += 1;
            match node_ptr.read().unwrap().next {
                Some(next) => {
                    let left_guard = next.as_ref().read().unwrap();
                    let left = left_guard.end.as_ptr();
                    let right = Arc::as_ptr(&list.data.end);
                    assert!(ptr::eq(left, right));
                    assert!(!ptr::eq(Arc::as_ptr(next.as_ref()), right));

                    last_ptr = Some(node_ptr);
                    node_ptr = &*next.as_ptr();
                }
                None => {
                    break;
                }
            }
        }

        // verify that the tail node points to the last node.
        let tail = list.data.get_tail().expect("some tail node");
        let tail_ptr = &*tail.as_ptr();
        assert_eq!(tail_ptr as *const Node<T>, node_ptr as *const Node<T>);
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
            assert_eq!(*m.pop_front().unwrap().as_ref(), elt)
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
            assert_eq!(*m.pop_front().unwrap().as_ref(), elt)
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
            assert_eq!(*m.pop_front().unwrap().as_ref(), elt)
        }
    }
}

#[test]
#[cfg_attr(target_os = "emscripten", ignore)]
fn test_send() {
    let n = list_from(&[1, 2, 3]);
    thread::spawn(move || {
        check_links(&n);
        let a: &[_] = &[&1, &2, &3];
        let b = n.iter().map(|x| *x.as_ref()).collect::<Vec<_>>();
        assert_eq!(a, &*b.iter().collect::<Vec<_>>());
    })
    .join()
    .ok()
    .unwrap();
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
        assert_eq!(*a.as_ref(), b);
    }
    assert_eq!(i, v.len());
}

#[test]
fn test_iter_move_peek() {
    let mut m: LinkedList<u32> = LinkedList::new();
    let n = [1, 2, 3, 4, 5, 6];
    m.extend(&n);
    let mut iter = m.iter();
    assert_eq!(*iter.unwrap().as_ref(), 1);
    assert_eq!(*iter.next().unwrap().as_ref(), 1);
    assert_eq!(*iter.next().unwrap().as_ref(), 2);
    assert_eq!(*iter.unwrap().as_ref(), 3);
    assert_eq!(*iter.next_back().unwrap().as_ref(), 3);
    assert_eq!(*iter.next_back().unwrap().as_ref(), 2);
    assert_eq!(*iter.next_back().unwrap().as_ref(), 1);
    assert_eq!(iter.next_back(), None);
    assert_eq!(iter.try_unwrap(), Err(LinkedListError::IteratorNotInList));
    assert_eq!(iter.next(), None);
    assert_eq!(*iter.unwrap().as_ref(), 1);

    /*
    assert_eq!(iter.current(), None);
    assert_eq!(iter.peek_next(), Some(&1));
    assert_eq!(iter.peek_prev(), Some(&6));
    assert_eq!(iter.index(), None);
    iter.move_next();
    iter.move_next();
    assert_eq!(iter.current(), Some(&2));
    assert_eq!(iter.peek_next(), Some(&3));
    assert_eq!(iter.peek_prev(), Some(&1));
    assert_eq!(iter.index(), Some(1));

    let mut iter = m.cursor_back();
    assert_eq!(iter.current(), Some(&6));
    assert_eq!(iter.peek_next(), None);
    assert_eq!(iter.peek_prev(), Some(&5));
    assert_eq!(iter.index(), Some(5));
    iter.move_next();
    assert_eq!(iter.current(), None);
    assert_eq!(iter.peek_next(), Some(&1));
    assert_eq!(iter.peek_prev(), Some(&6));
    assert_eq!(iter.index(), None);
    iter.move_prev();
    iter.move_prev();
    assert_eq!(iter.current(), Some(&5));
    assert_eq!(iter.peek_next(), Some(&6));
    assert_eq!(iter.peek_prev(), Some(&4));
    assert_eq!(iter.index(), Some(4));

    let mut m: LinkedList<u32> = LinkedList::new();
    m.extend(&[1, 2, 3, 4, 5, 6]);
    let mut iter = m.cursor_front_mut();
    assert_eq!(iter.current(), Some(&mut 1));
    assert_eq!(iter.peek_next(), Some(&mut 2));
    assert_eq!(iter.peek_prev(), None);
    assert_eq!(iter.index(), Some(0));
    iter.move_prev();
    assert_eq!(iter.current(), None);
    assert_eq!(iter.peek_next(), Some(&mut 1));
    assert_eq!(iter.peek_prev(), Some(&mut 6));
    assert_eq!(iter.index(), None);
    iter.move_next();
    iter.move_next();
    assert_eq!(iter.current(), Some(&mut 2));
    assert_eq!(iter.peek_next(), Some(&mut 3));
    assert_eq!(iter.peek_prev(), Some(&mut 1));
    assert_eq!(iter.index(), Some(1));
    let mut cursor2 = iter.as_cursor();
    assert_eq!(cursor2.current(), Some(&2));
    assert_eq!(cursor2.index(), Some(1));
    cursor2.move_next();
    assert_eq!(cursor2.current(), Some(&3));
    assert_eq!(cursor2.index(), Some(2));
    assert_eq!(iter.current(), Some(&mut 2));
    assert_eq!(iter.index(), Some(1));

    let mut m: LinkedList<u32> = LinkedList::new();
    m.extend(&[1, 2, 3, 4, 5, 6]);
    let mut iter = m.cursor_back_mut();
    assert_eq!(iter.current(), Some(&mut 6));
    assert_eq!(iter.peek_next(), None);
    assert_eq!(iter.peek_prev(), Some(&mut 5));
    assert_eq!(iter.index(), Some(5));
    iter.move_next();
    assert_eq!(iter.current(), None);
    assert_eq!(iter.peek_next(), Some(&mut 1));
    assert_eq!(iter.peek_prev(), Some(&mut 6));
    assert_eq!(iter.index(), None);
    iter.move_prev();
    iter.move_prev();
    assert_eq!(iter.current(), Some(&mut 5));
    assert_eq!(iter.peek_next(), Some(&mut 6));
    assert_eq!(iter.peek_prev(), Some(&mut 4));
    assert_eq!(iter.index(), Some(4));
    let mut cursor2 = iter.as_cursor();
    assert_eq!(cursor2.current(), Some(&5));
    assert_eq!(cursor2.index(), Some(4));
    cursor2.move_prev();
    assert_eq!(cursor2.current(), Some(&4));
    assert_eq!(cursor2.index(), Some(3));
    assert_eq!(iter.current(), Some(&mut 5));
    assert_eq!(iter.index(), Some(4));
    */
}
