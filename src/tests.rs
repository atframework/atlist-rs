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

    let mut iter = m.iter_back();
    assert_eq!(*iter.unwrap().as_ref(), 6);
    assert_eq!(*iter.next().unwrap().as_ref(), 6);
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next_back(), None);
    assert_eq!(*iter.unwrap().as_ref(), 6);
    assert_eq!(*iter.next_back().unwrap().as_ref(), 6);
    assert_eq!(*iter.unwrap().as_ref(), 5);

    let mut m: LinkedList<u32> = LinkedList::new();
    m.extend(&[1, 2, 3, 4, 5, 6]);
    let mut iter = m.iter_mut();
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

    let mut iter = m.iter_mut_back();
    assert_eq!(*iter.unwrap().as_ref(), 6);
    assert_eq!(*iter.next().unwrap().as_ref(), 6);
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next_back(), None);
    assert_eq!(*iter.unwrap().as_ref(), 6);
    assert_eq!(*iter.next_back().unwrap().as_ref(), 6);
    assert_eq!(*iter.unwrap().as_ref(), 5);
}

#[test]
fn test_iter_mut_insert() {
    let mut m: LinkedList<u32> = LinkedList::new();
    m.extend(&[1, 2, 3, 4, 5, 6]);
    let iter = m.iter_mut_front();
    assert!(m.insert_before(&iter, 7).is_ok());
    assert!(m.insert_after(&iter, 8).is_ok());
    check_links(&m);

    assert_eq!(
        m.iter().map(|elt| *elt.as_ref()).collect::<Vec<_>>(),
        &[7, 1, 8, 2, 3, 4, 5, 6]
    );

    let mut iter = m.iter_mut_front();
    assert_eq!(*iter.next_back().unwrap().as_ref(), 7);
    assert!(m.insert_before(&iter, 9).is_ok());
    assert!(m.insert_after(&iter, 10).is_ok());
    check_links(&m);
    assert_eq!(
        m.iter().map(|elt| *elt.as_ref()).collect::<Vec<_>>(),
        &[10, 7, 1, 8, 2, 3, 4, 5, 6, 9]
    );

    let mut iter = m.iter_mut_front();
    assert_eq!(*iter.next_back().unwrap().as_ref(), 10);
    assert_eq!(
        m.remove_iter_mut(&mut iter),
        Err(LinkedListError::IteratorNotInList)
    );
    assert_eq!(iter.next(), None);
    assert_eq!(*iter.next().unwrap().as_ref(), 10);
    assert_eq!(*m.remove_iter_mut(&mut iter).unwrap(), 7);
    assert_eq!(iter.try_unwrap(), Err(LinkedListError::IteratorNotInList));
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next_back(), None);
    assert_eq!(*iter.next().unwrap().as_ref(), 9);

    let mut iter = m.iter_mut_back();
    let _ = iter.next();
    let _ = iter.next_back();
    assert_eq!(*m.remove_iter_mut(&mut iter).unwrap(), 9);
    assert_eq!(iter.try_unwrap(), Err(LinkedListError::IteratorNotInList));
    assert_eq!(iter.next_back(), None);
    assert_eq!(iter.next(), None);
    assert_eq!(*iter.next_back().unwrap().as_ref(), 10);

    let mut iter = m.iter_mut();
    assert_eq!(*m.remove_iter_mut(&mut iter).unwrap(), 10);
    assert_eq!(iter.try_unwrap(), Err(LinkedListError::IteratorNotInList));
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next_back(), None);
    assert_eq!(*iter.next().unwrap().as_ref(), 6);

    check_links(&m);
    assert_eq!(
        m.iter().map(|elt| *elt.as_ref()).collect::<Vec<_>>(),
        &[1, 8, 2, 3, 4, 5, 6]
    );
}

#[test]
fn test_iter_mut_insert_into_empty_list() {
    let mut m: LinkedList<u32> = LinkedList::new();
    let iter = m.iter_mut();

    assert!(m.insert_before(&iter, 3).is_ok());
    assert!(m.insert_after(&iter, 2).is_ok());
    assert!(m.insert_before(&iter, 4).is_ok());
    assert!(m.insert_after(&iter, 1).is_ok());

    check_links(&m);
    assert_eq!(
        m.iter().map(|elt| *elt.as_ref()).collect::<Vec<_>>(),
        &[1, 2, 3, 4]
    );
}

#[test]
fn test_iter_len_is_empty() {
    let mut m: LinkedList<u32> = LinkedList::new();
    m.extend(&[1]);
    let mut iter = m.iter();
    assert!(!iter.is_empty());
    assert_eq!(iter.clone().count(), 1);
    assert_eq!(iter.size_hint(), (1, None));
    let _ = iter.next_back();
    assert!(iter.is_empty());
    assert_eq!(iter.clone().count(), 0);
    assert_eq!(iter.size_hint(), (0, None));

    let mut iter = m.iter_mut();
    assert!(!iter.is_empty());
    assert_eq!(iter.clone().count(), 1);
    assert_eq!(iter.size_hint(), (1, None));
    let _ = iter.next_back();
    assert!(iter.is_empty());
    assert_eq!(iter.clone().count(), 0);
    assert_eq!(iter.size_hint(), (0, None));
}

#[test]
fn test_document_list_len() {
    let mut dl = LinkedList::new();

    let _ = dl.push_front(2);
    assert_eq!(dl.len(), 1);

    let _ = dl.push_front(1);
    assert_eq!(dl.len(), 2);

    let _ = dl.push_back(3);
    assert_eq!(dl.len(), 3);
}

#[test]
fn test_document_list_is_empty() {
    let mut dl = LinkedList::new();
    assert!(dl.is_empty());

    let _ = dl.push_front("foo");
    assert!(!dl.is_empty());
}

#[test]
fn test_document_list_front() {
    let mut dl = LinkedList::new();
    assert_eq!(dl.front(), Err(LinkedListError::Empty));

    let _ = dl.push_front(1);
    assert_eq!(*dl.front().unwrap(), 1);
}

#[test]
fn test_document_list_back() {
    let mut dl = LinkedList::new();
    assert_eq!(dl.back(), Err(LinkedListError::Empty));

    let _ = dl.push_back(1);
    assert_eq!(*dl.back().unwrap(), 1);
}

#[test]
fn test_document_list_contains_iter() {
    let mut list: LinkedList<u32> = LinkedList::new();
    let mut another_list: LinkedList<u32> = LinkedList::new();

    let _ = list.push_back(0);
    let _ = list.push_back(1);
    let _ = another_list.push_back(2);

    assert_eq!(list.contains_iter(&list.iter()), Ok(()));
    assert_eq!(
        list.contains_iter(&another_list.iter()),
        Err(LinkedListError::IteratorNotInList)
    );
}

#[test]
fn test_document_list_contains_iter_mut() {
    let mut list: LinkedList<u32> = LinkedList::new();
    let mut another_list: LinkedList<u32> = LinkedList::new();

    let _ = list.push_back(0);
    let _ = list.push_back(1);
    let _ = another_list.push_back(2);

    let iter = list.iter_mut();
    let another_iter = another_list.iter_mut();
    assert_eq!(list.contains_iter_mut(&iter), Ok(()));
    assert_eq!(
        list.contains_iter_mut(&another_iter),
        Err(LinkedListError::IteratorNotInList)
    );
}
