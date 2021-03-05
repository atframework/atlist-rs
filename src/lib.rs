// MIT License

// Copyright (c) 2021 OWenT

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

//! A LinkedList which is allowed to insert/remove element by immutable iterator.
//! Adding, removing and moving the elements within the list or across several lists
//! does not invalidate the iterators or references. An iterator is invalidated only
//! when the corresponding element is deleted.
//!
//! ## Example
//!

//#![no_std]
#![cfg_attr(feature = "nightly", feature(negative_impls, auto_traits))]

use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::iter::{Extend, FromIterator, FusedIterator};
use core::marker;
use core::mem;
use core::pin::Pin;
use core::ptr;
use core::ptr::NonNull;
use core::result::Result;
use core::usize;
use std::{borrow::BorrowMut, error::Error};
use std::{
    ops::Deref,
    sync::{Arc, PoisonError, RwLock, TryLockError, Weak},
};

//#[cfg(test)]
//extern crate rand;

#[cfg(test)]
mod tests;

#[derive(PartialEq, PartialOrd, Eq, Ord)]
pub enum LinkedListError {
    /// Try mutex lock failed
    TryLockError(String),
    /// Iterator is not in specified LinkedList
    IteratorNotInList,
    /// LinkedList or iterator is empty
    Empty,
    /// LinkedList inner bad data
    BadData,
}

impl fmt::Display for LinkedListError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            &LinkedListError::TryLockError(ref e) => write!(f, "Try lock failed: {}", e),
            LinkedListError::IteratorNotInList => write!(f, "Iterator not in list"),
            LinkedListError::Empty => write!(f, "LinkedList or iterator is empty"),
            LinkedListError::BadData => write!(f, "LinkedList or iterator bad data"),
        }
    }
}

impl fmt::Debug for LinkedListError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            &LinkedListError::TryLockError(ref e) => write!(f, "Try lock failed: {}", e),
            LinkedListError::IteratorNotInList => write!(f, "Iterator not in list"),
            LinkedListError::Empty => write!(f, "LinkedList or iterator is empty"),
            LinkedListError::BadData => write!(f, "LinkedList or iterator bad data"),
        }
    }
}

impl Error for LinkedListError {
    #[allow(deprecated)] // call to `description`
    fn description(&self) -> &str {
        match self {
            &LinkedListError::TryLockError(_) => &"LinkedList or iterator lock failed",
            LinkedListError::IteratorNotInList => &"Iterator not in list",
            LinkedListError::Empty => &"LinkedList or iterator is empty",
            LinkedListError::BadData => &"LinkedList or iterator bad data",
        }
    }

    fn cause(&self) -> Option<&dyn Error> {
        match self {
            e => Some(e),
        }
    }
}

impl<'a, T> From<PoisonError<T>> for LinkedListError {
    fn from(err: PoisonError<T>) -> Self {
        LinkedListError::TryLockError(format!("{}", err))
    }
}

impl<'a, T> From<TryLockError<T>> for LinkedListError {
    fn from(err: TryLockError<T>) -> Self {
        LinkedListError::TryLockError(format!("{}", err))
    }
}

pub type LinkedListResult<T> = Result<T, LinkedListError>;
pub type LinkedListItem<T> = Arc<T>;
type Node<T> = Arc<RwLock<NodeEntry<T>>>;

struct NodeEntry<T> {
    next: Option<NonNull<Node<T>>>,
    prev: Option<NonNull<Node<T>>>,
    element: Option<LinkedListItem<T>>,
    end: Weak<RwLock<NodeEntry<T>>>,
    leak: Option<NonNull<Node<T>>>,
}

struct UnmoveableLinkedList<T> {
    end: Node<T>,
    len: usize,
}

pub struct LinkedList<T> {
    data: Pin<Box<UnmoveableLinkedList<T>>>,
}

pub struct Iter<T> {
    node: Weak<RwLock<NodeEntry<T>>>,
    last_back: bool,
}

pub struct IterMut<T> {
    node: Weak<RwLock<NodeEntry<T>>>,
    last_back: bool,
}

fn check_iter_valid<T>(iter: &Iter<T>) -> bool {
    iter.node.strong_count() > 0
}

fn check_iter_mut_valid<T>(iter: &IterMut<T>) -> bool {
    iter.node.strong_count() > 0
}

impl<T> NodeEntry<T> {
    #[inline]
    fn new(elt: T, container: &mut Pin<Box<UnmoveableLinkedList<T>>>) -> Box<Node<T>> {
        NodeEntry::from(Arc::new(elt), container)
    }

    fn from(
        elt: LinkedListItem<T>,
        container: &mut Pin<Box<UnmoveableLinkedList<T>>>,
    ) -> Box<Node<T>> {
        let container = unsafe { Pin::get_unchecked_mut(container.as_mut()) };
        let ret = NodeEntry {
            next: None,
            prev: None,
            element: Some(elt),
            end: Arc::downgrade(&container.end),
            leak: None,
        };

        Box::new(Arc::new(RwLock::new(ret)))
    }

    #[inline]
    fn uninited_new() -> Node<T> {
        let ret = NodeEntry {
            next: None,
            prev: None,
            element: None,
            end: Weak::default(),
            leak: None,
        };

        Arc::new(RwLock::new(ret))
    }
}

impl<T: fmt::Debug> fmt::Debug for Iter<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(x) = self.node.upgrade() {
            let current_node = match x.read() {
                Ok(x) => x,
                Err(e) => {
                    return write!(f, "Iter: Locked: {:?}", e);
                }
            };

            f.debug_tuple("Iter").field(&current_node.element).finish()
        } else {
            f.debug_tuple("Iter: Empty").finish()
        }
    }
}

impl<T> Clone for Iter<T> {
    fn clone(&self) -> Self {
        Iter {
            node: self.node.clone(),
            last_back: false,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for IterMut<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(x) = self.node.upgrade() {
            let current_node = match x.read() {
                Ok(x) => x,
                Err(e) => {
                    return write!(f, "IterMut: Locked: {:?}", e);
                }
            };

            f.debug_tuple("IterMut")
                .field(&current_node.element)
                .finish()
        } else {
            f.debug_tuple("IterMut: Empty").finish()
        }
    }
}

impl<T> Iterator for Iter<T> {
    type Item = LinkedListItem<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let watcher = self.node.upgrade()?;
        let node = match watcher.read() {
            Ok(x) => x,
            Err(_) => {
                return None;
            }
        };

        if !self.last_back && node.element.is_none() {
            return None;
        }

        let next_node = if let Some(next_watcher) = node.next {
            unsafe { Arc::downgrade(next_watcher.as_ref()) }
        } else {
            node.end.clone()
        };
        self.node = next_node;
        self.last_back = false;

        node.element.clone()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if check_iter_valid(&self) {
            (1, None)
        } else {
            (0, None)
        }
    }

    fn count(self) -> usize {
        self.size_hint().0
    }
}

impl<T> Iterator for IterMut<T> {
    type Item = LinkedListItem<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let watcher = self.node.upgrade()?;
        let node = match watcher.read() {
            Ok(x) => x,
            Err(_) => {
                return None;
            }
        };

        if !self.last_back && node.element.is_none() {
            return None;
        }

        let next_node = if let Some(next_watcher) = node.next {
            unsafe { Arc::downgrade(next_watcher.as_ref()) }
        } else {
            node.end.clone()
        };
        self.node = next_node;
        self.last_back = false;

        node.element.clone()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if check_iter_mut_valid(&self) {
            (1, None)
        } else {
            (0, None)
        }
    }

    fn count(self) -> usize {
        self.size_hint().0
    }
}

impl<T> DoubleEndedIterator for Iter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let watcher = self.node.upgrade()?;
        let node = match watcher.read() {
            Ok(x) => x,
            Err(_) => {
                return None;
            }
        };

        if self.last_back && node.element.is_none() {
            return None;
        }

        let prev_node = if let Some(prev_watcher) = node.prev {
            unsafe { Arc::downgrade(prev_watcher.as_ref()) }
        } else {
            node.end.clone()
        };
        self.node = prev_node;
        self.last_back = true;

        node.element.clone()
    }
}

impl<T> DoubleEndedIterator for IterMut<T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let watcher = self.node.upgrade()?;
        let node = match watcher.read() {
            Ok(x) => x,
            Err(_) => {
                return None;
            }
        };

        if self.last_back && node.element.is_none() {
            return None;
        }

        let prev_node = if let Some(prev_watcher) = node.prev {
            unsafe { Arc::downgrade(prev_watcher.as_ref()) }
        } else {
            node.end.clone()
        };
        self.node = prev_node;
        self.last_back = true;

        node.element.clone()
    }
}

impl<T> FusedIterator for Iter<T> {}
impl<T> FusedIterator for IterMut<T> {}

impl<T> Iter<T> {
    fn new() -> Iter<T> {
        Iter {
            node: Weak::new(),
            last_back: false,
        }
    }

    fn from(node: &Node<T>) -> Iter<T> {
        Iter {
            node: Arc::downgrade(&node),
            last_back: false,
        }
    }

    fn from_weak(node: Weak<RwLock<NodeEntry<T>>>) -> Iter<T> {
        Iter {
            node: node,
            last_back: false,
        }
    }

    pub fn try_unwrap(&self) -> LinkedListResult<LinkedListItem<T>> {
        let watcher = if let Some(x) = self.node.upgrade() {
            x
        } else {
            return Err(LinkedListError::IteratorNotInList);
        };

        let guard = watcher.read()?;
        if guard.element.is_none() {
            return Err(LinkedListError::IteratorNotInList);
        }

        let ret = guard.element.as_ref().unwrap().clone();
        drop(guard);
        Ok(ret)
    }

    pub fn unwrap(&self) -> LinkedListItem<T> {
        self.try_unwrap().unwrap()
    }

    pub fn is_empty(&self) -> bool {
        check_iter_valid(self)
    }
}

impl<T> IterMut<T> {
    fn new() -> IterMut<T> {
        IterMut {
            node: Weak::new(),
            last_back: false,
        }
    }

    fn from(node: &Node<T>) -> IterMut<T> {
        IterMut {
            node: Arc::downgrade(&node),
            last_back: false,
        }
    }

    fn from_weak(node: Weak<RwLock<NodeEntry<T>>>) -> IterMut<T> {
        IterMut {
            node: node,
            last_back: false,
        }
    }

    pub fn try_unwrap(&self) -> LinkedListResult<LinkedListItem<T>> {
        let watcher = if let Some(x) = self.node.upgrade() {
            x
        } else {
            return Err(LinkedListError::IteratorNotInList);
        };

        let guard = watcher.read()?;
        if guard.element.is_none() {
            return Err(LinkedListError::IteratorNotInList);
        }

        let ret = guard.element.as_ref().unwrap().clone();
        drop(guard);
        Ok(ret)
    }

    pub fn unwrap(&self) -> LinkedListItem<T> {
        self.try_unwrap().unwrap()
    }

    pub fn is_empty(&self) -> bool {
        check_iter_mut_valid(self)
    }
}

#[doc(hidden)]
struct LinkedListCheckContainerResult<T> {
    current_is_end: bool,
    current: NonNull<Node<T>>,
    prev: Option<NonNull<Node<T>>>,
    next: Option<NonNull<Node<T>>>,
}

impl<T> UnmoveableLinkedList<T> {
    /// Unlinks the specified node from the current list.
    ///
    /// Warning: this will not check that the provided node belongs to the current list.
    #[inline]
    fn unlink_node(&mut self, node: NonNull<Node<T>>) -> LinkedListResult<LinkedListItem<T>> {
        let mut node = unsafe { node.as_ref() }.write()?;
        if node.leak.is_none() {
            return Err(LinkedListError::BadData);
        }

        if node.prev.is_none() && node.next.is_none() && self.len > 0 {
            // Bad data
            return Err(LinkedListError::BadData);
        }

        if node.element.is_none() {
            return Err(LinkedListError::IteratorNotInList);
        }

        if node.prev == node.next {
            let mut prev_next_node = if let Some(x) = &node.prev {
                Some(unsafe { x.as_ref() }.write()?)
            } else {
                None
            };

            match &mut prev_next_node {
                Some(prev_next) => {
                    prev_next.next = node.next;
                    prev_next.prev = node.prev;
                }
                None => {
                    self.set_head(node.next);
                    self.set_tail(node.next);
                }
            };
        } else {
            let mut prev_node = if let Some(x) = &node.prev {
                Some(unsafe { x.as_ref() }.write()?)
            } else {
                None
            };

            let mut next_node = if let Some(x) = &node.next {
                Some(unsafe { x.as_ref() }.write()?)
            } else {
                None
            };

            match &mut prev_node {
                Some(prev) => prev.next = node.next,
                None => self.set_head(node.next),
            };

            match &mut next_node {
                Some(next) => next.prev = node.prev,
                // this node is the tail node
                None => self.set_tail(node.prev),
            };
        }

        self.len -= 1;

        let unlinked_node = unsafe { Box::from_raw(node.leak.unwrap().as_ptr()) };

        node.prev = None;
        node.next = None;
        node.leak = None;

        let ret = node.element.as_ref().unwrap().clone();

        drop(node);
        drop(unlinked_node);

        Ok(ret)
    }

    /// Splices a series of nodes between two existing nodes.
    ///
    /// Warning: this will not check that the provided node belongs to the two existing lists.
    #[inline]
    fn splice_node(
        &mut self,
        existing_prev: Option<NonNull<Node<T>>>,
        existing_next: Option<NonNull<Node<T>>>,
        splice_node: Box<Node<T>>,
    ) -> LinkedListResult<IterMut<T>> {
        let splice_node_rc = splice_node.as_ref().clone();
        let mut lock_node = splice_node_rc.write()?;
        if lock_node.leak.is_some() {
            return Err(LinkedListError::BadData);
        }

        // This method takes care not to create multiple mutable references to whole nodes at the same time,
        // to maintain validity of aliasing pointers into `element`.

        let leak_node;
        if existing_prev == existing_next {
            let mut prev_next_node = if let Some(x) = &existing_prev {
                Some(unsafe { x.as_ref() }.write()?)
            } else {
                None
            };

            leak_node = Box::leak(splice_node).into();

            if let Some(prev_next) = &mut prev_next_node {
                prev_next.next = Some(leak_node);
                prev_next.prev = Some(leak_node);
            } else {
                self.set_head(Some(leak_node));
                self.set_tail(Some(leak_node));
            }

            lock_node.leak = Some(leak_node);
        } else {
            let mut prev_node = if let Some(x) = &existing_prev {
                Some(unsafe { x.as_ref() }.write()?)
            } else {
                None
            };

            let mut next_node = if let Some(x) = &existing_next {
                Some(unsafe { x.as_ref() }.write()?)
            } else {
                None
            };

            leak_node = Box::leak(splice_node).into();

            if let Some(prev) = &mut prev_node {
                prev.next = Some(leak_node);
            } else {
                self.set_head(Some(leak_node));
            }
            if let Some(next) = &mut next_node {
                next.prev = Some(leak_node);
            } else {
                self.set_tail(Some(leak_node));
            }
        }

        lock_node.prev = existing_prev;
        lock_node.next = existing_next;
        lock_node.leak = Some(leak_node);

        self.len += 1;

        Ok(IterMut::from(unsafe { leak_node.as_ref() }))
    }

    /// Adds the given node to the front of the list.
    #[inline]
    fn push_front_node(&mut self, node: Box<Node<T>>) -> LinkedListResult<()> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        let node_rc = node.as_ref().clone();
        let mut lock_node = node_rc.write()?;

        let head_node_rc = match self.get_head() {
            None => None,
            Some(head) => Some(unsafe { head.as_ref() }.clone()),
        };

        let head_node = match &head_node_rc {
            None => None,
            Some(head) => Some(head.write()?),
        };

        lock_node.next = self.get_head();
        lock_node.prev = None;
        lock_node.leak = Some(Box::leak(node).into());

        match head_node {
            None => self.set_tail(lock_node.leak),
            Some(mut head) => head.prev = lock_node.leak,
        }

        self.set_head(lock_node.leak);
        self.len += 1;

        Ok(())
    }

    /// Removes and returns the node at the front of the list.
    #[inline]
    fn pop_front_node(&mut self) -> LinkedListResult<Box<Node<T>>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        let head_nonull = self.get_head();
        if head_nonull.is_none() {
            return Err(LinkedListError::Empty);
        }

        let node = head_nonull.unwrap();
        let mut head_node = unsafe { node.as_ref() }.write()?;
        if head_node.element.is_none() {
            return Err(LinkedListError::Empty);
        }

        let next_node_rc = match head_node.next {
            None => None,
            Some(next) => Some(unsafe { next.as_ref() }.clone()),
        };

        let next_node = match &next_node_rc {
            None => None,
            Some(next) => Some(next.write()?),
        };

        if head_node.leak.is_none() {
            return Err(LinkedListError::BadData);
        }

        let ret = unsafe { Box::from_raw(head_node.leak.unwrap().as_ptr()) };
        self.set_head(head_node.next);
        head_node.next = None;
        head_node.leak = None;

        match next_node {
            None => self.set_tail(None),
            Some(mut next) => next.prev = None,
        }

        self.len -= 1;

        Ok(ret)
    }

    /// Adds the given node to the back of the list.
    #[inline]
    fn push_back_node(&mut self, node: Box<Node<T>>) -> LinkedListResult<()> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        let node_rc = node.as_ref().clone();
        let mut lock_node = node_rc.write()?;

        let tail_node_rc = match self.get_tail() {
            None => None,
            Some(tail) => Some(unsafe { tail.as_ref() }.clone()),
        };

        let tail_node = match &tail_node_rc {
            None => None,
            Some(tail) => Some(tail.as_ref().write()?),
        };

        lock_node.next = None;
        lock_node.prev = self.get_tail();
        lock_node.leak = Some(Box::leak(node).into());

        match tail_node {
            None => self.set_head(lock_node.leak),
            Some(mut tail) => tail.next = lock_node.leak,
        }

        self.set_tail(lock_node.leak);
        self.len += 1;

        Ok(())
    }

    /// Removes and returns the node at the back of the list.
    #[inline]
    fn pop_back_node(&mut self) -> LinkedListResult<Box<Node<T>>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        let tail_nonull = self.get_tail();
        if tail_nonull.is_none() {
            return Err(LinkedListError::Empty);
        }

        let node = tail_nonull.unwrap();
        let mut tail_node = unsafe { node.as_ref() }.write()?;
        if tail_node.element.is_none() {
            return Err(LinkedListError::Empty);
        }

        let prev_node_rc = match tail_node.prev {
            None => None,
            Some(prev) => Some(unsafe { prev.as_ref() }.clone()),
        };
        let prev_node = match &prev_node_rc {
            None => None,
            Some(prev) => Some(prev.write()?),
        };

        if tail_node.leak.is_none() {
            return Err(LinkedListError::BadData);
        }

        let ret = unsafe { Box::from_raw(tail_node.leak.unwrap().as_ptr()) };
        self.set_tail(tail_node.prev);
        tail_node.prev = None;
        tail_node.leak = None;

        match prev_node {
            None => self.set_head(None),
            Some(mut prev) => prev.next = None,
        }

        self.len -= 1;

        Ok(ret)
    }

    #[inline]
    fn check_container(&self, x: &NodeEntry<T>) -> Option<LinkedListCheckContainerResult<T>> {
        if ptr::eq(x.end.as_ptr(), Arc::as_ptr(&self.end)) {
            x.leak.map(|y| LinkedListCheckContainerResult {
                next: x.next,
                prev: x.prev,
                current: y,
                current_is_end: x.element.is_none(),
            })
        } else {
            None
        }
    }

    #[inline]
    fn contains_iter(&self, x: &Iter<T>) -> LinkedListResult<LinkedListCheckContainerResult<T>> {
        let lock = if let Some(y) = x.node.upgrade() {
            y
        } else {
            return Err(LinkedListError::IteratorNotInList);
        };
        let lock = lock.read()?;
        match self.check_container(&lock) {
            Some(x) => Ok(x),
            None => Err(LinkedListError::IteratorNotInList),
        }
    }

    #[inline]
    fn contains_iter_mut(
        &self,
        x: &IterMut<T>,
    ) -> LinkedListResult<LinkedListCheckContainerResult<T>> {
        let lock = if let Some(y) = x.node.upgrade() {
            y
        } else {
            return Err(LinkedListError::IteratorNotInList);
        };
        let lock = lock.read()?;
        match self.check_container(&lock) {
            Some(x) => Ok(x),
            None => Err(LinkedListError::IteratorNotInList),
        }
    }

    #[inline]
    fn remove_iter(&mut self, iter: IterMut<T>) -> LinkedListResult<LinkedListItem<T>> {
        let node = self.contains_iter_mut(&iter)?;

        self.unlink_node(node.current)
    }
}

impl<T> UnmoveableLinkedList<T> {
    #[inline]
    fn new() -> Pin<Box<Self>> {
        let res = UnmoveableLinkedList {
            end: NodeEntry::uninited_new(),
            len: 0,
        };

        let mut boxed = Box::pin(res);
        let container = unsafe { Pin::get_unchecked_mut(boxed.as_mut()) };
        let container = unsafe { NonNull::new_unchecked(container) };
        let mut guard = boxed.end.write().unwrap();

        guard.borrow_mut().end = Arc::downgrade(&unsafe { container.as_ref() }.end);
        drop(guard);

        boxed
    }

    #[inline]
    fn get_head(&self) -> Option<NonNull<Node<T>>> {
        if let Ok(guard) = self.end.read() {
            guard.next
        } else {
            None
        }
    }

    #[inline]
    fn get_tail(&self) -> Option<NonNull<Node<T>>> {
        if let Ok(guard) = self.end.read() {
            guard.prev
        } else {
            None
        }
    }

    #[inline]
    fn set_head(&mut self, v: Option<NonNull<Node<T>>>) {
        self.end.write().unwrap().next = v;
    }

    #[inline]
    fn set_tail(&self, v: Option<NonNull<Node<T>>>) {
        self.end.write().unwrap().prev = v;
    }
}

impl<T> LinkedList<T> {
    #[inline]
    fn data_mut(&mut self) -> &mut UnmoveableLinkedList<T> {
        unsafe { Pin::get_unchecked_mut(self.data.as_mut()) }
    }

    #[inline]
    pub fn new() -> Self {
        let data = UnmoveableLinkedList::new();

        LinkedList { data: data }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.data.len
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        0 == self.data.len
    }

    /// Removes all elements from the `LinkedList`.
    ///
    /// This operation should compute in *O*(*n*) time.
    #[inline]
    pub fn clear(&mut self) {
        *self = Self::new();
    }

    #[inline]
    pub fn iter(&self) -> Iter<T> {
        self.iter_front()
    }

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<T> {
        self.iter_mut_front()
    }

    #[inline]
    pub fn iter_front(&self) -> Iter<T> {
        if let Some(head) = self.data.get_head() {
            Iter::from(unsafe { head.as_ref() })
        } else {
            Iter::new()
        }
    }

    #[inline]
    pub fn iter_back(&self) -> Iter<T> {
        if let Some(tail) = self.data.get_tail() {
            Iter::from(unsafe { tail.as_ref() })
        } else {
            Iter::new()
        }
    }

    #[inline]
    pub fn iter_mut_front(&mut self) -> IterMut<T> {
        if let Some(head) = self.data.get_head() {
            IterMut::from(unsafe { head.as_ref() })
        } else {
            IterMut::new()
        }
    }

    #[inline]
    pub fn iter_mut_back(&mut self) -> IterMut<T> {
        if let Some(tail) = self.data.get_tail() {
            IterMut::from(unsafe { tail.as_ref() })
        } else {
            IterMut::new()
        }
    }

    /// Adds an element first in the list.
    ///
    /// This operation should compute in *O*(1) time.
    pub fn push_front(&mut self, elt: T) -> LinkedListResult<()> {
        let node = NodeEntry::new(elt, &mut self.data);
        self.data_mut().push_front_node(node)
    }

    /// Removes the first element and returns it, or `None` if the list is
    /// empty.
    ///
    /// This operation should compute in *O*(1) time.
    pub fn pop_front(&mut self) -> LinkedListResult<LinkedListItem<T>> {
        let n = self.data_mut().pop_front_node()?;
        let ret = n.read()?;
        if ret.element.is_none() {
            return Err(LinkedListError::IteratorNotInList);
        }
        Ok(ret.element.as_ref().unwrap().clone())
    }

    /// Appends an element to the back of a list.
    ///
    /// This operation should compute in *O*(1) time.
    pub fn push_back(&mut self, elt: T) -> LinkedListResult<()> {
        let node = NodeEntry::new(elt, &mut self.data);
        self.data_mut().push_back_node(node)
    }

    /// Removes the last element from a list and returns it, or `None` if
    /// it is empty.
    ///
    /// This operation should compute in *O*(1) time.
    pub fn pop_back(&mut self) -> LinkedListResult<LinkedListItem<T>> {
        let n = self.data_mut().pop_back_node()?;
        let ret = n.read()?;
        if ret.element.is_none() {
            return Err(LinkedListError::IteratorNotInList);
        }
        Ok(ret.element.as_ref().unwrap().clone())
    }

    /// Provides a reference to the front element, or `None` if the list is
    /// empty.
    #[inline]
    pub fn front(&self) -> LinkedListResult<LinkedListItem<T>> {
        if let Some(head) = self.data.get_head() {
            unsafe { head.as_ref() }
                .read()
                .map_err(|x| x.into())
                .map(|x| x.element.as_ref().unwrap().clone())
        } else {
            Err(LinkedListError::Empty)
        }
    }

    /// Provides a reference to the back element, or `None` if the list is
    /// empty.
    #[inline]
    pub fn back(&self) -> LinkedListResult<LinkedListItem<T>> {
        if let Some(tail) = self.data.get_tail() {
            unsafe { tail.as_ref() }
                .read()
                .map_err(|x| x.into())
                .map(|x| x.element.as_ref().unwrap().clone())
        } else {
            Err(LinkedListError::Empty)
        }
    }

    #[inline]
    pub fn contains_iter(&self, x: &Iter<T>) -> LinkedListResult<bool> {
        self.data.contains_iter(&x).map(|_| true)
    }

    #[inline]
    pub fn contains_iter_mut(&self, x: &IterMut<T>) -> LinkedListResult<bool> {
        self.data.contains_iter_mut(&x).map(|_| true)
    }

    /// Inserts a new element into the `LinkedList` before the current one.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new element is
    /// inserted at the end of the `LinkedList`.
    #[inline]
    pub fn insert_before(&mut self, iter: &IterMut<T>, elt: T) -> LinkedListResult<IterMut<T>> {
        let current = self.data.contains_iter_mut(&iter)?;
        if current.current_is_end {
            self.push_back(elt)?;
            return Ok(self.iter_mut_back());
        }

        let new_node = NodeEntry::new(elt, &mut self.data);

        self.data_mut()
            .splice_node(current.prev, Some(current.current), new_node)
    }

    /// Inserts a new element into the `LinkedList` after the current one.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new element is
    /// inserted at the front of the `LinkedList`.
    #[inline]
    pub fn insert_after(&mut self, iter: &IterMut<T>, elt: T) -> LinkedListResult<IterMut<T>> {
        let current = self.data.contains_iter_mut(&iter)?;
        if current.current_is_end {
            self.push_front(elt)?;
            return Ok(self.iter_mut_front());
        }

        let new_node = NodeEntry::new(elt, &mut self.data);

        self.data_mut()
            .splice_node(Some(current.current), current.next, new_node)
    }

    #[inline]
    pub fn remove_iter(&mut self, iter: IterMut<T>) -> LinkedListResult<LinkedListItem<T>> {
        self.data_mut().remove_iter(iter)
    }
}

impl<T> Default for LinkedList<T> {
    /// Creates an empty `LinkedList<T>`.
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for UnmoveableLinkedList<T> {
    fn drop(&mut self) {
        struct DropGuard<'a, T>(&'a mut UnmoveableLinkedList<T>);

        impl<'a, T> Drop for DropGuard<'a, T> {
            fn drop(&mut self) {
                // Continue the same loop we do below. This only runs when a destructor has
                // panicked. If another one panics this will abort.
                while self.0.pop_front_node().is_ok() {}
            }
        }

        while let Ok(node) = self.pop_front_node() {
            let guard = DropGuard(self);
            drop(node);
            mem::forget(guard);
        }
    }
}

impl<T> FromIterator<T> for LinkedList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut list = Self::new();
        list.extend(iter);
        list
    }
}

impl<T> IntoIterator for &LinkedList<T> {
    type Item = LinkedListItem<T>;
    type IntoIter = Iter<T>;

    fn into_iter(self) -> Iter<T> {
        self.iter()
    }
}

impl<T> IntoIterator for &mut LinkedList<T> {
    type Item = LinkedListItem<T>;
    type IntoIter = IterMut<T>;

    fn into_iter(self) -> IterMut<T> {
        self.iter_mut()
    }
}

impl<T> Extend<T> for LinkedList<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |elt| {
            let _ = self.push_back(elt);
        });
    }

    #[cfg(feature = "nightly")]
    #[inline]
    fn extend_one(&mut self, elem: T) {
        let _ = self.push_back(elem);
    }
}

impl<'a, T: 'a + Copy> Extend<&'a T> for LinkedList<T> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        iter.into_iter().cloned().for_each(move |elt| {
            let _ = self.push_back(elt);
        });
    }

    #[cfg(feature = "nightly")]
    #[inline]
    fn extend_one(&mut self, &elem: &'a T) {
        let _ = self.push_back(elem);
    }
}

impl<T: PartialEq> PartialEq for NodeEntry<T> {
    fn eq(&self, other: &Self) -> bool {
        self.element.as_ref() == other.element.as_ref()
    }

    fn ne(&self, other: &Self) -> bool {
        !self.eq(&other)
    }
}

impl<T: Eq> Eq for NodeEntry<T> {}

fn _core_cmp_op_eq_list<T: PartialEq, CF>(
    left: &LinkedList<T>,
    right: &LinkedList<T>,
    mut cmp_op: CF,
) -> bool
where
    CF: FnMut(&T, &T) -> bool,
{
    let mut left_iter = left.iter();
    let mut right_iter = right.iter();
    loop {
        loop {
            let x = match left_iter.next() {
                None => return right_iter.next().is_none(),
                Some(val) => val,
            };

            let y = match right_iter.next() {
                None => return false,
                Some(val) => val,
            };

            if !cmp_op(x.as_ref(), y.as_ref()) {
                return false;
            }
        }
    }
}

impl<T: PartialEq> PartialEq for LinkedList<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && _core_cmp_op_eq_list(&self, &other, |x, y| x == y)
    }

    fn ne(&self, other: &Self) -> bool {
        self.len() != other.len() || !_core_cmp_op_eq_list(&self, &other, |x, y| x == y)
    }
}

impl<T: Eq> Eq for LinkedList<T> {}

fn _core_cmp_op_partial_cmp_by_list<T: PartialOrd, CF>(
    left: &LinkedList<T>,
    right: &LinkedList<T>,
    mut partial_cmp: CF,
) -> Option<Ordering>
where
    CF: FnMut(&T, &T) -> Option<Ordering>,
{
    let mut left_iter = left.iter();
    let mut right_iter = right.iter();
    loop {
        let x = match left_iter.next() {
            None => {
                if right_iter.next().is_none() {
                    return Some(Ordering::Equal);
                } else {
                    return Some(Ordering::Less);
                }
            }
            Some(val) => val,
        };

        let y = match right_iter.next() {
            None => return Some(Ordering::Greater),
            Some(val) => val,
        };

        match partial_cmp(x.as_ref(), y.as_ref()) {
            Some(Ordering::Equal) => (),
            non_eq => return non_eq,
        }
    }
}

impl<T: PartialOrd> PartialOrd for LinkedList<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        _core_cmp_op_partial_cmp_by_list(&self, &other, |x, y| x.partial_cmp(y))
    }
}

fn _core_cmp_op_cmp_by_list<T: Ord, CF>(
    left: &LinkedList<T>,
    right: &LinkedList<T>,
    mut cmp_op: CF,
) -> Ordering
where
    CF: FnMut(&T, &T) -> Ordering,
{
    let mut left_iter = left.iter();
    let mut right_iter = right.iter();
    loop {
        let x = match left_iter.next() {
            None => {
                if right_iter.next().is_none() {
                    return Ordering::Equal;
                } else {
                    return Ordering::Less;
                }
            }
            Some(val) => val,
        };

        let y = match right_iter.next() {
            None => return Ordering::Greater,
            Some(val) => val,
        };

        match cmp_op(x.as_ref(), y.as_ref()) {
            Ordering::Equal => (),
            non_eq => return non_eq,
        }
    }
}

impl<T: Ord> Ord for LinkedList<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        _core_cmp_op_cmp_by_list(&self, &other, |x, y| x.cmp(y))
    }
}

impl<T: Clone> Clone for LinkedList<T> {
    fn clone(&self) -> Self {
        let mut ret = LinkedList::new();
        for elem in self {
            let _ = ret.push_back(elem.as_ref().clone());
        }
        ret
    }

    fn clone_from(&mut self, other: &Self) {
        let mut iter_other = other.iter();
        while self.len() > other.len() {
            let _ = self.pop_back();
        }

        for (elem, elem_other) in self.iter_mut().zip(&mut iter_other) {
            let dst = unsafe { &mut *(Arc::as_ptr(&elem) as *mut T) };

            dst.clone_from(elem_other.as_ref());
        }

        while let Some(elem) = iter_other.next() {
            let _ = self.push_back(elem.deref().clone());
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for LinkedList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<T: Hash> Hash for LinkedList<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for elem in self {
            elem.as_ref().hash(state);
        }
    }
}

fn _core_cmp_op_weak<T: PartialEq, CF, EF>(
    left: &Weak<RwLock<NodeEntry<T>>>,
    right: &Weak<RwLock<NodeEntry<T>>>,
    mut cmp_op: CF,
    mut eq_op: EF,
) -> bool
where
    CF: FnMut(&NodeEntry<T>, &NodeEntry<T>) -> bool,
    EF: FnMut() -> Option<bool>,
{
    if Weak::ptr_eq(&left, &right) {
        if let Some(r) = eq_op() {
            return r;
        }
    }

    let left_ptr = left.upgrade();
    let right_ptr = right.upgrade();

    if left_ptr.is_none() && right_ptr.is_none() {
        if let Some(r) = eq_op() {
            return r;
        }
    }

    let left_ptr = left_ptr.unwrap();
    let right_ptr = right_ptr.unwrap();

    let left_node = if let Ok(g) = left_ptr.read() {
        g
    } else {
        return false;
    };
    let right_node = if let Ok(g) = right_ptr.read() {
        g
    } else {
        return false;
    };

    cmp_op(&left_node, &right_node)
}

#[inline]
fn _core_cmp_eq_weak<T: PartialEq>(
    left: &Weak<RwLock<NodeEntry<T>>>,
    right: &Weak<RwLock<NodeEntry<T>>>,
) -> bool {
    _core_cmp_op_weak(left, right, |x, y| x == y, || Some(true))
}

impl<T: PartialEq> PartialEq for Iter<T> {
    fn eq(&self, other: &Self) -> bool {
        _core_cmp_eq_weak(&self.node, &other.node)
    }
}

impl<T: PartialEq> PartialEq<IterMut<T>> for Iter<T> {
    fn eq(&self, other: &IterMut<T>) -> bool {
        _core_cmp_eq_weak(&self.node, &other.node)
    }
}

impl<T: PartialEq> Eq for Iter<T> {}

impl<T: PartialEq> PartialEq for IterMut<T> {
    fn eq(&self, other: &Self) -> bool {
        _core_cmp_eq_weak(&self.node, &other.node)
    }
}

impl<T: PartialEq> PartialEq<Iter<T>> for IterMut<T> {
    fn eq(&self, other: &Iter<T>) -> bool {
        _core_cmp_eq_weak(&self.node, &other.node)
    }
}

impl<T: PartialEq> Eq for IterMut<T> {}

impl<T> From<&Iter<T>> for IterMut<T> {
    fn from(iter: &Iter<T>) -> IterMut<T> {
        IterMut::from_weak(iter.node.clone())
    }
}

impl<T> From<Iter<T>> for IterMut<T> {
    fn from(iter: Iter<T>) -> IterMut<T> {
        IterMut::from_weak(iter.node)
    }
}

impl<T> From<&IterMut<T>> for Iter<T> {
    fn from(iter: &IterMut<T>) -> Iter<T> {
        Iter::from_weak(iter.node.clone())
    }
}

impl<T> From<IterMut<T>> for Iter<T> {
    fn from(iter: IterMut<T>) -> Iter<T> {
        Iter::from_weak(iter.node)
    }
}

// unsafe impl<T> !marker::Unpin for UnmoveableLinkedList<T> {}
unsafe impl<T: marker::Sync + marker::Send> marker::Send for UnmoveableLinkedList<T> {}
unsafe impl<T: marker::Sync + marker::Send> marker::Sync for UnmoveableLinkedList<T> {}
unsafe impl<T: marker::Sync + marker::Send> marker::Send for Iter<T> {}
unsafe impl<T: marker::Sync + marker::Send> marker::Sync for Iter<T> {}
unsafe impl<T: marker::Sync + marker::Send> marker::Send for IterMut<T> {}
unsafe impl<T: marker::Sync + marker::Send> marker::Sync for IterMut<T> {}
