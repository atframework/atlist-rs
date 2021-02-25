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
//! ```rust,no_run
//! extern crate atlist;
//!
//! use atlist::LinkedList;
//!
//! fn main() {
//!         let mut list = LinkedList::new();
//!         let _ = list.push_back(3);
//!         let i = list.push_front(2);
//!         let _ = list.insert_after(list.iter(), 4);
//!         list.remove(i);
//!
//!         // assert_eq!(*cache.get(&"apple").unwrap(), 3);
//! }
//! ```

//#![no_std]
#![cfg_attr(feature = "nightly", feature(negative_impls, auto_traits))]

//use alloc::borrow::Borrow;
//use alloc::boxed::Box;
use core::cell::{BorrowError, BorrowMutError, RefCell};
use core::fmt;
use core::iter::{Extend, FromIterator, FusedIterator};
use core::marker::PhantomData;
use core::mem;
use core::ptr;
use core::ptr::NonNull;
use core::result::Result;
use core::usize;
use std::sync::{Arc, Weak};
use std::{borrow::Borrow, error::Error};

#[cfg(test)]
mod tests;

#[derive(Debug)]
pub enum LinkedListError {
    /// Borrow failed
    BorrowFailed(BorrowError),
    /// Mutable borrow failed
    BorrowMutFailed(BorrowMutError),
    /// Iterator is not in specified LinkedList
    IteratorNotInList,
    /// LinkedList or iterator is empty
    Empty,
}

pub type LinkedListResult<T> = Result<T, LinkedListError>;

impl fmt::Display for LinkedListError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            &LinkedListError::BorrowFailed(ref e) => write!(f, "Borrow failed: {}", e),
            &LinkedListError::BorrowMutFailed(ref e) => write!(f, "Mutable borrow failed: {}", e),
            LinkedListError::IteratorNotInList => write!(f, "Iterator not in list"),
            LinkedListError::Empty => write!(f, "LinkedList or iterator is empty"),
        }
    }
}

impl Error for LinkedListError {
    #[allow(deprecated)] // call to `description`
    fn description(&self) -> &str {
        match self {
            &LinkedListError::BorrowFailed(ref e) => e.description(),
            &LinkedListError::BorrowMutFailed(ref e) => e.description(),
            LinkedListError::IteratorNotInList => &"Iterator not in list",
            LinkedListError::Empty => &"LinkedList or iterator is empty",
        }
    }

    fn cause(&self) -> Option<&dyn Error> {
        match self {
            &LinkedListError::BorrowFailed(ref e) => Some(e),
            &LinkedListError::BorrowMutFailed(ref e) => Some(e),
            e => Some(e),
        }
    }
}

impl From<BorrowError> for LinkedListError {
    fn from(err: BorrowError) -> Self {
        LinkedListError::BorrowFailed(err)
    }
}

impl From<BorrowMutError> for LinkedListError {
    fn from(err: BorrowMutError) -> Self {
        LinkedListError::BorrowMutFailed(err)
    }
}

pub type LinkedListItem<T> = Arc<RefCell<T>>;

struct Node<T> {
    next: Option<NonNull<Node<T>>>,
    prev: Option<NonNull<Node<T>>>,
    element: LinkedListItem<T>,
    watcher: Arc<NodeWatcher<T>>,
}

struct NodeWatcher<T> {
    owner: RefCell<Option<NonNull<Node<T>>>>,
    container: NonNull<LinkedList<T>>,
}

pub struct LinkedList<T> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<Node<T>>,
}

pub struct Iter<T> {
    node: Weak<NodeWatcher<T>>,
}

fn check_iter_valid<T>(iter: &Iter<T>) -> bool {
    iter.node.strong_count() > 0
}

impl<T> Node<T> {
    fn new(elt: T, container: NonNull<LinkedList<T>>) -> Box<Node<T>> {
        let mut ret = Box::new(Node {
            next: None,
            prev: None,
            element: Arc::new(RefCell::new(elt)),
            watcher: Arc::new(NodeWatcher {
                owner: RefCell::new(None),
                container: container,
            }),
        });

        unsafe {
            let watcher = Arc::as_ptr(&ret.watcher);
            (*(*watcher).owner.borrow_mut()) = Some(NonNull::new_unchecked(ret.as_mut()));
        }

        ret
    }

    fn into_element(self: Box<Self>) -> LinkedListItem<T> {
        self.element
    }
}

impl<T: fmt::Debug> fmt::Debug for Iter<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        //f.debug_tuple("Iter").field(&self.node.as_ref()).finish()
        f.debug_tuple("Iter").finish()
    }
}

impl<T> Clone for Iter<T> {
    fn clone(&self) -> Self {
        Iter {
            node: self.node.clone(),
        }
    }
}

impl<T> Iterator for Iter<T> {
    type Item = LinkedListItem<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let watcher = self.node.upgrade()?;
        let node = (*watcher.owner.borrow())?;

        let ret = unsafe { node.as_ref().element.clone() };

        let next_node = if let Some(next_watcher) = unsafe { &node.as_ref().next } {
            unsafe { Arc::downgrade(&next_watcher.as_ref().watcher.borrow()) }
        } else {
            Weak::new()
        };

        self.node = next_node;
        Some(ret)
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

impl<'a, T> DoubleEndedIterator for Iter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let watcher = self.node.upgrade()?;
        let node = (*watcher.owner.borrow())?;

        let ret = unsafe { node.as_ref().element.clone() };

        let prev_node = if let Some(prev_watcher) = unsafe { &node.as_ref().prev } {
            unsafe { Arc::downgrade(&prev_watcher.as_ref().watcher.borrow()) }
        } else {
            Weak::new()
        };

        self.node = prev_node;
        Some(ret)
    }
}

impl<T> FusedIterator for Iter<T> {}

impl<T> Iter<T> {
    fn new() -> Iter<T> {
        Iter { node: Weak::new() }
    }

    fn from(node: &Node<T>) -> Iter<T> {
        Iter {
            node: Arc::downgrade(&node.watcher),
        }
    }

    #[inline]
    #[allow(unused)]
    fn next_watcher(&self) -> Weak<NodeWatcher<T>> {
        let watcher = if let Some(x) = self.node.upgrade() {
            x
        } else {
            return Weak::new();
        };

        let node = if let Some(x) = *watcher.owner.borrow() {
            x
        } else {
            return Weak::new();
        };

        if let Some(next_watcher) = unsafe { &node.as_ref().next } {
            unsafe { Arc::downgrade(&next_watcher.as_ref().watcher) }
        } else {
            Weak::new()
        }
    }

    #[inline]
    #[allow(unused)]
    fn prev_watcher(&self) -> Weak<NodeWatcher<T>> {
        let watcher = if let Some(x) = self.node.upgrade() {
            x
        } else {
            return Weak::new();
        };

        let node = if let Some(x) = *watcher.owner.borrow() {
            x
        } else {
            return Weak::new();
        };

        if let Some(prev_watcher) = unsafe { &node.as_ref().prev } {
            unsafe { Arc::downgrade(&prev_watcher.as_ref().watcher) }
        } else {
            Weak::new()
        }
    }

    pub fn as_ref(&self) -> Option<LinkedListItem<T>> {
        let watcher = self.node.upgrade()?;
        let node = (*watcher.owner.borrow())?;

        let ret = unsafe { node.as_ref().element.clone() };
        Some(ret)
    }

    pub fn is_empty(&self) -> bool {
        check_iter_valid(self)
    }
}

// impl<T> FusedIterator for Iter<'_, T> {}

impl<T> LinkedList<T> {
    /// Unlinks the specified node from the current list.
    ///
    /// Warning: this will not check that the provided node belongs to the current list.
    #[inline]
    fn unlink_node(&mut self, mut node: NonNull<Node<T>>) {
        let node = unsafe { node.as_mut() };

        if node.prev.is_none() && node.next.is_none() && self.len() > 0 {
            // Bad data
            return;
        }

        match node.prev {
            Some(prev) => unsafe { (*prev.as_ptr()).next = node.next },
            None => self.head = node.next,
        }

        match node.next {
            Some(next) => unsafe { (*next.as_ptr()).prev = node.prev },
            // this node is the tail node
            None => self.tail = node.prev,
        }

        self.len -= 1;

        node.prev = None;
        node.next = None;
    }

    /// Splices a series of nodes between two existing nodes.
    ///
    /// Warning: this will not check that the provided node belongs to the two existing lists.
    #[inline]
    fn splice_nodes(
        &mut self,
        existing_prev: Option<NonNull<Node<T>>>,
        existing_next: Option<NonNull<Node<T>>>,
        mut splice_start: NonNull<Node<T>>,
        mut splice_end: NonNull<Node<T>>,
        splice_length: usize,
    ) {
        // This method takes care not to create multiple mutable references to whole nodes at the same time,
        // to maintain validity of aliasing pointers into `element`.
        if let Some(mut existing_prev) = existing_prev {
            unsafe {
                existing_prev.as_mut().next = Some(splice_start);
            }
        } else {
            self.head = Some(splice_start);
        }
        if let Some(mut existing_next) = existing_next {
            unsafe {
                existing_next.as_mut().prev = Some(splice_end);
            }
        } else {
            self.tail = Some(splice_end);
        }
        unsafe {
            splice_start.as_mut().prev = existing_prev;
            splice_end.as_mut().next = existing_next;
        }

        self.len += splice_length;
    }

    /// Adds the given node to the front of the list.
    #[inline]
    fn push_front_node(&mut self, mut node: Box<Node<T>>) {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
            node.next = self.head;
            node.prev = None;
            let node = Some(Box::leak(node).into());

            match self.head {
                None => self.tail = node,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(head) => (*head.as_ptr()).prev = node,
            }

            self.head = node;
            self.len += 1;
        }
    }

    /// Removes and returns the node at the front of the list.
    #[inline]
    fn pop_front_node(&mut self) -> Option<Box<Node<T>>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        self.head.map(|node| unsafe {
            let node = Box::from_raw(node.as_ptr());
            self.head = node.next;

            match self.head {
                None => self.tail = None,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(head) => (*head.as_ptr()).prev = None,
            }

            self.len -= 1;
            node
        })
    }

    /// Adds the given node to the back of the list.
    #[inline]
    fn push_back_node(&mut self, mut node: Box<Node<T>>) {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
            node.next = None;
            node.prev = self.tail;
            let node = Some(Box::leak(node).into());

            match self.tail {
                None => self.head = node,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(tail) => (*tail.as_ptr()).next = node,
            }

            self.tail = node;
            self.len += 1;
        }
    }

    /// Removes and returns the node at the back of the list.
    #[inline]
    fn pop_back_node(&mut self) -> Option<Box<Node<T>>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        self.tail.map(|node| unsafe {
            let node = Box::from_raw(node.as_ptr());
            self.tail = node.prev;

            match self.tail {
                None => self.head = None,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(tail) => (*tail.as_ptr()).next = None,
            }

            self.len -= 1;
            node
        })
    }

    #[inline]
    pub const fn new() -> LinkedList<T> {
        LinkedList {
            head: None,
            tail: None,
            len: 0,
            marker: PhantomData,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        0 == self.len
    }

    /// Removes all elements from the `LinkedList`.
    ///
    /// This operation should compute in *O*(*n*) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use atlist::LinkedList;
    ///
    /// let mut dl = LinkedList::new();
    /// dl.put(1);
    /// dl.put(2);
    /// dl.put(3);
    /// assert_eq!(dl.len(), 3);
    ///
    /// dl.clear();
    /// assert_eq!(dl.len(), 0);
    /// assert_eq!(dl.front().is_none());
    #[inline]
    pub fn clear(&mut self) {
        *self = Self::new();
    }

    #[inline]
    pub fn iter(&self) -> Iter<T> {
        self.iter_front()
    }

    #[inline]
    pub fn iter_front(&self) -> Iter<T> {
        if let Some(ref head) = self.head {
            Iter::from(unsafe { head.as_ref() })
        } else {
            Iter::new()
        }
    }

    #[inline]
    pub fn iter_back(&self) -> Iter<T> {
        if let Some(ref tail) = self.tail {
            Iter::from(unsafe { tail.as_ref() })
        } else {
            Iter::new()
        }
    }

    /// Adds an element first in the list.
    ///
    /// This operation should compute in *O*(1) time.
    pub fn push_front(&mut self, elt: T) {
        let container = unsafe { NonNull::new_unchecked(self) };
        self.push_front_node(Node::new(elt, container));
    }

    /// Removes the first element and returns it, or `None` if the list is
    /// empty.
    ///
    /// This operation should compute in *O*(1) time.
    pub fn pop_front(&mut self) -> Option<LinkedListItem<T>> {
        self.pop_front_node().map(Node::into_element)
    }

    /// Appends an element to the back of a list.
    ///
    /// This operation should compute in *O*(1) time.
    pub fn push_back(&mut self, elt: T) {
        let container = unsafe { NonNull::new_unchecked(self) };
        self.push_back_node(Node::new(elt, container));
    }

    /// Removes the last element from a list and returns it, or `None` if
    /// it is empty.
    ///
    /// This operation should compute in *O*(1) time.
    pub fn pop_back(&mut self) -> Option<LinkedListItem<T>> {
        self.pop_back_node().map(Node::into_element)
    }

    /// Provides a reference to the front element, or `None` if the list is
    /// empty.
    #[inline]
    pub fn front(&self) -> Option<LinkedListItem<T>> {
        unsafe { self.head.as_ref().map(|node| node.as_ref().element.clone()) }
    }

    /// Provides a reference to the back element, or `None` if the list is
    /// empty.
    #[inline]
    pub fn back(&self) -> Option<LinkedListItem<T>> {
        unsafe { self.tail.as_ref().map(|node| node.as_ref().element.clone()) }
    }

    #[inline]
    fn check_container(&self, x: &Iter<T>) -> (bool, Option<Arc<NodeWatcher<T>>>) {
        let node = if let Some(y) = x.node.upgrade() {
            y
        } else {
            return (false, None);
        };

        (
            unsafe { ptr::eq(node.container.as_ref(), self) },
            Some(node),
        )
    }

    #[inline]
    pub fn contains_iter(&self, x: &Iter<T>) -> bool {
        if !self.check_container(&x).0 {
            return false;
        }

        let mut cur = self.head;
        loop {
            if cur.is_none() {
                return false;
            }

            let cur_node = cur.unwrap();
            if ptr::eq(
                Arc::as_ptr(unsafe { &cur_node.as_ref().watcher }),
                x.node.as_ptr(),
            ) {
                return true;
            }

            cur = unsafe { cur_node.as_ref().next };
        }
    }

    /// Inserts a new element into the `LinkedList` before the current one.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new element is
    /// inserted at the end of the `LinkedList`.
    #[inline]
    pub fn insert_before(&mut self, iter: &mut Iter<T>, elt: T) -> LinkedListResult<Iter<T>> {
        let (check_container, p) = self.check_container(&iter);

        if !check_container && p.is_none() {
            self.push_back(elt);
            return Ok(self.iter_back());
        }

        if !check_container {
            return Err(LinkedListError::IteratorNotInList);
        }
        let watcher = p.unwrap();
        let current_node = *watcher.as_ref().owner.borrow();

        let ret = unsafe {
            let spliced_node = Box::leak(Node::new(elt, NonNull::new_unchecked(self))).into();
            let node_prev = match current_node {
                None => self.tail,
                Some(node) => node.as_ref().prev,
            };
            self.splice_nodes(node_prev, current_node, spliced_node, spliced_node, 1);

            Iter::from(spliced_node.as_ref())
        };

        Ok(ret)
    }

    /// Inserts a new element into the `LinkedList` after the current one.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new element is
    /// inserted at the front of the `LinkedList`.
    #[inline]
    pub fn insert_after(&mut self, iter: &mut Iter<T>, elt: T) -> LinkedListResult<Iter<T>> {
        let (check_container, p) = self.check_container(&iter);

        if !check_container && p.is_none() {
            self.push_front(elt);
            return Ok(self.iter_front());
        }

        if !check_container {
            return Err(LinkedListError::IteratorNotInList);
        }

        let watcher = p.unwrap();
        let current_node = *watcher.as_ref().owner.borrow();

        let ret = unsafe {
            let spliced_node = Box::leak(Node::new(elt, NonNull::new_unchecked(self))).into();
            let node_next = match current_node {
                None => self.head,
                Some(node) => node.as_ref().next,
            };
            self.splice_nodes(current_node, node_next, spliced_node, spliced_node, 1);

            Iter::from(spliced_node.as_ref())
        };

        Ok(ret)
    }

    #[inline]
    pub fn remove_iter(&mut self, iter: Iter<T>) -> LinkedListResult<LinkedListItem<T>> {
        let (check_container, p) = self.check_container(&iter);

        if !check_container {
            return Err(LinkedListError::IteratorNotInList);
        }

        let watcher = p.unwrap();
        let unlinked_node = watcher.as_ref().owner.borrow().unwrap();

        self.unlink_node(unlinked_node);

        let unlinked_node = unsafe { Box::from_raw(unlinked_node.as_ptr()) };
        Ok(unlinked_node.element)
    }
}

impl<T> Default for LinkedList<T> {
    /// Creates an empty `LinkedList<T>`.
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        struct DropGuard<'a, T>(&'a mut LinkedList<T>);

        impl<'a, T> Drop for DropGuard<'a, T> {
            fn drop(&mut self) {
                // Continue the same loop we do below. This only runs when a destructor has
                // panicked. If another one panics this will abort.
                while self.0.pop_front_node().is_some() {}
            }
        }

        while let Some(node) = self.pop_front_node() {
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

impl<T> Extend<T> for LinkedList<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |elt| self.push_back(elt));
    }
}

impl<T: Clone> Clone for LinkedList<T> {
    fn clone(&self) -> Self {
        let mut ret = LinkedList::new();
        for elem in self {
            ret.push_back(unsafe { &*elem.as_ptr() }.clone());
        }
        ret
    }

    fn clone_from(&mut self, other: &Self) {
        let mut iter_other = other.iter();
        while self.len() > other.len() {
            self.pop_back();
        }

        for (elem, elem_other) in self.iter().zip(&mut iter_other) {
            let elem_src = elem.as_ptr();
            unsafe { &mut *elem_src }.clone_from(unsafe { &*elem_other.as_ptr() });
        }

        while let Some(elem) = iter_other.next() {
            self.push_back(unsafe { &*elem.as_ptr() }.clone());
        }
    }
}

unsafe impl<T: Send> Send for LinkedList<T> {}
unsafe impl<T: Sync> Sync for LinkedList<T> {}
unsafe impl<T: Sync> Send for Iter<T> {}
unsafe impl<T: Sync> Sync for Iter<T> {}
