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
//!         let _ = list.insert_after("apple", &i, 4);
//!         list.remove(i);
//!
//!         // assert_eq!(*cache.get(&"apple").unwrap(), 3);
//! }
//! ```

//#![no_std]
#![cfg_attr(feature = "nightly", feature(negative_impls, auto_traits))]

//use alloc::borrow::Borrow;
//use alloc::boxed::Box;
use core::cell::{BorrowError, BorrowMutError, Ref, RefCell, RefMut};
use core::fmt;
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem;
use core::ptr;
use core::ptr::NonNull;
use core::result::Result;
use core::usize;
use std::{borrow::Borrow, error::Error};
use std::{
    borrow::BorrowMut,
    rc::{Rc, Weak},
};

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

type Node<T> = Rc<RefCell<NodeEntry<T>>>;
type WeakNode<T> = Weak<RefCell<NodeEntry<T>>>;

struct NodeEntry<T> {
    next: Option<Node<T>>,
    prev: Option<WeakNode<T>>,
    element: T,
    owner: Option<NonNull<LinkedList<T>>>,
}

pub struct LinkedList<T> {
    head: Option<Node<T>>,
    tail: Option<Node<T>>,
    len: usize,
    marker: PhantomData<Node<T>>,
}

pub struct Iter<T> {
    node: Option<Node<T>>,
}

fn try_borrow_node<T>(node: &Node<T>) -> LinkedListResult<Ref<T>> {
    let node_ref = node.try_borrow()?;

    if node_ref.owner.is_none() {
        return Err(LinkedListError::IteratorNotInList);
    }

    let ret = Ref::map(node_ref, |t| &t.element);

    Ok(ret)
}

fn try_borrow_mut_node<T>(node: &Node<T>) -> LinkedListResult<RefMut<T>> {
    let node_ref = node.try_borrow_mut()?;

    if node_ref.owner.is_none() {
        return Err(LinkedListError::IteratorNotInList);
    }

    let ret = RefMut::map(node_ref, |t| &mut t.element);
    Ok(ret)
}

impl<T> NodeEntry<T> {
    fn new(elt: T) -> NodeEntry<T> {
        NodeEntry {
            next: None,
            prev: None,
            element: elt,
            owner: None,
        }
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

impl<T> Iter<T> {
    pub fn try_borrow(&self) -> LinkedListResult<Ref<T>> {
        if let Some(ref node) = self.node {
            try_borrow_node(&node)
        } else {
            Err(LinkedListError::Empty)
        }
    }

    pub fn try_borrow_mut(&self) -> LinkedListResult<RefMut<T>> {
        if let Some(ref node) = self.node {
            try_borrow_mut_node(&node)
        } else {
            Err(LinkedListError::Empty)
        }
    }
}

impl<T> LinkedList<T> {
    #[inline]
    fn unlink_node_entry(entry: &mut NodeEntry<T>) -> LinkedListResult<()> {
        if entry.owner.is_none() {
            return Err(LinkedListError::IteratorNotInList);
        }

        let self_list = unsafe { entry.owner.as_mut().unwrap().as_mut() };

        match &entry.prev {
            Some(prev) => {
                if let Some(prev_entry) = prev.upgrade() {
                    prev_entry.as_ref().borrow_mut().next = entry.next.clone();
                } else {
                    self_list.head = entry.next.clone();
                }
            }
            None => self_list.head = entry.next.clone(),
        }

        match &entry.next {
            Some(next) => {
                next.as_ref().borrow_mut().prev = entry.prev.clone();
            }
            None => {
                self_list.tail = if let Some(ref prev) = entry.prev {
                    if let Some(prev_entry) = prev.upgrade() {
                        Some(prev_entry)
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
        }

        self_list.len -= 1;

        entry.prev = None;
        entry.next = None;
        entry.owner = None;
        Ok(())
    }

    #[inline]
    fn unlink_node(node: Node<T>) -> LinkedListResult<()> {
        let mut entry = node.try_borrow_mut()?;

        if let Err(e) = LinkedList::unlink_node_entry(entry.borrow_mut()) {
            return Err(e);
        }

        Ok(())
    }

    #[inline]
    fn insert_before_node(to: &mut Node<T>, node: Node<T>) -> LinkedListResult<Iter<T>> {
        {
            let to_entry = &mut *to.try_borrow_mut()?;
            if to_entry.owner.is_none() {
                return Err(LinkedListError::IteratorNotInList);
            }

            let self_list = unsafe { to_entry.owner.as_mut().unwrap().as_mut() };

            let node_entry = &mut *node.try_borrow_mut()?;
            if node_entry.owner.is_some() {
                LinkedList::unlink_node_entry(node_entry)?;
            }

            node_entry.owner = Some(unsafe { NonNull::new_unchecked(self_list) });
            node_entry.prev = to_entry.prev.clone();
            node_entry.next = Some(to.clone());
            if let Some(prev_watcher) = &to_entry.prev {
                if let Some(prev_node) = prev_watcher.upgrade() {
                    let prev_entry = &mut *prev_node.try_borrow_mut()?;
                    prev_entry.next = Some(node.clone());
                }
            }
            to_entry.prev = Some(Rc::downgrade(&node));

            self_list.len += 1;
            if Rc::ptr_eq(self_list.head.as_ref().unwrap(), to) {
                self_list.head = Some(node.clone());
            }
        }

        Ok(Iter { node: Some(node) })
    }

    #[inline]
    fn insert_after_node(to: &mut Node<T>, node: Node<T>) -> LinkedListResult<Iter<T>> {
        {
            let to_entry = &mut *to.try_borrow_mut()?;
            if to_entry.owner.is_none() {
                return Err(LinkedListError::IteratorNotInList);
            }

            let self_list = unsafe { to_entry.owner.as_mut().unwrap().as_mut() };

            let node_entry = &mut *node.try_borrow_mut()?;
            if node_entry.owner.is_some() {
                LinkedList::unlink_node_entry(node_entry)?;
            }

            node_entry.owner = Some(unsafe { NonNull::new_unchecked(self_list) });
            node_entry.prev = Some(Rc::downgrade(to));
            node_entry.next = to_entry.next.clone();
            if let Some(next_node) = &to_entry.next {
                let next_entry = &mut *next_node.try_borrow_mut()?;
                next_entry.prev = Some(Rc::downgrade(&node));
            }
            to_entry.next = Some(node.clone());

            self_list.len += 1;
            if Rc::ptr_eq(self_list.tail.as_ref().unwrap(), to) {
                self_list.tail = Some(node.clone());
            }
        }

        Ok(Iter { node: Some(node) })
    }

    #[inline]
    fn push_front_node(&mut self, node: Node<T>) -> LinkedListResult<Iter<T>> {
        {
            let entry = &mut *node.try_borrow_mut()?;

            unsafe {
                if ptr::eq(entry.owner.as_ref().unwrap().as_ref(), self) {
                    return Ok(Iter {
                        node: Some(node.clone()),
                    });
                }
            }

            if entry.owner.is_some() {
                LinkedList::unlink_node_entry(entry)?;
            }

            match &mut self.head {
                None => self.tail = Some(node.clone()),
                Some(head) => {
                    let head_entry = &mut *head.as_ref().try_borrow_mut()?;
                    head_entry.prev = Some(Rc::downgrade(&node));
                }
            }

            // Set entry
            entry.next = self.head.clone();
            entry.prev = None;
            entry.owner = Some(unsafe { NonNull::new_unchecked(self) });
        }

        // Set list
        self.head = Some(node.clone());
        self.len += 1;

        Ok(Iter { node: Some(node) })
    }

    #[inline]
    fn pop_front_node(&mut self) -> LinkedListResult<()> {
        if let Some(ref head_node) = self.head {
            LinkedList::unlink_node(head_node.clone())
        } else {
            Err(LinkedListError::Empty)
        }
    }

    #[inline]
    fn push_back_node(&mut self, node: Node<T>) -> LinkedListResult<Iter<T>> {
        {
            let entry = &mut *node.try_borrow_mut()?;

            unsafe {
                if ptr::eq(entry.owner.as_ref().unwrap().as_ref(), self) {
                    return Ok(Iter {
                        node: Some(node.clone()),
                    });
                }
            }

            if entry.owner.is_some() {
                LinkedList::unlink_node_entry(entry)?;
            }

            match &mut self.tail {
                None => self.head = Some(node.clone()),
                Some(tail) => {
                    let tail_entry = &mut *tail.as_ref().try_borrow_mut()?;
                    tail_entry.next = Some(node.clone());
                }
            }

            // Set entry
            entry.next = None;
            entry.prev = if let Some(tail) = &self.tail {
                Some(Rc::downgrade(&tail))
            } else {
                None
            };
            entry.owner = Some(unsafe { NonNull::new_unchecked(self) });
        }

        // Set list
        self.tail = Some(node.clone());
        self.len += 1;

        Ok(Iter { node: Some(node) })
    }

    #[inline]
    fn pop_back_node(&mut self) -> LinkedListResult<()> {
        if let Some(ref tail_node) = self.tail {
            LinkedList::unlink_node(tail_node.clone())
        } else {
            Err(LinkedListError::Empty)
        }
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

    #[inline]
    pub fn iter(&self) -> Iter<T> {
        if let Some(ref head) = self.head {
            Iter {
                node: Some(head.clone()),
            }
        } else {
            Iter { node: None }
        }
    }

    #[inline]
    pub fn push_front(&mut self, elt: T) -> LinkedListResult<Iter<T>> {
        self.push_front_node(Rc::new(RefCell::new(NodeEntry::new(elt))))
    }

    #[inline]
    pub fn pop_front(&mut self) -> LinkedListResult<()> {
        self.pop_front_node()
    }

    #[inline]
    pub fn push_back(&mut self, elt: T) -> LinkedListResult<Iter<T>> {
        self.push_back_node(Rc::new(RefCell::new(NodeEntry::new(elt))))
    }

    #[inline]
    pub fn pop_back(&mut self) -> LinkedListResult<()> {
        self.pop_back_node()
    }

    #[inline]
    pub fn front(&self) -> LinkedListResult<Ref<T>> {
        if let Some(ref head_node) = self.head {
            try_borrow_node(head_node)
        } else {
            Err(LinkedListError::Empty)
        }
    }

    #[inline]
    pub fn front_mut(&mut self) -> LinkedListResult<Ref<T>> {
        if let Some(ref head_node) = self.head {
            try_borrow_node(head_node)
        } else {
            Err(LinkedListError::Empty)
        }
    }

    #[inline]
    pub fn back(&self) -> LinkedListResult<Ref<T>> {
        if let Some(ref tail_node) = self.tail {
            try_borrow_node(tail_node)
        } else {
            Err(LinkedListError::Empty)
        }
    }

    #[inline]
    pub fn back_mut(&mut self) -> LinkedListResult<RefMut<T>> {
        if let Some(ref tail_node) = self.tail {
            try_borrow_mut_node(tail_node)
        } else {
            Err(LinkedListError::Empty)
        }
    }

    #[inline]
    pub fn contains_iter(&self, iter: &Iter<T>) -> bool {
        if iter.node.is_none() {
            return false;
        }

        let entry = if let Ok(x) = iter.node.as_ref().unwrap().try_borrow() {
            x
        } else {
            return false;
        };

        unsafe { ptr::eq(entry.owner.as_ref().unwrap().as_ref(), self) }
    }

    #[inline]
    pub fn insert_before(&mut self, iter: &mut Iter<T>, elt: T) -> LinkedListResult<Iter<T>> {
        if !self.contains_iter(iter) {
            return Err(LinkedListError::IteratorNotInList);
        }

        LinkedList::insert_before_node(
            iter.node.as_mut().unwrap(),
            Rc::new(RefCell::new(NodeEntry::new(elt))),
        )
    }

    #[inline]
    pub fn insert_after(&mut self, iter: &mut Iter<T>, elt: T) -> LinkedListResult<Iter<T>> {
        if !self.contains_iter(iter) {
            return Err(LinkedListError::IteratorNotInList);
        }

        LinkedList::insert_after_node(
            iter.node.as_mut().unwrap(),
            Rc::new(RefCell::new(NodeEntry::new(elt))),
        )
    }

    #[inline]
    pub fn remove_iter(&mut self, iter: Iter<T>) -> LinkedListResult<()> {
        if let Some(tail_node) = iter.node {
            LinkedList::unlink_node(tail_node)
        } else {
            Err(LinkedListError::Empty)
        }
    }
}

impl<T> Default for LinkedList<T> {
    /// Creates an empty `LinkedList<T>`.
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}
