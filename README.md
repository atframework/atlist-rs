# atlist

[![github action badge]][github action url]
[![codecov badge]][coverage status]
[![crates.io badge]][crates.io package]
[![docs.rs badge]][docs.rs documentation]
[![license badge]][license]

[Documentation]

A LinkedList in which the liftime of iterator is independent from LinkedList.So it's allowed to store iterator into anywhere and insert/remove element by iterator at any time.

Adding, removing and moving a iterator does not invalidate other iterators or references. An iterator is invalidated only when the corresponding element is deleted.

We use ```core::cell::RefCell``` and ```std::sync::Arc``` to manange lifetime of real data entry, so it's slightly slower than ```std::collections::LinkedList``` .


[github action badge]: https://github.com/atframework/atlist-rs/actions/workflows/build.yml/badge.svg
[github action url]: https://github.com/atframework/atlist-rs/actions/workflows/build.yml
[codecov badge]: https://codecov.io/gh/atframework/atlist-rs/branch/master/graph/badge.svg
[coverage status]: https://codecov.io/gh/atframework/atlist-rs
[crates.io badge]: https://img.shields.io/crates/v/atlist-rs.svg
[crates.io package]: https://crates.io/crates/atlist-rs/
[documentation]: https://docs.rs/atlist-rs/
[docs.rs badge]: https://docs.rs/atlist-rs/badge.svg
[docs.rs documentation]: (https://docs.rs/atlist-rs/)
[license badge]: https://img.shields.io/crates/l/atlist-rs
[license]: (https://github.com/atframework/atlist-rs/blob/master/LICENSE)
