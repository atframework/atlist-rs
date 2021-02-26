# atlist

A LinkedList in which the liftime of iterator is independent from LinkedList.So it's allowed to store iterator into anywhere and insert/remove element by iterator at any time.

Adding, removing and moving a iterator does not invalidate other iterators or references. An iterator is invalidated only when the corresponding element is deleted.

We use ```core::cell::RefCell``` and ```std::sync::Arc``` to manange lifetime of real data entry, so it's slightly slower than ```std::collections::LinkedList```.
