# atlist

下一代libatbus通信层中间件

A LinkedList which is allowed to insert/remove element by immutable iterator.The liftime of iterator is also independt with LinkedList.

Adding, removing and moving the elements within the list or across several lists does not invalidate the iterators or references. An iterator is invalidated only when the corresponding element is deleted.

We use ```core::cell::RefCell``` and ```std::rc::Rc``` to manange lifetime of real data entry, so it's slightly slower than ```std::collections::LinkedList```.

User should use ```try_borrow``` or ```try_borrow_mut``` to borrow value in ```Iter```. Just like the APIs in ```std::cell::RefCell``` .