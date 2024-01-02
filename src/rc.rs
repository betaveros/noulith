// "To err is human; to really foul things up requires a computer." — Bill Vaughan
// https://stackoverflow.com/questions/59362883/is-it-possible-to-have-conditional-trait-inheritance-such-as-send-sync-using

#[cfg(not(feature = "parallel"))]
mod inner {
    use std::cell::{BorrowError, BorrowMutError};
    pub use std::cell::{Ref, RefCell, RefMut};
    pub use std::rc::Rc;

    pub fn cell_borrow<T>(c: &RefCell<T>) -> Ref<'_, T> {
        c.borrow()
    }

    pub fn cell_try_borrow<T>(c: &RefCell<T>) -> Result<Ref<'_, T>, BorrowError> {
        c.try_borrow()
    }

    pub fn cell_borrow_mut<T>(c: &RefCell<T>) -> RefMut<'_, T> {
        c.borrow_mut()
    }

    pub fn cell_try_borrow_mut<T>(c: &RefCell<T>) -> Result<RefMut<'_, T>, BorrowMutError> {
        c.try_borrow_mut()
    }

    pub trait MaybeSync {}
    impl<T> MaybeSync for T where T: ?Sized {}
    pub trait MaybeSend {}
    impl<T> MaybeSend for T where T: ?Sized {}
}

#[cfg(feature = "parallel")]
mod inner {
    pub use std::sync::Arc as Rc;
    pub use std::sync::RwLock as RefCell;
    pub use std::sync::RwLockReadGuard as Ref;
    pub use std::sync::RwLockWriteGuard as RefMut;
    use std::sync::TryLockResult;

    pub fn cell_borrow<T>(c: &RefCell<T>) -> Ref<'_, T> {
        c.read().unwrap()
    }

    pub fn cell_try_borrow<T>(c: &RefCell<T>) -> TryLockResult<Ref<'_, T>> {
        c.try_read()
    }

    pub fn cell_borrow_mut<T>(c: &RefCell<T>) -> RefMut<'_, T> {
        c.write().unwrap()
    }

    pub fn cell_try_borrow_mut<T>(c: &RefCell<T>) -> TryLockResult<RefMut<'_, T>> {
        c.try_write()
    }

    pub use core::marker::Send as MaybeSend;
    pub use core::marker::Sync as MaybeSync;
}

pub use inner::*;
