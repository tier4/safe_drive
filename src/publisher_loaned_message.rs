use std::{mem::MaybeUninit, ptr::null_mut, sync::Arc};

use crate::{
    error::{DynError, RCLResult},
    msg::TypeSupport,
    rcl,
};

pub enum PublisherLoanedMessage<T: TypeSupport> {
    Copied(Copied<T>),
    Loaned(Loaned<T>),
}

impl<T: TypeSupport> PublisherLoanedMessage<T> {
    pub fn new(publisher: Arc<rcl::rcl_publisher_t>) -> RCLResult<Self> {
        if rcl::MTSafeFn::rcl_publisher_can_loan_messages(publisher.as_ref() as *const _) {
            Ok(Self::Loaned(Loaned::new(publisher)?))
        } else {
            // Allocate if loaning is not available
            Ok(Self::Copied(Copied::new(publisher)))
        }
    }

    pub fn send(self) -> Result<(), DynError> {
        match self {
            PublisherLoanedMessage::Copied(msg) => {
                if let Err(e) = rcl::MTSafeFn::rcl_publish(
                    msg.publisher.as_ref(),
                    &msg.value as *const T as _,
                    null_mut(),
                ) {
                    return Err(e.into());
                }
            }
            PublisherLoanedMessage::Loaned(mut msg) => {
                if let Err(e) = rcl::MTSafeFn::rcl_publish_loaned_message(
                    msg.publisher.as_ref(),
                    msg.into_raw() as *const _ as *mut _,
                    null_mut(),
                ) {
                    return Err(e.into());
                }

                // rcl_publish_loaned_message returns the loaned chunk to the middleware.
                msg.returned = true;
            }
        }

        Ok(())
    }
}

impl<T: TypeSupport> std::ops::Deref for PublisherLoanedMessage<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            PublisherLoanedMessage::Copied(msg) => &msg.value,
            PublisherLoanedMessage::Loaned(msg) => msg.get(),
        }
    }
}

impl<T: TypeSupport> std::ops::DerefMut for PublisherLoanedMessage<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            PublisherLoanedMessage::Copied(msg) => &mut msg.value,
            PublisherLoanedMessage::Loaned(inner) => inner.get(),
        }
    }
}

pub struct Copied<T: TypeSupport> {
    publisher: Arc<rcl::rcl_publisher_t>,
    value: T,
}

impl<T: TypeSupport> Copied<T> {
    pub fn new(publisher: Arc<rcl::rcl_publisher_t>) -> Self {
        let value: T = unsafe { MaybeUninit::zeroed().assume_init() };
        Self { publisher, value }
    }
}

pub struct Loaned<T: TypeSupport> {
    publisher: Arc<rcl::rcl_publisher_t>,
    chunk: *mut T,
    returned: bool,
}

impl<T: TypeSupport> Loaned<T> {
    pub fn new(publisher: Arc<rcl::rcl_publisher_t>) -> RCLResult<Self> {
        let mut chunk = null_mut();
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard.rcl_borrow_loaned_message(publisher.as_ref(), T::type_support(), &mut chunk)?;
        Ok(Self {
            publisher,
            chunk: chunk as *mut T,
            returned: false,
        })
    }

    pub fn get(&self) -> &mut T {
        unsafe { &mut *self.chunk }
    }

    pub fn into_raw(&self) -> *mut T {
        self.chunk
    }

    pub fn send(mut self) -> Result<(), DynError> {
        if let Err(e) = rcl::MTSafeFn::rcl_publish_loaned_message(
            self.publisher.as_ref(),
            self.into_raw() as *const _ as *mut _,
            null_mut(),
        ) {
            return Err(e.into());
        }

        // rcl_publish_loaned_message returns the loaned chunk to the middleware.
        self.returned = true;

        Ok(())
    }
}

impl<T: TypeSupport> Drop for Loaned<T> {
    fn drop(&mut self) {
        if self.returned {
            return;
        }

        let guard = rcl::MT_UNSAFE_FN.lock();
        let _ = guard.rcl_return_loaned_message_from_publisher(
            self.publisher.as_ref(),
            self.chunk as *const _ as *mut _,
        );
    }
}
