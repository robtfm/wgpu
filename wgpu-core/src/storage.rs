use std::{marker::PhantomData, ops, sync::Arc};

use wgt::Backend;

use crate::{id, resource::Resource, Epoch, FastHashMap, Index};

/// An entry in a `Storage::map` table.
#[derive(Debug)]
pub(crate) enum Element<T> {
    /// There are no live ids with this index.
    Vacant,

    /// There is one live id with this index, allocated at the given
    /// epoch.
    Occupied(Arc<T>, Epoch),

    /// Like `Occupied`, but an error occurred when creating the
    /// resource.
    ///
    /// The given `String` is the resource's descriptor label.
    Error(Epoch, String),
}

#[derive(Clone, Debug)]
pub(crate) struct InvalidId;

#[derive(Debug)]
pub(crate) struct VecLike<T> {
    size: usize,
    members: FastHashMap<usize, Element<T>>,
    vacant: Element<T>,
}

impl<T> VecLike<T> {
    fn new() -> Self {
        Self {
            size: 0,
            members: Default::default(),
            vacant: Element::Vacant,
        }
    }
    fn get(&self, ix: usize) -> Option<&Element<T>> {
        (ix < self.size).then_some(self.members.get(&ix).unwrap_or(&self.vacant))
    }

    pub(crate) fn iter_nonvacant(&self) -> impl Iterator<Item = (&usize, &Element<T>)> {
        self.members.iter()
    }

    pub(crate) fn iter_all(&self) -> impl Iterator<Item = &Element<T>> {
        (0..self.size).map(|ix| self.members.get(&ix).unwrap_or(&self.vacant))
    }

    pub(crate) fn clear(&mut self) {
        self.members.clear();
        self.size = 0;
    }

    pub(crate) fn drain_nonvacant(&mut self) -> impl Iterator<Item = Element<T>> + '_ {
        self.size = 0;
        self.members.drain().map(|(_, elt)| elt)
    }
}

/// A table of `T` values indexed by the id type `I`.
///
/// The table is represented as a vector indexed by the ids' index
/// values, so you should use an id allocator like `IdentityManager`
/// that keeps the index values dense and close to zero.
#[derive(Debug)]
pub struct Storage<T, I>
where
    T: Resource<I>,
    I: id::TypedId,
{
    pub(crate) map: VecLike<T>,
    kind: &'static str,
    _phantom: PhantomData<I>,
}

impl<T, I> ops::Index<I> for Storage<T, I>
where
    T: Resource<I>,
    I: id::TypedId,
{
    type Output = Arc<T>;
    fn index(&self, id: I) -> &Arc<T> {
        self.get(id).unwrap()
    }
}
impl<T, I> Storage<T, I>
where
    T: Resource<I>,
    I: id::TypedId,
{
    pub(crate) fn new() -> Self {
        Self {
            map: VecLike::new(),
            kind: T::TYPE,
            _phantom: PhantomData,
        }
    }
}

impl<T, I> Storage<T, I>
where
    T: Resource<I>,
    I: id::TypedId,
{
    #[allow(dead_code)]
    pub(crate) fn contains(&self, id: I) -> bool {
        let (index, epoch, _) = id.unzip();
        match self.map.get(index as usize) {
            Some(&Element::Vacant) => false,
            Some(&Element::Occupied(_, storage_epoch) | &Element::Error(storage_epoch, _)) => {
                storage_epoch == epoch
            }
            None => false,
        }
    }

    /// Attempts to get a reference to an item behind a potentially invalid ID.
    ///
    /// Returns [`None`] if there is an epoch mismatch, or the entry is empty.
    ///
    /// This function is primarily intended for the `as_hal` family of functions
    /// where you may need to fallibly get a object backed by an id that could
    /// be in a different hub.
    pub(crate) fn try_get(&self, id: I) -> Result<Option<&Arc<T>>, InvalidId> {
        let (index, epoch, _) = id.unzip();
        let (result, storage_epoch) = match self.map.get(index as usize) {
            Some(&Element::Occupied(ref v, epoch)) => (Ok(Some(v)), epoch),
            Some(&Element::Vacant) => return Ok(None),
            Some(&Element::Error(epoch, ..)) => (Err(InvalidId), epoch),
            None => return Err(InvalidId),
        };
        assert_eq!(
            epoch, storage_epoch,
            "{}[{:?}] is no longer alive",
            self.kind, id
        );
        result
    }

    /// Get a reference to an item behind a potentially invalid ID.
    /// Panics if there is an epoch mismatch, or the entry is empty.
    pub(crate) fn get(&self, id: I) -> Result<&Arc<T>, InvalidId> {
        let (index, epoch, _) = id.unzip();
        let (result, storage_epoch) = match self.map.get(index as usize) {
            Some(&Element::Occupied(ref v, epoch)) => (Ok(v), epoch),
            Some(&Element::Vacant) => panic!("{}[{:?}] does not exist", self.kind, id),
            Some(&Element::Error(epoch, ..)) => (Err(InvalidId), epoch),
            None => return Err(InvalidId),
        };
        assert_eq!(
            epoch, storage_epoch,
            "{}[{:?}] is no longer alive",
            self.kind, id
        );
        result
    }

    /// Get an owned reference to an item behind a potentially invalid ID.
    /// Panics if there is an epoch mismatch, or the entry is empty.
    pub(crate) fn get_owned(&self, id: I) -> Result<Arc<T>, InvalidId> {
        Ok(Arc::clone(self.get(id)?))
    }

    pub(crate) fn label_for_invalid_id(&self, id: I) -> &str {
        let (index, _, _) = id.unzip();
        match self.map.get(index as usize) {
            Some(Element::Error(_, label)) => label,
            _ => "",
        }
    }

    fn insert_impl(&mut self, index: usize, epoch: Epoch, element: Element<T>) {
        if index >= self.map.size {
            if index / 100 > self.map.size / 100 {
                println!("storage {} -> {}", std::any::type_name::<T>(), index);
            } 
            self.map.size = index + 1;
        }
        match self.map.members.insert(index, element) {
            None => {}
            Some(Element::Occupied(_, storage_epoch)) => {
                assert_ne!(
                    epoch,
                    storage_epoch,
                    "Index {index:?} of {} is already occupied",
                    T::TYPE
                );
            }
            Some(Element::Error(storage_epoch, _)) => {
                assert_ne!(
                    epoch,
                    storage_epoch,
                    "Index {index:?} of {} is already occupied with Error",
                    T::TYPE
                );
            }
            _ => panic!(),
        }
    }

    pub(crate) fn insert(&mut self, id: I, value: Arc<T>) {
        log::trace!("User is inserting {}{:?}", T::TYPE, id);
        let (index, epoch, _backend) = id.unzip();
        self.insert_impl(index as usize, epoch, Element::Occupied(value, epoch))
    }

    pub(crate) fn insert_error(&mut self, id: I, label: &str) {
        log::trace!("User is insering as error {}{:?}", T::TYPE, id);
        let (index, epoch, _) = id.unzip();
        self.insert_impl(
            index as usize,
            epoch,
            Element::Error(epoch, label.to_string()),
        )
    }

    pub(crate) fn replace_with_error(&mut self, id: I) -> Result<Arc<T>, InvalidId> {
        let (index, epoch, _) = id.unzip();
        match self.map.members.insert(index as usize, Element::Error(epoch, String::new())) {
            None => panic!("Cannot access vacant resource"),
            Some(Element::Occupied(value, storage_epoch)) => {
                assert_eq!(epoch, storage_epoch);
                Ok(value)
            }
            _ => Err(InvalidId),
        }
    }

    pub(crate) fn force_replace(&mut self, id: I, value: T) {
        log::trace!("User is replacing {}{:?}", T::TYPE, id);
        let (index, epoch, _) = id.unzip();
        self.map.members.insert(index as usize, Element::Occupied(Arc::new(value), epoch));
    }

    pub(crate) fn remove(&mut self, id: I) -> Option<Arc<T>> {
        log::trace!("User is removing {}{:?}", T::TYPE, id);
        let (index, epoch, _) = id.unzip();
        match self.map.members.remove(&(index as usize)) {
            Some(Element::Occupied(value, storage_epoch)) => {
                assert_eq!(epoch, storage_epoch);

                if self.map.members.capacity() > self.map.members.len() * 2 {
                    self.map.members.shrink_to_fit();
                }

                Some(value)
            }
            Some(Element::Error(..)) => None,
            None => panic!("Cannot remove a vacant resource"),
            _ => panic!(),
        }
    }

    pub(crate) fn iter(&self, backend: Backend) -> impl Iterator<Item = (I, &Arc<T>)> {
        self.map
            .iter_nonvacant()
            .filter_map(move |(index, x)| match *x {
                Element::Occupied(ref value, storage_epoch) => {
                    Some((I::zip(*index as Index, storage_epoch, backend), value))
                }
                _ => None,
            })
    }

    pub(crate) fn kind(&self) -> &str {
        self.kind
    }

    pub(crate) fn len(&self) -> usize {
        self.map.size
    }
}
