use ark_std::borrow::Borrow;
use ark_std::num::NonZeroUsize;

use crate::iterable::Iterable;

#[derive(Clone, Copy)]
pub struct LookupStreamer<'a, S, I>
where
    S: Iterable,
    I: Iterable,
{
    pub(crate) items: &'a S,
    pub(crate) indices: &'a I,
}

pub struct LookupIter<I, II>
where
    I: Iterator,
    II: Iterator,
    II::Item: Borrow<usize>,
{
    item_stream: I,
    index_stream: II,
    current_height: usize,
    current_item: Option<I::Item>,
}

impl<'a, S, I> LookupStreamer<'a, S, I>
where
    S: Iterable,
    I: Iterable,
    S::Item: Copy,
    I::Item: Borrow<usize>,
{
    pub fn new(items: &'a S, indices: &'a I) -> Self {
        Self { items, indices }
    }
}

impl<'a, S, I> Iterable for LookupStreamer<'a, S, I>
where
    S: Iterable,
    I: Iterable,
    S::Item: Copy,
    I::Item: Borrow<usize>,
{
    type Item = S::Item;

    type Iter = LookupIter<S::Iter, I::Iter>;

    fn iter(&self) -> Self::Iter {
        LookupIter {
            item_stream: self.items.iter(),
            index_stream: self.indices.iter(),
            current_height: self.items.len(),
            current_item: None,
        }
    }

    fn len(&self) -> usize {
        self.indices.len()
    }
}

impl<I, II> Iterator for LookupIter<I, II>
where
    I: Iterator,
    I::Item: Copy,
    II: Iterator,
    II::Item: Borrow<usize>,
{
    type Item = I::Item;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let &index = self.index_stream.next()?.borrow();
        if self.current_height == index {
            self.current_item
        } else if self.current_height > index {
            let delta = self.current_height - index - 1;
            self.item_stream.advance_by(delta).ok()?;
            let item = self.item_stream.next();
            self.current_height = index;
            self.current_item = item;
            item
        } else {
            panic!("unsorted indices!")
        }
    }

    fn advance_by(&mut self, n: usize) -> Result<(), NonZeroUsize> {
        self.index_stream.advance_by(n)
    }
}

#[test]
fn test_index() {
    use ark_std::vec::Vec;

    let indices = &[4, 4, 3, 2, 1, 0];
    let items = &[8, 7, 6, 5, 4, 3, 2, 1, 0];

    let stream = LookupStreamer::new(&items, &indices);
    let stream = stream.iter().cloned().collect::<Vec<_>>();
    assert_eq!(stream, indices);
}
