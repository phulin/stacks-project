import Formalization.Books.Topology.Unit02.BasicNotions

/-!
# Sheaves on Spaces, Chapter 2: Basic notions

The first item of the source section fixes the meaning of an indexed open
covering.  It is already represented by the earlier chapter's
`Formalization.Books.Topology.Unit02.IsOpenCoverOf`: for a set `U` in a
topological space `X` and a family `u : ι → Set X`, it asserts that every
`u i` is open and that `⋃ i, u i = U`.  Thus it also records the source's
conventions that empty members are allowed and that an empty index type covers
exactly the empty set; the latter is the existing theorem
`Formalization.Books.Topology.Unit02.isOpenCoverOf_empty_index_iff`.

The second list item is literally `etc., etc.` and contains no precise
mathematical assertion to formalize.
-/
