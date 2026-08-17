import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
# Homological Algebra, Chapter 32: Exactness of products

The source's family of complexes of abelian groups is represented by a family
of `ShortComplex (AddCommGrpCat)`.  Products are the canonical categorical
limits of the corresponding discrete diagrams.  The homology object of a
short complex is Mathlib's kernel/image homology; for abelian groups its
explicit kernel-quotient description is available through
`ShortComplex.abHomologyIso`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Formalization.Books.Homology.Unit32

/-! ## Products of complexes -/

/-- The product complex attached to a family of complexes of abelian groups.

The fact that the two displayed product maps compose to zero is part of the
`ShortComplex` structure supplied by the canonical limit construction. -/
noncomputable def productComplex {I : Type u}
    (S : I → ShortComplex (AddCommGrpCat.{u})) :
    ShortComplex (AddCommGrpCat.{u}) :=
  limit (Discrete.functor S)

/-- The product of the homology groups of a family of complexes. -/
noncomputable def productHomology {I : Type u}
    (S : I → ShortComplex (AddCommGrpCat.{u})) :
    AddCommGrpCat.{u} :=
  limit (Discrete.functor (fun i => (S i).homology))

/-- The homology of a product complex is the product of the homologies. -/
theorem product_abelian_groups_exact {I : Type u}
    (S : I → ShortComplex (AddCommGrpCat.{u})) :
    Nonempty ((productComplex S).homology ≅ productHomology S) := by
  sorry

end Formalization.Books.Homology.Unit32
