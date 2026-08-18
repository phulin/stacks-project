import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
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
  let J := Discrete I
  let T : ShortComplex (J ⥤ AddCommGrpCat.{u}) :=
    (ShortComplex.functorEquivalence J (AddCommGrpCat.{u})).inverse.obj
      (Discrete.functor S)
  let F := lim (J := J) (C := AddCommGrpCat.{u})
  let e : T.homology ≅ Discrete.functor (fun i => (S i).homology) :=
    Discrete.natIso (fun i =>
      (T.mapHomologyIso ((evaluation J (AddCommGrpCat.{u})).obj i)).symm ≪≫
        ShortComplex.homologyMapIso
          (show T.map ((evaluation J (AddCommGrpCat.{u})).obj i) ≅ S i.as from
            by simpa [T] using
              ((ShortComplex.FunctorEquivalence.counitIso J (AddCommGrpCat.{u})).app
                (Discrete.functor S)).app i))
  let q : productComplex S ≅ (ShortComplex.limitCone (Discrete.functor S)).pt :=
    (limit.isLimit (Discrete.functor S)).conePointUniqueUpToIso
      (ShortComplex.isLimitLimitCone (Discrete.functor S))
  let r : (ShortComplex.limitCone (Discrete.functor S)).pt ≅ T.map F := by
    exact ShortComplex.isoMk
      (show (ShortComplex.limitCone (Discrete.functor S)).pt.X₁ ≅ (T.map F).X₁ from
        Iso.refl _)
      (show (ShortComplex.limitCone (Discrete.functor S)).pt.X₂ ≅ (T.map F).X₂ from
        Iso.refl _)
      (show (ShortComplex.limitCone (Discrete.functor S)).pt.X₃ ≅ (T.map F).X₃ from
        Iso.refl _)
      (by
        change 𝟙 _ ≫ limMap ((Discrete.functor S).whiskerLeft ShortComplex.π₁Toπ₂) =
          limMap ((Discrete.functor S).whiskerLeft ShortComplex.π₁Toπ₂) ≫ 𝟙 _
        simp)
      (by
        change 𝟙 _ ≫ limMap ((Discrete.functor S).whiskerLeft ShortComplex.π₂Toπ₃) =
          limMap ((Discrete.functor S).whiskerLeft ShortComplex.π₂Toπ₃) ≫ 𝟙 _
        simp)
  let p : productComplex S ≅ T.map F := q ≪≫ r
  exact ⟨ShortComplex.homologyMapIso p ≪≫ T.mapHomologyIso F ≪≫ F.mapIso e⟩

end Formalization.Books.Homology.Unit32
