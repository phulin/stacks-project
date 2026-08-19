import Formalization.Books.Algebra.Unit154.FilteredColimitsEtale
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Pro-étale Cohomology, Chapter 7: Ind-étale algebra

The source's ind-étale predicate is the canonical filtered-colimit-of-étale
predicate from Algebra, Chapter 154.  This file records the chapter's
source-facing closure statements and the categorical interface for the lift
along a quotient.
-/

namespace Formalization.Books.Proetale.Unit07

open CategoryTheory CategoryTheory.Limits
open Formalization.Books.Algebra.Unit154
open scoped TensorProduct

universe u v

noncomputable section

/-! ## The definition and permanence properties -/

/-- The source's term “ind-étale” is the existing filtered-colimit-of-étale
predicate for a ring map. -/
abbrev IsIndEtale {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  Formalization.Books.Algebra.Unit154.IsFilteredColimitOfEtale f

/-- Base change preserves ind-étale ring maps.  The target is written in the
canonical tensor-product form used by Mathlib. -/
theorem indEtale_baseChange
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (f : A →+* B) (g : A →+* A')
    (hf : IsIndEtale f) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A A' := g.toAlgebra
    IsIndEtale
      (Algebra.TensorProduct.includeLeftRingHom :
        A' →+* A' ⊗[A] B) := by
  exact @base_change_colimit_etale A B A' _ _ _ f.toAlgebra g.toAlgebra hf

/-- The composite of ind-étale ring maps is ind-étale. -/
theorem indEtale_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hf : IsIndEtale f) (hg : IsIndEtale g) :
    IsIndEtale (g.comp f) :=
  composition_colimit_etale f g hf hg

/-- An outer filtered colimit of ind-étale algebras is ind-étale. -/
theorem indEtale_filteredColimit
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B)
    (h : Nonempty (FilteredEtaleStagesColimit f)) :
    IsIndEtale f :=
  colimit_colimit_etale f h

/-- If `B` and `C` are ind-étale `A`-algebras, then an `A`-algebra map
`B → C` exhibits `C` as ind-étale over `B`. -/
theorem indEtale_permanence
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C)
    (hB : IsIndEtale (algebraMap A B))
    (hC : IsIndEtale (algebraMap A C)) :
    IsIndEtale f.toRingHom := by
  apply colimits_of_etale f.toRingHom ?_ hB hC
  ext x
  exact f.commutes x

/-- Every ind-étale ring map is weakly étale. -/
theorem indEtale_isWeaklyEtale
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : IsIndEtale f) :
    letI : Algebra A B := f.toAlgebra
    Algebra.WeaklyEtale A B := by
  sorry

/-! ## The lifting statement -/

/-- The category of ind-étale `A`-algebras, as a full subcategory of
`CommAlgCat A`.  The property is Mathlib/Algebra's canonical filtered
colimit presentation, so no parallel notion of ind-étale algebra is defined.
-/
def indEtaleAlgebraProperty (A : Type u) [CommRing A] :
    ObjectProperty (CommAlgCat.{u} A) :=
  fun B => IsIndEtale (algebraMap A B)

abbrev IndEtaleAlgebra (A : Type u) [CommRing A] :=
  (indEtaleAlgebraProperty A).FullSubcategory

/-- A categorical interface for the source's base-change functor
`C ↦ C/IC`.  The object comparison is stated in `CommAlgCat` because the
quotient object is canonical there, while the ind-étale condition is carried
by the full-subcategory source and target. -/
structure IndEtaleBaseChangeData
    (A : Type u) [CommRing A] (I : Ideal A) where
  functor : IndEtaleAlgebra A ⥤ IndEtaleAlgebra (A ⧸ I)
  objectIso : ∀ X : IndEtaleAlgebra A, Nonempty
    ((functor.obj X).obj ≅
      CommAlgCat.of (A ⧸ I)
        (X.obj ⧸ Ideal.map (algebraMap A X.obj) I))

/-- The right-adjoint lifting assertion from the source.  The first natural
isomorphism records `u ∘ v = id`, and the second conjunct records the stated
full faithfulness of `v`. -/
theorem indEtale_lift_rightAdjoint
    (A : Type u) [CommRing A] (I : Ideal A) :
    ∃ (U : IndEtaleBaseChangeData A I)
      (V : IndEtaleAlgebra (A ⧸ I) ⥤ IndEtaleAlgebra A),
      Nonempty (U.functor ⊣ V) ∧
        Nonempty V.FullyFaithful ∧
        Nonempty (V.comp U.functor ≅ 𝟭 (IndEtaleAlgebra (A ⧸ I))) := by
  sorry

/-- A source-facing witness for the “in particular” clause of the lifting
lemma: every ind-étale algebra over `A/I` has an ind-étale lift over `A`,
whose quotient by `I` is isomorphic to it as an `A/I`-algebra. -/
structure IndEtaleLift
    (A : Type u) [CommRing A] (I : Ideal A)
    (Cbar : Type u) [CommRing Cbar] [Algebra (A ⧸ I) Cbar] where
  carrier : Type u
  [commRingCarrier : CommRing carrier]
  [algebraCarrier : Algebra A carrier]
  indEtale : IsIndEtale (algebraMap A carrier)
  quotientIso : Nonempty
    ((carrier ⧸ Ideal.map (algebraMap A carrier) I) ≃ₐ[A ⧸ I] Cbar)

theorem exists_indEtale_lift
    (A : Type u) [CommRing A] (I : Ideal A)
    (Cbar : Type u) [CommRing Cbar] [Algebra (A ⧸ I) Cbar]
    (hCbar : IsIndEtale (algebraMap (A ⧸ I) Cbar)) :
    Nonempty (IndEtaleLift A I Cbar) := by
  sorry

end

end Formalization.Books.Proetale.Unit07
