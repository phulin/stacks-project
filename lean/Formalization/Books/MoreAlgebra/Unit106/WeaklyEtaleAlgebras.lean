/-
# More on Algebra, Chapter 106: Weakly étale algebras over fields
-/

import Formalization.Books.MoreAlgebra.Unit105.WeaklyEtale
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Idempotents

/-!
This file records the statements in the section on weakly étale algebras over
fields.  `Algebra.WeaklyEtale` and `Algebra.Etale` are the canonical Mathlib
predicates.  The maximal subalgebra is represented by a chosen greatest
weakly étale subalgebra; this is the form used by the source proofs.
-/

namespace Formalization.Books.MoreAlgebra.Unit106

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

universe u v

/-! ## Weakly étale algebras over a field -/

/- The source's filtered-colimit assertion is expressed for a specified
   filtered presentation, using the presentation predicate from Chapter 105. -/
theorem weaklyEtale_over_field_iff_filteredColimit_etale
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    {J : Type v} [Category J] [IsFiltered J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F) :
    Algebra.WeaklyEtale K B ↔
      Formalization.Books.MoreAlgebra.Unit105.IsFilteredColimitOfEtale K B F c := by
  exact Formalization.Books.MoreAlgebra.Unit105.absolutelyFlat_over_field_iff_filteredColimit_etale
    F c

def ExistsFilteredColimitOfEtaleAlgebra
    {K B : Type u} [Field K] [CommRing B] [Algebra K B] : Prop :=
  ∃ J : Type u, ∃ hJ : Category.{u} J,
    ∃ hfiltered : @IsFiltered.{u, u} J hJ,
    letI : Category.{u} J := hJ
    letI : IsFiltered J := hfiltered
    ∃ (F : J ⥤ CommAlgCat K) (c : Cocone F),
      Formalization.Books.MoreAlgebra.Unit105.IsFilteredColimitOfEtale K B F c

theorem weaklyEtale_over_field_iff_exists_filteredColimit_etale
    {K B : Type u} [Field K] [CommRing B] [Algebra K B] :
    Algebra.WeaklyEtale K B ↔
      ExistsFilteredColimitOfEtaleAlgebra (K := K) (B := B) := by
  sorry

/-! ## The classification lemma -/

def NoNontrivialIdempotents (A : Type u) [CommRing A] : Prop :=
  ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1

theorem weaklyEtale_field_isReduced
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    [Algebra.WeaklyEtale K B] :
    IsReduced B := by
  exact Formalization.Books.MoreAlgebra.Unit105.reduced_of_weaklyEtale_of_reduced
    (A := K) (B := B) inferInstance

theorem weaklyEtale_field_isIntegral
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    [Algebra.WeaklyEtale K B] :
    RingHom.IsIntegral (algebraMap K B) := by
  sorry

theorem weaklyEtale_finiteType_subalgebra_isFiniteSeparableProduct
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    [Algebra.WeaklyEtale K B]
    (S : Subalgebra K B) [Algebra.FiniteType K S] :
    ∃ (I : Type u) (_ : Finite I) (Ai : I → Type u) (_ : ∀ i, Field (Ai i))
      (_ : ∀ i, Algebra K (Ai i)) (_ : S ≃ₐ[K] Π i, Ai i),
      ∀ i, Module.Finite K (Ai i) ∧ Algebra.IsSeparable K (Ai i) := by
  have hEtale : Algebra.Etale K S :=
    Formalization.Books.MoreAlgebra.Unit105.finitelyGenerated_subalgebra_etale
      (Algebra.WeaklyEtale.flat_lmul' K B) S
  exact (Algebra.Etale.iff_exists_algEquiv_prod K S).mp hEtale

/- A `CommRing` in Lean may be the zero ring.  The source uses the usual
   nonzero-ring convention, so the exact Lean form records nontriviality. -/
theorem weaklyEtale_field_isField_iff_noNontrivialIdempotents
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    [Algebra.WeaklyEtale K B] :
    IsField B ↔ NoNontrivialIdempotents B ∧ Nontrivial B := by
  sorry

theorem weaklyEtale_field_isSeparableAlgebraic_of_isField
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    [Algebra.WeaklyEtale K B] (hB : IsField B) :
    Algebra.IsAlgebraic K B ∧ Algebra.IsSeparable K B := by
  sorry

theorem weaklyEtale_field_subalgebra
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    [Algebra.WeaklyEtale K B] (S : Subalgebra K B) :
    Algebra.WeaklyEtale K S := by
  sorry

theorem weaklyEtale_field_quotient
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    [Algebra.WeaklyEtale K B] (I : Ideal B) :
    Algebra.WeaklyEtale K (B ⧸ I) := by
  sorry

theorem weaklyEtale_field_tensorProduct
    {K B B' : Type u} [Field K] [CommRing B] [CommRing B']
    [Algebra K B] [Algebra K B'] [Algebra.WeaklyEtale K B]
    [Algebra.WeaklyEtale K B'] :
    Algebra.WeaklyEtale K (B ⊗[K] B') := by
  sorry

/-! ## The maximal weakly étale subalgebra -/

def IsMaximalWeaklyEtaleSubalgebra
    (K A : Type u) [Field K] [CommRing A] [Algebra K A]
    (B : Subalgebra K A) : Prop :=
  Algebra.WeaklyEtale K B ∧
    ∀ C : Subalgebra K A, Algebra.WeaklyEtale K C → C ≤ B

theorem exists_maximalWeaklyEtaleSubalgebra
    (K A : Type u) [Field K] [CommRing A] [Algebra K A] :
    ∃ B : Subalgebra K A, IsMaximalWeaklyEtaleSubalgebra K A B := by
  sorry

noncomputable def maximalWeaklyEtaleSubalgebra
    (K A : Type u) [Field K] [CommRing A] [Algebra K A] : Subalgebra K A :=
  Classical.choose (exists_maximalWeaklyEtaleSubalgebra K A)

theorem maximalWeaklyEtaleSubalgebra_spec
    (K A : Type u) [Field K] [CommRing A] [Algebra K A] :
    IsMaximalWeaklyEtaleSubalgebra K A
      (maximalWeaklyEtaleSubalgebra K A) := by
  exact Classical.choose_spec (exists_maximalWeaklyEtaleSubalgebra K A)

theorem maximalWeaklyEtaleSubalgebra_map
    {K A A' : Type u} [Field K] [CommRing A] [CommRing A']
    [Algebra K A] [Algebra K A'] (f : A' →ₐ[K] A) :
    ∃ g : maximalWeaklyEtaleSubalgebra K A' →ₐ[K]
        maximalWeaklyEtaleSubalgebra K A,
      ∀ x, (g x : A) = f x := by
  sorry

theorem maximalWeaklyEtaleSubalgebra_comap
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (S : Subalgebra K A) :
    maximalWeaklyEtaleSubalgebra K S =
      (maximalWeaklyEtaleSubalgebra K A).comap S.val := by
  sorry

/- This elementwise form says that the chosen maximal subalgebra commutes
   with filtered colimits; it avoids choosing a separate functor of chosen
   subalgebras. -/
def IsFilteredColimitOfMaximalWeaklyEtaleSubalgebras
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    {J : Type v} [Category J] [IsFiltered J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F)
    (e : c.pt ≅ CommAlgCat.of K A) : Prop :=
  Nonempty (IsColimit c) ∧
    ∀ x : A, x ∈ maximalWeaklyEtaleSubalgebra K A ↔
      ∃ j : J, ∃ y : F.obj j,
        y ∈ maximalWeaklyEtaleSubalgebra K (F.obj j) ∧
          e.hom (c.ι.app j y) = x

theorem maximalWeaklyEtaleSubalgebra_filteredColimit
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    {J : Type v} [Category J] [IsFiltered J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F)
    (e : c.pt ≅ CommAlgCat.of K A) :
    IsFilteredColimitOfMaximalWeaklyEtaleSubalgebras F c e := by
  sorry

theorem maximalWeaklyEtaleSubalgebra_reducedQuotient
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] :
    Nonempty
      (maximalWeaklyEtaleSubalgebra K A ≃ₐ[K]
        maximalWeaklyEtaleSubalgebra K (A ⧸ nilradical A)) := by
  sorry

theorem maximalWeaklyEtaleSubalgebra_pi
    {K : Type u} [Field K] (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] :
    Nonempty
      (maximalWeaklyEtaleSubalgebra K (∀ i, A i) ≃ₐ[K]
        ∀ i, maximalWeaklyEtaleSubalgebra K (A i)) := by
  sorry

theorem maximalWeaklyEtaleSubalgebra_isField_of_noNontrivialIdempotents
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Nontrivial A]
    (hA : NoNontrivialIdempotents A) :
    IsField (maximalWeaklyEtaleSubalgebra K A) ∧
      Algebra.IsAlgebraic K (maximalWeaklyEtaleSubalgebra K A) ∧
      Algebra.IsSeparable K (maximalWeaklyEtaleSubalgebra K A) := by
  sorry

/-! ## Change of fields -/

theorem maximalWeaklyEtaleSubalgebra_baseChange
    {K L A : Type u} [Field K] [Field L] [Algebra K L]
    [CommRing A] [Algebra K A] :
    Nonempty
      ((maximalWeaklyEtaleSubalgebra K A) ⊗[K] L ≃ₐ[L]
        maximalWeaklyEtaleSubalgebra L (A ⊗[K] L)) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit106
