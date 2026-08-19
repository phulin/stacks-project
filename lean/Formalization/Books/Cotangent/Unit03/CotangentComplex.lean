import Formalization.Books.Cotangent.Unit03.StandardResolution
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The cotangent complex from a simplicial module

The source forms the simplicial `B`-module
`Ω[P_•/A] ⊗_{P_•, ε} B` and then applies the alternating face-map complex.
The former construction changes the base ring degree by degree and is not a
single Mathlib functor.  This file therefore packages that simplicial module
with its canonical degreewise tensor terms, and applies Mathlib's actual
alternating-face-map and extension constructions to it.
-/

namespace Formalization.Books.Cotangent.Unit03

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open scoped _root_.Simplicial TensorProduct

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-! ## Degreewise tensor terms -/

/-- The augmentation map in simplicial degree `n`. -/
noncomputable def standardResolutionAugmentationMap (n : ℕ) :
    iteratedPolynomial A (n + 1) B →+* B :=
  ((standardResolutionAugmentation (A := A) (B := B)).hom.app
      (Opposite.op (SimplexCategory.mk n))).hom

/-- The degree-`n` module `Ω[P_n/A] ⊗_{P_n} B`. -/
noncomputable def standardCotangentTerm (n : ℕ) : Type u :=
  let P := iteratedPolynomial A (n + 1) B
  let ε := standardResolutionAugmentationMap (A := A) (B := B) n
  letI := ε.toAlgebra
  -- The factors are written in the symmetric order `B ⊗[P] Ω[P/A]`,
  -- which exposes the canonical `B`-module structure.
  TensorProduct P B (KaehlerDifferential A P)

noncomputable instance standardCotangentTermAddCommGroup (n : ℕ) :
    AddCommGroup (standardCotangentTerm (A := A) (B := B) n) := by
  let P := iteratedPolynomial A (n + 1) B
  let ε := standardResolutionAugmentationMap (A := A) (B := B) n
  letI := ε.toAlgebra
  change AddCommGroup (TensorProduct P B (KaehlerDifferential A P))
  infer_instance

noncomputable instance standardCotangentTermModule (n : ℕ) :
    Module B (standardCotangentTerm (A := A) (B := B) n) := by
  let P := iteratedPolynomial A (n + 1) B
  let ε := standardResolutionAugmentationMap (A := A) (B := B) n
  letI := ε.toAlgebra
  change Module B (TensorProduct P B (KaehlerDifferential A P))
  infer_instance

/-- A simplicial `B`-module with the degreewise terms required by the source. -/
structure CotangentSimplicialModule (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] where
  module : SimplicialObject (ModuleCat.{u} B)
  termIso : ∀ n : ℕ,
    module.obj (Opposite.op (SimplexCategory.mk n)) ≅
      ModuleCat.of B (standardCotangentTerm (A := A) (B := B) n)

/-! ## Alternating face-map complex -/

/-- The cochain complex associated to a cotangent simplicial module.

The `embeddingDownNat` extension places simplicial degree `n` in cochain degree
`-n` and makes all positive degrees zero, exactly as in the source convention.
-/
noncomputable def cotangentComplex (Q : CotangentSimplicialModule (A := A) (B := B)) :
    CochainComplex (ModuleCat.{u} B) ℤ :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} B)).obj Q.module |>.extend
    ComplexShape.embeddingDownNat

noncomputable def cotangentComplex_degree (Q : CotangentSimplicialModule (A := A) (B := B))
    (n : ℕ) :
    (cotangentComplex Q).X (-(n : ℤ)) ≅
      Q.module.obj (Opposite.op (SimplexCategory.mk n)) :=
  HomologicalComplex.extendXIso
    ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} B)).obj Q.module)
    ComplexShape.embeddingDownNat (by rfl)

/-- The degree identification with the source's tensor-product term. -/
noncomputable def cotangentComplex_term (Q : CotangentSimplicialModule (A := A) (B := B))
    (n : ℕ) :
    (cotangentComplex Q).X (-(n : ℤ)) ≅
      ModuleCat.of B (standardCotangentTerm (A := A) (B := B) n) :=
  (cotangentComplex_degree Q n).trans (Q.termIso n)

theorem cotangentComplex_positive_degree (Q : CotangentSimplicialModule (A := A) (B := B))
    (m : ℤ) (hm : 0 < m) : CategoryTheory.Limits.IsZero ((cotangentComplex Q).X m) := by
  sorry

/-!
The textbook's filtered-colimit lemma is recorded at the level of complexes
as the canonical comparison property below.  The source does not specify the
transition maps on the cotangent complexes, so those maps are necessarily part
of the diagram parameter here.
-/
def CotangentComplexColimitStatement {I : Type u} [Preorder I]
    (D : I ⥤ CochainComplex (ModuleCat.{u} B) ℤ)
  (L : CochainComplex (ModuleCat.{u} B) ℤ) : Prop :=
  ∃ c : Cocone D, Nonempty (IsColimit c) ∧ Nonempty (L ≅ c.pt)

end Formalization.Books.Cotangent.Unit03
