import Formalization.Books.Simplicial.Unit20.Augmentations
import Formalization.Books.Simplicial.Unit26.Homotopies
import Formalization.Books.Simplicial.Unit30.TrivialKanFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# Simplicial Methods, Chapter 32: A homotopy equivalence

The source's `cosk₀(A)` is Mathlib's coskeleton of the constant simplicial
set on `A`.  The lifting and homotopy criteria below use the canonical units
of the truncation--coskeleton adjunction.  The final simplicial set is the
Čech nerve of a surjection of sets, using the established finite wide
pullback construction.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit32

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial

universe u

/-! ## The cosk₀ construction and its associated map -/

/-- The constant simplicial set with value `A`. -/
def constantSSet (A : Type u) : SSet.{u} :=
  (SimplicialObject.const (Type u)).obj A

/-- The source's `cosk₀(A)`. -/
def coskZero (A : Type u) : SSet.{u} :=
  (SSet.cosk 0).obj (constantSSet A)

/-- The simplicial map associated to a map of sets `f : A → B`. -/
def coskZeroMap {A B : Type u} (f : A → B) : coskZero A ⟶ coskZero B :=
  (SSet.cosk 0).map
    ((SimplicialObject.const (Type u)).map (TypeCat.ofHom f))

/-- The canonical map from a simplicial set to its `n`-coskeleton. -/
def canonicalCoskeletonMap (n : ℕ) (X : SSet.{u}) :
    X ⟶ (SSet.cosk n).obj X :=
  (SSet.coskAdj n).unit.app X

/-!
The source gives the degreewise formula for a homotopy between two maps of
`cosk₀` objects.  Mathlib's `SSet.Homotopy` is the canonical cylinder
interface for exactly this assertion; the componentwise formula is the
source-facing description of the witness supplied here.
-/

/-- Two maps between `cosk₀` simplicial sets are joined by a simplicial
homotopy. -/
theorem coskZeroMap_homotopy {A B : Type u} (f₀ f₁ : A → B) :
    Nonempty (SSet.Homotopy (coskZeroMap f₀) (coskZeroMap f₁)) := by
  sorry

/-- If a map is bijective below degree `n`, surjective in degree `n`, and
both simplicial sets are `n`-coskeletal, then it is a trivial Kan fibration.
-/
theorem section_lemma {V U : SSet.{u}} (f : V ⟶ U) (n : ℕ)
    (h_bijective : ∀ i : ℕ, i < n →
      Function.Bijective (f.app (op (SimplexCategory.mk i))))
    (h_surjective : Function.Surjective
      (f.app (op (SimplexCategory.mk n))))
    (hU : IsIso (canonicalCoskeletonMap n U))
    (hV : IsIso (canonicalCoskeletonMap n V)) :
    Unit30.TrivialKanFibration f := by
  sorry

/-- The degree-zero case of `section_lemma` for a surjective map of sets. -/
theorem coskZeroMap_trivialKanFibration {A B : Type u} (f : A → B)
    (hf : Function.Surjective f) :
    Unit30.TrivialKanFibration (coskZeroMap f) := by
  sorry

/-! ## Homotopy from agreement below the coskeleton degree -/

/-- Maps agreeing below degree `n` are homotopic when both simplicial sets are
`n`-coskeletal. -/
theorem homotopy_lemma {V U : SSet.{u}} (f₀ f₁ : V ⟶ U) (n : ℕ)
    (h_equal : ∀ i : ℕ, i < n →
      f₀.app (op (SimplexCategory.mk i)) =
        f₁.app (op (SimplexCategory.mk i)))
    (hU : IsIso (canonicalCoskeletonMap n U))
    (hV : IsIso (canonicalCoskeletonMap n V)) :
    Unit26.Homotopic f₀ f₁ := by
  sorry

/-! ## The `cosk₋₁` Čech nerve -/

/-- The wide pullbacks needed for the Čech nerve of a map of types. -/
def hasCechNerveOfFunction {A B : Type u} (f : A → B) :
    Unit20.HasCechNerve (C := Type u) (TypeCat.ofHom f) := by
  intro n
  infer_instance

/-- The simplicial set with degree `n` given by the `(n+1)`-fold fibre
product of `A` over `B`. -/
noncomputable def coskMinusOne {A B : Type u} (f : A → B) : SSet.{u} :=
  letI : ∀ n : ℕ, HasWidePullback B
      (fun _ : Fin (n + 1) => A) (fun _ => TypeCat.ofHom f) :=
    hasCechNerveOfFunction f
  (Arrow.mk (TypeCat.ofHom f)).cechNerve

/-- The canonical augmentation of the Čech nerve to the constant simplicial
set on `B`. -/
noncomputable def coskMinusOneAugmentation {A B : Type u} (f : A → B) :
    coskMinusOne f ⟶ constantSSet B := by
  letI : ∀ n : ℕ, HasWidePullback B
      (fun _ : Fin (n + 1) => A) (fun _ => TypeCat.ofHom f) :=
    hasCechNerveOfFunction f
  exact (Arrow.mk (TypeCat.ofHom f)).augmentedCechNerve.hom

/-- The Čech nerve is the pullback of `cosk₀(A)` along the canonical map
from the constant simplicial set on `B`. -/
theorem coskMinusOne_isPullback {A B : Type u} (f : A → B) :
    ∃ top : coskMinusOne f ⟶ coskZero A,
      IsPullback top (coskMinusOneAugmentation f)
        (coskZeroMap f) (canonicalCoskeletonMap 0 (constantSSet B)) := by
  sorry

/-- A surjection of sets gives a trivial Kan fibration from its Čech nerve
to the constant simplicial set on the target. -/
theorem coskMinusOne_trivialKanFibration {A B : Type u} (f : A → B)
    (hf : Function.Surjective f) :
    Unit30.TrivialKanFibration (coskMinusOneAugmentation f) := by
  sorry

end Formalization.Books.Simplicial.Unit32
