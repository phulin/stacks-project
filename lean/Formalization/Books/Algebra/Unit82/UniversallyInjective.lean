import Formalization.Books.Algebra.Unit81.CharacterizingFlatness
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Module

/-!
# Commutative Algebra, Chapter 82: Universally injective module maps

The source's universal injectivity predicate is expressed using Mathlib's
canonical tensor map LinearMap.rTensor.  Short exact sequences are kept at
the level of linear maps, while directed colimits of short exact sequences use
Mathlib's category of short complexes.
-/

namespace Formalization.Books.Algebra.Unit82

open CategoryTheory
open CategoryTheory.Limits
open scoped BigOperators

universe u v w

noncomputable section

/-! ## Universal injectivity and universal exactness -/

/-- A linear map is universally injective when tensoring it on the right by
every module preserves injectivity. -/
def universallyInjective
    {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) : Prop :=
  ∀ (Q : Type (max u (max v w))) [AddCommGroup Q] [Module R Q],
    Function.Injective (f.rTensor Q)

/-- A short exact sequence is universally exact when its first map remains
injective after every tensor base change. -/
def universallyExact
    {R : Type u} {M₁ : Type v} {M₂ : Type w} {M₃ : Type*}
    [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) : Prop :=
  Function.Injective f₁ ∧ Function.Exact f₁ f₂ ∧
    Function.Surjective f₂ ∧ universallyInjective f₁

/-- A directed colimit presentation of a short exact sequence. -/
structure DirectedUniversallyExactColimitPresentation
    {R : Type u} (M₁ M₂ M₃ : Type u) [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) where
  comp_eq_zero : f₂.comp f₁ = 0
  index : Type u
  [indexCategory : Category.{u} index]
  [indexFiltered : IsFiltered index]
  presentation : ColimitPresentation index
    (ShortComplex.moduleCatMk f₁ f₂ comp_eq_zero)

/-- A directed colimit of split exact sequences with finitely presented third
terms. -/
structure DirectedSplitExactColimitPresentation
    {R : Type u} (M₁ M₂ M₃ : Type u) [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃)
    extends DirectedUniversallyExactColimitPresentation M₁ M₂ M₃ f₁ f₂ where
  stage_split : ∀ i, presentation.diag.obj i |>.ShortExact ∧
    Nonempty (presentation.diag.obj i).Splitting
  finitelyPresented : ∀ i,
    Module.FinitePresentation R (presentation.diag.obj i).X₃

/-- A split short exact sequence is universally exact. -/
theorem universallyExact_of_split
    {R : Type u} {M₁ M₂ M₃ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃}
    (hshort : Function.Injective f₁ ∧ Function.Exact f₁ f₂ ∧
      Function.Surjective f₂)
    (s : M₂ →ₗ[R] M₁) (hs : s.comp f₁ = LinearMap.id) :
    universallyExact f₁ f₂ := by
  sorry

/-- Directed colimits of universally exact short sequences are universally exact. -/
theorem universallyExact_of_directedColimit
    {R : Type u} {M₁ M₂ M₃ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃}
    (P : DirectedUniversallyExactColimitPresentation M₁ M₂ M₃ f₁ f₂)
    (hstage : letI : Category.{u} P.index := P.indexCategory
      letI : IsFiltered P.index := P.indexFiltered
      ∀ i, universallyExact (P.presentation.diag.obj i).f.hom
        (P.presentation.diag.obj i).g.hom) :
    universallyExact f₁ f₂ := by
  sorry

/-- A colimit of split short exact sequences is universally exact. -/
theorem universallyExact_of_directedSplitColimit
    {R : Type u} {M₁ M₂ M₃ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃}
    (P : DirectedSplitExactColimitPresentation M₁ M₂ M₃ f₁ f₂) :
    universallyExact f₁ f₂ := by
  sorry

/-! ## The finite-presentation criteria -/

/-- The six equivalent criteria for a short exact sequence to be universally
exact.  Finite free modules are represented by finitely supported functions. -/
theorem universallyExact_criteria
    {R : Type u} {M₁ M₂ M₃ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃)
    (hshort : Function.Injective f₁ ∧ Function.Exact f₁ f₂ ∧
      Function.Surjective f₂) :
    List.TFAE [
      universallyExact f₁ f₂,
      ∀ (Q : Type u) [AddCommGroup Q] [Module R Q]
        [Module.FinitePresentation R Q],
        Function.Injective (f₁.rTensor Q) ∧
          Function.Exact (f₁.rTensor Q) (f₂.rTensor Q) ∧
            Function.Surjective (f₂.rTensor Q),
      ∀ {n m : ℕ} (x : Fin n → M₁) (y : Fin m → M₂)
        (a : Fin n → Fin m → R),
        (∀ i, f₁ (x i) = ∑ j, a i j • y j) →
          ∃ z : Fin m → M₁, ∀ i, x i = ∑ j, a i j • z j,
      ∀ {n m : ℕ}
        (a : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R))
        (u : (Fin n →₀ R) →ₗ[R] M₁)
        (v : (Fin m →₀ R) →ₗ[R] M₂),
        v.comp a = f₁.comp u →
          ∃ w : (Fin m →₀ R) →ₗ[R] M₁, w.comp a = u,
      ∀ (P : Type u) [AddCommGroup P] [Module R P]
        [Module.FinitePresentation R P],
        Function.Surjective
          (Formalization.Books.Algebra.Unit10.internalHomPostcomp
            (M := P) f₂),
      Nonempty (DirectedSplitExactColimitPresentation M₁ M₂ M₃ f₁ f₂)] := by
  sorry

/-- If the right term is finitely presented, universal exactness is equivalent
to the existence of a section of the quotient map. -/
theorem universallyExact_iff_split_of_finitePresentation
    {R : Type u} {M₁ M₂ M₃ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    [Module.FinitePresentation R M₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃)
    (hshort : Function.Injective f₁ ∧ Function.Exact f₁ f₂ ∧
      Function.Surjective f₂) :
    universallyExact f₁ f₂ ↔
      ∃ s : M₃ →ₗ[R] M₂, f₂.comp s = LinearMap.id := by
  sorry

/-- Flatness is equivalent to universal exactness of every exact sequence
ending in the module. -/
theorem flat_iff_exact_ending_universallyExact
    {R : Type u} [CommRing R] {M : Type u}
    [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ {M₁ M₂ : Type u} [AddCommGroup M₁] [Module R M₁]
        [AddCommGroup M₂] [Module R M₂]
        (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M),
        (Function.Injective f₁ ∧ Function.Exact f₁ f₂ ∧
          Function.Surjective f₂) →
          universallyExact f₁ f₂ := by
  sorry

/-! ## Split sequences and examples -/

/-- The standard split short exact sequence with middle term a product. -/
def splitSequenceInjection
    {R : Type u} {M : Type v} [Semiring R]
    [AddCommMonoid M] [Module R M] :
    M →ₗ[R] M × M :=
  LinearMap.inl R M M

/-- The projection in the standard split short exact sequence. -/
def splitSequenceProjection
    {R : Type u} {M : Type v} [Semiring R]
    [AddCommMonoid M] [Module R M] :
    M × M →ₗ[R] M :=
  LinearMap.snd R M M

/-- A split short exact sequence is universally exact. -/
theorem splitSequence_universallyExact
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    universallyExact (splitSequenceInjection (R := R) (M := M))
      (splitSequenceProjection (R := R) (M := M)) := by
  sorry

/-- A split sequence built from a non-flat module has no flat terms. -/
theorem splitSequence_nonflat
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (hM : ¬ Module.Flat R M) :
    ¬ Module.Flat R M ∧ ¬ Module.Flat R (M × M) ∧ ¬ Module.Flat R M := by
  sorry

/-- A nonzero torsion module over the integers gives the non-flat split
sequence from the source's second example. -/
theorem splitSequence_nonflat_of_nontrivial_torsion
    {M : Type u} [AddCommGroup M] [Module ℤ M] [Nontrivial M]
    (hM : Submodule.torsion ℤ M = ⊤) :
    ¬ Module.Flat ℤ M ∧ ¬ Module.Flat ℤ (M × M) ∧ ¬ Module.Flat ℤ M := by
  sorry

/-! ## Permanence properties -/

/-- In a universally exact sequence, flatness of the middle term implies
flatness of both end terms. -/
theorem flat_ends_of_universallyExact
    {R : Type u} {M₁ M₂ M₃ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃)
    (h : universallyExact f₁ f₂) (hflat : Module.Flat R M₂) :
    Module.Flat R M₁ ∧ Module.Flat R M₃ := by
  sorry

/-- Tensoring a universally injective map by an arbitrary module remains
universally injective. -/
theorem universallyInjective_tensor
    {R : Type u} {M N Q : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] N) (hf : universallyInjective f) :
    universallyInjective (f.rTensor Q) := by
  sorry

/-- A composite of universally injective maps is universally injective. -/
theorem universallyInjective_comp
    {R : Type u} {M N P : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : universallyInjective f) (hg : universallyInjective g) :
    universallyInjective (g.comp f) := by
  sorry

/-- If a composite is universally injective, then its first factor is
universally injective. -/
theorem universallyInjective_of_comp
    {R : Type u} {M N P : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hgf : universallyInjective (g.comp f)) :
    universallyInjective f := by
  sorry

/-- Finite products of universally exact sequences are universally exact. -/
theorem universallyExact_prod
    {R : Type u} {M₁ M₂ M₃ N₁ N₂ N₃ : Type v} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup N₃] [Module R N₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃)
    (g₁ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃)
    (hf : universallyExact f₁ f₂) (hg : universallyExact g₁ g₂) :
    universallyExact (f₁.prodMap g₁) (f₂.prodMap g₂) := by
  sorry

/-! ## The integer example and direct sums -/

abbrev integerDirectSum : Type := ℕ →₀ ℤ

abbrev integerDirectProduct : Type := ℕ → ℤ

/-- The canonical inclusion of the direct sum into the direct product. -/
def integerDirectSumToProduct : integerDirectSum →ₗ[ℤ] integerDirectProduct where
  toFun x n := x n
  map_add' x y := by
    funext n
    simp
  map_smul' a x := by
    funext n
    simp

/-- The cokernel of the direct-sum inclusion. -/
abbrev integerCokernel : Type :=
  integerDirectProduct ⧸ LinearMap.range integerDirectSumToProduct

/-- The quotient map in the integer example. -/
def integerProductToCokernel : integerDirectProduct →ₗ[ℤ] integerCokernel :=
  (LinearMap.range integerDirectSumToProduct).mkQ

/-- The element represented by the sequence of powers of two. -/
def integerPowerSequence : integerDirectProduct :=
  fun n => (2 : ℤ) ^ (n + 1)

/-- The class of the power sequence in the cokernel. -/
def integerPowerClass : integerCokernel :=
  integerProductToCokernel integerPowerSequence

/-- The direct-sum/direct-product sequence is universally exact. -/
theorem integerDirectSumToProduct_universallyExact :
    universallyExact integerDirectSumToProduct integerProductToCokernel := by
  sorry

/-- All three terms in the integer example are flat. -/
theorem integerDirectSumToProduct_flat_terms :
    Module.Flat ℤ integerDirectSum ∧
      Module.Flat ℤ integerDirectProduct ∧
        Module.Flat ℤ integerCokernel := by
  sorry

/-- The power class is divisible by every positive power of two. -/
theorem integerPowerClass_divisible (n : ℕ) (hn : 1 ≤ n) :
    ∃ y : integerCokernel, (2 : ℤ) ^ n • y = integerPowerClass := by
  sorry

/-- Every section of the quotient map kills the power class. -/
theorem integerPowerClass_killed_by_section
    (s : integerCokernel →ₗ[ℤ] integerDirectProduct)
    (hs : integerProductToCokernel.comp s = LinearMap.id) :
    s integerPowerClass = 0 := by
  sorry

/-- The integer universally exact sequence does not split. -/
theorem integerDirectSumToProduct_not_split :
    ¬ ∃ s : integerCokernel →ₗ[ℤ] integerDirectProduct,
      integerProductToCokernel.comp s = LinearMap.id := by
  sorry

/-- Taking a direct sum with a non-flat split sequence preserves universal
exactness and produces a universally exact nonsplit sequence with no flat term. -/
theorem universallyExact_directSum_with_nonflat_split
    {R : Type u} {M₁ M₂ M₃ M : Type v} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup M] [Module R M]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃)
    (h : universallyExact f₁ f₂)
    (hflat₁ : Module.Flat R M₁) (hflat₂ : Module.Flat R M₂)
    (hflat₃ : Module.Flat R M₃) (hM : ¬ Module.Flat R M)
    (hnonsplit : ¬ ∃ s : M₃ →ₗ[R] M₂, f₂.comp s = LinearMap.id) :
    universallyExact
        (f₁.prodMap (splitSequenceInjection (R := R) (M := M)))
        (f₂.prodMap (splitSequenceProjection (R := R) (M := M))) ∧
      (¬ ∃ s : (M₃ × M) →ₗ[R] (M₂ × (M × M)),
        (f₂.prodMap (splitSequenceProjection (R := R) (M := M))).comp s =
          LinearMap.id) ∧
      ¬ Module.Flat R (M₁ × M) ∧
        ¬ Module.Flat R (M₂ × (M × M)) ∧
        ¬ Module.Flat R (M₃ × M) := by
  sorry

/-! ## Universal injectivity over an algebra and at stalks -/

/-- Universal injectivity of a linear map relative to a possibly larger scalar
ring.  The modules carry compatible actions of the base ring and the larger
ring. -/
def universallyInjectiveOver
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M]
    [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A M] [IsScalarTower R A N]
    (f : M →ₗ[A] N) : Prop :=
  ∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
    Function.Injective ((f.restrictScalars R).rTensor Q)

/-- The algebra-specialized form of universal injectivity, with the base-ring
actions obtained by restricting scalars. -/
def universallyInjectiveAsAlgebra
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) : Prop :=
  letI : Module R M := Module.restrictScalars R A M
  letI : Module R N := Module.restrictScalars R A N
  letI : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  letI : IsScalarTower R A N := IsScalarTower.of_compHom R A N
  universallyInjectiveOver (R := R) (A := A) (M := M) (N := N) f

/-- Universal injectivity after localizing at a multiplicative subset. -/
noncomputable def universallyInjectiveLocalizedAsAlgebra
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (S : Submonoid A) (f : M →ₗ[A] N) : Prop :=
  letI : Algebra R (Localization S) :=
    ((algebraMap A (Localization S)).comp (algebraMap R A)).toAlgebra
  universallyInjectiveAsAlgebra
    (R := R) (A := Localization S)
    (LocalizedModule.map S f)

/-- Universal injectivity at a prime of an algebra, viewed over the prime of
the base ring lying below it. -/
noncomputable def universallyInjectiveAtPrimeOver
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (q : Ideal A) [q.IsPrime] (f : M →ₗ[A] N) : Prop :=
  let p := q.comap (algebraMap R A)
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  universallyInjectiveAsAlgebra
    (R := Localization.AtPrime p) (A := Localization.AtPrime q)
    (LocalizedModule.map q.primeCompl f)

/-- Universal injectivity can be checked on prime and maximal stalks, either
over the original base ring or over the corresponding localized base ring. -/
theorem universallyInjective_iff_check_stalks
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) :
    (universallyInjectiveAsAlgebra (R := R) (A := A) f ↔
      ∀ (q : Ideal A) [q.IsPrime],
        universallyInjectiveLocalizedAsAlgebra
          (R := R) (A := A) q.primeCompl f) ∧
    (universallyInjectiveAsAlgebra (R := R) (A := A) f ↔
      ∀ (q : Ideal A) [q.IsMaximal],
        universallyInjectiveLocalizedAsAlgebra
          (R := R) (A := A) q.primeCompl f) ∧
    (universallyInjectiveAsAlgebra (R := R) (A := A) f ↔
      ∀ (q : Ideal A) [q.IsPrime],
        universallyInjectiveAtPrimeOver (R := R) (A := A) q f) ∧
    (universallyInjectiveAsAlgebra (R := R) (A := A) f ↔
      ∀ (q : Ideal A) [q.IsMaximal],
        universallyInjectiveAtPrimeOver (R := R) (A := A) q f) := by
  sorry

/-! ## Localization and the finitely generated ideal criterion -/

/-- The ring map induced by localizing an algebra map. -/
noncomputable def localizationRingHom
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) (S' : Submonoid A)
    (hS : ∀ s : R, s ∈ S → algebraMap R A s ∈ S') :
    Localization S →+* Localization S' :=
  IsLocalization.map (Localization S') (algebraMap R A) (fun s hs => hS s hs)

/-- Localization preserves universal injectivity both over the original base
ring and over its localization. -/
theorem universallyInjective_localize
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (S : Submonoid R) (S' : Submonoid A)
    (hS : ∀ s : R, s ∈ S → algebraMap R A s ∈ S')
    (f : M →ₗ[A] N)
    (hf : universallyInjectiveAsAlgebra (R := R) (A := A) f) :
    (letI : Algebra R (Localization S') :=
      ((algebraMap A (Localization S')).comp (algebraMap R A)).toAlgebra
     universallyInjectiveAsAlgebra (R := R) (A := Localization S')
       (LocalizedModule.map S' f)) ∧
    (letI : Algebra (Localization S) (Localization S') :=
      (localizationRingHom S S' hS).toAlgebra
     universallyInjectiveAsAlgebra (R := Localization S)
       (A := Localization S') (LocalizedModule.map S' f)) := by
  sorry

/-- For modules on which the localized target ring already acts, universal
injectivity over the base ring is equivalent to universal injectivity over the
localized base ring. -/
theorem universallyInjective_localize_iff
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) (S' : Submonoid A)
    [AddCommGroup M] [Module A M] [Module (Localization S') M]
    [IsScalarTower A (Localization S') M]
    [AddCommGroup N] [Module A N] [Module (Localization S') N]
    [IsScalarTower A (Localization S') N]
    (hS : ∀ s : R, s ∈ S → algebraMap R A s ∈ S')
    (f : M →ₗ[A] N) :
    universallyInjectiveAsAlgebra (R := R) (A := A) f ↔
      (letI : Algebra (Localization S) (Localization S') :=
        (localizationRingHom S S' hS).toAlgebra
       universallyInjectiveAsAlgebra (R := Localization S)
         (A := Localization S')
         (f.extendScalarsOfIsLocalization S' (Localization S'))) := by
  sorry

/-- The map induced on quotients by a linear map modulo a finitely generated
ideal. -/
def quotientMapByIdeal
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (f : M →ₗ[R] N) :
    M ⧸ (I • (⊤ : Submodule R M)) →ₗ[R]
      N ⧸ (I • (⊤ : Submodule R N)) :=
  (I • (⊤ : Submodule R M)).mapQ
    (I • (⊤ : Submodule R N)) f
    (Submodule.smul_top_le_comap_smul_top I f)

/-- Into a flat module, universal injectivity is detected modulo finitely
generated ideals. -/
theorem universallyInjective_into_flat_iff
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hflat : Module.Flat R N) :
    universallyInjective f ↔
      ∀ (I : Ideal R), I.FG →
        Function.Injective (quotientMapByIdeal I f) := by
  sorry

/-! ## Faithfully flat base change -/

/-- Tensoring with a universally injective algebra map reflects injections,
surjections, and bijections of modules. -/
theorem baseChange_reflects_of_universallyInjective_algebraMap
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hA : universallyInjective (Algebra.linearMap R A)) :
    ∀ {M N : Type v} [AddCommGroup M] [Module R M]
      [AddCommGroup N] [Module R N] (f : M →ₗ[R] N),
      (Function.Injective (f.rTensor A) → Function.Injective f) ∧
      (Function.Surjective (f.rTensor A) → Function.Surjective f) ∧
      (Function.Bijective (f.rTensor A) → Function.Bijective f) := by
  sorry

/-- A faithfully flat algebra map is universally injective, and contraction
of an extended ideal recovers the original ideal. -/
theorem faithfullyFlat_universallyInjective_and_ideal_comap
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hA : RingHom.FaithfullyFlat (algebraMap R A)) :
    universallyInjective (Algebra.linearMap R A) ∧
      ∀ I : Ideal R,
        (I.map (algebraMap R A)).comap (algebraMap R A) = I := by
  sorry

end

end Formalization.Books.Algebra.Unit82
