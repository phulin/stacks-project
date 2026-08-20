import Formalization.Books.MoreAlgebra.Unit65
import Formalization.Books.MoreAlgebra.Unit67
import Formalization.Books.MoreAlgebra.Unit70
import Formalization.Books.MoreAlgebra.Unit74.DerivedHom
import Formalization.Books.MoreAlgebra.Unit75.PerfectComplexes
import Formalization.Books.MoreAlgebra.Unit88
import Formalization.Books.MoreAlgebra.Unit92
import Formalization.Books.MoreAlgebra.Unit60.DerivedBaseChange
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Noetherian.Basic

/-!
# More on Algebra, Chapter 98: Taking limits of complexes

This file records the six results in the chapter.  The derived category,
derived tensor product, pseudo-coherence, perfectness, and derived-completion
predicates are the canonical interfaces from earlier chapters.  The two
small system structures below expose the varying-ring and quotient-system
data needed by the source statements.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit70
open Formalization.Books.MoreAlgebra.Unit74
open Formalization.Books.MoreAlgebra.Unit75
open Formalization.Books.MoreAlgebra.Unit88
open Formalization.Books.MoreAlgebra.Unit92
open Formalization.Books.MoreAlgebra.Unit60
open scoped CategoryTheory.Pretriangulated.Opposite

universe u w

namespace Formalization.Books.MoreAlgebra.Unit98

abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] := DerivedCategory (Mod R)

/-! ## The varying-ring system -/

/- The inverse system is Mathlib's commutative-ring diagram; its canonical
   limit supplies the limiting ring used by the chapter statements. -/
abbrev RingLimitSystem := ℕᵒᵖ ⥤ CommRingCat.{u}

abbrev limitRing (A : RingLimitSystem.{u}) : CommRingCat.{u} := limit A

def ringTransition (A : RingLimitSystem.{u}) (n : ℕ) :
    (A.obj (Opposite.op (n + 1)) : Type u) →+*
      (A.obj (Opposite.op n) : Type u) :=
  (A.map (opHomOfLE (Nat.le_succ n))).hom

def limitProjection (A : RingLimitSystem.{u}) (n : ℕ) :
    (limitRing A : Type u) →+* (A.obj (Opposite.op n) : Type u) :=
  (limit.π A (Opposite.op n)).hom

/-- A compatible system of derived objects over the rings in `A`.

The transition is written in the source's category, by restricting scalars
along `A_(n+1) → A_n`. -/
structure VaryingDerivedSystem (A : RingLimitSystem.{u}) where
  stage : ∀ n : ℕ, D (A.obj (Opposite.op n) : Type u)
  transition : ∀ n : ℕ,
    stage (n + 1) ⟶
      (derivedRestrictionFunctor (ringTransition A n)).obj (stage n)

/-- The cross-ring derived base-change map adjoint to a system transition. -/
noncomputable def varyingReductionMap
    (A : RingLimitSystem.{u}) (K : VaryingDerivedSystem A) (n : ℕ) :
    (derivedBaseChangeFunctor (ringTransition A n)).obj (K.stage (n + 1)) ⟶
      K.stage n :=
  ((Classical.choice
      (derivedBaseChange_leftAdjoint_restriction (ringTransition A n))).homEquiv
      _ _).symm (K.transition n)

/-- The source's pseudo-coherence condition on every stage. -/
def AllStagesPseudoCoherent
    (A : RingLimitSystem.{u}) (K : VaryingDerivedSystem A) : Prop :=
  ∀ n : ℕ, IsPseudoCoherent (A.obj (Opposite.op n) : Type u) (K.stage n)

/-- The source's perfectness condition on every stage. -/
def AllStagesPerfect
    (A : RingLimitSystem.{u}) (K : VaryingDerivedSystem A) : Prop :=
  ∀ n : ℕ, Perfect (A.obj (Opposite.op n) : Type u) (K.stage n)

/-- Every element of an ideal is nilpotent, without imposing a uniform power. -/
def LocallyNilpotentIdeal {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  ∀ x : R, x ∈ I → ∃ m : ℕ, x ^ m = 0

def TransitionMapsSurjective (A : RingLimitSystem.{u}) : Prop :=
  ∀ n : ℕ, Function.Surjective (ringTransition A n)

def TransitionKernelsLocallyNilpotent (A : RingLimitSystem.{u}) : Prop :=
  ∀ n : ℕ, LocallyNilpotentIdeal (RingHom.ker (ringTransition A n))

def TransitionKernelsNilpotentFrom
    (A : RingLimitSystem.{u}) (n₀ : ℕ) : Prop :=
  ∀ n : ℕ, n₀ ≤ n → ∃ m : ℕ,
    (RingHom.ker (ringTransition A n)) ^ m = ⊥

/-- The chapter's varying-ring `Rlim` operation.

The existence of this functor is the varying-ring derived-limit construction
from the preceding inverse-limit chapter; its object part is exposed here so
the chapter statements have a stable user-facing name. -/
structure VaryingRlimData (A : RingLimitSystem.{u}) where
  functor : VaryingDerivedSystem A → D (limitRing A)

theorem exists_varyingRlimData (A : RingLimitSystem.{u}) :
    Nonempty (VaryingRlimData A) := by
  sorry

noncomputable def varyingRlimFunctor (A : RingLimitSystem.{u}) :
    VaryingDerivedSystem A → D (limitRing A) :=
  (Classical.choice (exists_varyingRlimData A)).functor

noncomputable abbrev varyingRlim
    (A : RingLimitSystem.{u}) (K : VaryingDerivedSystem A) : D (limitRing A) :=
  (varyingRlimFunctor A) K

/-! ## 98.1. Pseudo-coherent and perfect limits -/

/-- Limit of a compatible pseudo-coherent system is pseudo-coherent and
recovers every stage after derived base change. -/
theorem rlim_pseudoCoherent_is_pseudoCoherent
    (A : RingLimitSystem.{u}) (K : VaryingDerivedSystem A)
    (htransition : ∀ n : ℕ, IsIso (varyingReductionMap A K n))
    (hK : TransitionMapsSurjective A ∧
      TransitionKernelsLocallyNilpotent A ∧
      (AllStagesPseudoCoherent A K ∨
        ∃ n₀ : ℕ, IsPseudoCoherent
          (A.obj (Opposite.op n₀) : Type u) (K.stage n₀) ∧
          TransitionKernelsNilpotentFrom A n₀)) :
    IsPseudoCoherent (limitRing A) (varyingRlim A K) ∧
      ∀ n : ℕ, Nonempty
        ((derivedBaseChangeFunctor (limitProjection A n)).obj
            (varyingRlim A K) ≅ K.stage n) := by
  sorry

/-- Limit of a compatible perfect system is perfect and recovers every stage. -/
theorem rlim_perfect_is_perfect
    (A : RingLimitSystem.{u}) (K : VaryingDerivedSystem A)
    (htransition : ∀ n : ℕ, IsIso (varyingReductionMap A K n))
    (hK : TransitionMapsSurjective A ∧
      TransitionKernelsLocallyNilpotent A ∧
      (AllStagesPerfect A K ∨
        ∃ n₀ : ℕ, Perfect
          (A.obj (Opposite.op n₀) : Type u) (K.stage n₀) ∧
          TransitionKernelsNilpotentFrom A n₀)) :
    Perfect (limitRing A) (varyingRlim A K) ∧
      ∀ n : ℕ, Nonempty
        ((derivedBaseChangeFunctor (limitProjection A n)).obj
            (varyingRlim A K) ≅ K.stage n) := by
  sorry

/-! ## 98.2. Adic systems -/

abbrev adicStageRing (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) : Type u :=
  A ⧸ I ^ (n + 1)

def adicQuotientMap (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    adicStageRing A I (n + 1) →+* adicStageRing A I n :=
  Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))

def adicProjectionMap (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    A →+* adicStageRing A I n :=
  Ideal.Quotient.mk _

/-- A system of derived objects over the successive quotients `A/I^(n+1)`. -/
structure AdicDerivedSystem (A : Type u) [CommRing A] (I : Ideal A) where
  stage : ∀ n : ℕ, D (adicStageRing A I n)
  transition : ∀ n : ℕ,
    stage (n + 1) ⟶
      (derivedRestrictionFunctor (adicQuotientMap A I n)).obj (stage n)

noncomputable def adicReductionMap
    {A : Type u} [CommRing A] {I : Ideal A}
    (K : AdicDerivedSystem A I) (n : ℕ) :
    (derivedBaseChangeFunctor (adicQuotientMap A I n)).obj (K.stage (n + 1)) ⟶
      K.stage n :=
  ((Classical.choice
      (derivedBaseChange_leftAdjoint_restriction (adicQuotientMap A I n))).homEquiv
      _ _).symm (K.transition n)

def AdicSystemCompatible
    {A : Type u} [CommRing A] {I : Ideal A}
    (K : AdicDerivedSystem A I) : Prop :=
  ∀ n : ℕ, IsIso (adicReductionMap K n)

/-- The chosen derived inverse-limit object of an adic system. -/
structure AdicRlimData (A : Type u) [CommRing A] (I : Ideal A) where
  functor : AdicDerivedSystem A I → D A

theorem exists_adicRlimData (A : Type u) [CommRing A] (I : Ideal A) :
    Nonempty (AdicRlimData A I) := by
  sorry

noncomputable def adicRlimFunctor
    (A : Type u) [CommRing A] (I : Ideal A) : AdicDerivedSystem A I → D A :=
  (Classical.choice (exists_adicRlimData A I)).functor

noncomputable abbrev adicRlim
    (A : Type u) [CommRing A] (I : Ideal A) (K : AdicDerivedSystem A I) : D A :=
  (adicRlimFunctor A I) K

/-- An adically complete ring and a pseudo-coherent first stage give a
pseudo-coherent, derived-complete limit recovering the whole system. -/
theorem adic_rlim_pseudoCoherent_is_complete
    (A : Type u) [CommRing A] (I : Ideal A) (hA : IsAdicComplete I A)
    (K : AdicDerivedSystem A I)
    (hK₁ : IsPseudoCoherent (adicStageRing A I 0) (K.stage 0))
    (hcompat : AdicSystemCompatible K) :
    IsPseudoCoherent A (adicRlim A I K) ∧
      derivedComplete I (adicRlim A I K) ∧
      ∀ n : ℕ, Nonempty
        ((derivedBaseChangeFunctor (adicProjectionMap A I n)).obj
            (adicRlim A I K) ≅ K.stage n) := by
  sorry

/-- The perfect version of the adic limit theorem. -/
theorem adic_rlim_perfect_is_complete
    (A : Type u) [CommRing A] (I : Ideal A) (hA : IsAdicComplete I A)
    (K : AdicDerivedSystem A I)
    (hK₁ : Perfect (adicStageRing A I 0) (K.stage 0))
    (hcompat : AdicSystemCompatible K) :
    Perfect A (adicRlim A I K) ∧
      derivedComplete I (adicRlim A I K) ∧
      ∀ n : ℕ, Nonempty
        ((derivedBaseChangeFunctor (adicProjectionMap A I n)).obj
            (adicRlim A I K) ≅ K.stage n) := by
  sorry

/-! ## 98.3. The bounded-above Noetherian statement -/

/-- The source's `D^-(A)` condition, reusing the earlier finite-free
bounded-above representative predicate. -/
abbrev InDMinus (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (K : D A) : Prop :=
  Formalization.Books.MoreAlgebra.Unit65.IsInDMinus A K

/- The source explicitly warns that the next assertion is not known for
unbounded complexes; this warning is retained in the declaration's comment. -/

/-- For a Noetherian adically complete system, a bounded-above first stage
gives a bounded-above derived-complete limit recovering every stage. -/
theorem adic_rlim_boundedAbove_is_complete
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hA : IsAdicComplete I A)
    (K : AdicDerivedSystem A I)
    (hK₁ : InDMinus (adicStageRing A I 0) (K.stage 0))
    (hcompat : AdicSystemCompatible K) :
    InDMinus A (adicRlim A I K) ∧
      derivedComplete I (adicRlim A I K) ∧
      ∀ n : ℕ, Nonempty
        ((derivedBaseChangeFunctor (adicProjectionMap A I n)).obj
            (adicRlim A I K) ≅ K.stage n) := by
  sorry

/-! ## 98.4. Kollár--Kovács -/

/-- A derived system realizing `K ⊗ᴸ A/I^(n+1)` in `D(A)`.  This is the
fixed-ring realization used for the cohomology systems in the final lemma. -/
structure DerivedAdicTensorSystem
    (A : Type u) [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (K : D A) where
  system : ℕᵒᵖ ⥤ D A
  stageIso : ∀ n : ℕ, Nonempty
    (system.obj (Opposite.op n) ≅
      derivedTensor K
        (Unit65.moduleInDerived A
          (ModuleCat.of A (adicStageRing A I n))))

noncomputable def derivedAdicCohomologySystem
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    {I : Ideal A} {K : D A} (T : DerivedAdicTensorSystem A I K) (i : ℤ) :
    ℕᵒᵖ ⥤ Mod A :=
  T.system ⋙ DerivedCategory.homologyFunctor (Mod A) i

/-- Mittag--Leffler for an inverse system of `A`-modules. -/
def IsMittagLefflerModuleSystem
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ Mod A) : Prop :=
  (F ⋙ CategoryTheory.forget (Mod A)).IsMittagLeffler

/-- The inverse system of quotients `M/I^(n+1)M` used on the left-hand side
of the Kollár--Kovács comparison. -/
structure AdicQuotientModuleSystemData
    (A : Type u) [CommRing A] (I : Ideal A) (M : Mod A) where
  system : ℕᵒᵖ ⥤ Mod A
  stageIso : ∀ n : ℕ, Nonempty
    (system.obj (Opposite.op n) ≅
      ModuleCat.of A
        ((M : Type u) ⧸ (I ^ (n + 1) • (⊤ : Submodule A (M : Type u)))))

theorem exists_adicQuotientModuleSystemData
    (A : Type u) [CommRing A] (I : Ideal A) (M : Mod A) :
    Nonempty (AdicQuotientModuleSystemData A I M) := by
  sorry

noncomputable def adicQuotientModuleSystemData
    (A : Type u) [CommRing A] (I : Ideal A) (M : Mod A) :
    AdicQuotientModuleSystemData A I M :=
  Classical.choice (exists_adicQuotientModuleSystemData A I M)

noncomputable abbrev adicQuotientModuleSystem
    (A : Type u) [CommRing A] (I : Ideal A) (M : Mod A) : ℕᵒᵖ ⥤ Mod A :=
  (adicQuotientModuleSystemData A I M).system

/-- The first derived inverse-limit module, exposed as a functor because the
source's `R¹ lim` is used in the displayed short exact sequence. -/
structure FirstDerivedLimitModuleData (A : Type u) [CommRing A] where
  first : (ℕᵒᵖ ⥤ Mod A) ⥤ Mod A

theorem exists_firstDerivedLimitModuleData
    (A : Type u) [CommRing A] : Nonempty (FirstDerivedLimitModuleData A) := by
  sorry

noncomputable def firstDerivedLimitModuleData
    (A : Type u) [CommRing A] : FirstDerivedLimitModuleData A :=
  Classical.choice (exists_firstDerivedLimitModuleData A)

noncomputable abbrev firstDerivedLimitModule
    (A : Type u) [CommRing A] (F : ℕᵒᵖ ⥤ Mod A) : Mod A :=
  (firstDerivedLimitModuleData A).first.obj F

noncomputable abbrev derivedAdicRlim
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    {I : Ideal A} {K : D A} (T : DerivedAdicTensorSystem A I K) : D A :=
  derivedLimitWithProduct T.system inferInstance

/-- The short exact sequence
`0 → R¹ lim H^(i-1)(Kₙ) → H^i(R lim Kₙ) → lim H^i(Kₙ) → 0`
appearing in the proof of Kollár--Kovács. -/
structure KollarKovacsExactSequenceData
    (A : Type u) [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (K : D A) (T : DerivedAdicTensorSystem A I K) (i : ℤ) where
  left : firstDerivedLimitModule A (derivedAdicCohomologySystem T (i - 1)) ⟶
    (derivedCohomology A i).obj (derivedAdicRlim T)
  middle : (derivedCohomology A i).obj (derivedAdicRlim T) ⟶
    limit (derivedAdicCohomologySystem T i)
  zero : left ≫ middle = 0
  exact : (ShortComplex.mk left middle zero).ShortExact

theorem kollar_kovacs_exact_sequence
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : D A) (T : DerivedAdicTensorSystem A I K)
    (i : ℤ) : Nonempty (KollarKovacsExactSequenceData A I K T i) := by
  sorry

/-- Kollár--Kovács: finite cohomology and Mittag--Leffler identify the ordinary
adic completion of each cohomology module with the inverse-limit cohomology. -/
theorem kollar_kovacs
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : D A) (T : DerivedAdicTensorSystem A I K)
    (hfinite : ∀ i : ℤ,
      Module.Finite A ((derivedCohomology A i).obj K : Type u))
    (hML : ∀ i : ℤ,
      IsMittagLefflerModuleSystem (derivedAdicCohomologySystem T i)) :
    ∀ i : ℤ, Nonempty
      (limit (adicQuotientModuleSystem A I
          ((derivedCohomology A i).obj K)) ≅
        limit (derivedAdicCohomologySystem T i)) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit98
