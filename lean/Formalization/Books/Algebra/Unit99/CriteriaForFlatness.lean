import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit68.RegularSequences
import Formalization.Books.Algebra.Unit69.QuasiRegularSequences
import Formalization.Books.Algebra.Unit75.TorGroups
import Formalization.Books.Algebra.Unit76.FunctorialitiesForTor
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Commutative Algebra, Chapter 99: Criteria for flatness

This file records the theorem interfaces in the source section.  Flatness,
faithful flatness, Tor, regular sequences, quotient modules, and localization
use the canonical Mathlib and earlier-chapter APIs.
-/

namespace Formalization.Books.Algebra.Unit99

open CategoryTheory
open CategoryTheory.Limits
open Function
open Formalization.Books.Algebra.Unit75
open Formalization.Books.Algebra.Unit76
open scoped TensorProduct

noncomputable section

universe u v w z

/- A small source-facing abbreviation for the canonical Tor construction. -/
abbrev tor {R : Type u} [CommRing R]
    (M N : Type u) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (i : ℕ) : ModuleCat.{u} R :=
  Formalization.Books.Algebra.Unit75.Tor
    (ModuleCat.of R M) (ModuleCat.of R N) i

/-! ## The Noetherian local lemmas -/

/- The induced map on residue modules is Mathlib's `Submodule.mapQ`; the
   displayed maximal ideal action is written as `m • ⊤`. -/
theorem mod_injective
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] [Module R N] [IsScalarTower R S N]
    (hM : Module.Flat R M) (hN : Module.Finite S N)
    (u : N →ₗ[R] M)
    (hu : Function.Injective
      ((IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)).mapQ
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) u
        (Submodule.smul_top_le_comap_smul_top
          (IsLocalRing.maximalIdeal R) u))) :
    Function.Injective u ∧
      Module.Flat R (M ⧸ LinearMap.range u) := by
  sorry

theorem grothendieck
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (hflat : Module.Flat R S) (f : S)
    (hf : IsSMulRegular
      (S ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) : Submodule S S)) f) :
    Module.Flat R
        (S ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) : Submodule S S)) ∧
      IsSMulRegular S f := by
  sorry

theorem grothendieck_regular_sequence
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (hflat : Module.Flat R S) (xs : List S)
    (hxs : RingTheory.Sequence.IsRegular
      (S ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) : Submodule S S))
      (xs.map (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal R).map (algebraMap R S))))) :
    RingTheory.Sequence.IsRegular S xs ∧
      (∀ i : Fin xs.length,
        Module.Flat R
          (S ⧸ (Ideal.ofList (xs.take (i.1 + 1)) : Submodule S S))) := by
  sorry

theorem free_fibre_flat_free
    {R S M : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R]
    [IsNoetherianRing S] [AddCommGroup M] [Module S M]
    [Module R M] [IsScalarTower R S M]
    (hM : Nontrivial M) (hfinite : Module.Finite S M)
    (hfibre : Module.Free
      (S ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S)))
      (M ⧸ (((IsLocalRing.maximalIdeal R).map (algebraMap R S)) •
        (⊤ : Submodule S M))))
    (hflat : Module.Flat R M) :
    Module.Free S M ∧ Module.Flat R S := by
  sorry

/-! ## Finite complexes over a local homomorphism -/

/-- A finite complex indexed so that `differential i` maps the `(i+1)`st
term to the `i`th term.  The last term is the leading zero in the source's
displayed complex. -/
structure FiniteModuleComplex (S : Type u) [CommRing S] (e : ℕ) where
  term : Fin (e + 2) → ModuleCat.{u} S
  differential : ∀ i : Fin (e + 1),
    term i.succ ⟶ term i.castSucc
  isComplex : ∀ i : Fin e,
    differential i.succ ≫ differential i.castSucc = 0
  last_is_zero : IsZero (term ⟨e + 1, Nat.lt_succ_self (e + 1)⟩)

/-- Exactness of `0 → F_e → ⋯ → F_0`, expressed at the terms where the
source asserts exactness.  The cokernel at `F_0` is intentionally not
required to vanish. -/
def FiniteModuleComplex.IsExact
    {S : Type u} [CommRing S] {e : ℕ}
    (C : FiniteModuleComplex S e) : Prop :=
  Function.Injective (C.differential ⟨e, Nat.lt_succ_self e⟩) ∧
    ∀ i : Fin e,
      Function.Exact (C.differential i.succ) (C.differential i.castSucc)

/-- A finite complex whose terms are finite and flat over a ring below `S`. -/
structure FiniteFlatModuleComplex
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (e : ℕ)
    extends FiniteModuleComplex S e where
  rModule : ∀ i, Module R (term i)
  scalarTower : ∀ i,
    letI := rModule i
    IsScalarTower R S (term i)
  finite : ∀ i, Module.Finite S (term i)
  flat : ∀ i,
    letI := rModule i
    letI := scalarTower i
    Module.Flat R (term i)

/-- The quotient term and induced differential modulo an ideal of `S`. -/
abbrev FiniteModuleComplex.quotientTerm
    {S : Type u} [CommRing S] {e : ℕ}
    (C : FiniteModuleComplex S e) (J : Ideal S) (i : Fin (e + 2)) :=
  (C.term i) ⧸ (J • (⊤ : Submodule S (C.term i)))

def FiniteModuleComplex.quotientDifferential
    {S : Type u} [CommRing S] {e : ℕ}
    (C : FiniteModuleComplex S e) (J : Ideal S) (i : Fin (e + 1)) :
    C.quotientTerm J i.succ →ₗ[S] C.quotientTerm J i.castSucc :=
  (J • (⊤ : Submodule S (C.term i.succ))).mapQ
    (J • (⊤ : Submodule S (C.term i.castSucc)))
    (C.differential i).hom
    (Submodule.smul_top_le_comap_smul_top J (C.differential i).hom)

private def quotientRestrictScalarsEquiv
    {R S X : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
    (p : Submodule S X) :
    (X ⧸ p) ≃ₗ[R] (X ⧸ p.restrictScalars R) := by
  let f : (X ⧸ p) →ₗ[R] (X ⧸ p.restrictScalars R) :=
    { QuotientAddGroup.lift p.toAddSubgroup
        (p.restrictScalars R).mkQ.toAddMonoidHom (by
          intro x hx
          exact (Submodule.Quotient.mk_eq_zero _).mpr hx) with
      map_smul' := by
        intro r x
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          rw [← Submodule.Quotient.mk_smul p r x]
          change (p.restrictScalars R).mkQ (r • x) =
            r • (p.restrictScalars R).mkQ x
          exact Submodule.Quotient.mk_smul (p.restrictScalars R) r x }
  let g : (X ⧸ p.restrictScalars R) →ₗ[R] (X ⧸ p) :=
    { QuotientAddGroup.lift (p.restrictScalars R).toAddSubgroup
        p.mkQ.toAddMonoidHom (by
          intro x hx
          exact (Submodule.Quotient.mk_eq_zero _).mpr hx) with
      map_smul' := by
        intro r x
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          rw [← Submodule.Quotient.mk_smul (p.restrictScalars R) r x]
          change p.mkQ (r • x) = r • p.mkQ x
          exact Submodule.Quotient.mk_smul p r x }
  exact { toFun := f
          invFun := g
          left_inv := by
            intro x
            induction x using Submodule.Quotient.induction_on with
            | _ x =>
              dsimp [f, g]
              rfl
          right_inv := by
            intro x
            induction x using Submodule.Quotient.induction_on with
            | _ x =>
              dsimp [f, g]
              rfl
          map_add' := f.map_add
          map_smul' := f.map_smul }

/-- Exactness of the quotient complex modulo `J`. -/
def FiniteModuleComplex.quotientIsExact
    {S : Type u} [CommRing S] {e : ℕ}
    (C : FiniteModuleComplex S e) (J : Ideal S) : Prop :=
  Function.Injective (C.quotientDifferential J ⟨e, Nat.lt_succ_self e⟩) ∧
    ∀ i : Fin e,
      Function.Exact (C.quotientDifferential J i.succ)
        (C.quotientDifferential J i.castSucc)

theorem complex_exact_mod
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R]
    [IsNoetherianRing S] (e : ℕ)
    (C : FiniteFlatModuleComplex R S e)
    (hfibre : C.toFiniteModuleComplex.quotientIsExact
      ((IsLocalRing.maximalIdeal R).map (algebraMap R S))) :
    C.toFiniteModuleComplex.IsExact ∧
      (letI := C.rModule 0
       letI := C.scalarTower 0
       letI := C.rModule ((0 : Fin (e + 1)).castSucc)
       letI := C.scalarTower ((0 : Fin (e + 1)).castSucc)
       letI := C.rModule ((0 : Fin (e + 1)).succ)
       letI := C.scalarTower ((0 : Fin (e + 1)).succ)
       Module.Flat R
         (C.term 0 ⧸ LinearMap.range ((C.differential 0).hom.restrictScalars R))) := by
  induction e with
  | zero =>
    letI := C.rModule ((0 : Fin 1).castSucc)
    letI := C.scalarTower ((0 : Fin 1).castSucc)
    letI := C.rModule ((0 : Fin 1).succ)
    letI := C.scalarTower ((0 : Fin 1).succ)
    have hmem {X : Type u} [AddCommGroup X] [Module S X] [Module R X]
        [IsScalarTower R S X] (x : X)
        (hx : x ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
          (⊤ : Submodule S X))) :
        x ∈ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R X)) := by
      let K : Ideal S := {
        carrier := {s | ∀ y : X, s • y ∈
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R X))}
        zero_mem' := by intro y; simp
        add_mem' := by
          intro a b ha hb y
          simpa [add_smul] using
            (IsLocalRing.maximalIdeal R • (⊤ : Submodule R X)).add_mem
              (ha y) (hb y)
        smul_mem' := by
          intro c a ha y
          have hca : (c • a) • y = a • (c • y) := by
            calc
              (c • a) • y = c • (a • y) := by rw [smul_assoc]
              _ = a • (c • y) := by rw [smul_comm]
          rw [hca]
          exact ha (c • y)
      }
      have hK : (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ K := by
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        intro y
        simpa [Algebra.smul_def] using
          Submodule.smul_mem_smul hr (by simp : y ∈ (⊤ : Submodule R X))
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro s hs y hy
        exact (hK hs) y
      · intro a b ha hb
        simpa [add_smul] using
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R X)).add_mem ha hb
    have hmem' {X : Type u} [AddCommGroup X] [Module S X] [Module R X]
        [IsScalarTower R S X] (x : X)
        (hx : x ∈ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R X))) :
        x ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
          (⊤ : Submodule S X)) := by
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr y hy
        simpa [Algebra.smul_def] using
          Submodule.smul_mem_smul
            (Ideal.mem_map_of_mem (algebraMap R S) hr)
            (by simp : y ∈ (⊤ : Submodule S X))
      · intro a b ha hb
        simpa [add_smul] using
          ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
            (⊤ : Submodule S X)).add_mem ha hb
    letI : LinearMap.CompatibleSMul
        (C.term ((0 : Fin 1).succ) : Type u)
        (C.term ((0 : Fin 1).castSucc) : Type u) R S := ⟨by
      intro r s x
      exact r.map_smul_of_tower s x⟩
    have h := mod_injective (R := R) (S := S)
      (M := (C.term ((0 : Fin 1).castSucc) : Type u))
      (N := (C.term ((0 : Fin 1).succ) : Type u))
      (C.flat ((0 : Fin 1).castSucc))
      (C.finite ((0 : Fin 1).succ))
      ((C.differential 0).hom.restrictScalars R)
      (by
        intro x y hxy
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          induction y using Submodule.Quotient.induction_on with
          | _ y =>
            change (Submodule.Quotient.mk ((C.differential 0).hom x) :
              (C.term ((0 : Fin 1).castSucc) : Type u) ⧸
                (IsLocalRing.maximalIdeal R • (⊤ : Submodule R _))) =
              Submodule.Quotient.mk ((C.differential 0).hom y) at hxy
            have hdiffP : (C.differential 0).hom x -
                (C.differential 0).hom y ∈
                  IsLocalRing.maximalIdeal R • (⊤ : Submodule R _) := by
              apply (Submodule.Quotient.mk_eq_zero _).mp
              rw [Submodule.Quotient.mk_sub]
              exact sub_eq_zero.mpr hxy
            have hdiffJ : (C.differential 0).hom x -
                (C.differential 0).hom y ∈
                (IsLocalRing.maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S _) :=
              hmem' _ hdiffP
            have hxyS : C.quotientDifferential
                ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) 0
                (Submodule.Quotient.mk x) =
                C.quotientDifferential
                  ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) 0
                  (Submodule.Quotient.mk y) := by
              change (Submodule.Quotient.mk ((C.differential 0).hom x) :
                (C.term ((0 : Fin 1).castSucc) : Type u) ⧸
                  ((IsLocalRing.maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S _))) =
                Submodule.Quotient.mk ((C.differential 0).hom y)
              rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub]
              exact (Submodule.Quotient.mk_eq_zero _).mpr hdiffJ
            have hxyS' := hfibre.1 hxyS
            have hdiffJ' : x - y ∈
                (IsLocalRing.maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S _) := by
              have hzero : (Submodule.Quotient.mk (x - y) :
                  (C.term ((0 : Fin 1).succ) : Type u) ⧸
                    ((IsLocalRing.maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S _))) = 0 := by
                rw [Submodule.Quotient.mk_sub]
                exact sub_eq_zero.mpr hxyS'
              exact (Submodule.Quotient.mk_eq_zero _).mp hzero
            have hdiffP' := hmem _ hdiffJ'
            apply sub_eq_zero.mp
            rw [← Submodule.Quotient.mk_sub]
            exact (Submodule.Quotient.mk_eq_zero _).mpr hdiffP')
    simpa [FiniteModuleComplex.IsExact] using h
  | succ n =>
    have hmem {X : Type u} [AddCommGroup X] [Module S X] [Module R X]
        [IsScalarTower R S X] (x : X)
        (hx : x ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
          (⊤ : Submodule S X))) :
        x ∈ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R X)) := by
      let K : Ideal S := {
        carrier := {s | ∀ y : X, s • y ∈
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R X))}
        zero_mem' := by intro y; simp
        add_mem' := by
          intro a b ha hb y
          simpa [add_smul] using
            (IsLocalRing.maximalIdeal R • (⊤ : Submodule R X)).add_mem
              (ha y) (hb y)
        smul_mem' := by
          intro c a ha y
          have hca : (c • a) • y = a • (c • y) := by
            calc
              (c • a) • y = c • (a • y) := by rw [smul_assoc]
              _ = a • (c • y) := by rw [smul_comm]
          rw [hca]
          exact ha (c • y)
      }
      have hK : (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ K := by
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        intro y
        simpa [Algebra.smul_def] using
          Submodule.smul_mem_smul hr (by simp : y ∈ (⊤ : Submodule R X))
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro s hs y hy
        exact (hK hs) y
      · intro a b ha hb
        simpa [add_smul] using
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R X)).add_mem ha hb
    have hmem' {X : Type u} [AddCommGroup X] [Module S X] [Module R X]
        [IsScalarTower R S X] (x : X)
        (hx : x ∈ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R X))) :
        x ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
          (⊤ : Submodule S X)) := by
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr y hy
        simpa [Algebra.smul_def] using
          Submodule.smul_mem_smul
            (Ideal.mem_map_of_mem (algebraMap R S) hr)
            (by simp : y ∈ (⊤ : Submodule S X))
      · intro a b ha hb
        simpa [add_smul] using
          ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
            (⊤ : Submodule S X)).add_mem ha hb
    cases n with
    | zero =>
      let k : Fin 1 := ⟨0, by omega⟩
      let i : Fin 2 := k.castSucc
      letI := C.rModule i.castSucc
      letI := C.scalarTower i.castSucc
      letI := C.rModule i.succ
      letI := C.scalarTower i.succ
      have hlast : IsZero (C.term k.succ.succ) := by
        simpa [k] using C.last_is_zero
      letI : Subsingleton (C.term k.succ.succ : Type u) := by
        apply (ModuleCat.isZero_iff_subsingleton).mp
        exact hlast
      letI : Subsingleton
          (C.term (⟨1, by omega⟩ : Fin 2).succ : Type u) := by
        apply (ModuleCat.isZero_iff_subsingleton).mp
        simpa using C.last_is_zero
      haveI : Subsingleton (C.quotientTerm
          ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) k.succ.succ : Type u) := by
        constructor
        intro x y
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          induction y using Submodule.Quotient.induction_on with
          | _ y => exact Subsingleton.elim _ _
      have htopinj : Function.Injective
          (C.quotientDifferential
            ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) i) := by
        intro x y hxy
        have hzero : C.quotientDifferential
            ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) i (x - y) = 0 := by
          rw [map_sub, hxy]
          simp
        obtain ⟨z, hz⟩ := (hfibre.2 k (x - y)).mp hzero
        have hz0 : z = 0 := Subsingleton.elim _ _
        have hxy0 : x - y = 0 := by
          rw [← hz, hz0]
          simp
        exact sub_eq_zero.mp hxy0
      letI : LinearMap.CompatibleSMul
          (C.term i.succ : Type u) (C.term i.castSucc : Type u) R S := ⟨by
        intro r s x
        exact r.map_smul_of_tower s x⟩
      have h := mod_injective (R := R) (S := S)
        (M := (C.term i.castSucc : Type u))
        (N := (C.term i.succ : Type u))
        (C.flat i.castSucc) (C.finite i.succ)
        ((C.differential i).hom.restrictScalars R) (by
          intro x y hxy
          induction x using Submodule.Quotient.induction_on with
          | _ x =>
            induction y using Submodule.Quotient.induction_on with
            | _ y =>
              change (Submodule.Quotient.mk ((C.differential i).hom x) :
                (C.term i.castSucc : Type u) ⧸
                  (IsLocalRing.maximalIdeal R • (⊤ : Submodule R _))) =
                Submodule.Quotient.mk ((C.differential i).hom y) at hxy
              have hdiffP : (C.differential i).hom x -
                  (C.differential i).hom y ∈
                  IsLocalRing.maximalIdeal R • (⊤ : Submodule R _) := by
                apply (Submodule.Quotient.mk_eq_zero _).mp
                rw [Submodule.Quotient.mk_sub]
                exact sub_eq_zero.mpr hxy
              have hdiffJ : (C.differential i).hom x -
                  (C.differential i).hom y ∈
                  (IsLocalRing.maximalIdeal R).map (algebraMap R S) •
                    (⊤ : Submodule S _) := hmem' _ hdiffP
              have hxyS : C.quotientDifferential
                  ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) i
                  (Submodule.Quotient.mk x) =
                  C.quotientDifferential
                    ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) i
                    (Submodule.Quotient.mk y) := by
                change (Submodule.Quotient.mk ((C.differential i).hom x) :
                  (C.term i.castSucc : Type u) ⧸
                    ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
                      (⊤ : Submodule S _))) =
                  Submodule.Quotient.mk ((C.differential i).hom y)
                rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub]
                exact (Submodule.Quotient.mk_eq_zero _).mpr hdiffJ
              have hxyS' := htopinj hxyS
              have hdiffJ' : x - y ∈
                  (IsLocalRing.maximalIdeal R).map (algebraMap R S) •
                    (⊤ : Submodule S _) := by
                have hzero' : (Submodule.Quotient.mk (x - y) :
                    (C.term i.succ : Type u) ⧸
                      ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
                        (⊤ : Submodule S _))) = 0 := by
                  rw [Submodule.Quotient.mk_sub]
                  exact sub_eq_zero.mpr hxyS'
                exact (Submodule.Quotient.mk_eq_zero _).mp hzero'
              have hdiffP' := hmem _ hdiffJ'
              apply sub_eq_zero.mp
              rw [← Submodule.Quotient.mk_sub]
              exact (Submodule.Quotient.mk_eq_zero _).mpr hdiffP')
      refine ⟨?_, h.2⟩
      constructor
      · intro x y _
        exact Subsingleton.elim _ _
      · intro x y
        have hxk : x = k := Fin.ext (by simp [k])
        subst x
        constructor
        · intro hx
          have hy0 : y = 0 := h.1 (by simpa using hx)
          refine ⟨0, ?_⟩
          simpa [hy0]
        · rintro ⟨z, hz⟩
          have hz0 : z = 0 := Subsingleton.elim _ _
          rw [← hz, hz0]
          simp
    | succ m =>
      let k : Fin (m + 2) := ⟨m + 1, by omega⟩
      let a : Fin (m + 3) := k.castSucc
      letI := C.rModule a.castSucc
      letI := C.scalarTower a.castSucc
      letI := C.rModule a.succ
      letI := C.scalarTower a.succ
      have hlast : IsZero (C.term k.succ.succ) := by
        simpa [k] using C.last_is_zero
      letI : Subsingleton (C.term k.succ.succ : Type u) := by
        exact (ModuleCat.isZero_iff_subsingleton).mp hlast
      haveI : Subsingleton (C.quotientTerm
          ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) k.succ.succ : Type u) := by
        constructor
        intro x y
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          induction y using Submodule.Quotient.induction_on with
          | _ y => exact Subsingleton.elim _ _
      have htopinj : Function.Injective
          (C.quotientDifferential
            ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) a) := by
        intro x y hxy
        have hzero : C.quotientDifferential
            ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) a (x - y) = 0 := by
          rw [map_sub, hxy]
          simp
        obtain ⟨z, hz⟩ := (hfibre.2 k (x - y)).mp hzero
        have hz0 : z = 0 := Subsingleton.elim _ _
        have hxy0 : x - y = 0 := by
          rw [← hz, hz0]
          simp
        exact sub_eq_zero.mp hxy0
      letI : LinearMap.CompatibleSMul
          (C.term a.succ : Type u) (C.term a.castSucc : Type u) R S := ⟨by
        intro r s x
        exact r.map_smul_of_tower s x⟩
      have h := mod_injective (R := R) (S := S)
        (M := (C.term a.castSucc : Type u))
        (N := (C.term a.succ : Type u))
        (C.flat a.castSucc) (C.finite a.succ)
        ((C.differential a).hom.restrictScalars R) (by
          intro x y hxy
          induction x using Submodule.Quotient.induction_on with
          | _ x =>
            induction y using Submodule.Quotient.induction_on with
            | _ y =>
              change (Submodule.Quotient.mk ((C.differential a).hom x) :
                (C.term a.castSucc : Type u) ⧸
                  (IsLocalRing.maximalIdeal R • (⊤ : Submodule R _))) =
                Submodule.Quotient.mk ((C.differential a).hom y) at hxy
              have hdiffP : (C.differential a).hom x -
                  (C.differential a).hom y ∈
                  IsLocalRing.maximalIdeal R • (⊤ : Submodule R _) := by
                apply (Submodule.Quotient.mk_eq_zero _).mp
                rw [Submodule.Quotient.mk_sub]
                exact sub_eq_zero.mpr hxy
              have hdiffJ : (C.differential a).hom x -
                  (C.differential a).hom y ∈
                  (IsLocalRing.maximalIdeal R).map (algebraMap R S) •
                    (⊤ : Submodule S _) := hmem' _ hdiffP
              have hxyS : C.quotientDifferential
                  ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) a
                  (Submodule.Quotient.mk x) =
                  C.quotientDifferential
                    ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) a
                    (Submodule.Quotient.mk y) := by
                change (Submodule.Quotient.mk ((C.differential a).hom x) :
                  (C.term a.castSucc : Type u) ⧸
                    ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
                      (⊤ : Submodule S _))) =
                  Submodule.Quotient.mk ((C.differential a).hom y)
                rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub]
                exact (Submodule.Quotient.mk_eq_zero _).mpr hdiffJ
              have hxyS' := htopinj hxyS
              have hdiffJ' : x - y ∈
                  (IsLocalRing.maximalIdeal R).map (algebraMap R S) •
                    (⊤ : Submodule S _) := by
                have hzero' : (Submodule.Quotient.mk (x - y) :
                    (C.term a.succ : Type u) ⧸
                      ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
                        (⊤ : Submodule S _))) = 0 := by
                  rw [Submodule.Quotient.mk_sub]
                  exact sub_eq_zero.mpr hxyS'
                exact (Submodule.Quotient.mk_eq_zero _).mp hzero'
              have hdiffP' := hmem _ hdiffJ'
              apply sub_eq_zero.mp
              rw [← Submodule.Quotient.mk_sub]
              exact (Submodule.Quotient.mk_eq_zero _).mpr hdiffP')
      let b : Fin (m + 2) := ⟨m, by omega⟩
      have htopinjB : Function.Injective
          (C.quotientDifferential
            ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) b.succ) := by
        simpa [a, b, k] using htopinj
      letI := C.rModule b.succ.castSucc
      letI := C.scalarTower b.succ.castSucc
      letI := C.rModule b.succ.succ
      letI := C.scalarTower b.succ.succ
      have hB : Function.Injective
          ((C.differential b.succ).hom.restrictScalars R) ∧
          Module.Flat R
            ((C.term b.succ.castSucc : Type u) ⧸
              LinearMap.range ((C.differential b.succ).hom.restrictScalars R)) := by
        simpa [a, b, k] using h
      let pS : Submodule S (C.term b.succ.castSucc : Type u) :=
        LinearMap.range (C.differential b.succ).hom
      let pR : Submodule R (C.term b.succ.castSucc : Type u) :=
        LinearMap.range ((C.differential b.succ).hom.restrictScalars R)
      have hp : pR = pS.restrictScalars R := by
        ext x
        constructor <;> intro hx
        · rcases hx with ⟨y, rfl⟩
          exact ⟨y, rfl⟩
        · rcases hx with ⟨y, rfl⟩
          exact ⟨y, rfl⟩
      let eQ := (quotientRestrictScalarsEquiv pS).trans
        (Submodule.quotEquivOfEq (pS.restrictScalars R) pR hp.symm)
      letI : Module.Flat R
          ((C.term b.succ.castSucc : Type u) ⧸ pR) := hB.2
      have hflatQ : Module.Flat R
          ((C.term b.succ.castSucc : Type u) ⧸ pS) :=
        Module.Flat.of_linearEquiv eQ
      let qmap : ((C.term b.succ.castSucc : Type u) ⧸ pS) →ₗ[S]
          (C.term b.castSucc.castSucc : Type u) :=
        pS.liftQ (C.differential b.castSucc).hom (by
          intro x hx
          rcases hx with ⟨y, rfl⟩
          have hc := congrArg (fun f => f.hom y) (C.isComplex b)
          simpa [LinearMap.comp_apply] using hc)
      let J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
      have hrec : ∀ i : Fin (m + 2),
          (letI := C.rModule i.castSucc.castSucc
           letI := C.scalarTower i.castSucc.castSucc
           Module.Flat R
             ((C.term i.castSucc.castSucc : Type u) ⧸
               LinearMap.range (C.differential i.castSucc).hom)) ∧
          Function.Exact (C.differential i.succ).hom
            (C.differential i.castSucc).hom := by
        intro i
        induction i using Fin.reverseInduction with
        | last =>
          letI := C.rModule (Fin.last (m + 1)).castSucc.castSucc
          letI := C.scalarTower (Fin.last (m + 1)).castSucc.castSucc
          letI := C.rModule (Fin.last (m + 1)).castSucc.succ
          letI := C.scalarTower (Fin.last (m + 1)).castSucc.succ
          have ht : (Fin.last (m + 1)).castSucc = b.succ := by
            apply Fin.ext
            simp [b]
          letI : Subsingleton
              (C.term (Fin.last (m + 1)).succ.succ : Type u) := by
            apply (ModuleCat.isZero_iff_subsingleton).mp
            have heq : (Fin.last (m + 1)).succ.succ =
                (⟨m + 1 + 1 + 1, by omega⟩ : Fin (m + 1 + 1 + 2)) := by
              apply Fin.ext
              simp
            rw [heq]
            exact C.last_is_zero
          have hflat : Module.Flat R
              ((C.term (Fin.last (m + 1)).castSucc.castSucc : Type u) ⧸
                LinearMap.range (C.differential (Fin.last (m + 1)).castSucc).hom) := by
            simpa [ht, pS, b, Fin.last] using hflatQ
          have hinj : Function.Injective
              ((C.differential (Fin.last (m + 1)).castSucc).hom.restrictScalars R) := by
            simpa [ht, a, b, k, Fin.last] using h.1
          refine ⟨hflat, ?_⟩
          intro y
          constructor
          · intro hy
            have hy0 : y = 0 := hinj (by simpa using hy)
            refine ⟨0, ?_⟩
            simpa [hy0]
          · rintro ⟨z, hz⟩
            have hz0 : z = 0 := Subsingleton.elim _ _
            rw [← hz, hz0]
            simp
        | cast i ih =>
          letI := C.rModule i.castSucc.castSucc.castSucc
          letI := C.scalarTower i.castSucc.castSucc.castSucc
          letI := C.rModule i.castSucc.castSucc.succ
          letI := C.scalarTower i.castSucc.castSucc.succ
          letI := C.rModule i.succ.castSucc.castSucc
          letI := C.scalarTower i.succ.castSucc.castSucc
          let pS : Submodule S (C.term i.succ.castSucc.castSucc : Type u) :=
            LinearMap.range (C.differential i.succ.castSucc).hom
          let qmap : ((C.term i.succ.castSucc.castSucc : Type u) ⧸ pS) →ₗ[S]
              (C.term i.castSucc.castSucc.castSucc : Type u) :=
            pS.liftQ (C.differential i.castSucc.castSucc).hom (by
              intro x hx
              rcases hx with ⟨y, rfl⟩
              have hc := congrArg (fun f => f.hom y)
                (C.isComplex i.castSucc)
              simpa [LinearMap.comp_apply] using hc)
          letI : LinearMap.CompatibleSMul
              ((C.term i.succ.castSucc.castSucc : Type u) ⧸ pS)
              (C.term i.castSucc.castSucc.castSucc : Type u) R S := ⟨by
            intro r s x
            exact r.map_smul_of_tower s x⟩
          let qmapR :
              ((C.term i.succ.castSucc.castSucc : Type u) ⧸ pS) →ₗ[R]
                (C.term i.castSucc.castSucc.castSucc : Type u) :=
            LinearMap.restrictScalars R qmap
          letI : Module.Finite S (C.term i.succ.castSucc.castSucc : Type u) :=
            C.finite i.succ.castSucc.castSucc
          have hu : Function.Injective
              ((IsLocalRing.maximalIdeal R •
                (⊤ : Submodule R ((C.term i.succ.castSucc.castSucc : Type u) ⧸ pS))).mapQ
                (IsLocalRing.maximalIdeal R •
                  (⊤ : Submodule R (C.term i.castSucc.castSucc.castSucc : Type u)))
                qmapR
                (Submodule.smul_top_le_comap_smul_top
                  (IsLocalRing.maximalIdeal R) qmapR)) := by
            intro x y hxy
            induction x using Submodule.Quotient.induction_on with
            | _ x =>
              induction y using Submodule.Quotient.induction_on with
              | _ y =>
                induction x using Submodule.Quotient.induction_on with
                | _ x =>
                  induction y using Submodule.Quotient.induction_on with
                  | _ y =>
                    change (Submodule.Quotient.mk
                        ((C.differential i.castSucc.castSucc).hom x) :
                      (C.term i.castSucc.castSucc.castSucc : Type u) ⧸
                        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R _))) =
                      Submodule.Quotient.mk
                        ((C.differential i.castSucc.castSucc).hom y) at hxy
                    have hdiffP :
                        (C.differential i.castSucc.castSucc).hom x -
                            (C.differential i.castSucc.castSucc).hom y ∈
                          IsLocalRing.maximalIdeal R •
                            (⊤ : Submodule R _) := by
                      apply (Submodule.Quotient.mk_eq_zero _).mp
                      rw [Submodule.Quotient.mk_sub]
                      exact sub_eq_zero.mpr hxy
                    have hdiffJ :
                        (C.differential i.castSucc.castSucc).hom x -
                            (C.differential i.castSucc.castSucc).hom y ∈
                          J • (⊤ : Submodule S _) := by
                      exact hmem' _ hdiffP
                    have hxyS :
                        C.quotientDifferential J i.castSucc.castSucc
                            (Submodule.Quotient.mk x) =
                          C.quotientDifferential J i.castSucc.castSucc
                            (Submodule.Quotient.mk y) := by
                      change (Submodule.Quotient.mk
                          ((C.differential i.castSucc.castSucc).hom x) :
                        (C.term i.castSucc.castSucc.castSucc : Type u) ⧸
                          (J • (⊤ : Submodule S _))) =
                        Submodule.Quotient.mk
                          ((C.differential i.castSucc.castSucc).hom y)
                      rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub]
                      exact (Submodule.Quotient.mk_eq_zero _).mpr hdiffJ
                    have hzero :
                        C.quotientDifferential J i.castSucc.castSucc
                            (Submodule.Quotient.mk (x - y)) = 0 := by
                      change (Submodule.Quotient.mk
                          ((C.differential i.castSucc.castSucc).hom (x - y)) :
                        (C.term i.castSucc.castSucc.castSucc : Type u) ⧸
                          (J • (⊤ : Submodule S _))) = 0
                      rw [map_sub]
                      exact (Submodule.Quotient.mk_eq_zero _).mpr hdiffJ
                    obtain ⟨z, hz⟩ :=
                      ((hfibre.2 i.castSucc
                        (Submodule.Quotient.mk (x - y))).mp hzero)
                    induction z using Submodule.Quotient.induction_on with
                    | _ z =>
                      have hz' :
                          (Submodule.Quotient.mk
                            ((C.differential i.succ.castSucc).hom z) :
                            (C.term i.castSucc.castSucc.succ : Type u) ⧸
                              (J • (⊤ : Submodule S _))) =
                            Submodule.Quotient.mk (x - y) := by
                        change (Submodule.Quotient.mk
                            ((C.differential i.castSucc.succ).hom z) :
                            (C.term i.castSucc.castSucc.succ : Type u) ⧸
                              (J • (⊤ : Submodule S _))) =
                          Submodule.Quotient.mk (x - y)
                        convert hz using 1 <;>
                          simp [J, FiniteModuleComplex.quotientTerm,
                            FiniteModuleComplex.quotientDifferential]
                      have hdiffJ' :
                          (x - y) - (C.differential i.succ.castSucc).hom z ∈
                            J • (⊤ : Submodule S _) := by
                        have hzero' :
                            (Submodule.Quotient.mk
                              ((x - y) - (C.differential i.succ.castSucc).hom z) :
                              (C.term i.castSucc.castSucc.succ : Type u) ⧸
                                (J • (⊤ : Submodule S _))) = 0 := by
                          rw [Submodule.Quotient.mk_sub]
                          exact sub_eq_zero.mpr hz'.symm
                        exact (Submodule.Quotient.mk_eq_zero _).mp hzero'
                      have hdiffP' := hmem _ hdiffJ'
                      have hQsub :
                          (Submodule.Quotient.mk
                            ((x - y) - (C.differential i.succ.castSucc).hom z) :
                            (C.term i.succ.castSucc.castSucc : Type u) ⧸ pS) ∈
                            IsLocalRing.maximalIdeal R •
                              (⊤ : Submodule R _) := by
                        refine Submodule.smul_induction_on hdiffP' ?_ ?_
                        · intro r hr v hv
                          rw [Submodule.Quotient.mk_smul]
                          exact Submodule.smul_mem_smul hr (by simp)
                        · intro u v hu hv
                          rw [Submodule.Quotient.mk_add]
                          exact add_mem hu hv
                      have hmkdz :
                          (Submodule.Quotient.mk
                            ((C.differential i.succ.castSucc).hom z) :
                            (C.term i.succ.castSucc.castSucc : Type u) ⧸ pS) = 0 := by
                        apply (Submodule.Quotient.mk_eq_zero _).mpr
                        exact ⟨z, rfl⟩
                      have hQ :
                          (Submodule.Quotient.mk (x - y) :
                            (C.term i.succ.castSucc.castSucc : Type u) ⧸ pS) ∈
                            IsLocalRing.maximalIdeal R • (⊤ : Submodule R _) := by
                        have heq : (Submodule.Quotient.mk (x - y) :
                            (C.term i.succ.castSucc.castSucc : Type u) ⧸ pS) =
                          Submodule.Quotient.mk
                            ((x - y) - (C.differential i.succ.castSucc).hom z) := by
                          calc
                            Submodule.Quotient.mk (x - y) =
                                Submodule.Quotient.mk
                                  (((x - y) -
                                    (C.differential i.succ.castSucc).hom z) +
                                    (C.differential i.succ.castSucc).hom z) := by
                              congr 1 <;> abel
                            _ = Submodule.Quotient.mk
                                  ((x - y) -
                                    (C.differential i.succ.castSucc).hom z) +
                                  Submodule.Quotient.mk
                                    ((C.differential i.succ.castSucc).hom z) := by
                              rw [Submodule.Quotient.mk_add]
                            _ = Submodule.Quotient.mk
                                  ((x - y) -
                                    (C.differential i.succ.castSucc).hom z) := by
                              rw [hmkdz]
                              simp
                        rw [heq]
                        exact hQsub
                      rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub]
                      apply (Submodule.Quotient.mk_eq_zero _).mpr
                      rw [← Submodule.Quotient.mk_sub]
                      exact hQ
          have hq := mod_injective (R := R) (S := S)
            (M := (C.term i.castSucc.castSucc.castSucc : Type u))
            (N := (C.term i.succ.castSucc.castSucc : Type u) ⧸ pS)
            (C.flat i.castSucc.castSucc.castSucc)
            (Module.Finite.of_surjective pS.mkQ pS.mkQ_surjective)
            qmapR hu
          have hqrange : qmapR.range =
              LinearMap.range
                ((C.differential i.castSucc.castSucc).hom.restrictScalars R) := by
            ext y
            constructor
            · rintro ⟨x, rfl⟩
              induction x using Submodule.Quotient.induction_on with
              | _ x => exact ⟨x, by rfl⟩
            · rintro ⟨x, rfl⟩
              exact ⟨Submodule.Quotient.mk x, by rfl⟩
          rw [hqrange] at hq
          refine ⟨?_, ?_⟩
          · exact hq.2
          · intro x
            constructor
            · intro hx
              have hzero :
                  qmapR (Submodule.Quotient.mk x) = qmapR 0 := by
                simpa [qmapR, qmap, pS] using hx
              have hmk :
                  (Submodule.Quotient.mk x :
                    (C.term i.succ.castSucc.castSucc : Type u) ⧸ pS) = 0 :=
                hq.1 hzero
              have hmem : x ∈ pS :=
                (Submodule.Quotient.mk_eq_zero _).mp hmk
              simpa [pS] using hmem
            · rintro ⟨z, hz⟩
              have hc := congrArg (fun f => f.hom z)
                (C.isComplex i.castSucc)
              simpa [LinearMap.comp_apply, hz] using hc
      have hidx : (Fin.castSucc (0 : Fin (m + 2))).castSucc =
          (0 : Fin (m + 4)) := by
        apply Fin.ext
        simp
      cases hidx
      letI := C.rModule (0 : Fin (m + 4))
      letI := C.scalarTower (0 : Fin (m + 4))
      letI := C.rModule (0 : Fin (m + 3)).succ
      letI := C.scalarTower (0 : Fin (m + 3)).succ
      letI := C.rModule (0 : Fin (m + 3)).castSucc
      letI := C.scalarTower (0 : Fin (m + 3)).castSucc
      letI := C.rModule (Fin.castSucc (0 : Fin (m + 2))).castSucc
      letI := C.scalarTower (Fin.castSucc (0 : Fin (m + 2))).castSucc
      letI := C.rModule (Fin.castSucc (0 : Fin (m + 2))).succ
      letI := C.scalarTower (Fin.castSucc (0 : Fin (m + 2))).succ
      let pS0 : Submodule S
          (C.term (Fin.castSucc (0 : Fin (m + 2))).castSucc : Type u) :=
        LinearMap.range
          (C.differential (Fin.castSucc (0 : Fin (m + 2)))).hom
      let pR0 : Submodule R
          (C.term (Fin.castSucc (0 : Fin (m + 2))).castSucc : Type u) :=
        LinearMap.range
          ((C.differential (0 : Fin (m + 3))).hom.restrictScalars R)
      have hp0 : pR0 = pS0.restrictScalars R := by
        ext x
        constructor <;> intro hx
        · change x ∈ LinearMap.range
            ((C.differential (Fin.castSucc (0 : Fin (m + 2)))).hom.restrictScalars R) at hx
          change x ∈ LinearMap.range
            (C.differential (Fin.castSucc (0 : Fin (m + 2)))).hom
          rcases hx with ⟨y, rfl⟩
          exact ⟨y, rfl⟩
        · change x ∈ LinearMap.range
            (C.differential (Fin.castSucc (0 : Fin (m + 2)))).hom at hx
          change x ∈ LinearMap.range
            ((C.differential (Fin.castSucc (0 : Fin (m + 2)))).hom.restrictScalars R)
          rcases hx with ⟨y, rfl⟩
          exact ⟨y, rfl⟩
      dsimp [pR0] at hp0
      let eQ0 := (quotientRestrictScalarsEquiv pS0).trans
        (Submodule.quotEquivOfEq (pS0.restrictScalars R)
          (LinearMap.range
            ((C.differential (0 : Fin (m + 3))).hom.restrictScalars R)) hp0.symm)
      letI : Module.Flat R
          ((C.term (Fin.castSucc (0 : Fin (m + 2))).castSucc : Type u) ⧸ pS0) := by
        simpa [pS0] using (hrec (0 : Fin (m + 2))).1
      have hflat0 : Module.Flat R
          ((C.term (Fin.castSucc (0 : Fin (m + 2))).castSucc : Type u) ⧸
            LinearMap.range
              ((C.differential (0 : Fin (m + 3))).hom.restrictScalars R)) :=
        Module.Flat.of_linearEquiv eQ0.symm
      letI : Subsingleton
          (C.term ((⟨m + 2, by omega⟩ : Fin (m + 3)).succ) : Type u) := by
        apply (ModuleCat.isZero_iff_subsingleton).mp
        have heq : (⟨m + 2, by omega⟩ : Fin (m + 3)).succ =
            (⟨m + 3, by omega⟩ : Fin (m + 4)) := by
          apply Fin.ext
          simp
        rw [heq]
        exact C.last_is_zero
      refine ⟨?_, ?_⟩
      · constructor
        · intro x y _
          exact Subsingleton.elim _ _
        · intro i
          exact (hrec i).2
      · dsimp [pR0] at hflat0
        simpa using hflat0

/-! ## Tor vanishing and the local criterion -/

theorem prepare_local_criterion_flatness
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [IsLocalRing R]
    (hTor : IsZero
      (tor (R := R) (R ⧸ IsLocalRing.maximalIdeal R) M 1))
    {N : Type u} [AddCommGroup N] [Module R N]
    (hN : IsFiniteLength R N) :
    IsZero (tor (R := R) N M 1) := by
    induction hN with
    | of_subsingleton =>
      rename_i N' _ _ hsub
      have hflat : Module.Flat R N' := by infer_instance
      have hcrit : Module.Flat R N' ↔
          TorFunctorZero (ModuleCat.of R N') 1 :=
        (flat_iff_tor_criteria (ModuleCat.of R N')).out 0 2
      exact hcrit.mp hflat (ModuleCat.of R M)
    | of_simple_quotient =>
      rename_i M' hAdd hMod N' hsimple hfin ih
      obtain ⟨I, hI, eI⟩ :=
        (isSimpleModule_iff_quot_maximal (R := R) (M := M' ⧸ N')).mp hsimple
      have hIe : I = IsLocalRing.maximalIdeal R :=
        IsLocalRing.eq_maximalIdeal hI
      subst I
      have hTorI : IsZero (tor (R := R) (R ⧸ IsLocalRing.maximalIdeal R) M 1) := hTor
      have hTorI' : IsZero (tor (R := R) M
          (R ⧸ IsLocalRing.maximalIdeal R) 1) :=
        IsZero.of_iso hTorI
          (torLeftRightIso (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
            (ModuleCat.of R M) 1).symm
      let eQ : ModuleCat.of R (M' ⧸ N') ≅
          ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) :=
        (Classical.choice eI).toModuleIso
      let qMap := torMapSecond (ModuleCat.of R M)
        (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R (M' ⧸ N')) eQ.inv 1
      let qMapInv := torMapSecond (ModuleCat.of R M)
        (ModuleCat.of R (M' ⧸ N')) (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) eQ.hom 1
      have hq1 : qMap ≫ qMapInv = 𝟙 _ := by
        dsimp [qMap, qMapInv]
        rw [← torMapSecond_comp, eQ.inv_hom_id, torMapSecond_id]
      have hq2 : qMapInv ≫ qMap = 𝟙 _ := by
        dsimp [qMap, qMapInv]
        rw [← torMapSecond_comp, eQ.hom_inv_id, torMapSecond_id]
      haveI : IsIso qMap := ⟨⟨qMapInv, hq1, hq2⟩⟩
      have hquotSym : IsZero (tor (R := R) M (M' ⧸ N') 1) :=
        IsZero.of_iso hTorI' (asIso qMap).symm
      have hiSym : IsZero (tor (R := R) M (N' : Type u) 1) :=
        IsZero.of_iso ih
          (torLeftRightIso (ModuleCat.of R (N' : Type u)) (ModuleCat.of R M) 1).symm
      let S : ShortComplex (ModuleCat.{u} R) :=
        ShortComplex.mk (ModuleCat.ofHom N'.subtype)
          (ModuleCat.ofHom (Submodule.mkQ N')) (by
            apply ModuleCat.hom_ext
            ext x
            simp [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, x.property])
      have hS : S.ShortExact := by
        apply ModuleCat.shortComplex_shortExact
        · simpa [S] using (LinearMap.exact_subtype_mkQ N')
        · exact Subtype.val_injective
        · exact Submodule.mkQ_surjective N'
      let hseq := Classical.choice (exists_tor_long_exact_sequence
        (ModuleCat.of R M) S hS)
      have hzero1 : IsZero (Tor (ModuleCat.of R M) S.X₁ 1) := by
        simpa [S] using hiSym
      have hzero3 : IsZero (Tor (ModuleCat.of R M) S.X₃ 1) := by
        simpa [S] using hquotSym
      haveI : Subsingleton (Tor (ModuleCat.of R M) S.X₁ 1) :=
        (ModuleCat.isZero_iff_subsingleton).mp hzero1
      haveI : Subsingleton (Tor (ModuleCat.of R M) S.X₃ 1) :=
        (ModuleCat.isZero_iff_subsingleton).mp hzero3
      haveI : Subsingleton (Tor (ModuleCat.of R M) S.X₂ 1) := by
        constructor
        intro x y
        have hxker : hseq.map₂ x = 0 := Subsingleton.elim _ _
        obtain ⟨z, hz⟩ := (hseq.exact₁ x).mp hxker
        have hz0 : z = 0 := Subsingleton.elim _ _
        have hx0 : x = 0 := by
          rw [← hz, hz0]
          simp
        have hyker : hseq.map₂ y = 0 := Subsingleton.elim _ _
        obtain ⟨w, hw⟩ := (hseq.exact₁ y).mp hyker
        have hw0 : w = 0 := Subsingleton.elim _ _
        have hy0 : y = 0 := by
          rw [← hw, hw0]
          simp
        exact hx0.trans hy0.symm
      have hzero2 : IsZero (Tor (ModuleCat.of R M) S.X₂ 1) :=
        ModuleCat.isZero_of_subsingleton _
      have hzero2' : IsZero (tor (R := R) M M' 1) := by
        simpa [S] using hzero2
      exact IsZero.of_iso hzero2'
        (torLeftRightIso (ModuleCat.of R M') (ModuleCat.of R M) 1)

theorem local_criterion_flatness
    {R S M : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R]
    [IsNoetherianRing S]
    [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] (hfinite : Module.Finite S M)
    (hTor : IsZero
      (tor (R := R) (R ⧸ IsLocalRing.maximalIdeal R) M 1)) :
    Module.Flat R M := by
  apply ((Formalization.Books.Algebra.Unit39.flat_criteria
    (R := R) (M := M)).out 0 3).mpr
  intro I hIFG
  let m : Ideal R := IsLocalRing.maximalIdeal R
  have hfinitePower (n : ℕ) (hn : 0 < n) :
      IsFiniteLength R (R ⧸ m ^ n) := by
    have hmne : m ≠ (⊤ : Ideal R) := by
      intro hm
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hm
    have hpowne : m ^ n ≠ (⊤ : Ideal R) := by
      intro h
      apply hmne
      apply le_antisymm le_top
      rw [← h]
      exact Ideal.pow_le_self (R := R) (I := m) (n := n) hn.ne'
    let A := R ⧸ m ^ n
    letI : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr hpowne
    letI : IsLocalRing A := IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (m ^ n)) Ideal.Quotient.mk_surjective
    have hmax : (m.map (Ideal.Quotient.mk (m ^ n))) =
        IsLocalRing.maximalIdeal A :=
      IsLocalRing.map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk (m ^ n)) Ideal.Quotient.mk_surjective
    have hnil : IsNilpotent (IsLocalRing.maximalIdeal A) := by
      refine ⟨n, ?_⟩
      rw [← hmax, ← Ideal.map_pow, Ideal.zero_eq_bot,
        Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    letI : IsArtinianRing A :=
      (isArtinianRing_iff_isNilpotent_maximalIdeal A).2 hnil
    have hArt : IsArtinian R A :=
      isArtinian_of_surjective_algebraMap (R := A) (S := R) (M := A) (by
        simpa [A, Ideal.Quotient.algebraMap_eq] using (Ideal.Quotient.mk_surjective :
          Function.Surjective (Ideal.Quotient.mk (m ^ n))))
    exact (isFiniteLength_iff_isNoetherian_isArtinian).2
      ⟨inferInstance, hArt⟩
  have hfiniteSum (n : ℕ) (hn : 0 < n) :
      IsFiniteLength R (R ⧸ (I ⊔ m ^ n)) := by
    let q : (R ⧸ m ^ n) →ₗ[R] (R ⧸ (I ⊔ m ^ n)) :=
      { toFun := Ideal.Quotient.factor le_sup_right
        map_add' := by intro x y; simp
        map_smul' := by
          intro r x
          change (Ideal.Quotient.factor le_sup_right)
              (Ideal.Quotient.mk (m ^ n) r * x) =
            Ideal.Quotient.mk (I ⊔ m ^ n) r *
              (Ideal.Quotient.factor le_sup_right) x
          rw [map_mul]
          rfl }
    refine IsFiniteLength.of_surjective (f := q) (hfinitePower n hn) ?_
    change Function.Surjective (Ideal.Quotient.factor
      (S := m ^ n) (T := I ⊔ m ^ n) le_sup_right)
    exact Ideal.Quotient.factor_surjective
      (S := m ^ n) (T := I ⊔ m ^ n) le_sup_right
  let eBI := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M I
  letI : Module.Finite R I := inferInstance
  have hbase : Module.Finite S (TensorProduct R S I) :=
    Module.Finite.base_change R S I
  have hprod : Module.Finite S ((TensorProduct R S I) ⊗[S] M) :=
    Module.Finite.tensorProduct S (TensorProduct R S I) M
  have hfiniteTensor : Module.Finite S (M ⊗[R] I) :=
    Module.Finite.equiv eBI
  let act : ∀ J : Ideal R, (M ⊗[R] J) →ₗ[R] M := fun J =>
    TensorProduct.lift
      { toFun := fun m =>
          { toFun := fun a => (a : R) • m
            map_add' := by intro x y; simp [add_smul]
            map_smul' := by intro r x; simp [smul_smul, mul_comm] }
        map_add' := by intro x y; ext a; simp [add_smul]
        map_smul' := by intro r m; ext a; simp [smul_smul, mul_comm] }
  have hactinj_of_tor (J : Ideal R)
      (hzero : IsZero (tor (R := R) M (R ⧸ J) 1)) :
      Function.Injective (act J) := by
    let hzK : IsZero (idealTensorActionKernel J (ModuleCat.of R M)) :=
      IsZero.of_iso hzero
        (Classical.choice (tor_one_ideal_quotient_kernel
          (ModuleCat.of R M) J)).symm
    intro x y hxy
    have hz : act J (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hzmem : x - y ∈ LinearMap.ker (act J) :=
      LinearMap.mem_ker.mpr hz
    have hcomm (z : M ⊗[R] J) :
        idealTensorActionMap J (ModuleCat.of R M)
            ((TensorProduct.comm R M J) z) = act J z := by
      induction z using TensorProduct.induction_on with
      | zero => simp [act, idealTensorActionMap]
      | add x y ihx ihy =>
          calc
            idealTensorActionMap J (ModuleCat.of R M)
                ((TensorProduct.comm R M J) (x + y)) =
                idealTensorActionMap J (ModuleCat.of R M)
                  ((TensorProduct.comm R M J) x +
                    (TensorProduct.comm R M J) y) := by
                rw [(TensorProduct.comm R M J).map_add]
            _ = idealTensorActionMap J (ModuleCat.of R M)
                  ((TensorProduct.comm R M J) x) +
                idealTensorActionMap J (ModuleCat.of R M)
                  ((TensorProduct.comm R M J) y) := by rw [map_add]
            _ = act J x + act J y := by rw [ihx, ihy]
            _ = act J (x + y) := by rw [map_add]
      | tmul m a => rfl
    have hzmem' :
        (TensorProduct.comm R M J) (x - y) ∈
          LinearMap.ker (idealTensorActionMap J (ModuleCat.of R M)) := by
      rw [LinearMap.mem_ker]
      rw [hcomm]
      exact hz
    have hzzero :
        (TensorProduct.comm R M J) (x - y) = 0 := by
      letI : Subsingleton
          (LinearMap.ker (idealTensorActionMap J (ModuleCat.of R M))) :=
        (ModuleCat.isZero_iff_subsingleton).mp hzK
      have hz' :
          (⟨(TensorProduct.comm R M J) (x - y), hzmem'⟩ :
            LinearMap.ker (idealTensorActionMap J (ModuleCat.of R M))) = 0 :=
        Subsingleton.elim _ _
      exact congrArg Subtype.val hz'
    exact sub_eq_zero.mp ((TensorProduct.comm R M J).injective hzzero)
  have hactinj_power (n : ℕ) (hn : 0 < n) :
      Function.Injective (act (m ^ n)) :=
    hactinj_of_tor (m ^ n)
      (IsZero.of_iso
        (prepare_local_criterion_flatness hTor (hfinitePower n hn))
        (torLeftRightIso (ModuleCat.of R (R ⧸ m ^ n))
          (ModuleCat.of R M) 1).symm)
  have hactinj_sum (n : ℕ) (hn : 0 < n) :
      Function.Injective (act (I ⊔ m ^ n)) :=
    hactinj_of_tor (I ⊔ m ^ n)
      (IsZero.of_iso
        (prepare_local_criterion_flatness hTor (hfiniteSum n hn))
        (torLeftRightIso (ModuleCat.of R (R ⧸ (I ⊔ m ^ n)))
          (ModuleCat.of R M) 1).symm)
  let b : M →ₗ[S] I →ₗ[R] M :=
    { toFun := fun m =>
        { toFun := fun a => (a : R) • m
          map_add' := by intro x y; simp [add_smul]
          map_smul' := by intro r x; simp [smul_smul, mul_comm] }
      map_add' := by intro x y; ext a; simp [add_smul]
      map_smul' := by
        intro s m
        apply LinearMap.ext
        intro a
        calc
          (a : R) • s • m = (algebraMap R S a) • (s • m) := by
            rw [IsScalarTower.algebraMap_smul]
          _ = s • ((algebraMap R S a) • m) := by
            exact smul_comm _ _ _
          _ = s • ((a : R) • m) := by
            rw [IsScalarTower.algebraMap_smul] }
  let u : (M ⊗[R] I) →ₗ[S] M :=
    TensorProduct.AlgebraTensorModule.lift b
  let K : Submodule S (M ⊗[R] I) := LinearMap.ker u
  letI : Module.Finite S (M ⊗[R] I) := hfiniteTensor
  letI : Module.Finite S K := Module.Finite.of_injective K.subtype Subtype.val_injective
  have huact : u.restrictScalars R = act I := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [u, act]
    | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]
    | tmul m a => rfl
  have hkernel_range (n : ℕ) (hn : 0 < n) :
      K ≤ Submodule.span S (LinearMap.range (LinearMap.lTensor M
        (show (I ⊓ (m ^ n : Ideal R) : Submodule R R) →ₗ[R] I from
          { toFun := fun a => ⟨a.1, a.2.1⟩
            map_add' := by intro x y; rfl
            map_smul' := by intro r x; rfl }))) := by
    let J : Ideal R := m ^ n
    let L : Ideal R := I ⊔ J
    let A : Submodule R R := (I : Submodule R R) ⊓ (J : Submodule R R)
    let incA : A →ₗ[R] I :=
      { toFun := fun a => ⟨a.1, a.2.1⟩
        map_add' := by intro x y; rfl
        map_smul' := by intro r x; rfl }
    let inclI : I →ₗ[R] I × J :=
      { toFun := fun a => (a, ⟨0, J.zero_mem⟩)
        map_add' := by intro x y; ext <;> simp
        map_smul' := by intro r x; ext <;> simp }
    let projI : I × J →ₗ[R] I :=
      { toFun := fun z => z.1
        map_add' := by intro x y; rfl
        map_smul' := by intro r x; rfl }
    let f : A →ₗ[R] I × J :=
      { toFun := fun a =>
          (⟨a.1, a.2.1⟩, ⟨-a.1, J.neg_mem a.2.2⟩)
        map_add' := by intro x y; ext <;> simp <;> abel
        map_smul' := by intro r x; ext <;> simp [mul_add] }
    let g : I × J →ₗ[R] L :=
      { toFun := fun z =>
          ⟨(z.1 : R) + z.2,
            Ideal.add_mem L
              ((show I ≤ L from le_sup_left) z.1.property)
              ((show J ≤ L from le_sup_right) z.2.property)⟩
        map_add' := by
          intro x y
          apply Subtype.ext
          dsimp
          abel
        map_smul' := by
          intro r x
          apply Subtype.ext
          dsimp
          rw [mul_add] }
    let inclIL : I →ₗ[R] L :=
      { toFun := fun a => ⟨a.1, (show I ≤ L from le_sup_left) a.property⟩
        map_add' := by intro x y; rfl
        map_smul' := by intro r x; rfl }
    have hf_exact : Function.Exact f g := by
      intro z
      constructor
      · intro hz
        have hz0 : (z.1 : R) + z.2 = 0 := congrArg Subtype.val hz
        have hzrel : (z.2 : R) = -(z.1 : R) :=
          eq_neg_of_add_eq_zero_right hz0
        have hzJ : -(z.1 : R) ∈ J := by
          rw [← hzrel]
          exact z.2.property
        change -(z.1 : R) ∈ (J : Submodule R R) at hzJ
        have hzJ' : (z.1 : R) ∈ (J : Submodule R R) := by
          simpa using J.neg_mem hzJ
        let a : A := ⟨z.1, ⟨z.1.property, hzJ'⟩⟩
        refine ⟨a, ?_⟩
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          exact hzrel.symm
      · rintro ⟨a, rfl⟩
        apply Subtype.ext
        simp [f, g]
    have hg_surj : Function.Surjective g := by
      intro z
      rcases Submodule.mem_sup.mp z.property with ⟨i, hi, j, hj, hij⟩
      refine ⟨(⟨i, hi⟩, ⟨j, hj⟩), ?_⟩
      apply Subtype.ext
      simpa [g] using hij
    have htex : Function.Exact (LinearMap.lTensor M f)
        (LinearMap.lTensor M g) :=
      lTensor_exact M hf_exact hg_surj
    have hprojf : projI.comp f = incA := by
      apply LinearMap.ext
      intro a
      rfl
    have hprojincl : projI.comp inclI = LinearMap.id := by
      apply LinearMap.ext
      intro a
      rfl
    have hactmap : (act L).comp (LinearMap.lTensor M inclIL) = act I := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp [act]
      | add x y ihx ihy =>
          change act L ((LinearMap.lTensor M inclIL) x) = act I x at ihx
          change act L ((LinearMap.lTensor M inclIL) y) = act I y at ihy
          change act L ((LinearMap.lTensor M inclIL) (x + y)) = act I (x + y)
          rw [map_add, map_add, ihx, ihy, map_add]
      | tmul m a => rfl
    intro x hx
    have hxact : act I x = 0 := by
      calc
        act I x = u x := (DFunLike.congr_fun huact x).symm
        _ = 0 := hx
    have hxmap : (LinearMap.lTensor M inclIL) x = 0 := by
      apply hactinj_sum n hn
      have hnat := DFunLike.congr_fun hactmap x
      change act L ((LinearMap.lTensor M inclIL) x) = act I x at hnat
      rw [hnat, hxact]
      simp
    have hxker :
        (LinearMap.lTensor M (g))
            ((LinearMap.lTensor M inclI) x) = 0 := by
      change ((LinearMap.lTensor M g).comp
        (LinearMap.lTensor M inclI)) x = 0
      rw [← LinearMap.lTensor_comp]
      rw [show g.comp inclI = inclIL by
        apply LinearMap.ext
        intro a
        apply Subtype.ext
        simp [g, inclI, inclIL]]
      exact hxmap
    obtain ⟨w, hw⟩ := (htex ((LinearMap.lTensor M inclI) x)).mp hxker
    apply Submodule.subset_span
    refine ⟨w, ?_⟩
    have heq : (LinearMap.lTensor M incA) w = x := by
      calc
        (LinearMap.lTensor M incA) w =
            (LinearMap.lTensor M (projI.comp f)) w := by rw [hprojf]
        _ = (LinearMap.lTensor M projI)
            ((LinearMap.lTensor M f) w) := by
              exact LinearMap.lTensor_comp_apply M projI f w
        _ = (LinearMap.lTensor M projI)
            ((LinearMap.lTensor M inclI) x) := by rw [hw]
        _ = x := by
          calc
            (LinearMap.lTensor M projI)
                ((LinearMap.lTensor M inclI) x) =
                (LinearMap.lTensor M (projI.comp inclI)) x := by
                  exact (LinearMap.lTensor_comp_apply M projI inclI x).symm
            _ = x := by rw [hprojincl, LinearMap.lTensor_id_apply]
    simpa [incA, A, J] using heq
  let JS : Ideal S := m.map (algebraMap R S)
  have hJS : JS ≠ (⊤ : Ideal S) := by
    exact (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne
  obtain ⟨k, hk⟩ := m.exists_pow_inf_eq_pow_smul
    (I : Submodule R R)
  have hrange_power (n : ℕ) (hn : 0 < n) (hnk : k ≤ n) :
      Submodule.span S (LinearMap.range (LinearMap.lTensor M
        (show (I ⊓ (m ^ n : Ideal R) : Submodule R R) →ₗ[R] I from
          { toFun := fun a => ⟨a.1, a.2.1⟩
            map_add' := by intro x y; rfl
            map_smul' := by intro r x; rfl }))) ≤
        JS ^ (n - k) • (⊤ : Submodule S (M ⊗[R] I)) := by
    apply Submodule.span_le.mpr
    rintro z ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y ihx ihy =>
        rw [map_add]
        exact add_mem ihx ihy
    | tmul z a =>
        have ha : (a : R) ∈ m ^ n • (⊤ : Submodule R R) ⊓
            (I : Submodule R R) := by
          constructor
          · simpa [smul_eq_mul, Ideal.mul_top] using a.property.2
          · exact a.property.1
        rw [hk n hnk] at ha
        have hpure : ∀ (q : R), q ∈ m ^ (n - k) •
            (m ^ k • (⊤ : Submodule R R) ⊓ (I : Submodule R R)) →
            ∀ hq : q ∈ (I : Submodule R R),
              z ⊗ₜ[R] (⟨q, hq⟩ : I) ∈
                JS ^ (n - k) • (⊤ : Submodule S (M ⊗[R] I)) := by
          intro q hq
          have hleI : m ^ (n - k) •
              (m ^ k • (⊤ : Submodule R R) ⊓ (I : Submodule R R)) ≤
              (I : Submodule R R) := by
            refine Submodule.smul_le.mpr ?_
            intro r hr v hv
            exact (I : Submodule R R).smul_mem r hv.2
          refine Submodule.smul_induction_on' hq
            (p := fun q hq => ∀ hqI : q ∈ (I : Submodule R R),
              z ⊗ₜ[R] (⟨q, hqI⟩ : I) ∈
                JS ^ (n - k) • (⊤ : Submodule S (M ⊗[R] I))) ?_ ?_
          · intro r hr v hv hqI
            have hr' : algebraMap R S r ∈ JS ^ (n - k) := by
              rw [← Ideal.map_pow]
              exact Ideal.mem_map_of_mem (algebraMap R S) hr
            have hvI : v ∈ (I : Submodule R R) := hv.2
            have hmem := Submodule.smul_mem_smul hr'
              (show z ⊗ₜ[R] (⟨v, hvI⟩ : I) ∈
                (⊤ : Submodule S (M ⊗[R] I)) from Submodule.mem_top)
            have heq : z ⊗ₜ[R] (⟨r • v, hqI⟩ : I) =
                (algebraMap R S r) •
                  (z ⊗ₜ[R] (⟨v, hvI⟩ : I)) := by
              rw [show (⟨r • v, hqI⟩ : I) = r • (⟨v, hvI⟩ : I) by
                apply Subtype.ext
                rfl]
              rw [TensorProduct.tmul_smul]
              rw [IsScalarTower.algebraMap_smul]
            rw [heq]
            exact hmem
          · intro x hx y hy hxP hyP hxyI
            have hxI : x ∈ (I : Submodule R R) := hleI hx
            have hyI : y ∈ (I : Submodule R R) := hleI hy
            have heq : z ⊗ₜ[R] (⟨x + y, hxyI⟩ : I) =
                z ⊗ₜ[R] (⟨x, hxI⟩ : I) + z ⊗ₜ[R] (⟨y, hyI⟩ : I) := by
              rw [show (⟨x + y, hxyI⟩ : I) =
                  (⟨x, hxI⟩ : I) + (⟨y, hyI⟩ : I) by
                apply Subtype.ext
                rfl]
              rw [TensorProduct.tmul_add]
            rw [heq]
            exact add_mem (hxP hxI) (hyP hyI)
        exact hpure (a : R) ha a.property.1
  have hKpow (n : ℕ) (hn : 0 < n) (hnk : k ≤ n) :
      K ≤ JS ^ (n - k) • (⊤ : Submodule S (M ⊗[R] I)) := by
    exact (hkernel_range n hn).trans
      (hrange_power n hn hnk)
  have hKall : K ≤ ⨅ q : ℕ,
      JS ^ q • (⊤ : Submodule S (M ⊗[R] I)) := by
    intro x hx
    rw [Submodule.mem_iInf]
    intro q
    by_cases hq : q = 0
    · simp [hq]
    · have hnq : 0 < q + k := by omega
      have hnkq : k ≤ q + k := by omega
      have hqmem := hKpow (q + k) hnq hnkq hx
      simpa [Nat.add_sub_cancel_right] using hqmem
  have hKzero : K = ⊥ := by
    apply le_antisymm
    · rw [← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing JS hJS]
      exact hKall
    · exact bot_le
  have hactI : Function.Injective (act I) := by
    intro a b hab
    have hab0 : u (a - b) = 0 := by
      have hrel : u (a - b) = act I (a - b) := by
        exact DFunLike.congr_fun huact (a - b)
      rw [hrel, map_sub, hab, sub_self]
    have habK : a - b ∈ K := LinearMap.mem_ker.mpr hab0
    rw [hKzero] at habK
    exact sub_eq_zero.mp (show a - b = 0 by simpa using habK)
  have hcomm_act :
      (TensorProduct.lid R M).toLinearMap.comp
          (LinearMap.rTensor M (Submodule.subtype I)) =
        (act I).comp (TensorProduct.comm R I M).toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [act]
    | add x y ihx ihy =>
        rw [map_add, map_add, ihx, ihy]
    | tmul a m => rfl
  intro x y hxy
  have hxy' := congrArg (TensorProduct.lid R M) hxy
  change ((TensorProduct.lid R M).toLinearMap.comp
      (LinearMap.rTensor M (Submodule.subtype I))) x =
    ((TensorProduct.lid R M).toLinearMap.comp
      (LinearMap.rTensor M (Submodule.subtype I))) y at hxy'
  rw [hcomm_act] at hxy'
  exact (TensorProduct.comm R I M).injective (hactI hxy')

/-! ## Powers of an ideal and the local criterion -/

/-- An `R`-module is annihilated by the indicated power of an ideal. -/
def IsAnnihilatedByIdealPower
    {R N : Type u} [CommRing R] [AddCommGroup N] [Module R N]
    (I : Ideal R) (m : ℕ) : Prop :=
  I ^ m • (⊤ : Submodule R N) = ⊥

theorem what_does_it_mean
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hTor : IsZero (tor (R := R) (R ⧸ I) M 1)) :
    (∀ n : ℕ, 0 < n →
      Module.Flat (R ⧸ I ^ n)
        (M ⧸ (I ^ n • (⊤ : Submodule R M)))) ∧
      (∀ {N : Type u} [AddCommGroup N] [Module R N] (m : ℕ),
        IsAnnihilatedByIdealPower (N := N) I m →
          IsZero (tor (R := R) N M 1)) ∧
      ((∃ m : ℕ, I ^ m = ⊥) → Module.Flat R M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    sorry
  · intro N _ _ m hN
    sorry
  · intro hnil
    sorry

/-- Data for the canonical multiplication map on associated graded pieces.
The `on_pure` field fixes the map on representatives, so this is not an
arbitrary auxiliary linear map. -/
structure IdealPowerPieceMap
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (n : ℕ) where
  map : M ⊗[R] Unit69.quasiRegularPiece R R I n →ₗ[R]
    Unit69.quasiRegularPiece R M I n
  on_pure : ∀ (m : M) (a : ↥(I ^ n • (⊤ : Submodule R R))),
    map (TensorProduct.tmul R m (Submodule.Quotient.mk a)) =
      Submodule.Quotient.mk
        (⟨a.1 • m,
          Submodule.smul_mem_smul (by simpa using a.2)
            (Submodule.mem_top : m ∈ (⊤ : Submodule R M))⟩ :
          ↥(I ^ n • (⊤ : Submodule R M)))

theorem what_does_it_mean_again
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hmap : ∀ n : ℕ, IdealPowerPieceMap (M := M) I n)
    (hInjective : Function.Injective (hmap 1).map) :
    Module.Flat (R ⧸ I ^ 2)
        (M ⧸ (I ^ 2 • (⊤ : Submodule R M))) ∧
      (∀ k : ℕ,
        (∀ n : ℕ, 1 ≤ n → n ≤ k →
          Function.Injective (hmap n).map) →
        Module.Flat (R ⧸ I ^ (k + 1))
          (M ⧸ (I ^ (k + 1) • (⊤ : Submodule R M)))) := by
  sorry

theorem variant_local_criterion_flatness
    {R S M : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R]
    [IsNoetherianRing S] [AddCommGroup M] [Module S M]
    [Module R M] [IsScalarTower R S M]
    (I : Ideal R) (hI : I ≠ ⊤) (hfinite : Module.Finite S M)
    (hTor : IsZero (tor (R := R) M (R ⧸ I) 1))
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Flat R M := by
  sorry

theorem principal_ideal_tor_one_iff
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (x : R) (hx : IsSMulRegular R x) :
    IsZero (tor (R := R) M (R ⧸ Ideal.span {x}) 1) ↔
      IsSMulRegular M x := by
  sorry

/-- Flatness over the base ring of a module localized at a prime of an
algebra.  The base action is the canonical restriction of the action of the
localized algebra. -/
noncomputable def flatAtPrimeOverBase
    {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (q : PrimeSpectrum S) : Prop :=
  letI : Module R (LocalizedModule q.asIdeal.primeCompl M) :=
    Module.compHom _ (algebraMap R (Localization.AtPrime q.asIdeal))
  Module.Flat R (LocalizedModule q.asIdeal.primeCompl M)

theorem flat_module_powers
    {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S M]
    (I : Ideal R)
    (hflat : ∀ n : ℕ, 0 < n →
      Module.Flat (R ⧸ I ^ n)
        (M ⧸ (I ^ n • (⊤ : Submodule R M)))) :
    (∀ q : PrimeSpectrum S, I.map (algebraMap R S) ≤ q.asIdeal →
      flatAtPrimeOverBase (R := R) (M := M) q) ∧
      ((∀ [hSlocal : IsLocalRing S],
          I.map (algebraMap R S) ≤ IsLocalRing.maximalIdeal S →
            Module.Flat R M)) := by
  sorry

/-! ## Change-of-rings maps on Tor -/

/-- The `R`-linear map of regular modules induced by two composable ring
maps. -/
def ringHomAsBaseLinearMap
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) :
    restrictedModule f (ModuleCat.of A A) ⟶
      restrictedModule (g.comp f) (ModuleCat.of B B) := by
  letI : Module R A := Module.compHom A f
  letI : Module R B := Module.compHom B (g.comp f)
  exact ModuleCat.ofHom
    { toFun := g
      map_add' := g.map_add
      map_smul' := by
        intro r x
        change g (f r * x) = g (f r) * g x
        rw [map_mul] }

/-- The Tor map induced by the second-variable map between the two regular
modules in the preceding definition. -/
noncomputable def torSecondBaseChangeMap
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (f : R →+* R') (g : R' →+* R'') (M : ModuleCat.{u} R) :
    restrictedTor f M (ModuleCat.of R' R') 1 ⟶
      restrictedTor (g.comp f) M (ModuleCat.of R'' R'') 1 :=
  torMapSecond M
    (restrictedModule f (ModuleCat.of R' R'))
    (restrictedModule (g.comp f) (ModuleCat.of R'' R''))
    (ringHomAsBaseLinearMap f g) 1

/-- The source's natural base-change map on first Tor, with the target scalar
actions made explicit through the canonical `TargetTorModule` interface from
Chapter 76. -/
structure TorOneBaseChangeData
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (f : R →+* R') (g : R' →+* R'') (M : ModuleCat.{u} R) where
  source : TargetTorModule f M (ModuleCat.of R' R') 1
  target : TargetTorModule (g.comp f) M (ModuleCat.of R'' R'') 1
  map :
    letI := source.module
    letI := target.module
    (ModuleCat.extendScalars g).obj
        (ModuleCat.of R'
          (restrictedTor f M (ModuleCat.of R' R') 1)) ⟶
      ModuleCat.of R''
        (restrictedTor (g.comp f) M (ModuleCat.of R'' R'') 1)
  natural :
    letI : Algebra R' R'' := g.toAlgebra
    letI := source.module
    letI := target.module
    ∀ (s : R'')
      (x : restrictedTor f M (ModuleCat.of R' R') 1),
      map.hom (TensorProduct.tmul R' s x) =
        s • torSecondBaseChangeMap f g M x

theorem exists_tor_one_base_change_data
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (f : R →+* R') (g : R' →+* R'') (M : ModuleCat.{u} R) :
    Nonempty (TorOneBaseChangeData f g M) := by
  sorry

noncomputable def canonicalTorOneBaseChangeData
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (f : R →+* R') (g : R' →+* R'') (M : ModuleCat.{u} R) :
    TorOneBaseChangeData f g M :=
  Classical.choice (exists_tor_one_base_change_data f g M)

theorem surjective_on_tor_one
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (f : R →+* R') (g : R' →+* R'') (M : ModuleCat.{u} R)
    (hflat : Module.Flat R' ((ModuleCat.extendScalars f).obj M)) :
    Function.Surjective
      (let D := canonicalTorOneBaseChangeData f g M
       letI := D.source.module
       letI := D.target.module
       D.map.hom) := by
  sorry

/- The natural map in the trivial base-change situation.  It is the
change-of-rings map from Chapter 76 followed by the Tor map induced by the
extension/restriction counit on `R'/I'`. -/
noncomputable def canonicalTorOneTrivialChangeMap
    {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (I : Ideal R) (M : ModuleCat.{u} R) :
    Tor (restrictedModule f (ModuleCat.of R' (R' ⧸ I.map f))) M 1 ⟶
      (ModuleCat.restrictScalars f).obj
        (Tor (ModuleCat.of R' (R' ⧸ I.map f))
          ((ModuleCat.extendScalars f).obj M) 1) := by
  exact canonicalTorChangeOfRingsMap f
      (restrictedModule f (ModuleCat.of R' (R' ⧸ I.map f))) M 1 ≫
    (ModuleCat.restrictScalars f).map
      (torMapFirst (N := (ModuleCat.extendScalars f).obj M)
        ((ModuleCat.extendRestrictScalarsAdj f).counit.app
          (ModuleCat.of R' (R' ⧸ I.map f))) 1)

theorem surjective_on_tor_one_trivial
    {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (I : Ideal R) (M : ModuleCat.{u} R) :
    Function.Surjective
      (canonicalTorOneTrivialChangeMap f I M).hom := by
  sorry

/-! ## A localization of a tensor product -/

/-- The ring map from a tensor product to the target of a commutative square. -/
def tensorProductToSquareTarget
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    (compat : h.comp f = k.comp g) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    letI : Algebra R S' := (h.comp f).toAlgebra
    letI : Algebra R' S' := k.toAlgebra
    S ⊗[R] R' →+* S' := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  letI : Algebra R S' := (h.comp f).toAlgebra
  letI : Algebra R' S' := k.toAlgebra
  let hs : S →ₐ[R] S' :=
    { toRingHom := h
      commutes' := fun r => rfl }
  let hk : R' →ₐ[R] S' :=
    { toRingHom := k
      commutes' := fun r => by
        change k (g r) = h (f r)
        simpa [RingHom.comp_apply] using
          congrArg (fun q : R →+* S' => q r) compat.symm }
  exact (Algebra.TensorProduct.lift hs hk (fun _ _ => Commute.all _ _)).toRingHom

/-- `S'` is a localization of `S ⊗[R] R'` for the map supplied by the
commutative square. -/
def IsTensorProductLocalization
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    (compat : h.comp f = k.comp g) : Prop :=
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  letI : Algebra R S' := (h.comp f).toAlgebra
  letI : Algebra R' S' := k.toAlgebra
  ∃ P : Submonoid (S ⊗[R] R'),
    letI : Algebra (S ⊗[R] R') S' :=
      (tensorProductToSquareTarget f g h k compat).toAlgebra
    IsLocalization P S'

/-- The base-changed module `M ⊗_S S'`, viewed as an `R'`-module. -/
abbrev squareBaseChangedModule
    {R' S S' : Type u} [CommRing R'] [CommRing S] [CommRing S']
    (h : S →+* S') (k : R' →+* S') (M : ModuleCat.{u} S) : ModuleCat.{u} R' :=
  (ModuleCat.restrictScalars k).obj ((ModuleCat.extendScalars h).obj M)

/-- The natural Tor map for the second local-criterion variant, represented
as an `R`-linear map by restricting the target scalars along `R → R'`. -/
structure TorOneSquareMapData
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    (I : Ideal R) (M : ModuleCat.{u} S) where
  map :
    Tor ((ModuleCat.restrictScalars f).obj M)
        (ModuleCat.of R (R ⧸ I)) 1 ⟶
      (ModuleCat.restrictScalars g).obj
        (Tor (squareBaseChangedModule h k M)
          (ModuleCat.of R' (R' ⧸ I.map g)) 1)

theorem exists_tor_one_square_map_data
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    (I : Ideal R) (M : ModuleCat.{u} S) :
    Nonempty (TorOneSquareMapData f g h k I M) := by
  sorry

noncomputable def canonicalTorOneSquareMapData
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    (I : Ideal R) (M : ModuleCat.{u} S) :
    TorOneSquareMapData f g h k I M :=
  Classical.choice (exists_tor_one_square_map_data f g h k I M)

theorem another_variant_local_criterion_flatness
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing R']
    [IsNoetherianRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    [IsLocalHom f] [IsLocalHom g] [IsLocalHom h] [IsLocalHom k]
    (compat : h.comp f = k.comp g) (I : Ideal R) (hI : I ≠ ⊤)
    (M : ModuleCat.{u} S) (hfinite : Module.Finite S M)
    (hlocal : IsTensorProductLocalization f g h k compat)
    (hflat : Module.Flat (R ⧸ I)
      ((ModuleCat.restrictScalars f).obj M ⧸
        (I • (⊤ : Submodule R ((ModuleCat.restrictScalars f).obj M)))))
    (hzero : (canonicalTorOneSquareMapData f g h k I M).map = 0) :
    Module.Flat R' (squareBaseChangedModule h k M) := by
  sorry

/-! ## Fibre criterion and the scallop lemmas -/

theorem criterion_flatness_fibre_Noetherian
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing S']
    (f : R →+* S) (g : S →+* S') [IsLocalHom f] [IsLocalHom g]
    {M : ModuleCat.{u} S'} (hfinite : Module.Finite S' M)
    (hM : Nontrivial M)
    (hfibre : Module.Flat (S ⧸
        (IsLocalRing.maximalIdeal R).map f)
      ((ModuleCat.restrictScalars g).obj M ⧸
        ((IsLocalRing.maximalIdeal R).map f •
          (⊤ : Submodule S ((ModuleCat.restrictScalars g).obj M)))))
    (hflat : Module.Flat R
      ((ModuleCat.restrictScalars (g.comp f)).obj M)) :
    Module.Flat R ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) ∧
      Module.Flat S ((ModuleCat.restrictScalars g).obj M) := by
  sorry

theorem flatness_scallop
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (f : A) (hfA : IsSMulRegular A f) (hfM : IsSMulRegular M f)
    (hflat_local : Module.Flat (Localization (Submonoid.powers f))
      (LocalizedModule (Submonoid.powers f) M))
    (hflat_quotient : Module.Flat (A ⧸ Ideal.span {f})
      (M ⧸ (Ideal.span {f} • (⊤ : Submodule A M)))) :
    Module.Flat A M := by
  sorry

theorem faithfullyFlat_scallop
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (f : A) (hfA : IsSMulRegular A f) (hfM : IsSMulRegular M f)
    (hfaithful_local :
      Module.FaithfullyFlat (Localization (Submonoid.powers f))
        (LocalizedModule (Submonoid.powers f) M))
    (hfaithful_quotient : Module.FaithfullyFlat (A ⧸ Ideal.span {f})
      (M ⧸ (Ideal.span {f} • (⊤ : Submodule A M)))) :
    Module.FaithfullyFlat A M := by
  sorry

theorem flatness_scallop_pre
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (r : ℕ) (hr : 0 < r) (f : Fin r → A)
    (hflat_local : ∀ i : Fin r,
      Module.Flat (Localization (Submonoid.powers (f i)))
        (LocalizedModule (Submonoid.powers (f i)) M))
    (hflat_quotient :
      Module.Flat (A ⧸ Ideal.span (Set.range f))
        (M ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule A M))))
    (hTor : ∀ i : ℕ, 1 ≤ i → i ≤ r + 1 →
      IsZero (tor (R := A) M
        (A ⧸ Ideal.span (Set.range f)) i)) :
    Module.Flat A M := by
  sorry

theorem faithfullyFlat_scallop_pre
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (r : ℕ) (hr : 0 < r) (f : Fin r → A)
    (hfaithful_local : ∀ i : Fin r,
      Module.FaithfullyFlat (Localization (Submonoid.powers (f i)))
        (LocalizedModule (Submonoid.powers (f i)) M))
    (hfaithful_quotient :
      Module.FaithfullyFlat (A ⧸ Ideal.span (Set.range f))
        (M ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule A M))))
    (hTor : ∀ i : ℕ, 1 ≤ i → i ≤ r + 1 →
      IsZero (tor (R := A) M
        (A ⧸ Ideal.span (Set.range f)) i)) :
    Module.FaithfullyFlat A M := by
  sorry

end

end Formalization.Books.Algebra.Unit99
