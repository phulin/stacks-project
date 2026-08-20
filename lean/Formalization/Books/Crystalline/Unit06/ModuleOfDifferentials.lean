import Formalization.Books.Crystalline.Unit05.AffineSite
import Formalization.Books.Algebra.Unit131.Differentials
import Formalization.Books.Algebra.Unit13.TensorAlgebra
import Formalization.Books.Dpa.Unit04.ExtendingDividedPowers
import Formalization.Books.Crystalline.Unit02.DividedPowerEnvelope
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DividedPowers.SubDPIdeal
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Crystalline Cohomology, Chapter 6: Module of differentials

This file formalizes the section `Module of differentials`.  Ordinary
Kähler differentials and exterior powers are reused from the earlier
algebra formalizations; the additional structure here records the
divided-power derivation condition and its consequences.
-/

namespace Formalization.Books.Crystalline.Unit06

open CategoryTheory CategoryTheory.Limits
open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open Formalization.Books.Crystalline.Unit02
open Formalization.Books.Crystalline.Unit05
open Formalization.Books.Dpa.Unit03
open Formalization.Books.Dpa.Unit03.DividedPowerRing
open Formalization.Books.Dpa.Unit04
open Formalization.Books.Dpa.Unit05
open scoped TensorProduct

universe u

noncomputable section

/-! ## Divided-power derivations and the universal module -/

/-- A divided-power `A`-derivation from a divided-power ring `B` to a
`B`-module `M`.  The `n ≠ 0` formulation matches Mathlib's convention that
divided powers are extended to all natural numbers by zero away from the
ideal. -/
structure DividedPowerDerivation (A : Type u) [CommRing A]
    (B : DividedPowerRing.{u}) (f : A →+* (B : Type u))
    (M : ModuleCat (B : Type u)) extends (B : Type u) →+ (M : Type u) where
  map_base' : ∀ a : A, toAddMonoidHom (f a) = 0
  leibniz' : ∀ b b' : B,
    toAddMonoidHom (b * b') = b • toAddMonoidHom b' + b' • toAddMonoidHom b
  dpow' : ∀ {n : ℕ} {x : B}, n ≠ 0 → x ∈ B.ideal →
    toAddMonoidHom (B.dividedPowers.dpow n x) =
      B.dividedPowers.dpow (n - 1) x • toAddMonoidHom x

@[simp] theorem DividedPowerDerivation.map_zero
    {A : Type u} [CommRing A] {B : DividedPowerRing.{u}}
    {f : A →+* (B : Type u)} {M : ModuleCat (B : Type u)}
    (θ : DividedPowerDerivation A B f M) : θ.toAddMonoidHom 0 = 0 :=
  θ.toAddMonoidHom.map_zero

@[simp] theorem DividedPowerDerivation.map_add
    {A : Type u} [CommRing A] {B : DividedPowerRing.{u}}
    {f : A →+* (B : Type u)} {M : ModuleCat (B : Type u)}
    (θ : DividedPowerDerivation A B f M) (b b' : (B : Type u)) :
      θ.toAddMonoidHom (b + b') = θ.toAddMonoidHom b + θ.toAddMonoidHom b' :=
  θ.toAddMonoidHom.map_add b b'

/-- The divided-power analogue of the universal property of Kähler
differentials. -/
structure UniversalDividedPowerDifferential (A : Type u) [CommRing A]
    (B : DividedPowerRing.{u}) (f : A →+* (B : Type u)) where
  omega : ModuleCat (B : Type u)
  d : DividedPowerDerivation A B f omega
  lift : ∀ M : ModuleCat (B : Type u),
    (DividedPowerDerivation A B f M) → (omega ⟶ M)
  factor : ∀ (M : ModuleCat (B : Type u)) (θ : DividedPowerDerivation A B f M)
    (b : (B : Type u)),
      (lift M θ) (d.toAddMonoidHom b) = θ.toAddMonoidHom b
  unique : ∀ (M : ModuleCat (B : Type u)) (θ : DividedPowerDerivation A B f M)
    (ξ : omega ⟶ M),
      (∀ b : (B : Type u), ξ (d.toAddMonoidHom b) = θ.toAddMonoidHom b) →
        ξ = lift M θ

theorem exists_universalDividedPowerDifferential
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) :
    Nonempty (UniversalDividedPowerDifferential A B f) := by
  let _ : Algebra A (B : Type u) := f.toAlgebra
  let R : Submodule (B : Type u) (ModuleOfDifferentials A (B : Type u)) :=
    Submodule.span (B : Type u)
      {y | ∃ n : ℕ, n ≠ 0 ∧ ∃ x : B, x ∈ B.ideal ∧
        y = universalDifferential A (B : Type u)
              (B.dividedPowers.dpow n x) -
          B.dividedPowers.dpow (n - 1) x •
            universalDifferential A (B : Type u) x}
  let Ω : ModuleCat (B : Type u) :=
    ModuleCat.of (B : Type u)
      ((ModuleOfDifferentials A (B : Type u)) ⧸ R)
  let q : ModuleOfDifferentials A (B : Type u) →ₗ[B] (Ω : Type u) := R.mkQ
  let dθ : DividedPowerDerivation A B f Ω := by
    exact
      { toAddMonoidHom :=
          { toFun := fun b => q (universalDifferential A (B : Type u) b)
            map_zero' := by simp
            map_add' := by intro b b'; simp }
        map_base' := by
          intro a
          change q (universalDifferential A (B : Type u)
            (algebraMap A (B : Type u) a)) = 0
          simp
        leibniz' := by
          intro b b'
          change q (universalDifferential A (B : Type u) (b * b')) =
            b • q (universalDifferential A (B : Type u) b') +
              b' • q (universalDifferential A (B : Type u) b)
          rw [Derivation.leibniz]
          simp [LinearMap.map_add]
        dpow' := by
          intro n x hn hx
          change q (universalDifferential A (B : Type u)
              (B.dividedPowers.dpow n x)) =
            B.dividedPowers.dpow (n - 1) x •
              q (universalDifferential A (B : Type u) x)
          rw [← q.map_smul, ← sub_eq_zero]
          apply (Submodule.Quotient.mk_eq_zero R).mpr
          apply Submodule.subset_span
          exact ⟨n, hn, x, hx, rfl⟩ }
  refine ⟨{ omega := Ω, d := dθ, lift := ?_, factor := ?_, unique := ?_ }⟩
  · intro M θ
    letI : Module A (M : Type u) := Module.compHom (M : Type u) f
    let _ : IsScalarTower A (B : Type u) (M : Type u) :=
      IsScalarTower.of_compHom A (M : Type u)
    let θlin : B →ₗ[A] (M : Type u) :=
      { toFun := θ.toAddMonoidHom
        map_add' := by
          intro b b'
          exact θ.toAddMonoidHom.map_add b b'
        map_smul' := by
          intro a b
          change θ.toAddMonoidHom (f a * b) = f a • θ.toAddMonoidHom b
          rw [θ.leibniz', θ.map_base']
          simp }
    let Dθ : Derivation A (B : Type u) (M : Type u) :=
      Derivation.mk' θlin (by
        intro b b'
        simpa [θlin] using θ.leibniz' b b')
    let L : ModuleOfDifferentials A (B : Type u) →ₗ[B] (M : Type u) :=
      Dθ.liftKaehlerDifferential
    have hL : R ≤ LinearMap.ker L := by
      apply Submodule.span_le.2
      rintro y ⟨n, hn, x, hx, rfl⟩
      rw [LinearMap.mem_ker, map_sub, map_smul,
        Dθ.liftKaehlerDifferential_comp_D]
      rw [Dθ.liftKaehlerDifferential_comp_D]
      change θ.toAddMonoidHom (B.dividedPowers.dpow n x) -
        B.dividedPowers.dpow (n - 1) x • θ.toAddMonoidHom x = 0
      rw [θ.dpow' hn hx]
      exact sub_self _
    exact ModuleCat.ofHom (R.liftQ L hL)
  · intro M θ b
    letI : Module A (M : Type u) := Module.compHom (M : Type u) f
    let _ : IsScalarTower A (B : Type u) (M : Type u) :=
      IsScalarTower.of_compHom A (M : Type u)
    let θlin : B →ₗ[A] (M : Type u) :=
      { toFun := θ.toAddMonoidHom
        map_add' := by
          intro b b'
          exact θ.toAddMonoidHom.map_add b b'
        map_smul' := by
          intro a b
          change θ.toAddMonoidHom (f a * b) = f a • θ.toAddMonoidHom b
          rw [θ.leibniz', θ.map_base']
          simp }
    let Dθ : Derivation A (B : Type u) (M : Type u) :=
      Derivation.mk' θlin (by
        intro b b'
        simpa [θlin] using θ.leibniz' b b')
    let L : ModuleOfDifferentials A (B : Type u) →ₗ[B] (M : Type u) :=
      Dθ.liftKaehlerDifferential
    have hL : R ≤ LinearMap.ker L := by
      apply Submodule.span_le.2
      rintro y ⟨n, hn, x, hx, rfl⟩
      rw [LinearMap.mem_ker, map_sub, map_smul,
        Dθ.liftKaehlerDifferential_comp_D]
      change θ.toAddMonoidHom (B.dividedPowers.dpow n x) -
        B.dividedPowers.dpow (n - 1) x • θ.toAddMonoidHom x = 0
      rw [θ.dpow' hn hx]
      exact sub_self _
    change (R.liftQ L hL) (q (universalDifferential A (B : Type u) b)) =
      θ.toAddMonoidHom b
    rw [Submodule.liftQ_mkQ]
    exact Dθ.liftKaehlerDifferential_comp_D b
  · intro M θ ξ hξ
    letI : Module A (M : Type u) := Module.compHom (M : Type u) f
    let _ : IsScalarTower A (B : Type u) (M : Type u) :=
      IsScalarTower.of_compHom A (M : Type u)
    let θlin : B →ₗ[A] (M : Type u) :=
      { toFun := θ.toAddMonoidHom
        map_add' := by
          intro b b'
          exact θ.toAddMonoidHom.map_add b b'
        map_smul' := by
          intro a b
          change θ.toAddMonoidHom (f a * b) = f a • θ.toAddMonoidHom b
          rw [θ.leibniz', θ.map_base']
          simp }
    let Dθ : Derivation A (B : Type u) (M : Type u) :=
      Derivation.mk' θlin (by
        intro b b'
        simpa [θlin] using θ.leibniz' b b')
    let L : ModuleOfDifferentials A (B : Type u) →ₗ[B] (M : Type u) :=
      Dθ.liftKaehlerDifferential
    have hL : R ≤ LinearMap.ker L := by
      apply Submodule.span_le.2
      rintro y ⟨n, hn, x, hx, rfl⟩
      rw [LinearMap.mem_ker, map_sub, map_smul,
        Dθ.liftKaehlerDifferential_comp_D]
      change θ.toAddMonoidHom (B.dividedPowers.dpow n x) -
        B.dividedPowers.dpow (n - 1) x • θ.toAddMonoidHom x = 0
      rw [θ.dpow' hn hx]
      exact sub_self _
    have hmaps :
        (ξ.hom.comp q).compDer (universalDifferential A (B : Type u)) =
          L.compDer (universalDifferential A (B : Type u)) := by
      ext b
      change ξ.hom (q (universalDifferential A (B : Type u) b)) =
        θ.toAddMonoidHom b
      rw [← hξ b, Submodule.liftQ_mkQ]
      exact Dθ.liftKaehlerDifferential_comp_D b
    have hmaps' : ξ.hom.comp q = L :=
      Derivation.liftKaehlerDifferential_unique _ _ hmaps
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective R z
    rw [← Submodule.liftQ_mkQ R L hL y]
    exact congrArg (fun g => g y) hmaps'

/-- A chosen universal divided-power differential. -/
noncomputable def universalDividedPowerDifferential
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) : UniversalDividedPowerDifferential A B f :=
  Classical.choice (exists_universalDividedPowerDifferential A B f)

noncomputable abbrev dividedPowerOmega
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) : ModuleCat (B : Type u) :=
  (universalDividedPowerDifferential A B f).omega

noncomputable abbrev dividedPowerUniversalDifferential
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) :
    DividedPowerDerivation A B f (dividedPowerOmega A B f) :=
  (universalDividedPowerDifferential A B f).d

/-! ## Polynomial extensions and quotients -/

/-- The ordinary polynomial ring with the divided-power ideal used in the
source's polynomial calculation. -/
def ordinaryPolynomialDividedPowerRing
    (B : DividedPowerRing.{u}) (T : Type u)
    (δ : DividedPowers (polynomialExtensionIdeal B.ideal T)) :
    DividedPowerRing.{u} :=
  { toCommRing := CommRingCat.of (MvPolynomial T (B : Type u))
    ideal := polynomialExtensionIdeal B.ideal T
    dividedPowers := δ }

def ordinaryPolynomialCoefficientHom
    (B : DividedPowerRing.{u}) (T : Type u)
    (δ : DividedPowers (polynomialExtensionIdeal B.ideal T))
    (hδ : ∀ {n : ℕ} {x : B}, n ≠ 0 → x ∈ B.ideal →
      δ.dpow n (algebraMap (B : Type u) (MvPolynomial T (B : Type u)) x) =
        algebraMap (B : Type u) (MvPolynomial T (B : Type u))
          (B.dividedPowers.dpow n x)) :
    DividedPowerRing.Hom B (ordinaryPolynomialDividedPowerRing B T δ) :=
  { hom := algebraMap (B : Type u) (MvPolynomial T (B : Type u))
    ideal_map := by
      intro x hx
      exact Ideal.mem_sup_left (Ideal.mem_map_of_mem
        (algebraMap (B : Type u) (MvPolynomial T (B : Type u))) hx)
    dpow_comm := by
      intro n x hx
      by_cases hn : n = 0
      · subst hn
        have hmem : MvPolynomial.C x ∈ polynomialExtensionIdeal B.ideal T :=
          Ideal.mem_sup_left (Ideal.mem_map_of_mem
            (algebraMap (B : Type u) (MvPolynomial T (B : Type u))) hx)
        change δ.dpow 0 (algebraMap (B : Type u)
          (MvPolynomial T (B : Type u)) x) =
          algebraMap (B : Type u) (MvPolynomial T (B : Type u))
            (B.dividedPowers.dpow 0 x)
        have hδ0 :
            δ.dpow 0 (algebraMap (B : Type u)
              (MvPolynomial T (B : Type u)) x) = 1 := by
          exact δ.dpow_zero hmem
        have hB0 : B.dividedPowers.dpow 0 x = 1 :=
          B.dividedPowers.dpow_zero hx
        rw [hδ0, hB0]
        simp
      · exact hδ hn hx }

/-- The divided-power polynomial algebra with its canonical coefficient
compatibility condition. -/
def dividedPowerPolynomialExtension
    (B : DividedPowerRing.{u}) (t : ℕ)
    (δ : DividedPowers
      (dividedPowerPolynomialIdeal (B : Type u) B.ideal t))
    (hδ : CoefficientDpowCompatible B t δ) :
    DividedPowerRing.{u} :=
  dividedPowerPolynomialRing B t δ

def dividedPowerPolynomialExtensionHom
    (B : DividedPowerRing.{u}) (t : ℕ)
    (δ : DividedPowers
      (dividedPowerPolynomialIdeal (B : Type u) B.ideal t))
    (hδ : CoefficientDpowCompatible B t δ) :
    DividedPowerRing.Hom B (dividedPowerPolynomialExtension B t δ hδ) :=
  dividedPowerPolynomialCoefficientHom B t δ hδ

abbrev ordinaryDifferentialModule
    (A B : Type u) [CommRing A] [CommRing B]
    (f : A →+* B) : Type u :=
  @ModuleOfDifferentials A B _ _ f.toAlgebra

noncomputable def ordinaryDifferentialModuleCat
    (A B : Type u) [CommRing A] [CommRing B]
    (f : A →+* B) : ModuleCat.{u, u} B := by
  letI : Algebra A B := f.toAlgebra
  exact ModuleCat.of B (ordinaryDifferentialModule A B f)

noncomputable def baseChangeModuleCat
    (R S : Type u) [CommRing R] [CommRing S]
    (M : ModuleCat.{u, u} R) (g : R →+* S) : ModuleCat.{u, u} S := by
  letI : Algebra R S := g.toAlgebra
  exact ModuleCat.of S (S ⊗[R] (M : Type u))

/-- A source-facing direct sum of module objects. -/
def directSumModuleCat {R : Type u} [CommRing R]
    (M N : ModuleCat.{u, u} R) : ModuleCat.{u, u} R :=
  M ⊞ N

theorem omega_polynomial_extension_iso
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) (T : Type u)
    (δ : DividedPowers (polynomialExtensionIdeal B.ideal T))
    (hδ : ∀ {n : ℕ} {x : B}, n ≠ 0 → x ∈ B.ideal →
      δ.dpow n (algebraMap (B : Type u) (MvPolynomial T (B : Type u)) x) =
        algebraMap (B : Type u) (MvPolynomial T (B : Type u))
          (B.dividedPowers.dpow n x)) :
    Nonempty
      (dividedPowerOmega A (ordinaryPolynomialDividedPowerRing B T δ)
          ((ordinaryPolynomialCoefficientHom B T δ hδ).hom.comp f) ≅
        directSumModuleCat
          (baseChangeModuleCat B (MvPolynomial T (B : Type u))
            (ordinaryDifferentialModuleCat A (B : Type u) f)
            (ordinaryPolynomialCoefficientHom B T δ hδ).hom)
          (ModuleCat.of (MvPolynomial T (B : Type u))
            (MvPolynomial T (B : Type u)))) := by
  sorry

theorem omega_dividedPowerPolynomial_extension_iso
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) (t : ℕ)
    (δ : DividedPowers
      (dividedPowerPolynomialIdeal (B : Type u) B.ideal t))
    (hδ : CoefficientDpowCompatible B t δ) :
    Nonempty
      (dividedPowerOmega A (dividedPowerPolynomialExtension B t δ hδ)
          ((dividedPowerPolynomialExtensionHom B t δ hδ).hom.comp f) ≅
        directSumModuleCat
          (baseChangeModuleCat B
            (dividedPowerPolynomialExtension B t δ hδ : Type u)
            (ordinaryDifferentialModuleCat A (B : Type u) f)
            (dividedPowerPolynomialExtensionHom B t δ hδ).hom)
          (ModuleCat.of (dividedPowerPolynomialExtension B t δ hδ : Type u)
            (dividedPowerPolynomialExtension B t δ hδ : Type u))) := by
  sorry

/-! The quotient part of the polynomial lemma is recorded with an explicit
quotient divided-power ring.  The kernel-stability field is the exact
hypothesis used by the source to induce divided powers on the quotient. -/

structure DividedPowerQuotientPresentation
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) (K : Ideal (B : Type u)) where
  quotient : DividedPowerRing.{u}
  quotientMap : DividedPowerRing.Hom B quotient
  kernel_eq : RingHom.ker quotientMap.hom = K
  kernel_in_ideal : K ≤ B.ideal
  kernel_dpow_stable : ∀ {n : ℕ} {x : B}, n ≠ 0 → x ∈ K →
    B.dividedPowers.dpow n x ∈ K

noncomputable def quotientDifferentialRelation
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) (K : Ideal (B : Type u))
    (Q : DividedPowerQuotientPresentation A B f K) :
    Submodule (Q.quotient : Type u)
      ((baseChangeModuleCat B (Q.quotient : Type u)
        (ordinaryDifferentialModuleCat A (B : Type u) f)
        Q.quotientMap.hom : Type u)) := by
  letI : Algebra A (B : Type u) := f.toAlgebra
  letI : Algebra (B : Type u) (Q.quotient : Type u) :=
    Q.quotientMap.hom.toAlgebra
  exact Submodule.span (Q.quotient : Type u)
    {y | ∃ k : K, y = (1 : Q.quotient) ⊗ₜ[B]
      universalDifferential A (B : Type u) (k : B)}

noncomputable def quotientDifferentialModule
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) (K : Ideal (B : Type u))
    (Q : DividedPowerQuotientPresentation A B f K) :
    ModuleCat (Q.quotient : Type u) :=
  ModuleCat.of (Q.quotient : Type u)
    ((baseChangeModuleCat B (Q.quotient : Type u)
      (ordinaryDifferentialModuleCat A (B : Type u) f)
      Q.quotientMap.hom : Type u) ⧸ quotientDifferentialRelation A B f K Q)

theorem omega_quotient_differential_iso
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) (K : Ideal (B : Type u))
    (Q : DividedPowerQuotientPresentation A B f K) :
    Nonempty (dividedPowerOmega A Q.quotient
        (Q.quotientMap.hom.comp f) ≅ quotientDifferentialModule A B f K Q) := by
  sorry

noncomputable def dividedPowerDifferentialRelation
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) :
    Submodule (B : Type u) (ordinaryDifferentialModule A (B : Type u) f) := by
  letI : Algebra A (B : Type u) := f.toAlgebra
  exact Submodule.span B
    {y | ∃ n : ℕ, n > 1 ∧ ∃ x : B, x ∈ B.ideal ∧
      y = universalDifferential A B
          (B.dividedPowers.dpow n x) -
        B.dividedPowers.dpow (n - 1) x • universalDifferential A B x}

noncomputable def dividedPowerOrdinaryQuotientModule
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) : ModuleCat (B : Type u) := by
  exact ModuleCat.of (B : Type u)
    ((ordinaryDifferentialModule A (B : Type u) f) ⧸
      dividedPowerDifferentialRelation A B f)

theorem dividedPowerOmega_is_ordinary_quotient
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) :
    Nonempty (dividedPowerOmega A B f ≅
      dividedPowerOrdinaryQuotientModule A B f) := by
  let _ : Algebra A (B : Type u) := f.toAlgebra
  let U := universalDividedPowerDifferential A B f
  let N := dividedPowerDifferentialRelation A B f
  let qN : ModuleOfDifferentials A (B : Type u) →ₗ[B]
      (dividedPowerOrdinaryQuotientModule A B f : Type u) := N.mkQ
  let dQ : DividedPowerDerivation A B f
      (dividedPowerOrdinaryQuotientModule A B f) :=
    { toAddMonoidHom :=
        { toFun := fun b => qN (universalDifferential A (B : Type u) b)
          map_zero' := by simp
          map_add' := by intro b b'; simp }
      map_base' := by
        intro a
        change qN (universalDifferential A (B : Type u)
          (algebraMap A (B : Type u) a)) = 0
        simp
      leibniz' := by
        intro b b'
        change qN (universalDifferential A (B : Type u) (b * b')) =
          b • qN (universalDifferential A (B : Type u) b') +
            b' • qN (universalDifferential A (B : Type u) b)
        rw [Derivation.leibniz]
        simp [LinearMap.map_add]
      dpow' := by
        intro n x hn hx
        by_cases hn' : 1 < n
        · change qN (universalDifferential A (B : Type u)
              (B.dividedPowers.dpow n x)) =
            B.dividedPowers.dpow (n - 1) x •
              qN (universalDifferential A (B : Type u) x)
          rw [← qN.map_smul, ← sub_eq_zero]
          apply (Submodule.Quotient.mk_eq_zero N).mpr
          apply Submodule.subset_span
          exact ⟨n, hn', x, hx, rfl⟩
        · have hn1 : n = 1 := by omega
          subst n
          simp [B.dividedPowers.dpow_one hx] }
  let φ : (dividedPowerOmega A B f) ⟶
      dividedPowerOrdinaryQuotientModule A B f :=
    U.lift _ dQ
  let _ : Module A (dividedPowerOmega A B f : Type u) :=
    Module.compHom (dividedPowerOmega A B f : Type u) f
  let _ : IsScalarTower A (B : Type u)
      (dividedPowerOmega A B f : Type u) :=
    IsScalarTower.of_compHom A (dividedPowerOmega A B f : Type u)
  let θlin : (B : Type u) →ₗ[A]
      (dividedPowerOmega A B f : Type u) :=
    { toFun := (dividedPowerUniversalDifferential A B f).toAddMonoidHom
      map_add' := by intro b b'; simp
      map_smul' := by
        intro a b
        change (dividedPowerUniversalDifferential A B f).toAddMonoidHom
            (f a * b) = f a •
              (dividedPowerUniversalDifferential A B f).toAddMonoidHom b
        rw [(dividedPowerUniversalDifferential A B f).leibniz',
          (dividedPowerUniversalDifferential A B f).map_base']
        simp }
  let Dω : Derivation A (B : Type u)
      (dividedPowerOmega A B f : Type u) :=
    Derivation.mk' θlin (by
      intro b b'
      simpa [θlin] using
        (dividedPowerUniversalDifferential A B f).leibniz' b b')
  let L : ModuleOfDifferentials A (B : Type u) →ₗ[B]
      (dividedPowerOmega A B f : Type u) := Dω.liftKaehlerDifferential
  have hN : N ≤ LinearMap.ker L := by
    apply Submodule.span_le.2
    rintro y ⟨n, hn, x, hx, rfl⟩
    rw [LinearMap.mem_ker, map_sub, map_smul,
      Dω.liftKaehlerDifferential_comp_D]
    change (dividedPowerUniversalDifferential A B f).toAddMonoidHom
          (B.dividedPowers.dpow n x) -
        B.dividedPowers.dpow (n - 1) x •
          (dividedPowerUniversalDifferential A B f).toAddMonoidHom x = 0
    rw [(dividedPowerUniversalDifferential A B f).dpow'
      (by omega) hx]
    exact sub_self _
  let ψ : dividedPowerOrdinaryQuotientModule A B f ⟶
      dividedPowerOmega A B f := ModuleCat.ofHom (N.liftQ L hN)
  have hbase : φ.hom.comp (N.liftQ L hN) = qN := by
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    change φ.hom (L (universalDifferential A (B : Type u) b)) =
      qN (universalDifferential A (B : Type u) b)
    rw [Dω.liftKaehlerDifferential_comp_D]
    change φ.hom ((dividedPowerUniversalDifferential A B f).toAddMonoidHom b) = _
    rw [U.factor]
    rfl
  refine ⟨{ hom := φ, inv := ψ, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · apply U.unique U.omega U.d (φ ≫ ψ)
    intro b
    change ψ (φ (U.d.toAddMonoidHom b)) = U.d.toAddMonoidHom b
    rw [U.factor]
    change (N.liftQ L hN) (qN (universalDifferential A (B : Type u) b)) = _
    rw [N.liftQ_mkQ]
    exact Dω.liftKaehlerDifferential_comp_D b
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective N z
    change φ.hom ((N.liftQ L hN) (N.mkQ y)) = N.mkQ y
    rw [N.liftQ_mkQ]
    exact congrArg (fun g => g y) hbase

noncomputable def dividedPowerDifferentialSubmodule
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) :
    Submodule (B : Type u) (dividedPowerOmega A B f : Type u) := by
  letI : Algebra A (B : Type u) := f.toAlgebra
  exact Submodule.span (B : Type u)
    {y | ∃ x : B, x ∈ B.ideal ∧
      y = (dividedPowerUniversalDifferential A B f).toAddMonoidHom x}

theorem dividedPowerDifferentialSubmodule_minimal
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u))
    (N : Submodule (B : Type u) (dividedPowerOmega A B f : Type u))
    (hN : ∀ x : B, x ∈ B.ideal →
      (dividedPowerUniversalDifferential A B f).toAddMonoidHom x ∈ N) :
    dividedPowerDifferentialSubmodule A B f ≤ N := by
  unfold dividedPowerDifferentialSubmodule
  apply Submodule.span_le.2
  rintro y ⟨x, hx, rfl⟩
  exact hN x hx

/-! ## Divided-power powers of an ideal -/

/-- The ideal generated by products of divided powers whose total exponent
is at least `n`.  The empty product makes the convention at `n = 0`
explicit. -/
def dividedPowerIdealPower {B : Type u} [CommRing B] (I : Ideal B)
    (δ : DividedPowers I) (n : ℕ) : Ideal B :=
  Ideal.span {y : B | ∃ t : ℕ, ∃ e : Fin t → ℕ, n ≤ ∑ i, e i ∧
    ∃ x : Fin t → B, (∀ i, x i ∈ I) ∧
      y = ∏ i, δ.dpow (e i) (x i)}

theorem ideal_pow_le_dividedPowerIdealPower
    {B : Type u} [CommRing B] (I : Ideal B) (δ : DividedPowers I) (n : ℕ) :
    I ^ n ≤ dividedPowerIdealPower I δ n := by
  sorry

theorem dividedPowerIdealPower_one
    {B : Type u} [CommRing B] (I : Ideal B) (δ : DividedPowers I) :
    dividedPowerIdealPower I δ 1 = I := by
  sorry

theorem dividedPowerIdealPower_zero
    {B : Type u} [CommRing B] (I : Ideal B) (δ : DividedPowers I) :
    dividedPowerIdealPower I δ 0 = ⊤ := by
  sorry

/-! ## The diagonal presentation -/

/-- A divided-power coproduct of two copies of `B` over `A`, together with
the codiagonal used to define its diagonal ideal. -/
structure DividedPowerDiagonal (A : DividedPowerRing.{u})
    (B : DividedPowerRing.{u}) (base : DividedPowerRing.Hom A B) where
  pushoutObject : DividedPowerRing.{u}
  left : DividedPowerRing.Hom B pushoutObject
  right : DividedPowerRing.Hom B pushoutObject
  over_base : left.hom.comp base.hom = right.hom.comp base.hom
  codiagonal : DividedPowerRing.Hom pushoutObject B
  codiagonal_left : codiagonal.hom.comp left.hom = RingHom.id _
  codiagonal_right : codiagonal.hom.comp right.hom = RingHom.id _
  universal : ∀ (C : DividedPowerRing.{u})
    (g h : DividedPowerRing.Hom B C),
    g.hom.comp base.hom = h.hom.comp base.hom →
      ∃! k : DividedPowerRing.Hom pushoutObject C,
        k.hom.comp left.hom = g.hom ∧ k.hom.comp right.hom = h.hom

def diagonalKernel {A B : DividedPowerRing.{u}}
    {base : DividedPowerRing.Hom A B} (P : DividedPowerDiagonal A B base) :
    Ideal (P.pushoutObject : Type u) := RingHom.ker P.codiagonal.hom

noncomputable def diagonalRelationIdeal {A B : DividedPowerRing.{u}}
    {base : DividedPowerRing.Hom A B} (P : DividedPowerDiagonal A B base) :
    Ideal (P.pushoutObject : Type u) := by
  classical
  exact diagonalKernel P ^ 2 ⊔
    dividedPowerIdealPower
      (diagonalKernel P ⊓ P.pushoutObject.ideal)
      (DividedPowers.IsSubDPIdeal.dividedPowers
        P.pushoutObject.dividedPowers
        (kernel_inf_isSubDPIdeal P.codiagonal)) 2

instance diagonalKernelModule {A B : DividedPowerRing.{u}}
    {base : DividedPowerRing.Hom A B} (P : DividedPowerDiagonal A B base) :
    Module (B : Type u) (diagonalKernel P : Type u) :=
  Module.compHom (diagonalKernel P : Type u) P.left.hom

def diagonalRelationSubmodule {A B : DividedPowerRing.{u}}
    {base : DividedPowerRing.Hom A B} (P : DividedPowerDiagonal A B base) :
    Submodule (B : Type u) (diagonalKernel P : Type u) :=
  Submodule.span (B : Type u) {x : diagonalKernel P |
    (x : P.pushoutObject) ∈ diagonalRelationIdeal P}

def diagonalDifferentialModule {A B : DividedPowerRing.{u}}
    {base : DividedPowerRing.Hom A B} (P : DividedPowerDiagonal A B base) :
    ModuleCat (B : Type u) :=
  ModuleCat.of (B : Type u)
    ((diagonalKernel P : Type u) ⧸ diagonalRelationSubmodule P)

def diagonalDpowSubideal {A B : DividedPowerRing.{u}}
    {base : DividedPowerRing.Hom A B} (P : DividedPowerDiagonal A B base) : Prop :=
  P.pushoutObject.dividedPowers.IsSubDPIdeal
    (diagonalKernel P ⊓ P.pushoutObject.ideal)

theorem diagonal_kernel_inf_isSubDPIdeal
    {A B : DividedPowerRing.{u}} {base : DividedPowerRing.Hom A B}
    (P : DividedPowerDiagonal A B base) : diagonalDpowSubideal P := by
  sorry

theorem diagonal_differential_iso
    {A B : DividedPowerRing.{u}} {base : DividedPowerRing.Hom A B}
    (P : DividedPowerDiagonal A B base) :
    Nonempty (dividedPowerOmega (A : Type u) B base.hom ≅
      diagonalDifferentialModule P) := by
  sorry

/-! ## The affine-site variant of the diagonal lemma -/

theorem affine_diagonal_differential_iso
    (S : AffineCrystallineSituation.{u}) (X : AffineThickening S)
    (P : DividedPowerDiagonal S.A X.B X.base) :
    Nonempty (dividedPowerOmega (S.A : Type u) X.B X.base.hom ≅
      diagonalDifferentialModule P) := by
  sorry

/-! ## Divided-power envelopes -/

theorem envelope_differentials_iso
    (A : DividedPowerRing.{u}) {B : Type u} [CommRing B]
    (f : (A : Type u) →+* B) (J : Ideal B)
    (hIJ : Ideal.map f A.ideal ≤ J)
    (E : DividedPowerEnvelope A f J hIJ) :
    Nonempty (dividedPowerOmega (A : Type u) E.D E.base.hom ≅
      baseChangeModuleCat B (E.D : Type u)
        (ordinaryDifferentialModuleCat (A : Type u) B f) E.toD) := by
  sorry

/-! ## Divided-power de Rham complexes -/

/-- The exterior-power terms attached to a quotient of ordinary Kähler
differentials. -/
abbrev dividedPowerForm (B : Type u) [CommRing B] (Ω : Type u)
    [AddCommGroup Ω] [Module B Ω] (i : ℕ) : Type u := exteriorPower B Ω i

structure DividedPowerDeRhamData (A : Type u) [CommRing A]
    (B : DividedPowerRing.{u}) (f : A →+* (B : Type u)) where
  omega : ModuleCat (B : Type u)
  quotient : ordinaryDifferentialModule A (B : Type u) f →ₗ[B] omega
  quotient_condition : Nonempty (omega ≅ dividedPowerOrdinaryQuotientModule A B f)
  differential : ∀ i : ℕ,
    dividedPowerForm (B : Type u) (omega : Type u) i →+
      dividedPowerForm (B : Type u) (omega : Type u) (i + 1)
  differential_zero : Prop
  square_zero : ∀ i : ℕ,
    (differential (i + 1)).comp (differential i) = 0

theorem exists_dividedPowerDeRhamData
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) :
    Nonempty (DividedPowerDeRhamData A B f) := by
  sorry

/-! ## Connections -/

/-- A quotient of ordinary differentials satisfying the condition needed to
define the de Rham differential. -/
structure DifferentialQuotient (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] where
  omega : ModuleCat.{u, u} B
  quotient : ModuleOfDifferentials A B →ₗ[B] omega
  deRham_condition : Prop
  formDifferential : ∀ i : ℕ,
    dividedPowerForm B (omega : Type u) i →+
      dividedPowerForm B (omega : Type u) (i + 1)
  form_square_zero : ∀ i : ℕ,
    (formDifferential (i + 1)).comp (formDifferential i) = 0

/-- A connection on a `B`-module with values in a differential quotient. -/
structure Connection (A B M : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module B M]
    (Ω : DifferentialQuotient A B) where
  map : M →+ (M ⊗[B] (Ω.omega : Type u))
  leibniz : ∀ b m,
      map (b • m) = b • map m + (m ⊗ₜ[B] Ω.quotient
      (universalDifferential A B b))

def connectionIsIntegrable {A B M : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module B M]
    (Ω : DifferentialQuotient A B) (conn : Connection A B M Ω) : Prop :=
  ∃ d₂ : M ⊗[B] (Ω.omega : Type u) →+
      (M ⊗[B] dividedPowerForm B (Ω.omega : Type u) 2),
    d₂.comp conn.map = 0

structure ConnectionDeRhamExtension
    {A B M : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module B M]
    {Ω : DifferentialQuotient A B} (conn : Connection A B M Ω) where
  first : M →+ (M ⊗[B] (Ω.omega : Type u))
  first_eq : first = conn.map
  differential_one :
    (M ⊗[B] (Ω.omega : Type u)) →+
      (M ⊗[B] dividedPowerForm B (Ω.omega : Type u) 2)
  differential_higher : ∀ i : ℕ,
    (M ⊗[B] dividedPowerForm B (Ω.omega : Type u) (i + 2)) →+
      (M ⊗[B] dividedPowerForm B (Ω.omega : Type u) (i + 3))
  square_zero_one : differential_one.comp conn.map = 0
  square_zero_higher : ∀ i : ℕ,
    (differential_higher (i + 1)).comp (differential_higher i) = 0

theorem exists_connectionDeRhamExtension
    {A B M : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module B M]
    {Ω : DifferentialQuotient A B} (conn : Connection A B M Ω) :
    connectionIsIntegrable Ω conn → Nonempty (ConnectionDeRhamExtension conn) := by
  sorry

def connection_extension_statement
    {A B M : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module B M]
    (Ω : DifferentialQuotient A B) (conn : Connection A B M Ω) :
    Prop := connectionIsIntegrable Ω conn →
      Nonempty (ConnectionDeRhamExtension conn)

/-! ## Base change of connections -/

structure DifferentialBaseChangeData
    (A B A' B' : Type u) [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] where
  base : A →+* A'
  target : B →+* B'
  compatible : ∀ a, target (algebraMap A B a) = algebraMap A' B' (base a)
  sourceΩ : DifferentialQuotient A B
  targetΩ : DifferentialQuotient A' B'
  differentialsMap : sourceΩ.omega →+ targetΩ.omega

noncomputable def baseChangedConnectionModule
    {B B' M : Type u} [CommRing B] [CommRing B']
    [AddCommGroup M] [Module B M]
    (target : B →+* B') : ModuleCat.{u, u} B' :=
  baseChangeModuleCat B B' (ModuleCat.of B M) target

structure ConnectionBaseChangeWitness
    {A B A' B' M : Type u} [CommRing A] [CommRing B] [CommRing A']
    [CommRing B'] [AddCommGroup M] [Module B M]
    [Algebra A B] [Algebra A' B']
    (D : DifferentialBaseChangeData A B A' B')
    (conn : Connection A B M D.sourceΩ) where
  targetConnection :
    Connection A' B'
      (baseChangedConnectionModule D.target (M := M) : Type u) D.targetΩ
  integrability_preserved :
    connectionIsIntegrable D.sourceΩ conn →
      connectionIsIntegrable D.targetΩ targetConnection
  degree_zero_map :
    M →+ (baseChangedConnectionModule D.target (M := M) : Type u)
  positive_degree_map : ∀ i : ℕ,
    (M ⊗[B] dividedPowerForm B (D.sourceΩ.omega : Type u) (i + 1)) →+
      ((baseChangedConnectionModule D.target (M := M) : Type u) ⊗[B']
        dividedPowerForm B' (D.targetΩ.omega : Type u) (i + 1))
  map_complexes_condition : Prop

def connection_base_change_statement
    {A B A' B' M : Type u} [CommRing A] [CommRing B] [CommRing A']
    [CommRing B'] [AddCommGroup M] [Module B M]
    [Algebra A B] [Algebra A' B']
    (D : DifferentialBaseChangeData A B A' B')
    (conn : Connection A B M D.sourceΩ) : Prop :=
  Nonempty (ConnectionBaseChangeWitness D conn)

/-! ## Completion -/

structure ZLocalizedAlgebra (A : Type u) [CommRing A] (p : ℕ) where
  primeIdeal : Ideal ℤ
  primeIdeal_isPrime : primeIdeal.IsPrime
  primeIdeal_eq : primeIdeal = Ideal.span {(p : ℤ)}
  map : Localization.AtPrime primeIdeal →+* A

structure DifferentialCompletionSystem (A : Type u) [CommRing A]
    (B : DividedPowerRing.{u}) (f : A →+* (B : Type u)) (p : ℕ) where
  pPrime : Nat.Prime p
  zLocalized : ZLocalizedAlgebra A p
  p_nilpotent : IsNilpotent
    (Ideal.Quotient.mk B.ideal (p : (B : Type u)))

noncomputable def moduleQuotientByNat {R : Type u} [CommRing R]
    (M : ModuleCat.{u, u} R) (n : ℕ) : ModuleCat.{u, u} R := by
  letI : AddCommGroup (M : Type u) := M.isAddCommGroup
  letI : Module R (M : Type u) := M.isModule
  let L : Submodule R (M : Type u) :=
    Submodule.span R {x | ∃ y : (M : Type u), x = (n : R) • y}
  exact ModuleCat.of R ((M : Type u) ⧸ L)

structure DifferentialCompletionComparison
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) (p : ℕ)
    (h : DifferentialCompletionSystem A B f p) where
  e₀ : ℕ
  level : ∀ e, e₀ ≤ e → DividedPowerRing.{u}
  levelMap : ∀ (e : ℕ) (he : e₀ ≤ e),
    DividedPowerRing.Hom B (level e he)
  level_kernel : ∀ (e : ℕ) (he : e₀ ≤ e),
    RingHom.ker (levelMap e he).hom = Ideal.span {(p ^ e : B)}
  completed : DividedPowerRing.{u}
  completionMap : DividedPowerRing.Hom B completed
  finite_level_comparison : ∀ (e : ℕ) (he : e₀ ≤ e),
    Nonempty ((dividedPowerOmega A (level e he)
      ((levelMap e he).hom.comp f) : Type u) ≃+
      (moduleQuotientByNat (dividedPowerOmega A B f) (p ^ e) : Type u))
  completion_level_comparison : ∀ (e : ℕ) (he : e₀ ≤ e),
    Nonempty ((moduleQuotientByNat (dividedPowerOmega A B f) (p ^ e) : Type u) ≃+
      (moduleQuotientByNat
        (dividedPowerOmega A completed
          (completionMap.hom.comp f)) (p ^ e) : Type u))

def differentials_completion
    (A : Type u) [CommRing A] (B : DividedPowerRing.{u})
    (f : A →+* (B : Type u)) (p : ℕ)
    (h : DifferentialCompletionSystem A B f p) :
    Prop := Nonempty (DifferentialCompletionComparison A B f p h)

end
end Formalization.Books.Crystalline.Unit06
