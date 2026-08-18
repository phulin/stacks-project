import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Field.Rat
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Chow Homology and Chern Classes, Chapter 2: Periodic complexes and Herbrand quotients

The source section works with modules over a ring.  Bundled `ModuleCat` objects
give the varying modules in a complex a single Lean type, while the underlying
linear maps and submodule quotients give the source's concrete cohomology
modules.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace Formalization.Books.Chow.Unit02

/-! ## Two-periodic complexes -/

/-- A two-periodic complex of `R`-modules.

The two fields `phi_psi` and `psi_phi` record the two consecutive-zero
compositions in the bi-infinite periodic complex.
-/
structure TwoPeriodicComplex (R : Type u) [Ring R] where
  M : ModuleCat.{v} R
  N : ModuleCat.{v} R
  phi : M ⟶ N
  psi : N ⟶ M
  phi_psi : phi ≫ psi = 0
  psi_phi : psi ≫ phi = 0

namespace TwoPeriodicComplex

variable {R : Type u} [Ring R]

/- The source's image submodules are maps into the corresponding kernels.
   These codomain restrictions make the quotient presentation of cohomology
   literal rather than merely isomorphic to it. -/

theorem range_psi_le_ker_phi (C : TwoPeriodicComplex R) :
    LinearMap.range C.psi.hom ≤ LinearMap.ker C.phi.hom := by
  rw [LinearMap.range_le_ker_iff]
  exact ModuleCat.hom_ext_iff.mp C.psi_phi

theorem range_phi_le_ker_psi (C : TwoPeriodicComplex R) :
    LinearMap.range C.phi.hom ≤ LinearMap.ker C.psi.hom := by
  rw [LinearMap.range_le_ker_iff]
  exact ModuleCat.hom_ext_iff.mp C.phi_psi

/-- The map `psi` viewed as a map into `ker phi`. -/
def psiIntoKer (C : TwoPeriodicComplex R) :
    C.N →ₗ[R] LinearMap.ker C.phi.hom :=
  C.psi.hom.codRestrict _ fun x => C.range_psi_le_ker_phi ⟨x, rfl⟩

/-- The map `phi` viewed as a map into `ker psi`. -/
def phiIntoKer (C : TwoPeriodicComplex R) :
    C.M →ₗ[R] LinearMap.ker C.psi.hom :=
  C.phi.hom.codRestrict _ fun x => C.range_phi_le_ker_psi ⟨x, rfl⟩

/-- The degree-zero cohomology module `ker(phi) / im(psi)`. -/
abbrev H0 (C : TwoPeriodicComplex R) :=
  LinearMap.ker C.phi.hom ⧸ LinearMap.range C.psiIntoKer

/-- The degree-one cohomology module `ker(psi) / im(phi)`. -/
abbrev H1 (C : TwoPeriodicComplex R) :=
  LinearMap.ker C.psi.hom ⧸ LinearMap.range C.phiIntoKer

/-- Exactness means that both periodic cohomology modules are zero. -/
def Exact (C : TwoPeriodicComplex R) : Prop :=
  Subsingleton C.H0 ∧ Subsingleton C.H1

/-! ## Morphisms and the abelian category -/

/-- A morphism of two-periodic complexes is a commuting pair of module maps. -/
@[ext]
structure Hom (C D : TwoPeriodicComplex R) where
  f : C.M ⟶ D.M
  g : C.N ⟶ D.N
  comm_phi : f ≫ D.phi = C.phi ≫ g
  comm_psi : g ≫ D.psi = C.psi ≫ f

instance : Category (TwoPeriodicComplex R) where
  Hom := Hom
  id C :=
    { f := 𝟙 C.M
      g := 𝟙 C.N
      comm_phi := by simp
      comm_psi := by simp }
  comp f g :=
    { f := f.f ≫ g.f
      g := f.g ≫ g.g
      comm_phi := by
        simp only [Category.assoc]
        rw [g.comm_phi, ← Category.assoc, f.comm_phi]
        simp only [Category.assoc]
      comm_psi := by
        simp only [Category.assoc]
        rw [g.comm_psi, ← Category.assoc, f.comm_psi]
        simp only [Category.assoc] }
  id_comp := by
    intro C D f
    ext <;> simp
  comp_id := by
    intro C D f
    ext <;> simp
  assoc := by
    intro A B C D f g h
    ext <;> simp [Category.assoc]

/-- Zero morphisms are given componentwise. -/
instance {C D : TwoPeriodicComplex R} : Zero (C ⟶ D) where
  zero :=
    { f := 0
      g := 0
      comm_phi := by simp
      comm_psi := by simp }

instance : HasZeroMorphisms (TwoPeriodicComplex R) where
  comp_zero := by
    intro C D f E
    apply Hom.ext
    · change f.f ≫ 0 = 0
      simp
    · change f.g ≫ 0 = 0
      simp
  zero_comp := by
    intro C D E f
    apply Hom.ext
    · change 0 ≫ f.f = 0
      simp
    · change 0 ≫ f.g = 0
      simp

/- The construction is the abelian category of representations of the
   two-vertex periodic quiver with the two displayed relations.  Mathlib's
   `Abelian` class is the reusable interface for its kernels and cokernels;
   the existence assertion is left for the proof stage. -/
noncomputable instance twoPeriodicComplexes_are_abelian :
    Abelian (TwoPeriodicComplex R) := by
  sorry

end TwoPeriodicComplex

/-! ## `(2, 1)`-periodic complexes -/

/-- A `(2, 1)`-periodic complex, with both terms equal to `M`. -/
structure TwoOnePeriodicComplex (R : Type u) [Ring R] where
  M : ModuleCat.{v} R
  phi : M ⟶ M
  psi : M ⟶ M
  phi_psi : phi ≫ psi = 0
  psi_phi : psi ≫ phi = 0

namespace TwoOnePeriodicComplex

variable {R : Type u} [Ring R]

/-- The `(2, 1)`-periodic complex regarded as a two-periodic complex. -/
def toTwoPeriodic (C : TwoOnePeriodicComplex R) : TwoPeriodicComplex R where
  M := C.M
  N := C.M
  phi := C.phi
  psi := C.psi
  phi_psi := C.phi_psi
  psi_phi := C.psi_phi

abbrev H0 (C : TwoOnePeriodicComplex R) := C.toTwoPeriodic.H0

abbrev H1 (C : TwoOnePeriodicComplex R) := C.toTwoPeriodic.H1

abbrev Exact (C : TwoOnePeriodicComplex R) : Prop := C.toTwoPeriodic.Exact

/-- A morphism of `(2, 1)`-periodic complexes. -/
@[ext]
structure Hom (C D : TwoOnePeriodicComplex R) where
  f : C.M ⟶ D.M
  comm_phi : f ≫ D.phi = C.phi ≫ f
  comm_psi : f ≫ D.psi = C.psi ≫ f

/- The underlying module kernel and cokernel are the canonical concrete
   representatives of the categorical kernel and cokernel in `ModuleCat`. -/
abbrev moduleKernel {M N : ModuleCat.{v} R} (f : M ⟶ N) :=
  LinearMap.ker f.hom

abbrev moduleCokernel {M N : ModuleCat.{v} R} (f : M ⟶ N) :=
  N ⧸ LinearMap.range f.hom

def Hom.FiniteLengthKernelAndCokernel
    {C D : TwoOnePeriodicComplex R} (f : Hom C D) : Prop :=
  IsFiniteLength R (moduleKernel f.f) ∧
    IsFiniteLength R (moduleCokernel f.f)

end TwoOnePeriodicComplex

/-! ## Lengths and Herbrand quotients -/

/-- The natural-number value of the canonical module length.

The finite-length proof is an explicit argument so this helper is only used on
the domain where the source's integer-valued length is defined.
-/
noncomputable def moduleLengthNat (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M] (_hM : IsFiniteLength R M) : ℕ :=
  (Module.length R M).toNat

def TwoPeriodicComplex.HasFiniteLengthCohomology
    {R : Type u} [Ring R] (C : TwoPeriodicComplex R) : Prop :=
  IsFiniteLength R C.H0 ∧ IsFiniteLength R C.H1

/-- The additive Herbrand quotient, i.e. the difference of the two lengths. -/
def TwoPeriodicComplex.multiplicity
    {R : Type u} [Ring R] (C : TwoPeriodicComplex R)
    (hC : C.HasFiniteLengthCohomology) : ℤ :=
  (moduleLengthNat R C.H0 hC.1 : ℤ) - moduleLengthNat R C.H1 hC.2

abbrev TwoOnePeriodicComplex.HasFiniteLengthCohomology
    {R : Type u} [Ring R] (C : TwoOnePeriodicComplex R) : Prop :=
  C.toTwoPeriodic.HasFiniteLengthCohomology

abbrev TwoOnePeriodicComplex.multiplicity
    {R : Type u} [Ring R] (C : TwoOnePeriodicComplex R)
    (hC : C.HasFiniteLengthCohomology) : ℤ :=
  C.toTwoPeriodic.multiplicity hC

/-! ## Multiplicative Herbrand quotients -/

/-- The multiplicative Herbrand quotient of a `(2, 1)`-periodic complex. -/
noncomputable def TwoOnePeriodicComplex.multiplicativeHerbrandQuotient
    {R : Type u} [Ring R] (C : TwoOnePeriodicComplex R)
    [Finite C.H0] [Finite C.H1] : ℚ :=
  (Nat.card C.H0 : ℚ) / Nat.card C.H1

theorem TwoOnePeriodicComplex.multiplicativeHerbrandQuotient_eq_residue_power
    {R : Type u} [CommRing R] [IsLocalRing R]
    (C : TwoOnePeriodicComplex R)
    [Finite C.H0] [Finite C.H1]
    [Finite (IsLocalRing.ResidueField R)]
    (q : ℕ)
    (hq : Nat.card (IsLocalRing.ResidueField R) = q)
    (hC : C.HasFiniteLengthCohomology) :
    C.multiplicativeHerbrandQuotient = (q : ℚ) ^ C.multiplicity hC := by
  sorry

/-! ## Basic multiplicity statements -/

/-- Two out of three finite-length cohomology conditions for a short exact
sequence of two-periodic complexes. -/
def TwoPeriodicComplex.TwoOfThreeFiniteLength
    {R : Type u} [Ring R]
    (S : ShortComplex (TwoPeriodicComplex R)) : Prop :=
  (S.X₁.HasFiniteLengthCohomology ∧ S.X₂.HasFiniteLengthCohomology) ∨
    (S.X₁.HasFiniteLengthCohomology ∧ S.X₃.HasFiniteLengthCohomology) ∨
    (S.X₂.HasFiniteLengthCohomology ∧ S.X₃.HasFiniteLengthCohomology)

theorem TwoPeriodicComplex.multiplicity_additive
    {R : Type u} [Ring R]
    (S : ShortComplex (TwoPeriodicComplex R))
    (hS : S.ShortExact)
    (hfin : TwoPeriodicComplex.TwoOfThreeFiniteLength S) :
    ∃ h₁ : S.X₁.HasFiniteLengthCohomology,
      ∃ h₂ : S.X₂.HasFiniteLengthCohomology,
        ∃ h₃ : S.X₃.HasFiniteLengthCohomology,
          S.X₂.multiplicity h₂ = S.X₁.multiplicity h₁ + S.X₃.multiplicity h₃ := by
  sorry

theorem TwoPeriodicComplex.hasFiniteLengthCohomology_of_finite_terms
    {R : Type u} [Ring R]
    (C : TwoPeriodicComplex R)
    (hM : IsFiniteLength R C.M)
    (hN : IsFiniteLength R C.N) :
    C.HasFiniteLengthCohomology := by
  sorry

theorem TwoPeriodicComplex.multiplicity_eq_moduleLength_sub
    {R : Type u} [Ring R]
    (C : TwoPeriodicComplex R)
    (hM : IsFiniteLength R C.M)
    (hN : IsFiniteLength R C.N) :
    C.multiplicity (C.hasFiniteLengthCohomology_of_finite_terms hM hN) =
      (moduleLengthNat R C.M hM : ℤ) - moduleLengthNat R C.N hN := by
  sorry

theorem TwoOnePeriodicComplex.multiplicity_eq_zero
    {R : Type u} [Ring R]
    (C : TwoOnePeriodicComplex R)
    (hM : IsFiniteLength R C.M) :
    C.multiplicity
        (C.toTwoPeriodic.hasFiniteLengthCohomology_of_finite_terms hM hM) = 0 := by
  sorry

/-- The example `(M, 0, psi)` from the source. -/
def TwoOnePeriodicComplex.zeroFirst
    {R : Type u} [Ring R] (M : ModuleCat.{v} R) (psi : M ⟶ M) :
    TwoOnePeriodicComplex R where
  M := M
  phi := 0
  psi := psi
  phi_psi := by simp
  psi_phi := by simp

theorem TwoOnePeriodicComplex.zeroFirst_hasFiniteLengthCohomology_of_finite_kernel_cokernel
    {R : Type u} [Ring R]
    (M : ModuleCat.{v} R) (psi : M ⟶ M)
    (hker : IsFiniteLength R (moduleKernel psi))
    (hcoker : IsFiniteLength R (moduleCokernel psi)) :
    (TwoOnePeriodicComplex.zeroFirst M psi).HasFiniteLengthCohomology := by
  sorry

theorem TwoOnePeriodicComplex.zeroFirst_multiplicity_eq_cokernel_sub_kernel
    {R : Type u} [Ring R]
    (M : ModuleCat.{v} R) (psi : M ⟶ M)
    (hker : IsFiniteLength R (moduleKernel psi))
    (hcoker : IsFiniteLength R (moduleCokernel psi)) :
    (TwoOnePeriodicComplex.zeroFirst M psi).multiplicity
        (TwoOnePeriodicComplex.zeroFirst_hasFiniteLengthCohomology_of_finite_kernel_cokernel
          M psi hker hcoker) =
      (moduleLengthNat R (moduleCokernel psi) hcoker : ℤ) -
        moduleLengthNat R (moduleKernel psi) hker := by
  sorry

theorem TwoOnePeriodicComplex.multiplicity_invariant_under_finite_kernel_cokernel
    {R : Type u} [Ring R]
    (C D : TwoOnePeriodicComplex R)
    (f : TwoOnePeriodicComplex.Hom C D)
    (hC : C.HasFiniteLengthCohomology)
    (hD : D.HasFiniteLengthCohomology)
    (hf : f.FiniteLengthKernelAndCokernel) :
    C.multiplicity hC = D.multiplicity hD := by
  sorry

end Formalization.Books.Chow.Unit02
