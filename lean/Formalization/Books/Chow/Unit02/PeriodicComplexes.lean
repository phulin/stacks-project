import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Transfer
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

private def twoPeriodicShape : ComplexShape Bool where
  Rel i j := i ≠ j
  next_eq := by
    intro i j k hij hik
    cases i <;> cases j <;> cases k <;> simp_all
  prev_eq := by
    intro i j k hij hik
    cases i <;> cases j <;> cases k <;> simp_all

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

private def toHomologicalComplex (C : TwoPeriodicComplex R) :
    HomologicalComplex (ModuleCat.{v} R) twoPeriodicShape where
  X i := match i with
    | false => C.M
    | true => C.N
  d i j := match i, j with
    | false, true => C.phi
    | true, false => C.psi
    | _, _ => 0
  shape := by
    intro i j hij
    cases i <;> cases j <;> simp_all [twoPeriodicShape]
  d_comp_d' := by
    intro i j k hij hjk
    cases i <;> cases j <;> cases k <;>
      simp_all [twoPeriodicShape, TwoPeriodicComplex.phi_psi,
        TwoPeriodicComplex.psi_phi]

private def fromHomologicalComplex
    (K : HomologicalComplex (ModuleCat.{v} R) twoPeriodicShape) :
    TwoPeriodicComplex R where
  M := K.X false
  N := K.X true
  phi := K.d false true
  psi := K.d true false
  phi_psi := by simpa [twoPeriodicShape] using K.d_comp_d false true false
  psi_phi := by simpa [twoPeriodicShape] using K.d_comp_d true false true

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

private def toHomologicalComplexFunctor :
    TwoPeriodicComplex R ⥤ HomologicalComplex (ModuleCat.{v} R) twoPeriodicShape where
  obj := toHomologicalComplex
  map {C D} f :=
    { f i := match i with
        | false => f.f
        | true => f.g
      comm' := by
        intro i j hij
        cases i <;> cases j <;> simp [twoPeriodicShape, toHomologicalComplex,
          HomologicalComplex.Hom.comm, f.comm_phi, f.comm_psi] }
  map_id := by
    intro C
    ext i
    cases i <;> rfl
  map_comp := by
    intro C D E f g
    ext i
    cases i <;> rfl

private def fromHomologicalComplexFunctor :
    HomologicalComplex (ModuleCat.{v} R) twoPeriodicShape ⥤ TwoPeriodicComplex R where
  obj := fromHomologicalComplex
  map {C D} f :=
    { f := f.f false
      g := f.f true
      comm_phi := by simpa [fromHomologicalComplex] using f.comm false true
      comm_psi := by simpa [fromHomologicalComplex] using f.comm true false }
  map_id := by
    intro C
    apply Hom.ext <;> rfl
  map_comp := by
    intro C D E f g
    apply Hom.ext <;> rfl

private theorem from_to (C : TwoPeriodicComplex R) :
    fromHomologicalComplex (toHomologicalComplex C) = C := by
  rfl

private def to_from_iso
    (K : HomologicalComplex (ModuleCat.{v} R) twoPeriodicShape) :
    toHomologicalComplex (fromHomologicalComplex K) ≅ K where
  hom :=
    { f i := match i with
        | false => 𝟙 (K.X false)
        | true => 𝟙 (K.X true)
      comm' := by
        intro i j hij
        cases i <;> cases j <;>
          simp [toHomologicalComplex, fromHomologicalComplex, twoPeriodicShape] }
  inv :=
    { f i := match i with
        | false => 𝟙 (K.X false)
        | true => 𝟙 (K.X true)
      comm' := by
        intro i j hij
        cases i <;> cases j <;>
          simp [toHomologicalComplex, fromHomologicalComplex, twoPeriodicShape] }
  hom_inv_id := by
    ext i
    cases i <;> rfl
  inv_hom_id := by
    ext i
    cases i <;> rfl

private instance toHomologicalComplexFunctor_faithful :
    toHomologicalComplexFunctor (R := R) |>.Faithful where
  map_injective := by
    intro C D f g h
    apply Hom.ext
    · exact congrArg (fun k => k.f false) h
    · exact congrArg (fun k => k.f true) h

private instance toHomologicalComplexFunctor_full :
    toHomologicalComplexFunctor (R := R) |>.Full where
  map_surjective := by
    intro C D f
    refine ⟨{ f := f.f false
              g := f.f true
              comm_phi := by
                change f.f false ≫ D.phi = C.phi ≫ f.f true
                exact f.comm false true
              comm_psi := by
                change f.f true ≫ D.psi = C.psi ≫ f.f false
                exact f.comm true false }, ?_⟩
    ext i
    cases i <;> rfl

private instance toHomologicalComplexFunctor_essSurj :
    toHomologicalComplexFunctor (R := R) |>.EssSurj where
  mem_essImage K := ⟨fromHomologicalComplex K, ⟨to_from_iso K⟩⟩

/- The construction is the abelian category of representations of the
   two-vertex periodic quiver with the two displayed relations.  Mathlib's
   `Abelian` class is the reusable interface for its kernels and cokernels;
   the existence assertion is left for the proof stage. -/
noncomputable instance twoPeriodicComplexes_are_abelian :
    Abelian (TwoPeriodicComplex R) := by
  let F := toHomologicalComplexFunctor (R := R)
  let hF : Functor.FullyFaithful F := Functor.FullyFaithful.ofFullyFaithful F
  letI : Preadditive (TwoPeriodicComplex R) := Preadditive.ofFullyFaithful hF
  let _ : Functor.IsEquivalence F :=
    { faithful := by dsimp [F]; infer_instance
      full := by dsimp [F]; infer_instance
      essSurj := by dsimp [F]; infer_instance }
  let e := F.asEquivalence
  letI : HasFiniteProducts (TwoPeriodicComplex R) :=
    ⟨fun n => Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
  exact CategoryTheory.abelianOfEquivalence F

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

private theorem natCard_eq_residueField_pow_moduleLengthNat
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) :
    Nat.card M = Nat.card (IsLocalRing.ResidueField R) ^ moduleLengthNat R M hM := by
  induction hM with
  | of_subsingleton =>
      simp [moduleLengthNat, Module.length_eq_zero]
  | @of_simple_quotient M _ _ S _ _ hS =>
      obtain ⟨I, hI, ⟨e⟩⟩ :=
        isSimpleModule_iff_quot_maximal.mp
          (inferInstance : IsSimpleModule R (M ⧸ S))
      have hIeq : I = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hI
      have hquot : Nat.card (M ⧸ S) = Nat.card (IsLocalRing.ResidueField R) := by
        exact Nat.card_congr
          (e.trans (Submodule.quotEquivOfEq I (IsLocalRing.maximalIdeal R) hIeq)).toEquiv
      have hlen : Module.length R M = Module.length R S + 1 := by
        rw [Module.length_eq_add_of_exact S.subtype S.mkQ S.subtype_injective
          S.mkQ_surjective (LinearMap.exact_subtype_mkQ S)]
        rw [Module.length_eq_one (R := R) (M := M ⧸ S)]
      rw [Submodule.card_eq_card_quotient_mul_card S, hS, hquot]
      have hSfin : IsFiniteLength R S := by exact ‹IsFiniteLength R S›
      have hMfin : IsFiniteLength R M := IsFiniteLength.of_simple_quotient hSfin
      change Nat.card (IsLocalRing.ResidueField R) ^ moduleLengthNat R S hSfin *
        Nat.card (IsLocalRing.ResidueField R) =
        Nat.card (IsLocalRing.ResidueField R) ^ moduleLengthNat R M hMfin
      have hlenNat : moduleLengthNat R M hMfin = moduleLengthNat R S hSfin + 1 := by
        simp only [moduleLengthNat]
        rw [hlen, ENat.toNat_add (Module.length_ne_top_iff.mpr hSfin) (by simp)]
        simp only [ENat.toNat_one]
      rw [hlenNat]
      simp only [pow_succ]

private noncomputable def homologyZeroIso
    {R : Type u} [Ring R] (C : TwoPeriodicComplex R) :
    ((TwoPeriodicComplex.toHomologicalComplexFunctor (R := R)).obj C).homology false ≅
      ModuleCat.of R C.H0 :=
  by
    let K := (TwoPeriodicComplex.toHomologicalComplexFunctor (R := R)).obj C
    have hp : twoPeriodicShape.prev false = true :=
      twoPeriodicShape.prev_eq' (by simp [twoPeriodicShape])
    have hn : twoPeriodicShape.next false = true :=
      twoPeriodicShape.next_eq' (by simp [twoPeriodicShape])
    change (K.sc false).homology ≅ ModuleCat.of R C.H0
    exact ShortComplex.homologyMapIso (K.isoSc' true false true hp hn) ≪≫
      ((K.sc' true false true).moduleCatHomologyIso)

private noncomputable def homologyOneIso
    {R : Type u} [Ring R] (C : TwoPeriodicComplex R) :
    ((TwoPeriodicComplex.toHomologicalComplexFunctor (R := R)).obj C).homology true ≅
      ModuleCat.of R C.H1 :=
  by
    let K := (TwoPeriodicComplex.toHomologicalComplexFunctor (R := R)).obj C
    have hp : twoPeriodicShape.prev true = false :=
      twoPeriodicShape.prev_eq' (by simp [twoPeriodicShape])
    have hn : twoPeriodicShape.next true = false :=
      twoPeriodicShape.next_eq' (by simp [twoPeriodicShape])
    change (K.sc true).homology ≅ ModuleCat.of R C.H1
    exact ShortComplex.homologyMapIso (K.isoSc' false true false hp hn) ≪≫
      ((K.sc' false true false).moduleCatHomologyIso)

private theorem moduleLength_eq_range_add_range
    {R : Type u} [Ring R]
    {A B C : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hex : Function.Exact f g) :
    Module.length R B = Module.length R (LinearMap.range f) +
      Module.length R (LinearMap.range g) := by
  exact Module.length_eq_add_of_exact (LinearMap.range f).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict
    (Function.Exact.iff_linearMap_rangeRestrict.mp hex)

private theorem isFiniteLength_of_exact_middle
    {R : Type u} [Ring R]
    {A B C : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hex : Function.Exact f g)
    (hA : IsFiniteLength R A) (hC : IsFiniteLength R C) :
    IsFiniteLength R B := by
  have hrange : IsFiniteLength R (LinearMap.range f) :=
    IsFiniteLength.of_surjective hA f.surjective_rangeRestrict
  have hquot : IsFiniteLength R (B ⧸ LinearMap.range f) :=
    IsFiniteLength.of_injective hC (LinearMap.injective_range_liftQ_of_exact hex)
  rw [← Module.length_ne_top_iff]
  rw [Module.length_eq_add_of_exact (LinearMap.range f).subtype
    (Submodule.mkQ (LinearMap.range f)) (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)]
  simp [Module.length_ne_top_iff.mpr hrange, Module.length_ne_top_iff.mpr hquot]

theorem TwoOnePeriodicComplex.multiplicativeHerbrandQuotient_eq_residue_power
    {R : Type u} [CommRing R] [IsLocalRing R]
    (C : TwoOnePeriodicComplex R)
    [Finite C.H0] [Finite C.H1]
    [Finite (IsLocalRing.ResidueField R)]
    (q : ℕ)
    (hq : Nat.card (IsLocalRing.ResidueField R) = q)
    (hC : C.HasFiniteLengthCohomology) :
    C.multiplicativeHerbrandQuotient = (q : ℚ) ^ C.multiplicity hC := by
  have h0 := natCard_eq_residueField_pow_moduleLengthNat C.H0 hC.1
  have h1 := natCard_eq_residueField_pow_moduleLengthNat C.H1 hC.2
  have hqpos : 0 < q := by
    rw [← hq]
    exact Nat.card_pos
  have hq0 : (q : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hqpos)
  change (Nat.card C.H0 : ℚ) / (Nat.card C.H1 : ℚ) =
    (q : ℚ) ^ ((moduleLengthNat R C.H0 hC.1 : ℤ) -
      moduleLengthNat R C.H1 hC.2)
  rw [h0, h1, hq]
  simp only [Nat.cast_pow]
  rw [← zpow_natCast, ← zpow_natCast, (zpow_sub₀ hq0 _ _).symm]

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
  let F := TwoPeriodicComplex.toHomologicalComplexFunctor (R := R)
  letI : Functor.IsEquivalence F :=
    { faithful := by dsimp [F]; infer_instance
      full := by dsimp [F]; infer_instance
      essSurj := by dsimp [F]; infer_instance }
  let T := S.map F
  have hT : T.ShortExact := by
    dsimp [T]
    exact hS.map_of_exact F
  have hrel01 : twoPeriodicShape.Rel false true := by simp [twoPeriodicShape]
  have hrel10 : twoPeriodicShape.Rel true false := by simp [twoPeriodicShape]
  have hA := hT.homology_exact₁ true false hrel10
  have hB := hT.homology_exact₂ false
  have hC := hT.homology_exact₃ false true hrel01
  have hD := hT.homology_exact₁ false true hrel01
  have hE := hT.homology_exact₂ true
  have hF := hT.homology_exact₃ true false hrel10
  have finite0 (C : TwoPeriodicComplex R) (hC : IsFiniteLength R C.H0) :
      IsFiniteLength R ((F.obj C).homology false) := by
    simpa [F, TwoPeriodicComplex.toHomologicalComplexFunctor] using
      homologyZeroIso C |>.toLinearEquiv.symm.isFiniteLength hC
  have finite1 (C : TwoPeriodicComplex R) (hC : IsFiniteLength R C.H1) :
      IsFiniteLength R ((F.obj C).homology true) := by
    simpa [F, TwoPeriodicComplex.toHomologicalComplexFunctor] using
      homologyOneIso C |>.toLinearEquiv.symm.isFiniteLength hC
  have custom0 (C : TwoPeriodicComplex R)
      (hC : IsFiniteLength R ((F.obj C).homology false)) :
      IsFiniteLength R C.H0 := by
    apply (homologyZeroIso C).toLinearEquiv.isFiniteLength
    simpa [F, TwoPeriodicComplex.toHomologicalComplexFunctor] using hC
  have custom1 (C : TwoPeriodicComplex R)
      (hC : IsFiniteLength R ((F.obj C).homology true)) :
      IsFiniteLength R C.H1 := by
    apply (homologyOneIso C).toLinearEquiv.isFiniteLength
    simpa [F, TwoPeriodicComplex.toHomologicalComplexFunctor] using hC
  have hexA : Function.Exact (hT.δ true false hrel10).hom
      (HomologicalComplex.homologyMap T.f false).hom := by
    let Q := ShortComplex.mk (hT.δ true false hrel10)
      (HomologicalComplex.homologyMap T.f false) (by simp)
    have hQ := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact Q).mp
      (by simpa [Q] using hA)
    simpa [Q] using hQ
  have hexB : Function.Exact (HomologicalComplex.homologyMap T.f false).hom
      (HomologicalComplex.homologyMap T.g false).hom := by
    let Q := ShortComplex.mk (HomologicalComplex.homologyMap T.f false)
      (HomologicalComplex.homologyMap T.g false) (by
        rw [← HomologicalComplex.homologyMap_comp]
        simp)
    have hQ := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact Q).mp
      (by simpa [Q] using hB)
    simpa [Q] using hQ
  have hexC : Function.Exact (HomologicalComplex.homologyMap T.g false).hom
      (hT.δ false true hrel01).hom := by
    let Q := ShortComplex.mk (HomologicalComplex.homologyMap T.g false)
      (hT.δ false true hrel01) (by simp)
    have hQ := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact Q).mp
      (by simpa [Q] using hC)
    simpa [Q] using hQ
  have hexD : Function.Exact (hT.δ false true hrel01).hom
      (HomologicalComplex.homologyMap T.f true).hom := by
    let Q := ShortComplex.mk (hT.δ false true hrel01)
      (HomologicalComplex.homologyMap T.f true) (by simp)
    have hQ := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact Q).mp
      (by simpa [Q] using hD)
    simpa [Q] using hQ
  have hexE : Function.Exact (HomologicalComplex.homologyMap T.f true).hom
      (HomologicalComplex.homologyMap T.g true).hom := by
    let Q := ShortComplex.mk (HomologicalComplex.homologyMap T.f true)
      (HomologicalComplex.homologyMap T.g true) (by
        rw [← HomologicalComplex.homologyMap_comp]
        simp)
    have hQ := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact Q).mp
      (by simpa [Q] using hE)
    simpa [Q] using hQ
  have hexF : Function.Exact (HomologicalComplex.homologyMap T.g true).hom
      (hT.δ true false hrel10).hom := by
    let Q := ShortComplex.mk (HomologicalComplex.homologyMap T.g true)
      (hT.δ true false hrel10) (by simp)
    have hQ := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact Q).mp
      (by simpa [Q] using hF)
    simpa [Q] using hQ
  have length0 (C : TwoPeriodicComplex R) :
      Module.length R ((F.obj C).homology false) = Module.length R C.H0 := by
    simpa [F, TwoPeriodicComplex.toHomologicalComplexFunctor] using
      (homologyZeroIso C).toLinearEquiv.length_eq
  have length1 (C : TwoPeriodicComplex R) :
      Module.length R ((F.obj C).homology true) = Module.length R C.H1 := by
    simpa [F, TwoPeriodicComplex.toHomologicalComplexFunctor] using
      (homologyOneIso C).toLinearEquiv.length_eq
  have hlenA := moduleLength_eq_range_add_range
    (hT.δ true false hrel10).hom (HomologicalComplex.homologyMap T.f false).hom hexA
  have hlenB := moduleLength_eq_range_add_range
    (HomologicalComplex.homologyMap T.f false).hom
      (HomologicalComplex.homologyMap T.g false).hom hexB
  have hlenC := moduleLength_eq_range_add_range
    (HomologicalComplex.homologyMap T.g false).hom (hT.δ false true hrel01).hom hexC
  have hlenD := moduleLength_eq_range_add_range
    (hT.δ false true hrel01).hom (HomologicalComplex.homologyMap T.f true).hom hexD
  have hlenE := moduleLength_eq_range_add_range
    (HomologicalComplex.homologyMap T.f true).hom
      (HomologicalComplex.homologyMap T.g true).hom hexE
  have hlenF := moduleLength_eq_range_add_range
    (HomologicalComplex.homologyMap T.g true).hom (hT.δ true false hrel10).hom hexF
  have hEuler :
      Module.length R (T.X₂.homology false) +
          (Module.length R (T.X₁.homology true) + Module.length R (T.X₃.homology true)) =
        Module.length R (T.X₁.homology false) +
          (Module.length R (T.X₃.homology false) + Module.length R (T.X₂.homology true)) := by
    rw [hlenB, hlenD, hlenF, hlenA, hlenC, hlenE]
    ac_rfl
  have multiplicity_eq
      (h₁ : S.X₁.HasFiniteLengthCohomology)
      (h₂ : S.X₂.HasFiniteLengthCohomology)
      (h₃ : S.X₃.HasFiniteLengthCohomology) :
      S.X₂.multiplicity h₂ = S.X₁.multiplicity h₁ + S.X₃.multiplicity h₃ := by
    have hEuler' :
        Module.length R S.X₂.H0 +
            (Module.length R S.X₁.H1 + Module.length R S.X₃.H1) =
          Module.length R S.X₁.H0 +
            (Module.length R S.X₃.H0 + Module.length R S.X₂.H1) := by
      have e20 : Module.length R (T.X₂.homology false) = Module.length R S.X₂.H0 := by
        change Module.length R ((F.obj S.X₂).homology false) = Module.length R S.X₂.H0
        exact length0 S.X₂
      have e11 : Module.length R (T.X₁.homology true) = Module.length R S.X₁.H1 := by
        change Module.length R ((F.obj S.X₁).homology true) = Module.length R S.X₁.H1
        exact length1 S.X₁
      have e31 : Module.length R (T.X₃.homology true) = Module.length R S.X₃.H1 := by
        change Module.length R ((F.obj S.X₃).homology true) = Module.length R S.X₃.H1
        exact length1 S.X₃
      have e10 : Module.length R (T.X₁.homology false) = Module.length R S.X₁.H0 := by
        change Module.length R ((F.obj S.X₁).homology false) = Module.length R S.X₁.H0
        exact length0 S.X₁
      have e30 : Module.length R (T.X₃.homology false) = Module.length R S.X₃.H0 := by
        change Module.length R ((F.obj S.X₃).homology false) = Module.length R S.X₃.H0
        exact length0 S.X₃
      have e21 : Module.length R (T.X₂.homology true) = Module.length R S.X₂.H1 := by
        change Module.length R ((F.obj S.X₂).homology true) = Module.length R S.X₂.H1
        exact length1 S.X₂
      rw [e20, e11, e31, e10, e30, e21] at hEuler
      exact hEuler
    have hDF : Module.length R S.X₁.H1 + Module.length R S.X₃.H1 ≠ ⊤ := by
      simp [Module.length_ne_top_iff.mpr h₁.2,
        Module.length_ne_top_iff.mpr h₃.2]
    have hCE : Module.length R S.X₃.H0 + Module.length R S.X₂.H1 ≠ ⊤ := by
      simp [Module.length_ne_top_iff.mpr h₃.1,
        Module.length_ne_top_iff.mpr h₂.2]
    have hNat := congrArg ENat.toNat hEuler'
    rw [ENat.toNat_add (Module.length_ne_top_iff.mpr h₂.1) hDF,
      ENat.toNat_add (Module.length_ne_top_iff.mpr h₁.2)
        (Module.length_ne_top_iff.mpr h₃.2),
      ENat.toNat_add (Module.length_ne_top_iff.mpr h₁.1) hCE,
      ENat.toNat_add (Module.length_ne_top_iff.mpr h₃.1)
        (Module.length_ne_top_iff.mpr h₂.2)] at hNat
    change (moduleLengthNat R S.X₂.H0 h₂.1 : ℤ) -
        moduleLengthNat R S.X₂.H1 h₂.2 =
      ((moduleLengthNat R S.X₁.H0 h₁.1 : ℤ) -
          moduleLengthNat R S.X₁.H1 h₁.2) +
      ((moduleLengthNat R S.X₃.H0 h₃.1 : ℤ) -
          moduleLengthNat R S.X₃.H1 h₃.2)
    simp only [moduleLengthNat] at hNat ⊢
    omega
  rcases hfin with h12 | h13 | h23
  · rcases h12 with ⟨h1, h2⟩
    have h30T : IsFiniteLength R (T.X₃.homology false) := by
      apply isFiniteLength_of_exact_middle
        (HomologicalComplex.homologyMap T.g false).hom
        (hT.δ false true hrel01).hom hexC
      · change IsFiniteLength R ((F.obj S.X₂).homology false)
        exact finite0 S.X₂ h2.1
      · change IsFiniteLength R ((F.obj S.X₁).homology true)
        exact finite1 S.X₁ h1.2
    have h31T : IsFiniteLength R (T.X₃.homology true) := by
      apply isFiniteLength_of_exact_middle
        (HomologicalComplex.homologyMap T.g true).hom
        (hT.δ true false hrel10).hom hexF
      · change IsFiniteLength R ((F.obj S.X₂).homology true)
        exact finite1 S.X₂ h2.2
      · change IsFiniteLength R ((F.obj S.X₁).homology false)
        exact finite0 S.X₁ h1.1
    let h3 : S.X₃.HasFiniteLengthCohomology :=
      ⟨custom0 S.X₃ (by
          change IsFiniteLength R (T.X₃.homology false)
          exact h30T),
        custom1 S.X₃ (by
          change IsFiniteLength R (T.X₃.homology true)
          exact h31T)⟩
    exact ⟨h1, h2, h3, multiplicity_eq h1 h2 h3⟩
  · rcases h13 with ⟨h1, h3⟩
    have h20T : IsFiniteLength R (T.X₂.homology false) := by
      apply isFiniteLength_of_exact_middle
        (HomologicalComplex.homologyMap T.f false).hom
        (HomologicalComplex.homologyMap T.g false).hom hexB
      · change IsFiniteLength R ((F.obj S.X₁).homology false)
        exact finite0 S.X₁ h1.1
      · change IsFiniteLength R ((F.obj S.X₃).homology false)
        exact finite0 S.X₃ h3.1
    have h21T : IsFiniteLength R (T.X₂.homology true) := by
      apply isFiniteLength_of_exact_middle
        (HomologicalComplex.homologyMap T.f true).hom
        (HomologicalComplex.homologyMap T.g true).hom hexE
      · change IsFiniteLength R ((F.obj S.X₁).homology true)
        exact finite1 S.X₁ h1.2
      · change IsFiniteLength R ((F.obj S.X₃).homology true)
        exact finite1 S.X₃ h3.2
    let h2 : S.X₂.HasFiniteLengthCohomology :=
      ⟨custom0 S.X₂ (by
          change IsFiniteLength R (T.X₂.homology false)
          exact h20T),
        custom1 S.X₂ (by
          change IsFiniteLength R (T.X₂.homology true)
          exact h21T)⟩
    exact ⟨h1, h2, h3, multiplicity_eq h1 h2 h3⟩
  · rcases h23 with ⟨h2, h3⟩
    have h10T : IsFiniteLength R (T.X₁.homology false) := by
      apply isFiniteLength_of_exact_middle
        (hT.δ true false hrel10).hom
        (HomologicalComplex.homologyMap T.f false).hom hexA
      · change IsFiniteLength R ((F.obj S.X₃).homology true)
        exact finite1 S.X₃ h3.2
      · change IsFiniteLength R ((F.obj S.X₂).homology false)
        exact finite0 S.X₂ h2.1
    have h11T : IsFiniteLength R (T.X₁.homology true) := by
      apply isFiniteLength_of_exact_middle
        (hT.δ false true hrel01).hom
        (HomologicalComplex.homologyMap T.f true).hom hexD
      · change IsFiniteLength R ((F.obj S.X₃).homology false)
        exact finite0 S.X₃ h3.1
      · change IsFiniteLength R ((F.obj S.X₂).homology true)
        exact finite1 S.X₂ h2.2
    let h1 : S.X₁.HasFiniteLengthCohomology :=
      ⟨custom0 S.X₁ (by
          change IsFiniteLength R (T.X₁.homology false)
          exact h10T),
        custom1 S.X₁ (by
          change IsFiniteLength R (T.X₁.homology true)
          exact h11T)⟩
    exact ⟨h1, h2, h3, multiplicity_eq h1 h2 h3⟩

theorem TwoPeriodicComplex.hasFiniteLengthCohomology_of_finite_terms
    {R : Type u} [Ring R]
    (C : TwoPeriodicComplex R)
    (hM : IsFiniteLength R C.M)
    (hN : IsFiniteLength R C.N) :
    C.HasFiniteLengthCohomology := by
  refine ⟨?_, ?_⟩
  · let hker : IsFiniteLength R (LinearMap.ker C.phi.hom) :=
      IsFiniteLength.of_injective hM (Submodule.subtype_injective _)
    exact IsFiniteLength.of_surjective hker
      (Submodule.mkQ_surjective (LinearMap.range C.psiIntoKer))
  · let hker : IsFiniteLength R (LinearMap.ker C.psi.hom) :=
      IsFiniteLength.of_injective hN (Submodule.subtype_injective _)
    exact IsFiniteLength.of_surjective hker
      (Submodule.mkQ_surjective (LinearMap.range C.phiIntoKer))

theorem TwoPeriodicComplex.multiplicity_eq_moduleLength_sub
    {R : Type u} [Ring R]
    (C : TwoPeriodicComplex R)
    (hM : IsFiniteLength R C.M)
    (hN : IsFiniteLength R C.N) :
    C.multiplicity (C.hasFiniteLengthCohomology_of_finite_terms hM hN) =
      (moduleLengthNat R C.M hM : ℤ) - moduleLengthNat R C.N hN := by
  let hC := C.hasFiniteLengthCohomology_of_finite_terms hM hN
  have hkerφ : IsFiniteLength R (LinearMap.ker C.phi.hom) :=
    IsFiniteLength.of_injective hM (Submodule.subtype_injective _)
  have hkerψ : IsFiniteLength R (LinearMap.ker C.psi.hom) :=
    IsFiniteLength.of_injective hN (Submodule.subtype_injective _)
  have hrangeφ : IsFiniteLength R (LinearMap.range C.phi.hom) :=
    IsFiniteLength.of_surjective hM C.phi.hom.surjective_rangeRestrict
  have hrangeψ : IsFiniteLength R (LinearMap.range C.psi.hom) :=
    IsFiniteLength.of_surjective hN C.psi.hom.surjective_rangeRestrict
  have hMlen : Module.length R C.M =
      Module.length R (LinearMap.ker C.phi.hom) +
        Module.length R (LinearMap.range C.phi.hom) := by
    exact Module.length_eq_add_of_exact
      (LinearMap.ker C.phi.hom).subtype C.phi.hom.rangeRestrict
      (Submodule.subtype_injective _) C.phi.hom.surjective_rangeRestrict (by
        rw [LinearMap.exact_iff]
        simp)
  have hNlen : Module.length R C.N =
      Module.length R (LinearMap.ker C.psi.hom) +
        Module.length R (LinearMap.range C.psi.hom) := by
    exact Module.length_eq_add_of_exact
      (LinearMap.ker C.psi.hom).subtype C.psi.hom.rangeRestrict
      (Submodule.subtype_injective _) C.psi.hom.surjective_rangeRestrict (by
        rw [LinearMap.exact_iff]
        simp)
  have hH0len : Module.length R (LinearMap.ker C.phi.hom) =
      Module.length R (LinearMap.range C.psiIntoKer) +
        Module.length R C.H0 := by
    exact Module.length_eq_add_of_exact
      (LinearMap.range C.psiIntoKer).subtype
      (Submodule.mkQ (LinearMap.range C.psiIntoKer))
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ _)
  have hH1len : Module.length R (LinearMap.ker C.psi.hom) =
      Module.length R (LinearMap.range C.phiIntoKer) +
        Module.length R C.H1 := by
    exact Module.length_eq_add_of_exact
      (LinearMap.range C.phiIntoKer).subtype
      (Submodule.mkQ (LinearMap.range C.phiIntoKer))
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ _)
  have hrangeψ' : IsFiniteLength R (LinearMap.range C.psiIntoKer) :=
    IsFiniteLength.of_surjective hN C.psiIntoKer.surjective_rangeRestrict
  have hrangeφ' : IsFiniteLength R (LinearMap.range C.phiIntoKer) :=
    IsFiniteLength.of_surjective hM C.phiIntoKer.surjective_rangeRestrict
  have hlenψ :
      Module.length R (LinearMap.range C.psiIntoKer) =
        Module.length R (LinearMap.range C.psi.hom) := by
    rw [show LinearMap.range C.psiIntoKer =
        Submodule.comap (LinearMap.ker C.phi.hom).subtype
          (LinearMap.range C.psi.hom) by
      simpa [TwoPeriodicComplex.psiIntoKer] using
        (LinearMap.range_codRestrict (LinearMap.ker C.phi.hom)
          C.psi.hom (fun x => C.range_psi_le_ker_phi ⟨x, rfl⟩))]
    exact (Submodule.comapSubtypeEquivOfLe C.range_psi_le_ker_phi).length_eq
  have hlenφ :
      Module.length R (LinearMap.range C.phiIntoKer) =
        Module.length R (LinearMap.range C.phi.hom) := by
    rw [show LinearMap.range C.phiIntoKer =
        Submodule.comap (LinearMap.ker C.psi.hom).subtype
          (LinearMap.range C.phi.hom) by
      simpa [TwoPeriodicComplex.phiIntoKer] using
        (LinearMap.range_codRestrict (LinearMap.ker C.psi.hom)
          C.phi.hom (fun x => C.range_phi_le_ker_psi ⟨x, rfl⟩))]
    exact (Submodule.comapSubtypeEquivOfLe C.range_phi_le_ker_psi).length_eq
  have hMnat := congrArg ENat.toNat hMlen
  have hNnat := congrArg ENat.toNat hNlen
  have hH0nat := congrArg ENat.toNat hH0len
  have hH1nat := congrArg ENat.toNat hH1len
  rw [ENat.toNat_add (Module.length_ne_top_iff.mpr hkerφ)
      (Module.length_ne_top_iff.mpr hrangeφ)] at hMnat
  rw [ENat.toNat_add (Module.length_ne_top_iff.mpr hkerψ)
      (Module.length_ne_top_iff.mpr hrangeψ)] at hNnat
  rw [ENat.toNat_add (Module.length_ne_top_iff.mpr hrangeψ')
      (Module.length_ne_top_iff.mpr hC.1)] at hH0nat
  rw [ENat.toNat_add (Module.length_ne_top_iff.mpr hrangeφ')
      (Module.length_ne_top_iff.mpr hC.2)] at hH1nat
  have hlenψnat := congrArg ENat.toNat hlenψ
  have hlenφnat := congrArg ENat.toNat hlenφ
  change (moduleLengthNat R C.H0 hC.1 : ℤ) -
      moduleLengthNat R C.H1 hC.2 =
    (moduleLengthNat R C.M hM : ℤ) - moduleLengthNat R C.N hN
  simp only [moduleLengthNat] at hMnat hNnat hH0nat hH1nat ⊢
  omega

theorem TwoOnePeriodicComplex.multiplicity_eq_zero
    {R : Type u} [Ring R]
    (C : TwoOnePeriodicComplex R)
    (hM : IsFiniteLength R C.M) :
    C.multiplicity
        (C.toTwoPeriodic.hasFiniteLengthCohomology_of_finite_terms hM hM) = 0 := by
  change C.toTwoPeriodic.multiplicity
      (C.toTwoPeriodic.hasFiniteLengthCohomology_of_finite_terms hM hM) = 0
  simpa [TwoOnePeriodicComplex.toTwoPeriodic] using
    (TwoPeriodicComplex.multiplicity_eq_moduleLength_sub C.toTwoPeriodic hM hM)

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
  let C₀ := TwoOnePeriodicComplex.zeroFirst M psi
  let e₀ : (M : Type v) ≃ₗ[R] LinearMap.ker (0 : (M →ₗ[R] M)) :=
    { toFun := fun x => ⟨x, by simp⟩
      invFun := fun x => x
      left_inv := by intro x; rfl
      right_inv := by intro x; apply Subtype.ext; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have he₀_comp :
      (e₀ : M →ₗ[R] LinearMap.ker (0 : (M →ₗ[R] M))).comp psi.hom =
        C₀.toTwoPeriodic.psiIntoKer := by
    ext x
    rfl
  have he₀_range :
      (LinearMap.range psi.hom).map
          (e₀ : M →ₗ[R] LinearMap.ker (0 : (M →ₗ[R] M))) =
        LinearMap.range C₀.toTwoPeriodic.psiIntoKer := by
    rw [LinearMap.range_eq_map, ← Submodule.map_comp,
      ← LinearMap.range_eq_map, he₀_comp]
    rfl
  have hmap := Submodule.Quotient.equiv
    (LinearMap.range psi.hom)
    (LinearMap.range C₀.toTwoPeriodic.psiIntoKer)
    e₀ he₀_range
  have hzero : IsFiniteLength R C₀.toTwoPeriodic.H0 := by
    exact (hmap.isFiniteLength hcoker)
  have hphi_range :
      LinearMap.range C₀.toTwoPeriodic.phiIntoKer = ⊥ := by
    apply LinearMap.range_eq_bot.mpr
    ext x
    rfl
  have hker₀ : IsFiniteLength R (LinearMap.ker C₀.toTwoPeriodic.psi.hom) := by
    change IsFiniteLength R (LinearMap.ker psi.hom)
    exact hker
  have hone : IsFiniteLength R C₀.toTwoPeriodic.H1 := by
    change IsFiniteLength R
      ((LinearMap.ker C₀.toTwoPeriodic.psi.hom) ⧸
        LinearMap.range C₀.toTwoPeriodic.phiIntoKer)
    rw [hphi_range]
    exact (Submodule.quotEquivOfEqBot
      (⊥ : Submodule R (LinearMap.ker C₀.toTwoPeriodic.psi.hom)) rfl).symm.isFiniteLength hker₀
  change C₀.toTwoPeriodic.HasFiniteLengthCohomology
  exact ⟨hzero, hone⟩

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
  let C₀ := TwoOnePeriodicComplex.zeroFirst M psi
  let hC := TwoOnePeriodicComplex.zeroFirst_hasFiniteLengthCohomology_of_finite_kernel_cokernel
    M psi hker hcoker
  let e₀ : (M : Type v) ≃ₗ[R] LinearMap.ker (0 : (M →ₗ[R] M)) :=
    { toFun := fun x => ⟨x, by simp⟩
      invFun := fun x => x
      left_inv := by intro x; rfl
      right_inv := by intro x; apply Subtype.ext; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have he₀_comp :
      (e₀ : M →ₗ[R] LinearMap.ker (0 : (M →ₗ[R] M))).comp psi.hom =
        C₀.toTwoPeriodic.psiIntoKer := by
    ext x
    rfl
  have he₀_range :
      (LinearMap.range psi.hom).map
          (e₀ : M →ₗ[R] LinearMap.ker (0 : (M →ₗ[R] M))) =
        LinearMap.range C₀.toTwoPeriodic.psiIntoKer := by
    rw [LinearMap.range_eq_map, ← Submodule.map_comp,
      ← LinearMap.range_eq_map, he₀_comp]
    rfl
  have hmap := Submodule.Quotient.equiv
    (LinearMap.range psi.hom)
    (LinearMap.range C₀.toTwoPeriodic.psiIntoKer)
    e₀ he₀_range
  have hphi_range :
      LinearMap.range C₀.toTwoPeriodic.phiIntoKer = ⊥ := by
    apply LinearMap.range_eq_bot.mpr
    ext x
    rfl
  have hlen₀ : Module.length R (moduleCokernel psi) =
      Module.length R C₀.toTwoPeriodic.H0 := by
    exact hmap.length_eq
  have hlen₁ : Module.length R C₀.toTwoPeriodic.H1 =
      Module.length R (moduleKernel psi) := by
    change Module.length R
        ((LinearMap.ker C₀.toTwoPeriodic.psi.hom) ⧸
          LinearMap.range C₀.toTwoPeriodic.phiIntoKer) =
      Module.length R (LinearMap.ker psi.hom)
    rw [hphi_range]
    exact (Submodule.quotEquivOfEqBot
      (⊥ : Submodule R (LinearMap.ker C₀.toTwoPeriodic.psi.hom)) rfl).length_eq
  have hnat₀ := congrArg ENat.toNat hlen₀
  have hnat₁ := congrArg ENat.toNat hlen₁
  change (moduleLengthNat R C₀.toTwoPeriodic.H0 hC.1 : ℤ) -
      moduleLengthNat R C₀.toTwoPeriodic.H1 hC.2 =
    (moduleLengthNat R (moduleCokernel psi) hcoker : ℤ) -
      moduleLengthNat R (moduleKernel psi) hker
  simp only [moduleLengthNat] at hnat₀ hnat₁ ⊢
  omega

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
