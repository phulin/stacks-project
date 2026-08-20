import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Formalization.Books.MoreAlgebra.Unit112

/-!
This file formalizes the declarations in More on Algebra, Chapter 113.

The repeated hypotheses in the source are packaged in `GaloisDVRContext`.
Its action fields are the Lean interface for the canonical action of the
finite Galois group on the integral closure, its maximal ideal, the residue
field, the cotangent space, and the associated graded ring.  The chapter's
proofs are intentionally deferred.
-/

namespace Formalization.Books.MoreAlgebra.Unit113

noncomputable section

universe u v w z

variable {A K L B κ κB Gr V W : Type*}
variable [CommRing A] [Field K] [Field L] [CommRing B]
variable [Field κ] [Field κB] [CommRing Gr] [AddCommGroup V] [AddCommGroup W]
variable [Algebra A K] [Algebra A L] [Algebra K L]
variable [Algebra A B] [Algebra B L] [Algebra κ κB]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [FiniteDimensional K L] [IsGalois K L]

/-! ## The common finite Galois DVR context -/

structure GaloisDVRContext
    (A K L B κ κB Gr V W : Type*)
    [CommRing A] [Field K] [Field L] [CommRing B]
    [Field κ] [Field κB] [CommRing Gr] [AddCommGroup V] [AddCommGroup W]
    [Algebra A K] [Algebra A L] [Algebra K L]
    [Algebra A B] [Algebra B L] [Algebra κ κB]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L] where
  fractionField : IsFractionRing A K
  integralClosure : IsIntegralClosure A B L
  maximalIdeal : Ideal B
  maximalIdeal_isMaximal : maximalIdeal.IsMaximal
  idealAction : Gal(L / K) → Ideal B → Ideal B
  idealAction_one : idealAction 1 = id
  idealAction_mul : ∀ σ τ J, idealAction (σ * τ) J = idealAction σ (idealAction τ J)
  decomposition : Subgroup (Gal(L / K))
  decomposition_spec : ∀ σ,
    σ ∈ decomposition ↔ idealAction σ maximalIdeal = maximalIdeal
  residueAction : decomposition →* (κB ≃ₐ[κ] κB)
  inertia : Subgroup (Gal(L / K))
  inertia_le_decomposition : inertia ≤ decomposition
  inertia_spec : ∀ σ : decomposition,
    (σ : Gal(L / K)) ∈ inertia ↔ residueAction σ = 1
  wildInertia : Subgroup (Gal(L / K))
  wildInertia_le_inertia : wildInertia ≤ inertia
  ramificationIndex : ℕ
  residualDegree : ℕ
  numberOfPlaces : ℕ
  placeRamificationIndex : Fin numberOfPlaces → ℕ
  placeResidualDegree : Fin numberOfPlaces → ℕ
  inertiaCharacter : inertia →* rootsOfUnity ramificationIndex κB
  wildInertia_spec : ∀ σ : inertia,
    (σ : Gal(L / K)) ∈ wildInertia ↔ inertiaCharacter σ = 1
  tameInertia : Type*
  tameInertia_group : Group tameInertia
  tameProjection : inertia →* tameInertia
  tameProjection_surjective : Function.Surjective tameProjection
  tameProjection_kernel : ∀ σ : inertia,
    tameProjection σ = 1 ↔
      ∃ τ : wildInertia, (⟨τ.1, wildInertia_le_inertia τ.2⟩ : inertia) = σ
  gradedAction : decomposition →* (Gr ≃+* Gr)
  cotangentAction : inertia → (V →+ V)
  firstOrderAction : decomposition → (W →+ W)

instance tameInertiaGroup.instGroup
    (X : GaloisDVRContext A K L B κ κB Gr V W) : Group X.tameInertia :=
  X.tameInertia_group

abbrev BaseResidueField (X : GaloisDVRContext A K L B κ κB Gr V W) := κ

abbrev ResidueFieldAt (X : GaloisDVRContext A K L B κ κB Gr V W) := κB

def decompositionGroup
    (X : GaloisDVRContext A K L B κ κB Gr V W) : Subgroup (Gal(L / K)) :=
  X.decomposition

def inertiaGroup
    (X : GaloisDVRContext A K L B κ κB Gr V W) : Subgroup (Gal(L / K)) :=
  X.inertia

def wildInertiaGroup
    (X : GaloisDVRContext A K L B κ κB Gr V W) : Subgroup (Gal(L / K)) :=
  X.wildInertia

def tameInertiaGroup
    (X : GaloisDVRContext A K L B κ κB Gr V W) : Type _ :=
  X.tameInertia

instance tameInertiaGroup.instGroup_def
    (X : GaloisDVRContext A K L B κ κB Gr V W) : Group (tameInertiaGroup X) :=
  X.tameInertia_group

def inertiaCharacter
    (X : GaloisDVRContext A K L B κ κB Gr V W) :
    X.inertia →* rootsOfUnity X.ramificationIndex κB :=
  X.inertiaCharacter

def IsTrivialOnGraded (X : GaloisDVRContext A K L B κ κB Gr V W)
    (σ : X.decomposition) : Prop := X.gradedAction σ = 1

def IsTrivialOnCotangent (X : GaloisDVRContext A K L B κ κB Gr V W)
    (σ : X.inertia) : Prop := X.cotangentAction σ = AddMonoidHom.id _

def IsTrivialModuloSquare (X : GaloisDVRContext A K L B κ κB Gr V W)
    (σ : X.decomposition) : Prop := X.firstOrderAction σ = AddMonoidHom.id _

/-! ## Galois action and the uniformity of ramification data -/

theorem galois_action_on_integral_closure_transitive
    (X : GaloisDVRContext A K L B κ κB Gr V W) :
    ∀ J : Ideal B, J.IsMaximal →
      ∃ σ : Gal(L / K), X.idealAction σ X.maximalIdeal = J := by
  sorry

theorem galois_uniform_ramification_and_residue_degree
    (X : GaloisDVRContext A K L B κ κB Gr V W) :
    ∃ e f : ℕ, 0 < e ∧ 0 < f ∧
      (∀ i, X.placeRamificationIndex i = e) ∧
      (∀ i, X.placeResidualDegree i = f) ∧
      Module.finrank K L = X.numberOfPlaces * e * f := by
  sorry

theorem residue_field_is_separable_over_a_perfect_base
    (X : GaloisDVRContext A K L B κ κB Gr V W) [PerfectField κ] :
    Algebra.IsSeparable κ κB := by
  sorry

/-! ## Decomposition and inertia -/

theorem decomposition_group_spec
    (X : GaloisDVRContext A K L B κ κB Gr V W) (σ : Gal(L / K)) :
    σ ∈ decompositionGroup X ↔ X.idealAction σ X.maximalIdeal = X.maximalIdeal :=
  X.decomposition_spec σ

theorem inertia_group_is_the_kernel_of_the_residue_action
    (X : GaloisDVRContext A K L B κ κB Gr V W) :
    ∀ σ : X.decomposition,
      (σ : Gal(L / K)) ∈ inertiaGroup X ↔ X.residueAction σ = 1 := by
  intro σ
  exact X.inertia_spec σ

/-! ## The residue-field Galois statement -/

theorem residue_field_extension_is_normal
    (X : GaloisDVRContext A K L B κ κB Gr V W) :
    Normal κ κB := by
  sorry

theorem decomposition_group_surjects_onto_residue_automorphisms
    (X : GaloisDVRContext A K L B κ κB Gr V W) :
    Function.Surjective X.residueAction := by
  sorry

theorem residue_field_extension_is_galois_when_separable
    (X : GaloisDVRContext A K L B κ κB Gr V W)
    [Algebra.IsSeparable κ κB] :
    IsGalois κ κB := by
  sorry

theorem decomposition_group_surjects_onto_residue_galois_group
    (X : GaloisDVRContext A K L B κ κB Gr V W)
    [Algebra.IsSeparable κ κB] :
    Function.Surjective X.residueAction := by
  sorry

/-! ## Wild and tame inertia -/

structure GroupExactSequence (P I T : Type*)
    [Group P] [Group I] [Group T] where
  inclusion : P →* I
  projection : I →* T
  projection_surjective : Function.Surjective projection
  exact_at_middle : ∀ x, projection x = 1 ↔ ∃ y, inclusion y = x

def inertiaExactSequence
    (X : GaloisDVRContext A K L B κ κB Gr V W) :
    GroupExactSequence X.wildInertia X.inertia (tameInertiaGroup X) := by
  let inclusion : X.wildInertia →* X.inertia :=
    { toFun := fun σ => ⟨σ.1, X.wildInertia_le_inertia σ.2⟩
      map_one' := rfl
      map_mul' := by intro σ τ; rfl }
  exact
    { inclusion := inclusion
      projection := X.tameProjection
      projection_surjective := X.tameProjection_surjective
      exact_at_middle := by
        intro σ
        constructor
        · intro h
          rcases (X.tameProjection_kernel σ).1 h with ⟨τ, hτ⟩
          refine ⟨τ, ?_⟩
          apply Subtype.ext
          exact congrArg Subtype.val hτ
        · rintro ⟨τ, hτ⟩
          apply (X.tameProjection_kernel σ).2
          refine ⟨τ, ?_⟩
          exact hτ }

theorem wild_inertia_is_kernel_on_cotangent_and_graded
    (X : GaloisDVRContext A K L B κ κB Gr V W) :
    (∀ σ : X.inertia,
      (σ : Gal(L / K)) ∈ wildInertiaGroup X ↔ IsTrivialOnCotangent X σ) ∧
    (∀ σ : X.decomposition,
      (σ : Gal(L / K)) ∈ wildInertiaGroup X ↔ IsTrivialOnGraded X σ) := by
  sorry

theorem wild_inertia_is_normal_in_decomposition_group
    (X : GaloisDVRContext A K L B κ κB Gr V W) :
    ∀ σ : decompositionGroup X, ∀ τ : wildInertiaGroup X,
      (σ : Gal(L / K)) * τ * (σ : Gal(L / K))⁻¹ ∈ wildInertiaGroup X := by
  sorry

theorem wild_inertia_is_a_p_group_in_positive_residue_characteristic
    (X : GaloisDVRContext A K L B κ κB Gr V W) {p : ℕ}
    [CharP κ p] (hp : 0 < p) : IsPGroup p X.wildInertia := by
  sorry

theorem wild_inertia_is_trivial_in_residue_characteristic_zero
    (X : GaloisDVRContext A K L B κ κB Gr V W)
    [CharZero κ] : Subsingleton X.wildInertia := by
  sorry

theorem tame_inertia_is_cyclic_of_prime_to_characteristic_order
    (X : GaloisDVRContext A K L B κ κB Gr V W) {p : ℕ}
    [CharP κ p] :
    IsCyclic (tameInertiaGroup X) ∧
      Nat.Coprime (Nat.card (tameInertiaGroup X)) p := by
  sorry

theorem inertia_character_induces_roots_of_unity_equivalence
    (X : GaloisDVRContext A K L B κ κB Gr V W) :
    ∃ e : ℕ, e = X.ramificationIndex ∧
      Nonempty (X.tameInertia ≃* rootsOfUnity e κB) := by
  sorry

theorem wild_inertia_is_trivial_modulo_square_when_residue_extension_separable
    (X : GaloisDVRContext A K L B κ κB Gr V W)
    [Algebra.IsSeparable κ κB] :
    ∀ σ : X.decomposition,
      (σ : Gal(L / K)) ∈ wildInertiaGroup X ↔ IsTrivialModuloSquare X σ := by
  sorry

/-! The example following the inertia lemma records that the square-level
    description is genuinely stronger than the cotangent-level one. -/

structure WildInertiaCounterexampleData where
  firstOrder : Type u
  squareLevel : Type v
  firstOrderAction : firstOrder → firstOrder
  squareLevelAction : squareLevel → squareLevel
  firstOrder_action_is_nontrivial : firstOrderAction ≠ id
  squareLevel_action_is_trivial : squareLevelAction = id

theorem wild_inertia_modulo_square_counterexample_exists :
    ∃ X : WildInertiaCounterexampleData,
      X.firstOrderAction ≠ id := by
  sorry

/-! ## Wild and tame inertia as named definitions -/

def wildInertia
    (X : GaloisDVRContext A K L B κ κB Gr V W) : Subgroup (Gal(L / K)) :=
  wildInertiaGroup X

def tameInertia
    (X : GaloisDVRContext A K L B κ κB Gr V W) : Type _ :=
  tameInertiaGroup X

theorem inertia_character_is_surjective_with_wild_kernel
    (X : GaloisDVRContext A K L B κ κB Gr V W) :
    Function.Surjective X.inertiaCharacter ∧
      ∀ σ : X.inertia,
        (σ : Gal(L / K)) ∈ wildInertiaGroup X ↔ X.inertiaCharacter σ = 1 := by
  sorry

/-! ## Equivariance of the inertia character -/

theorem inertia_character_conjugation_equivariant
    (X : GaloisDVRContext A K L B κ κB Gr V W)
    (τ : X.decomposition) (σ : X.inertia) :
      X.inertiaCharacter
        ⟨(τ : Gal(L / K)) * (σ : Gal(L / K)) * (τ : Gal(L / K))⁻¹,
          by sorry⟩ =
      ⟨Units.map (X.residueAction τ).toRingEquiv.toRingHom.toMonoidHom
          (X.inertiaCharacter σ).1, by sorry⟩ := by
  sorry

/-! ## Invariants under inertia and the tower of fixed rings -/

structure InertialInvariantConclusion (A K L B : Type*) where
  fixedRing : Type
  fixedField : Type
  fixedRing_is_integralClosure : Prop
  localized_map_is_etale : Prop

def InertialInvariantStatement
    (X : GaloisDVRContext A K L B κ κB Gr V W) : Prop :=
  ∃ Y : InertialInvariantConclusion A K L B,
    Y.fixedRing_is_integralClosure ∧ Y.localized_map_is_etale

theorem inertia_invariants_are_unramified
    (X : GaloisDVRContext A K L B κ κB Gr V W) :
    InertialInvariantStatement X := by
  sorry

structure FixedFieldTowerConclusion where
  extension_LI_over_LD_is_galois : Prop
  extension_LP_over_LI_is_galois : Prop
  extension_LP_over_LD_is_galois : Prop
  mI_unique_prime_over_mD : Prop
  mP_unique_prime_over_mI : Prop
  m_unique_prime_over_mP : Prop
  mP_unique_prime_over_mD : Prop
  m_unique_prime_over_mI : Prop
  m_unique_prime_over_mD : Prop
  A_to_BD_is_etale_with_trivial_residue_extension : Prop
  BD_to_BI_is_etale_with_galois_residue_extension : Prop
  A_to_BI_is_etale : Prop
  BI_to_BP_has_prime_to_p_ramification_and_trivial_residue_extension : Prop
  BD_to_BP_has_prime_to_p_ramification_and_separable_residue_extension : Prop
  A_to_BP_has_prime_to_p_ramification_and_separable_residue_extension : Prop

def FixedFieldTowerStatement
    (X : GaloisDVRContext A K L B κ κB Gr V W) : Prop :=
  ∃ Y : FixedFieldTowerConclusion,
    Y.extension_LI_over_LD_is_galois ∧
      Y.extension_LP_over_LI_is_galois ∧
      Y.extension_LP_over_LD_is_galois ∧
      Y.mI_unique_prime_over_mD ∧ Y.mP_unique_prime_over_mI ∧
      Y.m_unique_prime_over_mP ∧ Y.mP_unique_prime_over_mD ∧
      Y.m_unique_prime_over_mI ∧ Y.m_unique_prime_over_mD ∧
      Y.A_to_BD_is_etale_with_trivial_residue_extension ∧
      Y.BD_to_BI_is_etale_with_galois_residue_extension ∧
      Y.A_to_BI_is_etale ∧
      Y.BI_to_BP_has_prime_to_p_ramification_and_trivial_residue_extension ∧
      Y.BD_to_BP_has_prime_to_p_ramification_and_separable_residue_extension ∧
      Y.A_to_BP_has_prime_to_p_ramification_and_separable_residue_extension

theorem fixed_field_tower_statements
    (X : GaloisDVRContext A K L B κ κB Gr V W) :
    FixedFieldTowerStatement X := by
  sorry

/-! ## Comparison in a finite Galois tower -/

structure CompareInertiaData (G' G : Type*) [Group G'] [Group G] where
  restriction : G' →* G

  wildInertia' : Subgroup G'
  inertia' : Subgroup G'
  decomposition' : Subgroup G'
  wildInertia : Subgroup G
  inertia : Subgroup G
  decomposition : Subgroup G

structure CompareInertiaConclusion (G' G : Type*) [Group G'] [Group G]
    (Y : CompareInertiaData G' G) where
  wildRestriction : Y.wildInertia' →* Y.wildInertia
  inertiaRestriction : Y.inertia' →* Y.inertia
  decompositionRestriction : Y.decomposition' →* Y.decomposition
  wild_surjective : Function.Surjective wildRestriction
  inertia_surjective : Function.Surjective inertiaRestriction
  decomposition_surjective : Function.Surjective decompositionRestriction
  residue_action_square : Prop
  inertia_character_square : Prop

def CompareInertiaStatement {G' G : Type*} [Group G'] [Group G]
    (Y : CompareInertiaData G' G) : Prop :=
  ∃ Z : CompareInertiaConclusion G' G Y,
    Function.Surjective Z.wildRestriction ∧
      Function.Surjective Z.inertiaRestriction ∧
      Function.Surjective Z.decompositionRestriction ∧
      Z.residue_action_square ∧ Z.inertia_character_square

theorem compare_inertia_groups_in_a_galois_tower
    (Y : CompareInertiaData (Gal(L / K)) (Gal(L / K))) :
    CompareInertiaStatement Y := by
  sorry

/-! ## The canonical scaled inertia character -/

def CanonicalInertiaCharacterStatement
    (X : GaloisDVRContext A K L B κ κB Gr V W) : Prop :=
  ∃ q : ℕ, X.ramificationIndex = q * Nat.card (tameInertiaGroup X) ∧
    ∃ θcan : X.inertia →* rootsOfUnity (Nat.card (tameInertiaGroup X)) κB,
      Function.Surjective θcan ∧
      (∀ τ : X.decomposition, ∀ σ : X.inertia,
        θcan ⟨(τ : Gal(L / K)) * (σ : Gal(L / K)) * (τ : Gal(L / K))⁻¹,
          by sorry⟩ =
          ⟨Units.map (X.residueAction τ).toRingEquiv.toRingHom.toMonoidHom
              (θcan σ).1, by sorry⟩) ∧
      Nonempty (X.tameInertia ≃* rootsOfUnity (Nat.card (tameInertiaGroup X)) κB)

theorem canonical_scaled_inertia_character
    (X : GaloisDVRContext A K L B κ κB Gr V W) :
    CanonicalInertiaCharacterStatement X := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit113
