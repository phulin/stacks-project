import Formalization.Books.Exercises.Unit35.Core
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Exercises, Chapter 35: Tangent Spaces

The declarations below follow the source order.  The constructions are in
`Core.lean`; proposition-valued exercise proofs are deferred to the proving
stage.
-/

namespace Formalization.Books.Exercises.Unit35

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Opposite

universe u

noncomputable section

/-! ## Definition `definition-dual-numbers` and Exercise
`exercise-tangent-space-Zariski` -/

theorem dual_number_square_zero (R : Type u) [CommRing R] :
    dualNumberEpsilon R * dualNumberEpsilon R = 0 := by
  exact DualNumber.eps_mul_eps

theorem dual_number_is_free_rank_two (R : Type u) [CommRing R] :
    Module.Free R (dualNumberRing R) ∧
      Nonempty (Module.Basis (Fin 2) R (dualNumberRing R)) := by
  sorry

/-- The Zariski description of dotted arrows by the dual of the relative
cotangent quotient.  Equality of residue fields is expressed as equality of
their canonical `CommRingCat` representatives. -/
theorem tangent_arrow_zariski_correspondence
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (hκ : X.residueField x = S.residueField (f x)) :
    Nonempty (TangentSpace f x ≃ tangentLinearMaps f x) := by
  sorry

/-- The parenthetical separable-extension variant of the Zariski description. -/
theorem tangent_arrow_zariski_correspondence_of_separable
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    [Algebra (S.residueField (f x) : Type u) (X.residueField x : Type u)]
    [Algebra.IsSeparable (S.residueField (f x) : Type u)
      (X.residueField x : Type u)]
    (hκ : Function.Injective (f.residueFieldMap x).hom) :
    Nonempty (TangentSpace f x ≃ tangentLinearMaps f x) := by
  sorry

/-! ## Definition `definition-tangent-space` -/

theorem tangent_space_is_the_dotted_arrow_type
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    TangentSpace f x = TangentArrow f x :=
  rfl

/-! ## Exercise `exercise-simple-push-out` -/

/-- The two reductions agree after pulling back along the two projections of
the ring-theoretic pullback. -/
theorem dual_number_pushout_ring_condition (K : Type u) [Field K] :
    (dualNumberProjection K).comp (dualNumberPushoutLeft K) =
      (dualNumberProjection K).comp (dualNumberPushoutRight K) := by
  exact RingHom.pullback_comm_sq _ _

theorem dual_number_pushout_displayed_presentation (K : Type u) [Field K] :
    Nonempty (dualNumberPushoutRing K ≃+* dualNumberDisplayedPushoutRing K) := by
  sorry

/-- The displayed square is a pushout in schemes.  The target is the canonical
ring pullback, whose standard presentation is
`K[ε₁, ε₂]/(ε₁ε₂)` with both squares zero. -/
theorem simple_dual_number_pushout (K : Type u) [Field K] :
    ∃ c : PushoutCocone (dualNumberClosedPoint K) (dualNumberClosedPoint K),
      c.pt = affineSpec (dualNumberPushoutRing K) ∧
        HEq c.inl (dualNumberPushoutInl K) ∧
          HEq c.inr (dualNumberPushoutInr K) ∧
            Nonempty (IsColimit c) := by
  sorry

/-! ## Exercise `exercise-tangent-space-vectors-space` -/

theorem tangent_space_has_additive_vector_structure
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Nonempty (AddCommGroup (TangentSpace f x)) := by
  sorry

theorem tangent_space_has_scalar_module_structure
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    [AddCommGroup (TangentSpace f x)] :
    Nonempty (Module (X.residueField x : Type u) (TangentSpace f x)) := by
  sorry

/-! ## Exercise `exercise-compute-TS` and its relative remark -/

theorem affine_line_closed_tangent_space_dimension
    (k : Type u) [Field k] (x : affineLine k)
    (hx : IsClosed ({x} : Set (affineLine k))) :
    HasTangentSpaceDimension (affineLineStructureMap k) x 1 := by
  sorry

theorem affine_line_generic_tangent_space_dimension
    (k : Type u) [Field k] (η : affineLine k)
    (hη : IsAffineLineGenericPoint η) :
    HasTangentSpaceDimension (affineLineStructureMap k) η 0 := by
  sorry

theorem affine_line_over_int_closed_tangent_space_dimension
    (k : Type) [Field k] (x : affineLine k)
    (hx : IsClosed ({x} : Set (affineLine k))) :
    HasTangentSpaceDimension (affineLineOverIntStructureMap k) x 1 := by
  sorry

theorem affine_line_over_int_generic_tangent_space_dimension
    (k : Type) [Field k] (η : affineLine k)
    (hη : IsAffineLineGenericPoint η) :
    HasTangentSpaceDimension (affineLineOverIntStructureMap k) η 0 := by
  sorry

/-! ## Exercise `exercise-compute-TS-field` -/

/-- A field-spectrum morphism induced by a field homomorphism. -/
def fieldSpectrumMorphism {K L : Type u} [Field K] [Field L]
    (φ : K →+* L) : affineSpec L ⟶ affineSpec K :=
  affineSpecMap φ

theorem purely_inseparable_field_tangent_space_dimension
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsPurelyInseparable K L]
    (φ : K →+* L) (hφ : φ = algebraMap K L) :
    HasTangentSpaceDimension (fieldSpectrumMorphism φ)
      (fieldSpectrumPoint L) 1 := by
  sorry

theorem purely_inseparable_field_polynomial_model_is_not_invisible
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsPurelyInseparable K L] (φ : K →+* L) :
    Function.Injective φ → ¬ Function.Surjective φ →
      Nonempty (TangentSpace (fieldSpectrumMorphism φ) (fieldSpectrumPoint L)) := by
  sorry

/-! ## Exercise `exercise-compute-TS-cusp` -/

theorem cusp_origin_tangent_space_dimension
    (k : Type u) [Field k] (x : cuspScheme k)
    (horigin : x.asIdeal =
      Ideal.map (Ideal.Quotient.mk (cuspIdeal k))
        (Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
          Set (cuspPolynomialRing k)))) :
    HasTangentSpaceDimension
      (affineSpecMap (algebraMap k (cuspRing k))) x 2 := by
  sorry

/-! ## Exercise `exercise-map-tangent-spaces` -/

theorem map_on_tangent_spaces
    {X Y S : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (f : X ⟶ Y) (hbase : f ≫ pY = pX) (x : X)
    (hκ : Function.Bijective (f.residueFieldMap x).hom) :
    ∃ d : TangentSpace pX x → TangentSpace pY (f x),
      ∀ v, HEq (d v).lift (v.lift ≫ f) := by
  sorry

theorem map_on_tangent_spaces_agrees_with_local_ring_map
    {X Y S : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (f : X ⟶ Y) (hbase : f ≫ pY = pX) (x : X)
    (_hκ : X.residueField x = S.residueField (pX x))
    (hκf : Function.Bijective (f.residueFieldMap x).hom) :
    Nonempty (TangentMapLocalRingAgreement pX pY f x) := by
  obtain ⟨d, hd⟩ := map_on_tangent_spaces pX pY f hbase x hκf
  exact ⟨{
    map := d
    lift_eq := hd
    localRingMap := (f.stalkMap x).hom
    localRingMap_eq := rfl
  }⟩

/-! ## Exercise `exercise-Jacobian` -/

theorem jacobian_matrix_gives_tangent_map
    (k : Type u) [Field k] [IsAlgClosed k] {n m : ℕ}
    (p : Fin m → MvPolynomial (Fin n) k)
    (a : Fin n → k) :
    ∃ d : (Fin n → k) → (Fin m → k),
      (∀ v, d v = Matrix.mulVec (jacobianAt p a) v) := by
  sorry

end
end Formalization.Books.Exercises.Unit35
