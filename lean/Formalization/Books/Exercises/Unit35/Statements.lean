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
  exact ⟨Module.Free.of_basis (Module.Basis.finTwoProd R),
    ⟨Module.Basis.finTwoProd R⟩⟩

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
  let I := dualNumberPushoutRelationIdeal K
  let e₀ : dualNumberPushoutRing K :=
    ⟨((0, 1), (0, 0)), by
      change (0 : K) = 0
      rfl⟩
  let e₁ : dualNumberPushoutRing K :=
    ⟨((0, 0), (0, 1)), by
      change (0 : K) = 0
      rfl⟩
  let p : dualNumberPushoutPolynomialRing K →+* dualNumberPushoutRing K :=
    MvPolynomial.eval₂Hom (algebraMap K (dualNumberPushoutRing K)) ![e₀, e₁]
  have hp0 : p (MvPolynomial.X (0 : Fin 2)) = e₀ := by
    simp [p]
  have hp1 : p (MvPolynomial.X (1 : Fin 2)) = e₁ := by
    simp [p]
  have hp : I ≤ RingHom.ker p := by
    dsimp [I, dualNumberPushoutRelationIdeal]
    rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · change p (MvPolynomial.X (0 : Fin 2) ^ 2) = 0
      rw [map_pow, hp0]
      have he : e₀ ^ 2 = 0 := by
        dsimp [e₀]
        apply Subtype.ext
        apply Prod.ext
        · exact DualNumber.eps_pow_two
        · change (0 : DualNumber K) ^ 2 = 0
          simp
      exact he
    · change p (MvPolynomial.X (1 : Fin 2) ^ 2) = 0
      rw [map_pow, hp1]
      have he : e₁ ^ 2 = 0 := by
        dsimp [e₁]
        apply Subtype.ext
        apply Prod.ext
        · change (0 : DualNumber K) ^ 2 = 0
          simp
        · exact DualNumber.eps_pow_two
      exact he
    · change p (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) = 0
      rw [map_mul, hp0, hp1]
      have he : e₀ * e₁ = 0 := by
        apply Subtype.ext
        apply Prod.ext
        · change (DualNumber.eps : DualNumber K) * 0 = 0
          simp
        · change (0 : DualNumber K) * DualNumber.eps = 0
          simp
      exact he
  let q : dualNumberDisplayedPushoutRing K →+*
      dualNumberPushoutRing K := Ideal.Quotient.lift I p hp
  have h0 : MvPolynomial.X (0 : Fin 2) ^ 2 ∈ I := by
    apply Ideal.subset_span
    simp [dualNumberPushoutRelationIdeal]
  have h1 : MvPolynomial.X (1 : Fin 2) ^ 2 ∈ I := by
    apply Ideal.subset_span
    simp [dualNumberPushoutRelationIdeal]
  have h01 : MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) ∈ I := by
    apply Ideal.subset_span
    simp [dualNumberPushoutRelationIdeal]
  let qInv : dualNumberPushoutRing K →+*
      dualNumberDisplayedPushoutRing K :=
    { toFun := fun z =>
        Ideal.Quotient.mk I
          (MvPolynomial.C (z.1.1.1) +
            MvPolynomial.C (z.1.1.2) * MvPolynomial.X 0 +
            MvPolynomial.C (z.1.2.2) * MvPolynomial.X 1)
      map_one' := by
        apply Ideal.Quotient.eq.2
        change (MvPolynomial.C (1 : K) + MvPolynomial.C 0 * MvPolynomial.X 0 +
          MvPolynomial.C 0 * MvPolynomial.X 1) - 1 ∈ I
        simp
      map_zero' := by
        apply Ideal.Quotient.eq.2
        change (MvPolynomial.C (0 : K) + MvPolynomial.C 0 * MvPolynomial.X 0 +
          MvPolynomial.C 0 * MvPolynomial.X 1) - 0 ∈ I
        simp
      map_add' := by
        rintro ⟨⟨⟨zr, zs⟩, ⟨wr, zt⟩⟩, hz⟩
          ⟨⟨⟨ar, ys⟩, ⟨br, zt2⟩⟩, hw⟩
        apply Ideal.Quotient.eq.2
        change (MvPolynomial.C (zr + ar) + MvPolynomial.C (zs + ys) * MvPolynomial.X 0 +
          MvPolynomial.C (zt + zt2) * MvPolynomial.X 1) -
          ((MvPolynomial.C zr + MvPolynomial.C zs * MvPolynomial.X 0 +
            MvPolynomial.C zt * MvPolynomial.X 1) +
          (MvPolynomial.C ar + MvPolynomial.C ys * MvPolynomial.X 0 +
            MvPolynomial.C zt2 * MvPolynomial.X 1)) ∈ I
        simp only [map_add, add_mul]
        ring_nf
        exact I.zero_mem
      map_mul' := by
        rintro ⟨⟨⟨zr, zs⟩, ⟨wr, zt⟩⟩, hz⟩
          ⟨⟨⟨ar, ys⟩, ⟨br, zt2⟩⟩, hw⟩
        have hz' : zr = wr := hz
        have hw' : ar = br := hw
        apply Ideal.Quotient.eq.2
        change (MvPolynomial.C (zr * ar) +
          MvPolynomial.C (zr * ys + zs * ar) * MvPolynomial.X 0 +
          MvPolynomial.C (wr * zt2 + zt * br) * MvPolynomial.X 1) -
          ((MvPolynomial.C zr + MvPolynomial.C zs * MvPolynomial.X 0 +
            MvPolynomial.C zt * MvPolynomial.X 1) *
          (MvPolynomial.C ar + MvPolynomial.C ys * MvPolynomial.X 0 +
            MvPolynomial.C zt2 * MvPolynomial.X 1)) ∈ I
        rw [hz', hw']
        simp only [map_mul, map_add, add_mul, mul_add]
        have hm0 : (MvPolynomial.C zs * MvPolynomial.C ys) * MvPolynomial.X 0 ^ 2 ∈ I :=
          I.mul_mem_left _ h0
        have hm1 : (MvPolynomial.C zt * MvPolynomial.C zt2) * MvPolynomial.X 1 ^ 2 ∈ I :=
          I.mul_mem_left _ h1
        have hm01 :
            (MvPolynomial.C zs * MvPolynomial.C zt2 + MvPolynomial.C zt * MvPolynomial.C ys) *
              (MvPolynomial.X 0 * MvPolynomial.X 1) ∈ I :=
          I.mul_mem_left _ h01
        have hsum :
            (MvPolynomial.C zs * MvPolynomial.C ys) * MvPolynomial.X 0 ^ 2 +
              ((MvPolynomial.C zs * MvPolynomial.C zt2 +
                MvPolynomial.C zt * MvPolynomial.C ys) *
                (MvPolynomial.X 0 * MvPolynomial.X 1)) +
              (MvPolynomial.C zt * MvPolynomial.C zt2) * MvPolynomial.X 1 ^ 2 ∈ I :=
          I.add_mem (I.add_mem hm0 hm01) hm1
        convert I.neg_mem hsum using 1 <;> ring
    }
  have hqC (c : K) :
      (q (Ideal.Quotient.mk I (MvPolynomial.C c))).val =
        (TrivSqZeroExt.inl c, TrivSqZeroExt.inl c) := by
    change (p (MvPolynomial.C c)).val =
      (TrivSqZeroExt.inl c, TrivSqZeroExt.inl c)
    simp [p, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl]
  have hqX0 :
      (q (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2)))).val =
        (DualNumber.eps, (0 : DualNumber K)) := by
    change (p (MvPolynomial.X (0 : Fin 2))).val =
      (DualNumber.eps, (0 : DualNumber K))
    rw [hp0]
    rfl
  have hqX1 :
      (q (Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2)))).val =
        ((0 : DualNumber K), DualNumber.eps) := by
    change (p (MvPolynomial.X (1 : Fin 2))).val =
      ((0 : DualNumber K), DualNumber.eps)
    rw [hp1]
    rfl
  have hleft : Function.LeftInverse (q : _ →+* _) qInv := by
    intro z
    rcases z with ⟨⟨⟨zr, zs⟩, ⟨wr, zt⟩⟩, hz⟩
    have hz' : zr = wr := hz
    simp only [qInv, RingHom.coe_mk]
    change q (qInv.toFun ⟨((zr, zs), (wr, zt)), hz⟩) =
      ⟨((zr, zs), (wr, zt)), hz⟩
    dsimp only [qInv]
    apply Subtype.ext
    change (q (Ideal.Quotient.mk I
      (MvPolynomial.C zr + MvPolynomial.C zs * MvPolynomial.X 0 +
        MvPolynomial.C zt * MvPolynomial.X 1))).val = ((zr, zs), (wr, zt))
    simp only [map_add, map_mul]
    change
      (q (Ideal.Quotient.mk I (MvPolynomial.C zr))).val +
          (q (Ideal.Quotient.mk I (MvPolynomial.C zs))).val *
            (q (Ideal.Quotient.mk I (MvPolynomial.X 0))).val +
        (q (Ideal.Quotient.mk I (MvPolynomial.C zt))).val *
          (q (Ideal.Quotient.mk I (MvPolynomial.X 1))).val =
      ((zr, zs), (wr, zt))
    rw [hqC, hqC, hqX0, hqC, hqX1]
    rw [hz']
    apply Prod.ext
    · apply TrivSqZeroExt.ext
      · change
          (((wr, 0) : DualNumber K) + ((zs, 0) : DualNumber K) * (0, 1) +
            ((zt, 0) : DualNumber K) * (0, 0)).fst = wr
        simp [Prod.fst_add, Prod.snd_add, Prod.mk_mul_mk,
          TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
          TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]
      · rw [Prod.fst_add]
        change
          (((TrivSqZeroExt.inl wr : DualNumber K) +
                (TrivSqZeroExt.inl zs : DualNumber K) * DualNumber.eps).snd +
            ((TrivSqZeroExt.inl zt : DualNumber K) * (0 : DualNumber K)).snd) = zs
        simp [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul]
    · apply TrivSqZeroExt.ext
      · change
          (((wr, 0) : DualNumber K) + ((zs, 0) : DualNumber K) * (0, 0) +
            ((zt, 0) : DualNumber K) * (0, 1)).fst = wr
        simp [Prod.fst_add, Prod.snd_add, Prod.mk_mul_mk,
          TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
          TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]
      · rw [Prod.snd_add]
        change
          (((TrivSqZeroExt.inl wr : DualNumber K) +
                (TrivSqZeroExt.inl zs : DualNumber K) * (0 : DualNumber K)).snd +
            ((TrivSqZeroExt.inl zt : DualNumber K) * DualNumber.eps).snd) = zt
        simp [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul]
  have hsurj : Function.Surjective qInv := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction r using MvPolynomial.induction_on with
    | C c =>
        let z : dualNumberPushoutRing K :=
          ⟨((c, 0), (c, 0)), by simp [dualNumberPushoutRing]⟩
        exact ⟨z, by simp [qInv, z, I]⟩
    | add r s hr hs =>
        obtain ⟨z, hz⟩ := hr
        obtain ⟨w, hw⟩ := hs
        exact ⟨z + w, by simpa only [map_add] using (show qInv z + qInv w =
          (Ideal.Quotient.mk I) r + (Ideal.Quotient.mk I) s by rw [hz, hw])⟩
    | mul_X r i hr =>
        obtain ⟨z, hz⟩ := hr
        fin_cases i
        · have hqInvE₀ : qInv e₀ = Ideal.Quotient.mk I (MvPolynomial.X 0) := by
            apply Ideal.Quotient.eq.2
            simp [qInv, e₀]
          exact ⟨z * e₀, by
            rw [map_mul, hz, hqInvE₀]
            change (Ideal.Quotient.mk I) r * (Ideal.Quotient.mk I) (MvPolynomial.X 0) =
              (Ideal.Quotient.mk I) r *
                (Ideal.Quotient.mk I) (MvPolynomial.X (⟨0, by decide⟩ : Fin 2))
            apply congrArg (fun t => (Ideal.Quotient.mk I) r * t)
            apply congrArg (Ideal.Quotient.mk I)
            apply congrArg MvPolynomial.X
            apply Fin.ext
            rfl⟩
        · have hqInvE₁ : qInv e₁ = Ideal.Quotient.mk I (MvPolynomial.X 1) := by
            apply Ideal.Quotient.eq.2
            simp [qInv, e₁]
          exact ⟨z * e₁, by
            rw [map_mul, hz, hqInvE₁]
            change (Ideal.Quotient.mk I) r * (Ideal.Quotient.mk I) (MvPolynomial.X 1) =
              (Ideal.Quotient.mk I) r *
                (Ideal.Quotient.mk I) (MvPolynomial.X (⟨1, by decide⟩ : Fin 2))
            apply congrArg (fun t => (Ideal.Quotient.mk I) r * t)
            apply congrArg (Ideal.Quotient.mk I)
            apply congrArg MvPolynomial.X
            apply Fin.ext
            rfl⟩
  exact ⟨RingEquiv.ofBijective qInv ⟨hleft.injective, hsurj⟩⟩

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
