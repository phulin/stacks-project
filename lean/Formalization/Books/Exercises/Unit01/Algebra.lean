import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Exercises, Chapter 1: Algebra

This file records the definitions and theorem interfaces from the numbered
exercises in `books/exercises.tex`.  The propositions are intentionally left
unproved at this stage.
-/

noncomputable section

universe u v

open CategoryTheory
open CategoryTheory.ShortComplex
open IsLocalRing
open scoped TensorProduct

namespace Formalization.Books.Exercises.Unit01

/-! ## Localization and coherent rings -/

/-- The ideal `(m, p)` in a polynomial ring, written using Mathlib's ideal maps. -/
def shiftedPolynomialIdeal {A : Type*} [CommRing A] (m : Ideal A) (p : Polynomial A) :
    Ideal (Polynomial A) :=
  Ideal.map (Polynomial.C : A →+* Polynomial A) m ⊔ Ideal.span {p}

/-- The two localizations at `(m, X)` and `(m, X - 1)` are isomorphic. -/
theorem polynomial_shifted_localizations_equiv {A : Type v} [CommRing A]
    (m : Ideal A) [m.IsMaximal] :
    (shiftedPolynomialIdeal m Polynomial.X).IsMaximal ∧
      (shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1)).IsMaximal ∧
      ∃ (h₁ : (shiftedPolynomialIdeal m Polynomial.X).IsPrime)
        (h₂ : (shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1)).IsPrime),
        Nonempty
          (@Localization.AtPrime (Polynomial A) _
              (shiftedPolynomialIdeal m Polynomial.X) h₁ ≃+*
            @Localization.AtPrime (Polynomial A) _
              (shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1)) h₂) := by
  have hmax (x : A) :
      (shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C x)).IsMaximal := by
    let _i : Field (A ⧸ m) := Ideal.Quotient.field m
    let φ : Polynomial A →+* (A ⧸ m) :=
      Polynomial.eval₂RingHom (Ideal.Quotient.mk m) (Ideal.Quotient.mk m x)
    have hsurj : Function.Surjective φ := by
      intro y
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Polynomial.C a, by simp [φ]⟩
    have hker : RingHom.ker φ =
        shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C x) := by
      apply le_antisymm
      · intro p hp
        have hp0 : Ideal.Quotient.mk m (p.eval x) = 0 := by
          simpa [φ] using hp
        have hpm : p.eval x ∈ m := Ideal.Quotient.eq_zero_iff_mem.mp hp0
        have hdecomp :=
          Polynomial.modByMonic_add_div p (Polynomial.X - Polynomial.C x)
        rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at hdecomp
        rw [shiftedPolynomialIdeal]
        rw [← hdecomp]
        apply add_mem
        · exact Ideal.mem_sup_left
            (Ideal.mem_map_of_mem (Polynomial.C : A →+* Polynomial A) hpm)
        · exact Ideal.mem_sup_right <|
            by
              simpa [mul_comm] using
                (Ideal.span {Polynomial.X - Polynomial.C x}).mul_mem_left
                  (p /ₘ (Polynomial.X - Polynomial.C x))
                  (Ideal.subset_span (by rfl))
      · rw [shiftedPolynomialIdeal]
        apply sup_le
        · intro p hp
          rw [RingHom.mem_ker]
          have hcoeff := Ideal.mem_map_C_iff.mp hp
          have heval : p.eval x ∈ m := by
            rw [Polynomial.eval_eq_sum]
            exact m.sum_mem fun n _ => by
              simpa [mul_comm] using m.mul_mem_left (x ^ n) (hcoeff n)
          simpa [φ] using Ideal.Quotient.eq_zero_iff_mem.mpr heval
        · intro p hp
          rw [RingHom.mem_ker]
          obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hp
          rw [hq, map_mul]
          simp [φ]
    rw [← hker]
    exact RingHom.ker_isMaximal_of_surjective φ hsurj
  have hI₁ : (shiftedPolynomialIdeal m Polynomial.X).IsMaximal := by
    simpa using hmax 0
  have hI₂ :
      (shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1)).IsMaximal := by
    simpa using hmax 1
  let σ : Polynomial A ≃+* Polynomial A :=
    { __ := Polynomial.compRingHom (Polynomial.X - Polynomial.C 1)
      invFun := Polynomial.compRingHom (Polynomial.X + Polynomial.C 1)
      left_inv := by
        intro p
        change (p.comp (Polynomial.X - Polynomial.C 1)).comp
          (Polynomial.X + Polynomial.C 1) = p
        rw [Polynomial.comp_assoc]
        simp
      right_inv := by
        intro p
        change (p.comp (Polynomial.X + Polynomial.C 1)).comp
          (Polynomial.X - Polynomial.C 1) = p
        rw [Polynomial.comp_assoc]
        simp }
  have hσC : σ.toRingHom.comp (Polynomial.C : A →+* Polynomial A) =
      Polynomial.C := by
    ext a
    simp [σ]
  have hσX : σ.toRingHom Polynomial.X = Polynomial.X - Polynomial.C 1 := by
    simp [σ]
  have hmap :
      (shiftedPolynomialIdeal m Polynomial.X).map σ =
        shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1) := by
    change (shiftedPolynomialIdeal m Polynomial.X).map σ.toRingHom =
      shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1)
    simp only [shiftedPolynomialIdeal, Ideal.map_sup, Ideal.map_map,
      Ideal.map_span, Set.image_singleton]
    rw [hσC, hσX]
  have hIJ :
      shiftedPolynomialIdeal m Polynomial.X =
        (shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1)).comap
          σ.toRingHom := by
    calc
      shiftedPolynomialIdeal m Polynomial.X =
          ((shiftedPolynomialIdeal m Polynomial.X).comap σ.symm).comap
            σ.toRingHom :=
        (Ideal.comap_of_equiv
          (I := shiftedPolynomialIdeal m Polynomial.X) σ).symm
      _ = ((shiftedPolynomialIdeal m Polynomial.X).map σ).comap
          σ.toRingHom := by
        rw [Ideal.comap_symm]
      _ = (shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1)).comap
          σ.toRingHom := by rw [hmap]
  refine ⟨hI₁, hI₂, ?_⟩
  refine ⟨hI₁.isPrime, hI₂.isPrime, ?_⟩
  let _i₁ : (shiftedPolynomialIdeal m Polynomial.X).IsPrime := hI₁.isPrime
  let _i₂ :
      (shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1)).IsPrime :=
    hI₂.isPrime
  exact ⟨Localization.localRingEquiv
    (shiftedPolynomialIdeal m Polynomial.X)
    (shiftedPolynomialIdeal m (Polynomial.X - Polynomial.C 1)) σ hIJ⟩

/-- A commutative ring is coherent when finitely generated ideals are finitely presented. -/
def IsCoherentRing (R : Type*) [CommRing R] : Prop :=
  ∀ I : Ideal R, I.FG → Module.FinitePresentation R I

/-- There is a coherent ring which is not Noetherian. -/
theorem exists_coherent_non_noetherian_ring :
    ∃ R : CommRingCat.{u}, IsCoherentRing R ∧ ¬ IsNoetherianRing R := by
  sorry

/-! ## Minimal numbers of generators and flat ideals -/

/-- In a Noetherian local ring, the span rank of a finite module is its residue-field dimension. -/
theorem minimal_generators_eq_residue_field_dimension
    {A M : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    (⊤ : Submodule A M).spanFinrank =
      Module.finrank (A ⧸ IsLocalRing.maximalIdeal A)
        ((⊤ : Submodule A M) ⧸
          (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (⊤ : Submodule A M))) ∧
      (⊤ : Submodule A M).spanFinrank =
        Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField A ⊗[A] M) := by
  constructor
  · exact IsLocalRing.spanFinrank_eq_finrank_quotient (⊤ : Submodule A M)
      Module.Finite.fg_top
  · calc
      (⊤ : Submodule A M).spanFinrank =
          (⊤ : Submodule (IsLocalRing.ResidueField A)
            ((IsLocalRing.ResidueField A) ⊗[A] (⊤ : Submodule A M))).spanFinrank :=
        (TensorProduct.spanFinrank_top_eq_of_residueField (⊤ : Submodule A M)
          Module.Finite.fg_top).symm
      _ = Module.finrank (IsLocalRing.ResidueField A)
          ((IsLocalRing.ResidueField A) ⊗[A] (⊤ : Submodule A M)) :=
        Module.finrank_eq_spanFinrank_of_free.symm
      _ = Module.finrank (IsLocalRing.ResidueField A)
          ((IsLocalRing.ResidueField A) ⊗[A] M) := by
        exact (LinearEquiv.lTensor (IsLocalRing.ResidueField A)
          (Submodule.topEquiv (R := A) (M := M))).extendScalarsOfSurjective
          IsLocalRing.residue_surjective |>.finrank_eq

/-- Minimal generator counts multiply under tensor products over a local ring. -/
theorem minimal_generators_tensorProduct_mul
    {A M N : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] :
    (⊤ : Submodule A (M ⊗[A] N)).spanFinrank =
      (⊤ : Submodule A M).spanFinrank * (⊤ : Submodule A N).spanFinrank := by
  calc
    (⊤ : Submodule A (M ⊗[A] N)).spanFinrank =
        Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField A ⊗[A] (M ⊗[A] N)) :=
      (minimal_generators_eq_residue_field_dimension (A := A) (M := M ⊗[A] N)).2
    _ = Module.finrank (IsLocalRing.ResidueField A)
          ((IsLocalRing.ResidueField A ⊗[A] M) ⊗[IsLocalRing.ResidueField A]
            (IsLocalRing.ResidueField A ⊗[A] N)) := by
      exact (TensorProduct.AlgebraTensorModule.distribBaseChange A
        (IsLocalRing.ResidueField A) M N).finrank_eq
    _ = Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField A ⊗[A] M) *
        Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField A ⊗[A] N) := by
      rw [Module.finrank_tensorProduct]
    _ = (⊤ : Submodule A M).spanFinrank * (⊤ : Submodule A N).spanFinrank := by
      rw [(minimal_generators_eq_residue_field_dimension (A := A) (M := M)).2,
        (minimal_generators_eq_residue_field_dimension (A := A) (M := N)).2]

/-- A non-principal ideal has strictly fewer generators after squaring than the naive bound. -/
theorem ideal_square_spanFinrank_lt
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : 1 < I.spanFinrank) :
    (I ^ 2).spanFinrank < I.spanFinrank ^ 2 := by
  classical
  have hfg : I.FG := IsNoetherian.noetherian I
  obtain ⟨s, hs_card, hs_span⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  have hr : 2 ≤ s.card := (Nat.succ_le_iff.mpr hI).trans_eq hs_card.symm
  let i0 : Fin s.card := ⟨0, Nat.lt_of_lt_of_le (by decide) hr⟩
  let i1 : Fin s.card := ⟨1, Nat.lt_of_lt_of_le (by decide) hr⟩
  let e : Fin s.card ≃ s := s.equivFin.symm
  let p : s × s := (e i1, e i0)
  let q : Finset (s × s) := Finset.univ.product Finset.univ
  let t : Finset (s × s) :=
    q.filter (fun z => s.equivFin z.1 ≤ s.equivFin z.2)
  have hpq : p ∈ q := by simp [q, p]
  have hpt : p ∉ t := by simp [t, p, e, i0, i1]
  have hproper : t ⊂ q := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hEq
    exact hpt (hEq ▸ hpq)
  have ht_card : t.card < s.card ^ 2 := by
    calc
      t.card < q.card := Finset.card_lt_card hproper
      _ = s.card ^ 2 := by simp [q, pow_two]
  let all : Set A := Set.image2 (· * ·) (s : Set A) (s : Set A)
  let u : Finset A :=
    t.image (fun z : s × s => (z.1 : A) * (z.2 : A))
  have hspan : Ideal.span all = Ideal.span (u : Set A) := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro z hz
      rcases hz with ⟨x, hx, y, hy, rfl⟩
      let p : s × s := (⟨x, hx⟩, ⟨y, hy⟩)
      by_cases hp : s.equivFin p.1 ≤ s.equivFin p.2
      · have hpt' : p ∈ t := by simp [t, q, p, hp]
        exact Ideal.subset_span (Finset.mem_image.mpr ⟨p, hpt', rfl⟩)
      · have hp' : s.equivFin p.2 ≤ s.equivFin p.1 := le_of_not_ge hp
        let p' : s × s := (p.2, p.1)
        have hpt' : p' ∈ t := by simp [t, q, p', hp']
        have hu : (p'.1 : A) * (p'.2 : A) ∈ u :=
          Finset.mem_image.mpr ⟨p', hpt', rfl⟩
        simpa [p', mul_comm] using (Ideal.subset_span hu)
    · apply Ideal.span_le.mpr
      intro z hz
      rcases Finset.mem_coe.mp hz with hz
      rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
      exact Ideal.subset_span
        ⟨(p.1 : A), p.1.2, (p.2 : A), p.2.2, rfl⟩
  have hsq : I ^ 2 = Ideal.span all := by
    rw [← hs_span, pow_two]
    change Ideal.span (s : Set A) * Ideal.span (s : Set A) = Ideal.span all
    rw [Ideal.span_mul_span]
    rfl
  have hsq' : I ^ 2 = Ideal.span (u : Set A) := hsq.trans hspan
  calc
    (I ^ 2).spanFinrank ≤ u.card := by
      rw [hsq']
      simpa using
        (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite (u : Set A)))
    _ ≤ t.card := Finset.card_image_le
    _ < s.card ^ 2 := ht_card
    _ = I.spanFinrank ^ 2 := by rw [hs_card]

/-- If every ideal is flat, a Noetherian local ring is a PID or a field. -/
theorem flat_ideals_imply_pid_or_field
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hflat : ∀ I : Ideal A, Module.Flat A I) :
    IsField A ∨ (IsDomain A ∧ IsPrincipalIdealRing A) := by
  classical
  let m (I : Ideal A) : I ⊗[A] I →ₗ[A] I :=
    (TensorProduct.lid A I).toLinearMap.comp (I.subtype.rTensor I)
  have hcomp (I : Ideal A) :
      LinearMap.range (I.subtype.comp (m I)) = (I ^ 2 : Ideal A) := by
    rw [pow_two]
    apply le_antisymm
    · intro z hz
      rcases hz with ⟨w, rfl⟩
      refine TensorProduct.induction_on w (by simp) ?_ ?_
      · intro x y
        simpa [m] using
          (Ideal.mul_mem_mul (I := I) (J := I) x.property y.property)
      · intro x y hx hy
        simpa only [map_add] using add_mem hx hy
    · refine Ideal.mul_le.mpr ?_
      intro x hx y hy
      refine ⟨(⟨x, hx⟩ : I) ⊗ₜ[A] (⟨y, hy⟩ : I), ?_⟩
      simp [m]
  have hbound : ∀ I : Ideal A, I.spanFinrank ≤ 1 := by
    intro I
    by_contra hI
    have hI' : 1 < I.spanFinrank := Nat.lt_of_not_ge hI
    have hTensor : Function.Injective (I.subtype.rTensor I) :=
      (Module.Flat.iff_rTensor_injective.mp (hflat I))
        (IsNoetherian.noetherian I)
    have hm : Function.Injective (m I) :=
      (TensorProduct.lid A I).injective.comp hTensor
    have hp : Function.Injective (I.subtype.comp (m I)) :=
      (Submodule.injective_subtype I).comp hm
    have hsqfin : (I ^ 2).spanFinrank = I.spanFinrank ^ 2 := by
      calc
        (I ^ 2).spanFinrank =
            ((⊤ : Submodule A (I ⊗[A] I)).map
              (I.subtype.comp (m I))).spanFinrank := by
          rw [Submodule.map_top, hcomp]
        _ = (⊤ : Submodule A (I ⊗[A] I)).spanFinrank :=
          Submodule.spanFinrank_map_eq_of_injective
            (I.subtype.comp (m I)) hp
        _ = I.spanFinrank * I.spanFinrank := by
          simpa only [Submodule.spanFinrank_top] using
            (minimal_generators_tensorProduct_mul (A := A) (M := I) (N := I))
        _ = I.spanFinrank ^ 2 := by rw [pow_two]
    have hstrict := ideal_square_spanFinrank_lt I hI'
    rw [hsqfin] at hstrict
    exact (Nat.lt_irrefl _ hstrict)
  have hprincipal (I : Ideal A) : I.IsPrincipal := by
    by_cases hI0 : I = ⊥
    · subst I
      infer_instance
    · have hpos : 0 < I.spanFinrank := by
        by_contra hpos
        have hz : I.spanFinrank = 0 := Nat.eq_zero_of_not_pos hpos
        exact hI0 ((Submodule.spanFinrank_eq_zero_iff_eq_bot
          (IsNoetherian.noetherian I)).mp hz)
      have hone : I.spanFinrank = 1 :=
        Nat.le_antisymm (hbound I) hpos
      exact (Submodule.spanFinrank_eq_one_iff I).mp hone |>.1
  have hPIR : IsPrincipalIdealRing A :=
    { principal := hprincipal }
  have hregular : ∀ a : A, a ≠ 0 → ∀ b : A, a * b = 0 → b = 0 := by
    intro a ha b hab
    let I : Ideal A := Ideal.span {a}
    have hI0 : I ≠ ⊥ := by
      dsimp [I]
      exact Ideal.span_singleton_eq_bot.not.mpr ha
    let hfree : Module.Free A I := Module.free_of_flat_of_isLocalRing
    have hIspan : I.spanFinrank = 1 := by
      have hpos : 0 < I.spanFinrank := by
        by_contra hpos
        have hz : I.spanFinrank = 0 := Nat.eq_zero_of_not_pos hpos
        exact hI0 ((Submodule.spanFinrank_eq_zero_iff_eq_bot
          (IsNoetherian.noetherian I)).mp hz)
      exact Nat.le_antisymm (hbound I) hpos
    have hIfin : Module.finrank A I = 1 := by
      calc
        Module.finrank A I = (⊤ : Submodule A I).spanFinrank :=
          @Module.finrank_eq_spanFinrank_of_free A I _ _ _ _ hfree
        _ = I.spanFinrank := Submodule.spanFinrank_top I
        _ = 1 := hIspan
    let y : I := ⟨a, Ideal.subset_span (by simp)⟩
    let φ : A →ₗ[A] I :=
      { toFun := fun x => x • y
        map_add' := by
          intro x z
          simp [add_smul]
        map_smul' := by
          intro r x
          simp [smul_smul] }
    have hφ : Function.Surjective φ := by
      intro z
      rcases Ideal.mem_span_singleton'.mp z.property with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      apply Subtype.ext
      change c * a = (z : A)
      simpa [φ, y] using hc
    have hφbij : Function.Bijective φ :=
      OrzechProperty.bijective_of_surjective_of_finrank_le φ hφ (by
        rw [CommSemiring.finrank_self, hIfin])
    apply hφbij.1
    apply Subtype.ext
    dsimp [φ, y]
    simpa [mul_comm] using hab
  have hdom : IsDomain A := by
    refine
      { mul_left_cancel_of_ne_zero := ?_
        mul_right_cancel_of_ne_zero := ?_
        exists_pair_ne := exists_pair_ne A }
    · intro a ha b c hbc
      change a * b = a * c at hbc
      apply sub_eq_zero.mp
      apply hregular a ha (b - c)
      rw [mul_sub, hbc, sub_self]
    · intro a ha b c hbc
      change b * a = c * a at hbc
      apply sub_eq_zero.mp
      apply hregular a ha (b - c)
      rw [mul_sub]
      have hbc' : a * b = a * c := by simpa [mul_comm] using hbc
      rw [hbc', sub_self]
  exact Or.inr ⟨hdom, hPIR⟩

/-! ## Non-isomorphic polynomial rings -/

/-- Polynomial rings in successive positive finite numbers of variables are not isomorphic. -/
theorem mvPolynomial_fin_not_ringEquiv {k : Type*} [Field k] (n : ℕ) (hn : 1 ≤ n) :
    ¬ Nonempty (MvPolynomial (Fin n) k ≃+* MvPolynomial (Fin (n + 1)) k) := by
  rintro ⟨e⟩
  have he := ringKrullDim_eq_of_ringEquiv e
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field] at he
  simp only [Nat.card_fin, zero_add] at he
  cases n with
  | zero => exact (Nat.not_succ_le_zero 0) hn
  | succ n => exact Nat.succ_ne_self (n + 1) (by exact_mod_cast he.symm)

/-- The six-variable quadratic used in the two quotient-ring exercises. -/
def sixVariableQuadratic (k : Type*) [CommSemiring k] : MvPolynomial (Fin 6) k :=
  MvPolynomial.X (0 : Fin 6) * MvPolynomial.X (1 : Fin 6) +
    MvPolynomial.X (2 : Fin 6) * MvPolynomial.X (3 : Fin 6) +
    MvPolynomial.X (4 : Fin 6) * MvPolynomial.X (5 : Fin 6)

/-- The six-variable quadratic quotient is not a polynomial ring in five variables. -/
theorem sixVariableQuadratic_quotient_not_mvPolynomial_five
    {k : Type*} [Field k] :
    ¬ Nonempty
      ((MvPolynomial (Fin 6) k ⧸ Ideal.span {sixVariableQuadratic k}) ≃+*
        MvPolynomial (Fin 5) k) := by
  sorry

/-- The same quotient is not a polynomial ring in six variables. -/
theorem sixVariableQuadratic_quotient_not_mvPolynomial_six
    {k : Type*} [Field k] :
    ¬ Nonempty
      ((MvPolynomial (Fin 6) k ⧸ Ideal.span {sixVariableQuadratic k}) ≃+*
        MvPolynomial (Fin 6) k) := by
  rintro ⟨e⟩
  have hq0 : sixVariableQuadratic k ≠ 0 := by
    rw [MvPolynomial.ne_zero_iff]
    refine ⟨Finsupp.single (0 : Fin 6) 1 + Finsupp.single (1 : Fin 6) 1, ?_⟩
    simp [sixVariableQuadratic, MvPolynomial.coeff_X_mul']
  have hdimQ := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (R := MvPolynomial (Fin 6) k)
    (mem_nonZeroDivisors_iff_ne_zero.mpr hq0)
  have hdimR : ringKrullDim (MvPolynomial (Fin 6) k) = 6 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field]
    norm_num
  have hdimIso :
      ringKrullDim (MvPolynomial (Fin 6) k ⧸ Ideal.span {sixVariableQuadratic k}) = 6 := by
    calc
      ringKrullDim (MvPolynomial (Fin 6) k ⧸ Ideal.span {sixVariableQuadratic k}) =
          ringKrullDim (MvPolynomial (Fin 6) k) :=
        ringKrullDim_eq_of_ringEquiv e
      _ = 6 := hdimR
  rw [hdimIso, hdimR] at hdimQ
  norm_num at hdimQ

/-! ## Short exact sequences -/

/-- A short exact sequence becomes split after faithfully flat base change. -/
def SplitsAfterFaithfullyFlatBaseChange {A B : CommRingCat.{u}} (f : A ⟶ B)
    (S : ShortComplex (ModuleCat A)) : Prop :=
  RingHom.FaithfullyFlat f.hom ∧
    (S.map (ModuleCat.extendScalars f.hom)).ShortExact ∧
      Nonempty (S.map (ModuleCat.extendScalars f.hom)).Splitting

/-- There is a nonsplit short exact sequence of modules over the integers. -/
theorem exists_nonsplit_short_exact_sequence :
    ∃ S : ShortComplex (ModuleCat ℤ), S.ShortExact ∧ ¬ Nonempty S.Splitting := by
  let f₀ : ℤ →ₗ[ℤ] ℤ := LinearMap.mulLeft ℤ 2
  let g₀ : ℤ →ₗ[ℤ] ZMod 2 :=
    (Int.castRingHom (ZMod 2)).toIntAlgHom.toLinearMap
  let f : ULift ℤ →ₗ[ℤ] ULift ℤ :=
    ULift.moduleEquiv.symm.toLinearMap.comp (f₀.comp ULift.moduleEquiv.toLinearMap)
  let g : ULift ℤ →ₗ[ℤ] ULift (ZMod 2) :=
    ULift.moduleEquiv.symm.toLinearMap.comp (g₀.comp ULift.moduleEquiv.toLinearMap)
  have hcomp : g.comp f = 0 := by
    apply LinearMap.ext
    intro x
    apply ULift.ext
    change ((2 * x.down : ℤ) : ZMod 2) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨x.down, rfl⟩
  have hexact : Function.Exact f g := by
    intro x
    constructor
    · intro hx
      have hx0 : (x.down : ZMod 2) = 0 := by
        simpa [g, g₀] using congrArg ULift.down hx
      obtain ⟨y, hy⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x.down 2).mp hx0
      refine ⟨ULift.up y, ?_⟩
      apply ULift.ext
      change (2 : ℤ) * y = x.down
      exact hy.symm
    · rintro ⟨y, rfl⟩
      apply ULift.ext
      change ((2 * y.down : ℤ) : ZMod 2) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ⟨y.down, rfl⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply ULift.ext
    have hxy' := congrArg ULift.down hxy
    simpa [f, f₀] using mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num) hxy'
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨y, hy⟩ := ZMod.intCast_surjective z.down
    refine ⟨ULift.up y, ?_⟩
    apply ULift.ext
    simpa [g, g₀] using hy
  let S : ShortComplex (ModuleCat ℤ) := ShortComplex.moduleCatMk f g hcomp
  have hS : S.ShortExact := by
    exact ModuleCat.shortComplex_shortExact S hexact hinj hsurj
  refine ⟨S, hS, ?_⟩
  rintro ⟨s⟩
  have hsection := ModuleCat.hom_ext_iff.mp s.s_g
  have hsection1 := LinearMap.congr_fun hsection (ULift.up (1 : ZMod 2))
  change S.g.hom (s.s.hom (ULift.up (1 : ZMod 2))) =
    (ULift.up (1 : ZMod 2) : ULift (ZMod 2)) at hsection1
  have ht : (2 : ℤ) • ULift.up (1 : ZMod 2) = 0 := by
    apply ULift.ext
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd 2 2).2 ⟨1, rfl⟩
  have hzero_down : ULift.down (s.s.hom (ULift.up (1 : ZMod 2))) = 0 := by
    have hmap' : (2 : ℤ) • s.s.hom (ULift.up (1 : ZMod 2)) = 0 := by
      calc
        (2 : ℤ) • s.s.hom (ULift.up (1 : ZMod 2)) =
            s.s.hom ((2 : ℤ) • ULift.up (1 : ZMod 2)) :=
          (s.s.hom.map_smul _ _).symm
        _ = s.s.hom 0 := congrArg s.s.hom ht
        _ = 0 := map_zero _
    have hmul := congrArg ULift.down hmap'
    change (2 : ℤ) * ULift.down (s.s.hom (ULift.up (1 : ZMod 2))) = 0 at hmul
    rcases mul_eq_zero.mp hmul with h | h
    · norm_num at h
    · exact h
  have hzero : s.s.hom (ULift.up (1 : ZMod 2)) = 0 := by
    apply ULift.ext
    change ULift.down (s.s.hom (ULift.up (1 : ZMod 2))) = 0
    exact hzero_down
  have hgzero : S.g.hom (s.s.hom (ULift.up (1 : ZMod 2))) = 0 := by
    rw [hzero]
    exact map_zero _
  have hcontra : (0 : ULift (ZMod 2)) = ULift.up (1 : ZMod 2) :=
    hgzero.symm.trans hsection1
  have h01 : (0 : ZMod 2) = 1 := by
    simpa using congrArg ULift.down hcontra
  exact zero_ne_one h01

/-- There is a nonsplit sequence whose tensor sequence splits after a faithfully flat extension. -/
theorem exists_nonsplit_sequence_split_after_faithfullyFlat_baseChange :
    ∃ (A B : CommRingCat.{u}) (f : A ⟶ B) (S : ShortComplex (ModuleCat A)),
      S.ShortExact ∧ ¬ Nonempty S.Splitting ∧ SplitsAfterFaithfullyFlatBaseChange f S := by
  sorry

/-! ## Kummer extensions -/

/-- A primitive `n`th root of unity forces the characteristic to be coprime to `n`. -/
theorem primitive_root_characteristic_coprime
    {k : Type*} [Field k] {n : ℕ} (hn : 0 < n) {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) :
    ringChar k = 0 ∨ Nat.Coprime (ringChar k) n := by
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hzero
  · right
    apply hp.coprime_iff_not_dvd.mpr
    intro hpn
    have hncast : NeZero (n : k) :=
      @IsPrimitiveRoot.neZero' k ζ _ _ n ⟨Nat.ne_of_gt hn⟩ hζ
    apply hncast.ne
    obtain ⟨r, hr⟩ := hpn
    rw [hr, Nat.cast_mul, ringChar.Nat.cast_ringChar, zero_mul]
  · exact Or.inl hzero

/-- The standard Kummer irreducibility criterion gives a field quotient. -/
theorem kummer_polynomial_quotient_is_field
    {k : Type*} [Field k] {n : ℕ} (hn : 0 < n) {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) (a : k)
    (ha : ∀ d : ℕ, d ∣ n → d ≤ n → 1 < d → ¬ ∃ b : k, b ^ d = a) :
    IsField (Polynomial k ⧸ Ideal.span {Polynomial.X ^ n - Polynomial.C a}) := by
  classical
  have hirr : Irreducible (Polynomial.X ^ n - Polynomial.C a) := by
    induction n using induction_on_primes generalizing k ζ a with
    | zero => exact (Nat.not_lt_zero _ hn).elim
    | one => simpa using Polynomial.irreducible_X_sub_C a
    | prime_mul p n hp IH =>
        rw [mul_comm]
        have hnpos : 0 < n := Nat.pos_of_ne_zero (by
          intro hn0
          subst n
          simp at hn)
        by_cases hp2 : p = 2
        · subst p
          apply X_pow_mul_sub_C_irreducible
              (X_pow_sub_C_irreducible_of_prime (by decide) (by
                intro b hb
                exact ha 2 (dvd_mul_right _ _)
                  (Nat.le_mul_of_pos_right 2 hnpos) (by decide) ⟨b, hb⟩))
          intro E _ _ x hx
          have hxint : IsIntegral k x := not_not.mp fun h ↦ by
            simpa only [Polynomial.degree_zero,
              Polynomial.degree_X_pow_sub_C (n := 2) (a := a) (by decide),
              WithBot.natCast_ne_bot] using
              congr_arg Polynomial.degree (hx.symm.trans (dif_neg h))
          have hζp : IsPrimitiveRoot (ζ ^ 2) n := hζ.pow hn (by rfl)
          let L := IntermediateField.adjoin k {x}
          have hζL : IsPrimitiveRoot (algebraMap k L (ζ ^ 2)) n :=
            hζp.map_of_injective (FaithfulSMul.algebraMap_injective k L)
          refine IH (k := L) (ζ := algebraMap k L (ζ ^ 2))
            (a := IntermediateField.AdjoinSimple.gen k x) hnpos hζL ?_
          intro q hq hqn hqone hb
          rcases hb with ⟨b, hb⟩
          have hdiv : n = (n / q) * q := (Nat.div_mul_cancel hq).symm
          have hζ2q : IsPrimitiveRoot (ζ ^ (n / q)) (2 * q) := by
            apply hζ.pow hn
            have hprod : 2 * n = (n / q) * (2 * q) := by
              calc
                2 * n = 2 * ((n / q) * q) := congrArg (fun t => 2 * t) hdiv
                _ = (n / q) * (2 * q) := by
                  simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
            exact hprod
          have hζ2 : IsPrimitiveRoot ((ζ ^ (n / q)) ^ q) 2 := by
            apply hζ2q.pow
            · exact Nat.mul_pos (by decide) (Nat.zero_lt_of_lt hqone)
            · simp [Nat.mul_comm]
          have hneg : (ζ ^ (n / q)) ^ q = (-1 : k) :=
            hζ2.eq_neg_one_of_two_right
          have hnorm : (Algebra.norm k b) ^ q = -a := by
            rw [← map_pow, hb, ← IntermediateField.adjoin.powerBasis_gen hxint,
              Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
            rw [IntermediateField.adjoin.powerBasis_gen,
              IntermediateField.adjoin.powerBasis_dim,
              IntermediateField.minpoly_gen, hx]
            simp
          apply ha q (dvd_mul_of_dvd_right hq 2)
            (hqn.trans (Nat.le_mul_of_pos_left n (by decide))) hqone
          refine ⟨ζ ^ (n / q) * Algebra.norm k b, ?_⟩
          rw [mul_pow, hneg, hnorm]
          simp
        · apply X_pow_mul_sub_C_irreducible
            (X_pow_sub_C_irreducible_of_prime hp (by
              intro b hb
              exact ha p (dvd_mul_right _ _)
                (Nat.le_mul_of_pos_right p hnpos) hp.one_lt ⟨b, hb⟩))
          intro E _ _ x hx
          have hxint : IsIntegral k x := not_not.mp fun h ↦ by
            simpa only [Polynomial.degree_zero,
              Polynomial.degree_X_pow_sub_C hp.pos,
              WithBot.natCast_ne_bot] using
              congr_arg Polynomial.degree (hx.symm.trans (dif_neg h))
          have hζp : IsPrimitiveRoot (ζ ^ p) n := hζ.pow hn (by rfl)
          let L := IntermediateField.adjoin k {x}
          have hζL : IsPrimitiveRoot (algebraMap k L (ζ ^ p)) n :=
            hζp.map_of_injective (FaithfulSMul.algebraMap_injective k L)
          refine IH (k := L) (ζ := algebraMap k L (ζ ^ p))
            (a := IntermediateField.AdjoinSimple.gen k x) hnpos hζL ?_
          intro q hq hqn hqone hb
          rcases hb with ⟨b, hb⟩
          apply ha q (dvd_mul_of_dvd_right hq p)
            (hqn.trans (Nat.le_mul_of_pos_left n hp.pos)) hqone
          refine ⟨Algebra.norm _ b, ?_⟩
          rw [← map_pow, hb, ← IntermediateField.adjoin.powerBasis_gen hxint,
            Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
          rw [IntermediateField.adjoin.powerBasis_gen,
            IntermediateField.adjoin.powerBasis_dim,
            IntermediateField.minpoly_gen, hx]
          simp [(hp.odd_of_ne_two hp2).neg_one_pow]
          exact hp.ne_zero.symm
  let I : Ideal (Polynomial k) := Ideal.span {Polynomial.X ^ n - Polynomial.C a}
  have hIp : I.IsPrime := by
    apply (Ideal.span_singleton_prime hirr.ne_zero).mpr hirr.prime
  let _i : I.IsPrime := hIp
  have hIm : I.IsMaximal := by
    apply IsPrime.to_maximal_ideal
    change Ideal.span ({Polynomial.X ^ n - Polynomial.C a} : Set (Polynomial k)) ≠ ⊥
    exact Ideal.span_singleton_eq_bot.not.mpr hirr.ne_zero
  let _i : I.IsMaximal := hIm
  exact (Ideal.Quotient.field I).toIsField

/-! ## Integer-valued valuations on `k[x]` -/

/-- The valuation axioms used in the exercise, restricted to nonzero polynomials. -/
structure PolynomialValuation (k : Type*) [Field k] where
  toFun : {f : Polynomial k // f ≠ 0} → ℤ
  map_mul' : ∀ {f g : Polynomial k} (hf : f ≠ 0) (hg : g ≠ 0),
    toFun ⟨f * g, mul_ne_zero hf hg⟩ = toFun ⟨f, hf⟩ + toFun ⟨g, hg⟩
  map_add_min' : ∀ {f g : Polynomial k} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0),
    min (toFun ⟨f, hf⟩) (toFun ⟨g, hg⟩) ≤ toFun ⟨f + g, hfg⟩
  map_C' : ∀ {c : k} (hc : c ≠ 0),
    toFun ⟨Polynomial.C c, Polynomial.C_ne_zero.mpr hc⟩ = 0

instance {k : Type*} [Field k] : CoeFun (PolynomialValuation k)
    (fun _ => {f : Polynomial k // f ≠ 0} → ℤ) :=
  ⟨PolynomialValuation.toFun⟩

/-- Evaluation of a valuation at a polynomial together with its nonvanishing proof. -/
def PolynomialValuation.value {k : Type*} [Field k] (ν : PolynomialValuation k)
    (f : Polynomial k) (hf : f ≠ 0) : ℤ :=
  ν.toFun ⟨f, hf⟩

/-- The value of `X`, used in the termwise lower bound. -/
def PolynomialValuation.xValue {k : Type*} [Field k] (ν : PolynomialValuation k) : ℤ :=
  ν.value Polynomial.X Polynomial.X_ne_zero

/-- The set which is asserted to be a prime ideal when `ν(X) ≥ 0`. -/
def PolynomialValuation.positiveSet {k : Type*} [Field k] (ν : PolynomialValuation k) :
    Set (Polynomial k) :=
  {f | f = 0 ∨ ∃ hf : f ≠ 0, 0 < ν.value f hf}

/-- The values of the monomials occurring in a polynomial. -/
def PolynomialValuation.termValues {k : Type*} [Field k] (ν : PolynomialValuation k)
    (f : Polynomial k) : Finset ℤ :=
  f.support.image (fun i : ℕ => (i : ℤ) * ν.xValue)

/-- The minimum of the term values of a nonzero polynomial. -/
def PolynomialValuation.termMinimum {k : Type*} [Field k] (ν : PolynomialValuation k)
    (f : Polynomial k) (hf : f ≠ 0) : ℤ :=
  (ν.termValues f).min' (by
    change (f.support.image (fun i : ℕ => (i : ℤ) * ν.xValue)).Nonempty
    exact (Polynomial.support_nonempty.mpr hf).image _)

/-- Unequal values cannot cancel in a sum. -/
theorem polynomial_valuation_add_of_unequal_values
    {k : Type*} [Field k] (ν : PolynomialValuation k)
    {f g : Polynomial k} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0)
    (hneq : ν.value f hf ≠ ν.value g hg) :
    ν.value (f + g) hfg = min (ν.value f hf) (ν.value g hg) := by
  let hnegone : (-1 : Polynomial k) ≠ 0 := by simp
  have hC : ν.toFun ⟨(-1 : Polynomial k), hnegone⟩ = 0 := by
    simpa [PolynomialValuation.value] using
      (ν.map_C' (c := (-1 : k)) (neg_ne_zero.mpr one_ne_zero))
  have hneg (p : Polynomial k) (hp : p ≠ 0) :
      ν.value (-p) (neg_ne_zero.mpr hp) = ν.value p hp := by
    have hm := ν.map_mul' (f := (-1 : Polynomial k)) (g := p) hnegone hp
    simpa [PolynomialValuation.value, hC] using hm
  have hlow : min (ν.value f hf) (ν.value g hg) ≤ ν.value (f + g) hfg :=
    ν.map_add_min' hf hg hfg
  have hrev0 := ν.map_add_min' (f := f + g) (g := -g) hfg
    (neg_ne_zero.mpr hg) (by simpa using hf)
  change min (ν.value (f + g) hfg) (ν.value (-g) (neg_ne_zero.mpr hg)) ≤
    ν.value ((f + g) + (-g)) (by simpa using hf) at hrev0
  rw [hneg g hg] at hrev0
  have hrev : min (ν.value (f + g) hfg) (ν.value g hg) ≤ ν.value f hf := by
    simpa only [add_neg_cancel_right] using hrev0
  by_cases hab : ν.value f hf < ν.value g hg
  · have hac : ν.value f hf ≤ ν.value (f + g) hfg := by
      simpa only [min_eq_left (le_of_lt hab)] using hlow
    have hca : ν.value (f + g) hfg ≤ ν.value f hf := by
      by_cases hcb : ν.value (f + g) hfg ≤ ν.value g hg
      · simpa only [min_eq_left hcb] using hrev
      · have hbc : ν.value g hg ≤ ν.value (f + g) hfg := le_of_not_ge hcb
        have hba : ν.value g hg ≤ ν.value f hf := by
          simpa only [min_eq_right hbc] using hrev
        exact False.elim ((not_lt_of_ge hba) hab)
    rw [min_eq_left (le_of_lt hab)]
    exact le_antisymm hca hac
  · have hba : ν.value g hg < ν.value f hf :=
      lt_of_le_of_ne (le_of_not_gt hab) hneq.symm
    have hbc : ν.value g hg ≤ ν.value (f + g) hfg := by
      simpa only [min_eq_right (le_of_lt hba)] using hlow
    have hrev'0 := ν.map_add_min' (f := f + g) (g := -f) hfg
      (neg_ne_zero.mpr hf) (by simpa using hg)
    change min (ν.value (f + g) hfg) (ν.value (-f) (neg_ne_zero.mpr hf)) ≤
      ν.value ((f + g) + (-f)) (by simpa using hg) at hrev'0
    rw [hneg f hf] at hrev'0
    have hrev' : min (ν.value (f + g) hfg) (ν.value f hf) ≤ ν.value g hg := by
      simpa [add_assoc, add_left_comm, add_comm] using hrev'0
    have hcb : ν.value (f + g) hfg ≤ ν.value g hg := by
      by_cases hca : ν.value (f + g) hfg ≤ ν.value f hf
      · simpa only [min_eq_left hca] using hrev'
      · have hac : ν.value f hf ≤ ν.value (f + g) hfg := le_of_not_ge hca
        have hac' : ν.value f hf ≤ ν.value g hg := by
          simpa only [min_eq_right hac] using hrev'
        exact False.elim ((not_lt_of_ge hac') hba)
    rw [min_eq_right (le_of_lt hba)]
    exact le_antisymm hcb hbc

/-- Every nonzero coefficient term gives a lower bound on the value of a polynomial. -/
theorem polynomial_valuation_lower_bound
    {k : Type*} [Field k] (ν : PolynomialValuation k)
    (f : Polynomial k) (hf : f ≠ 0) :
    ν.value f hf ≥ ν.termMinimum f hf := by
  classical
  have hpow : ∀ n : ℕ, ν.value (Polynomial.X ^ n) (pow_ne_zero n Polynomial.X_ne_zero) =
      (n : ℤ) * ν.xValue := by
    intro n
    induction n with
    | zero =>
        simpa [PolynomialValuation.value, PolynomialValuation.xValue] using
          (ν.map_C' (c := (1 : k)) one_ne_zero)
    | succ n ih =>
        have hm := ν.map_mul' (f := Polynomial.X ^ n) (g := Polynomial.X)
          (pow_ne_zero n Polynomial.X_ne_zero) Polynomial.X_ne_zero
        have hm' := hm
        change ν.value (Polynomial.X ^ n * Polynomial.X) _ =
          ν.value (Polynomial.X ^ n) _ + ν.value Polynomial.X _ at hm'
        rw [ih] at hm'
        calc
          ν.value (Polynomial.X ^ (n + 1)) _ =
              ν.value (Polynomial.X ^ n * Polynomial.X) _ := by
            rfl
          _ = (n : ℤ) * ν.xValue + ν.xValue := hm'
          _ = ((n + 1 : ℕ) : ℤ) * ν.xValue := by
            norm_num [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc,
              mul_add, add_mul]
  have hmono : ∀ (n : ℕ) (a : k) (ha : a ≠ 0) (hmn : Polynomial.monomial n a ≠ 0),
      ν.value (Polynomial.monomial n a) hmn = (n : ℤ) * ν.xValue := by
    intro n a ha hmn
    have hm := ν.map_mul' (f := Polynomial.C a) (g := Polynomial.X ^ n)
      (Polynomial.C_ne_zero.mpr ha) (pow_ne_zero n Polynomial.X_ne_zero)
    have hm' := hm
    change ν.value (Polynomial.C a * Polynomial.X ^ n) _ =
      ν.value (Polynomial.C a) _ + ν.value (Polynomial.X ^ n) _ at hm'
    have hC : ν.value (Polynomial.C a) (Polynomial.C_ne_zero.mpr ha) = 0 := by
      simpa [PolynomialValuation.value] using ν.map_C' ha
    rw [hC, hpow n] at hm'
    have hval : ν.value (Polynomial.monomial n a) hmn = (n : ℤ) * ν.xValue := by
      simpa only [Polynomial.C_mul_X_pow_eq_monomial, zero_add] using hm'
    exact hval
  have hbound : ∀ (s : Finset ℕ) (p : Polynomial k),
      p.support = s → ∀ hp : p ≠ 0, ν.value p hp ≥ ν.termMinimum p hp := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro p hps hp
        exact False.elim (hp (Polynomial.support_eq_empty.mp hps))
    | @insert i s hi ih =>
        intro p hps hp
        have hi_mem : i ∈ p.support := by
          rw [hps]
          simp
        have hcoeff : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi_mem
        let g := p.erase i
        have hg_support : g.support = s := by
          simp [g, hps, hi]
        have hdecomp : Polynomial.monomial i (p.coeff i) + g = p := by
          simpa [g] using Polynomial.monomial_add_erase p i
        have hmonzero : Polynomial.monomial i (p.coeff i) ≠ 0 :=
          (Polynomial.monomial_eq_zero_iff (p.coeff i) i).not.mpr hcoeff
        have hmonval := hmono i (p.coeff i) hcoeff hmonzero
        have hmin_i : ν.termMinimum p hp ≤
            (i : ℤ) * ν.xValue := by
          change (ν.termValues p).min' _ ≤ _
          apply Finset.min'_le
          exact Finset.mem_image.mpr ⟨i, hi_mem, rfl⟩
        by_cases hg : g = 0
        · have hs0 : s = ∅ := by
            rw [← hg_support, hg]
            simp
          have hpsingle : p.support = {i} := by
            simpa [hs0] using hps
          have hterm : ν.termMinimum p hp = (i : ℤ) * ν.xValue := by
            simp [PolynomialValuation.termMinimum, PolynomialValuation.termValues, hpsingle]
          have hp_eq : p = Polynomial.monomial i (p.coeff i) := by
            calc
              p = Polynomial.monomial i (p.coeff i) + g := hdecomp.symm
              _ = Polynomial.monomial i (p.coeff i) := by rw [hg, add_zero]
          have heq : ν.value p hp = ν.termMinimum p hp := by
            calc
              ν.value p hp = ν.value (Polynomial.monomial i (p.coeff i)) hmonzero := by
                simpa [PolynomialValuation.value] using
                  congrArg ν.toFun (Subtype.ext hp_eq)
              _ = (i : ℤ) * ν.xValue := hmonval
              _ = ν.termMinimum p hp := hterm.symm
          exact le_of_eq heq.symm
        · have hgbound := ih g hg_support hg
          have hsupp : g.support ⊆ p.support := by
            intro j hj
            have hj' : j ∈ (p.support).erase i := by
              simpa [g] using hj
            exact Finset.mem_of_mem_erase hj'
          have htv : ν.termValues g ⊆ ν.termValues p := by
            intro z hz
            rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
            exact Finset.mem_image.mpr ⟨j, hsupp hj, rfl⟩
          have hmin_g : ν.termMinimum p hp ≤ ν.termMinimum g hg := by
            have hng : (ν.termValues g).Nonempty := by
              change (g.support.image (fun j : ℕ => (j : ℤ) * ν.xValue)).Nonempty
              exact (Polynomial.support_nonempty.mpr hg).image _
            change (ν.termValues p).min' _ ≤ (ν.termValues g).min' _
            exact Finset.min'_subset hng htv
          have hsum : Polynomial.monomial i (p.coeff i) + g ≠ 0 := by
            rw [hdecomp]
            exact hp
          have hmap := ν.map_add_min' hmonzero hg hsum
          have hmap' : min ((i : ℤ) * ν.xValue) (ν.value g hg) ≤
              ν.value (Polynomial.monomial i (p.coeff i) + g) hsum := by
            rw [← hmonval]
            exact hmap
          have hgbound' : ν.termMinimum g hg ≤ ν.value g hg := hgbound
          have hmap'' : min ((i : ℤ) * ν.xValue) (ν.termMinimum g hg) ≤
              ν.value (Polynomial.monomial i (p.coeff i) + g) hsum :=
            (min_le_min_left _ hgbound').trans hmap'
          calc
            ν.termMinimum p hp ≤ min ((i : ℤ) * ν.xValue)
                (ν.termMinimum g hg) :=
              le_min hmin_i hmin_g
            _ ≤ ν.value (Polynomial.monomial i (p.coeff i) + g) hsum := hmap''
            _ = ν.value p hp := by simp [hdecomp]
  exact hbound f.support f rfl hf

/-- A unique lowest-valued term forces equality in the lower bound. -/
theorem polynomial_valuation_eq_lower_bound_of_unique_min
    {k : Type*} [Field k] (ν : PolynomialValuation k)
    (f : Polynomial k) (hf : f ≠ 0)
    (hmin : ∃ i ∈ f.support,
      (∀ j ∈ f.support, (i : ℤ) * ν.xValue ≤ (j : ℤ) * ν.xValue) ∧
        (∀ j ∈ f.support, (i : ℤ) * ν.xValue = (j : ℤ) * ν.xValue → j = i)) :
    ν.value f hf = ν.termMinimum f hf := by
  classical
  have hpow : ∀ n : ℕ, ν.value (Polynomial.X ^ n) (pow_ne_zero n Polynomial.X_ne_zero) =
      (n : ℤ) * ν.xValue := by
    intro n
    induction n with
    | zero =>
        simpa [PolynomialValuation.value, PolynomialValuation.xValue] using
          (ν.map_C' (c := (1 : k)) one_ne_zero)
    | succ n ih =>
        have hm := ν.map_mul' (f := Polynomial.X ^ n) (g := Polynomial.X)
          (pow_ne_zero n Polynomial.X_ne_zero) Polynomial.X_ne_zero
        have hm' := hm
        change ν.value (Polynomial.X ^ n * Polynomial.X) _ =
          ν.value (Polynomial.X ^ n) _ + ν.value Polynomial.X _ at hm'
        rw [ih] at hm'
        calc
          ν.value (Polynomial.X ^ (n + 1)) _ =
              ν.value (Polynomial.X ^ n * Polynomial.X) _ := by rfl
          _ = (n : ℤ) * ν.xValue + ν.xValue := hm'
          _ = ((n + 1 : ℕ) : ℤ) * ν.xValue := by
            norm_num [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc,
              mul_add, add_mul]
  have hmono : ∀ (n : ℕ) (a : k) (ha : a ≠ 0) (hmn : Polynomial.monomial n a ≠ 0),
      ν.value (Polynomial.monomial n a) hmn = (n : ℤ) * ν.xValue := by
    intro n a ha hmn
    have hm := ν.map_mul' (f := Polynomial.C a) (g := Polynomial.X ^ n)
      (Polynomial.C_ne_zero.mpr ha) (pow_ne_zero n Polynomial.X_ne_zero)
    have hm' := hm
    change ν.value (Polynomial.C a * Polynomial.X ^ n) _ =
      ν.value (Polynomial.C a) _ + ν.value (Polynomial.X ^ n) _ at hm'
    have hC : ν.value (Polynomial.C a) (Polynomial.C_ne_zero.mpr ha) = 0 := by
      simpa [PolynomialValuation.value] using ν.map_C' ha
    rw [hC, hpow n] at hm'
    have hval : ν.value (Polynomial.monomial n a) hmn = (n : ℤ) * ν.xValue := by
      simpa only [Polynomial.C_mul_X_pow_eq_monomial, zero_add] using hm'
    exact hval
  obtain ⟨i, hi, hle, huniq⟩ := hmin
  have hcoeff : f.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  let g := f.erase i
  have hg_support : g.support = f.support.erase i := by
    simp [g]
  have hdecomp : Polynomial.monomial i (f.coeff i) + g = f := by
    simpa [g] using Polynomial.monomial_add_erase f i
  have hmonzero : Polynomial.monomial i (f.coeff i) ≠ 0 :=
    (Polynomial.monomial_eq_zero_iff (f.coeff i) i).not.mpr hcoeff
  have hmonval := hmono i (f.coeff i) hcoeff hmonzero
  have hterm : ν.termMinimum f hf = (i : ℤ) * ν.xValue := by
    apply le_antisymm
    · change (ν.termValues f).min' _ ≤ _
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    · change (i : ℤ) * ν.xValue ≤ (ν.termValues f).min' _
      apply Finset.le_min'
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
      exact hle j hj
  by_cases hg : g = 0
  · have hf_eq : f = Polynomial.monomial i (f.coeff i) := by
      calc
        f = Polynomial.monomial i (f.coeff i) + g := hdecomp.symm
        _ = Polynomial.monomial i (f.coeff i) := by rw [hg, add_zero]
    have hval : ν.value f hf = (i : ℤ) * ν.xValue := by
      calc
        ν.value f hf = ν.value (Polynomial.monomial i (f.coeff i)) hmonzero := by
          simpa [PolynomialValuation.value] using
            congrArg ν.toFun (Subtype.ext hf_eq)
        _ = (i : ℤ) * ν.xValue := hmonval
    exact hval.trans hterm.symm
  · have hstrict : (i : ℤ) * ν.xValue < ν.termMinimum g hg := by
      change (i : ℤ) * ν.xValue < (ν.termValues g).min' _
      rw [Finset.lt_min'_iff]
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
      have hj' : j ∈ f.support.erase i := by
        simpa [hg_support] using hj
      have hjf : j ∈ f.support := Finset.mem_of_mem_erase hj'
      have hne : (i : ℤ) * ν.xValue ≠ (j : ℤ) * ν.xValue := by
        intro heq
        have hji : j = i := huniq j hjf heq
        exact (Finset.mem_erase.mp hj').1 hji
      exact lt_of_le_of_ne (hle j hjf) hne
    have hgbound : ν.termMinimum g hg ≤ ν.value g hg :=
      polynomial_valuation_lower_bound ν g hg
    have hgv : (i : ℤ) * ν.xValue < ν.value g hg := hstrict.trans_le hgbound
    have hneq : ν.value (Polynomial.monomial i (f.coeff i)) hmonzero ≠
        ν.value g hg := by
      intro heq
      exact (ne_of_lt hgv) (hmonval.symm.trans heq)
    have hsum : Polynomial.monomial i (f.coeff i) + g ≠ 0 := by
      rw [hdecomp]
      exact hf
    have hadd := polynomial_valuation_add_of_unequal_values ν hmonzero hg hsum hneq
    have hval : ν.value f hf = (i : ℤ) * ν.xValue := by
      calc
        ν.value f hf = ν.value (Polynomial.monomial i (f.coeff i) + g) hsum := by
          simpa [PolynomialValuation.value] using
            congrArg ν.toFun (Subtype.ext hdecomp.symm)
        _ = min (ν.value (Polynomial.monomial i (f.coeff i)) hmonzero)
            (ν.value g hg) := hadd
        _ = (i : ℤ) * ν.xValue := by
          rw [hmonval, min_eq_left hgv.le]
    exact hval.trans hterm.symm

/-- If `ν(X) ≠ 0`, the term minimum is attained uniquely and equality holds. -/
theorem polynomial_valuation_eq_lower_bound_of_xValue_ne_zero
    {k : Type*} [Field k] (ν : PolynomialValuation k)
    {f : Polynomial k} (hf : f ≠ 0) (hx : ν.xValue ≠ 0) :
    ν.value f hf = ν.termMinimum f hf := by
  classical
  have hs : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  have hcancel : ∀ a b : ℕ, (a : ℤ) * ν.xValue = (b : ℤ) * ν.xValue → a = b := by
    intro a b hab
    have hab' := mul_right_cancel₀ hx hab
    exact_mod_cast hab'
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · let i := f.support.max' hs
    have hi : i ∈ f.support := by
      exact Finset.max'_mem _ _
    have hle : ∀ j ∈ f.support, (i : ℤ) * ν.xValue ≤ (j : ℤ) * ν.xValue := by
      intro j hj
      have hji : (j : ℤ) ≤ (i : ℤ) := by
        exact_mod_cast (Finset.le_max' f.support j hj)
      exact mul_le_mul_of_nonpos_right hji (le_of_lt hxneg)
    have huniq : ∀ j ∈ f.support,
        (i : ℤ) * ν.xValue = (j : ℤ) * ν.xValue → j = i := by
      intro j hj heq
      exact (hcancel i j heq).symm
    exact polynomial_valuation_eq_lower_bound_of_unique_min ν f hf
      ⟨i, hi, hle, huniq⟩
  · let i := f.support.min' hs
    have hi : i ∈ f.support := by
      exact Finset.min'_mem _ _
    have hle : ∀ j ∈ f.support, (i : ℤ) * ν.xValue ≤ (j : ℤ) * ν.xValue := by
      intro j hj
      have hij : (i : ℤ) ≤ (j : ℤ) := by
        exact_mod_cast (Finset.min'_le f.support j hj)
      exact mul_le_mul_of_nonneg_right hij (le_of_lt hxpos)
    have huniq : ∀ j ∈ f.support,
        (i : ℤ) * ν.xValue = (j : ℤ) * ν.xValue → j = i := by
      intro j hj heq
      exact (hcancel i j heq).symm
    exact polynomial_valuation_eq_lower_bound_of_unique_min ν f hf
      ⟨i, hi, hle, huniq⟩

/-- A valuation which takes a negative value is a negative multiple of degree. -/
theorem polynomial_valuation_negative_is_negative_degree
    {k : Type*} [Field k] (ν : PolynomialValuation k)
    (hneg : ∃ (f : Polynomial k) (hf : f ≠ 0), ν.value f hf < 0) :
    ∃ n : ℕ, 0 < n ∧
      ∀ (f : Polynomial k) (hf : f ≠ 0),
        ν.value f hf = -(n : ℤ) * (f.natDegree : ℤ) := by
  obtain ⟨g, hg, hgv⟩ := hneg
  have hxneg : ν.xValue < 0 := by
    by_contra hx
    have hlow := polynomial_valuation_lower_bound ν g hg
    have hs : (ν.termValues g).Nonempty := by
      change (g.support.image (fun i : ℕ => (i : ℤ) * ν.xValue)).Nonempty
      exact (Polynomial.support_nonempty.mpr hg).image _
    have hnonneg : 0 ≤ ν.termMinimum g hg := by
      change 0 ≤ (ν.termValues g).min' hs
      apply Finset.le_min' (s := ν.termValues g) (H := hs)
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      exact mul_nonneg (Int.natCast_nonneg i) (le_of_not_gt hx)
    exact False.elim ((not_lt_of_ge hnonneg) (lt_of_le_of_lt hlow hgv))
  let n : ℕ := Int.toNat (-ν.xValue)
  have hncast : (n : ℤ) = -ν.xValue := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (le_of_lt (neg_pos.mpr hxneg))]
  have hnpos : 0 < n := by
    exact_mod_cast (show (0 : ℤ) < (n : ℤ) by rw [hncast]; exact neg_pos.mpr hxneg)
  refine ⟨n, hnpos, ?_⟩
  intro f hf
  have hvalue := polynomial_valuation_eq_lower_bound_of_xValue_ne_zero ν hf
    (ne_of_lt hxneg)
  have hs : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  have hi : f.natDegree ∈ f.support := by
    rw [Polynomial.natDegree_eq_support_max' hf]
    exact Finset.max'_mem _ _
  have hterm : ν.termMinimum f hf = (f.natDegree : ℤ) * ν.xValue := by
    apply le_antisymm
    · change (ν.termValues f).min' _ ≤ _
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨f.natDegree, hi, rfl⟩
    · change _ ≤ (ν.termValues f).min' _
      apply Finset.le_min'
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
      have hj' : j ≤ f.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
      have hj'' : (j : ℤ) ≤ (f.natDegree : ℤ) := by exact_mod_cast hj'
      exact mul_le_mul_of_nonpos_right hj'' (le_of_lt hxneg)
  calc
    ν.value f hf = ν.termMinimum f hf := hvalue
    _ = (f.natDegree : ℤ) * ν.xValue := hterm
    _ = -(n : ℤ) * (f.natDegree : ℤ) := by rw [hncast]; ring

/-- For nonnegative `ν(X)`, the positive-value set is a prime ideal. -/
theorem polynomial_valuation_positiveSet_is_prime
    {k : Type*} [Field k] (ν : PolynomialValuation k) (hx : 0 ≤ ν.xValue) :
    ∃ I : Ideal (Polynomial k),
      (I : Set (Polynomial k)) = ν.positiveSet ∧ I.IsPrime := by
  have hterm_nonneg : ∀ (f : Polynomial k) (hf : f ≠ 0),
      0 ≤ ν.termMinimum f hf := by
    intro f hf
    have hs : (ν.termValues f).Nonempty := by
      change (f.support.image (fun i : ℕ => (i : ℤ) * ν.xValue)).Nonempty
      exact (Polynomial.support_nonempty.mpr hf).image _
    change 0 ≤ (ν.termValues f).min' hs
    apply Finset.le_min' (s := ν.termValues f) (H := hs)
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    exact mul_nonneg (Int.natCast_nonneg i) hx
  have hvalue_nonneg : ∀ (f : Polynomial k) (hf : f ≠ 0),
      0 ≤ ν.value f hf := by
    intro f hf
    exact (hterm_nonneg f hf).trans (polynomial_valuation_lower_bound ν f hf)
  let I : Ideal (Polynomial k) :=
    { carrier := ν.positiveSet
      zero_mem' := by
        change (0 : Polynomial k) = 0 ∨ _
        exact Or.inl rfl
      add_mem' := by
        intro f g hf hg
        change f = 0 ∨ ∃ h : f ≠ 0, 0 < ν.value f h at hf
        change g = 0 ∨ ∃ h : g ≠ 0, 0 < ν.value g h at hg
        change f + g = 0 ∨ ∃ h : f + g ≠ 0, 0 < ν.value (f + g) h
        rcases hf with rfl | ⟨hf, hfp⟩
        · simpa using hg
        rcases hg with rfl | ⟨hg, hgp⟩
        · exact Or.inr ⟨by simpa using hf, by simpa using hfp⟩
        by_cases hfg : f + g = 0
        · exact Or.inl hfg
        · right
          refine ⟨hfg, ?_⟩
          exact lt_of_lt_of_le (lt_min hfp hgp) (ν.map_add_min' hf hg hfg)
      smul_mem' := by
        intro a f hf
        change f = 0 ∨ ∃ h : f ≠ 0, 0 < ν.value f h at hf
        change a * f = 0 ∨ ∃ h : a * f ≠ 0, 0 < ν.value (a * f) h
        rcases hf with rfl | ⟨hf, hfp⟩
        · simp
        by_cases ha : a = 0
        · simp [ha]
        · right
          have haf : a * f ≠ 0 := mul_ne_zero ha hf
          refine ⟨haf, ?_⟩
          have hmul := ν.map_mul' ha hf
          change ν.value (a * f) haf = ν.value a ha + ν.value f hf at hmul
          rw [hmul]
          exact lt_of_lt_of_le hfp (le_add_of_nonneg_left (hvalue_nonneg a ha)) }
  have hone : (1 : Polynomial k) ∉ I := by
    change (1 : Polynomial k) ∉ ν.positiveSet
    intro h
    rcases h with h | ⟨h1, hpos⟩
    · exact one_ne_zero h
    · have hval : ν.value (1 : Polynomial k) h1 = 0 := by
        simpa [PolynomialValuation.value] using
          (ν.map_C' (c := (1 : k)) one_ne_zero)
      exact (lt_irrefl 0) (hval ▸ hpos)
  have hIne : I ≠ (⊤ : Ideal (Polynomial k)) := by
    intro h
    apply hone
    rw [h]
    trivial
  refine ⟨I, ?_, ⟨hIne, ?_⟩⟩
  · rfl
  · intro f g hfg
    change f * g = 0 ∨ ∃ h : f * g ≠ 0, 0 < ν.value (f * g) h at hfg
    change (f = 0 ∨ ∃ h : f ≠ 0, 0 < ν.value f h) ∨
      (g = 0 ∨ ∃ h : g ≠ 0, 0 < ν.value g h)
    rcases hfg with hfg | ⟨hfg, hprod⟩
    · rcases mul_eq_zero.mp hfg with rfl | rfl
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr (Or.inl rfl)
    have hf : f ≠ 0 := by
      intro hf
      subst f
      exact hfg (zero_mul g)
    have hg : g ≠ 0 := by
      intro hg
      subst g
      exact hfg (mul_zero f)
    have hmap := ν.map_mul' hf hg
    change ν.value (f * g) hfg = ν.value f hf + ν.value g hg at hmap
    have hsum : 0 < ν.value f hf + ν.value g hg := by
      rw [← hmap]
      exact hprod
    by_cases hfp : 0 < ν.value f hf
    · exact Or.inl (Or.inr ⟨hf, hfp⟩)
    · right
      have hf0 : ν.value f hf ≤ 0 := le_of_not_gt hfp
      have hgp : 0 < ν.value g hg := by
        by_contra hgp
        exact (not_lt_of_ge (add_nonpos hf0 (le_of_not_gt hgp))) hsum
      exact Or.inr ⟨hg, hgp⟩

/-- All such valuations are either trivial, degree valuations, or orders at an irreducible. -/
theorem polynomial_valuation_classification
    {k : Type*} [Field k] (ν : PolynomialValuation k) :
    (∀ (f : Polynomial k) (hf : f ≠ 0), ν.value f hf = 0) ∨
      (∃ n : ℕ, 0 < n ∧
        ∀ (f : Polynomial k) (hf : f ≠ 0),
          ν.value f hf = -(n : ℤ) * (f.natDegree : ℤ)) ∨
      (∃ (p : Polynomial k) (n : ℕ), Irreducible p ∧ 0 < n ∧
        ∀ (f : Polynomial k) (hf : f ≠ 0),
          ν.value f hf = (n : ℤ) * (multiplicity p f : ℤ)) := by
  classical
  by_cases hneg : ∃ (f : Polynomial k) (hf : f ≠ 0), ν.value f hf < 0
  · exact Or.inr (Or.inl (polynomial_valuation_negative_is_negative_degree ν hneg))
  have hnonneg : ∀ (f : Polynomial k) (hf : f ≠ 0), 0 ≤ ν.value f hf := by
    intro f hf
    exact le_of_not_gt (fun h => hneg ⟨f, hf, h⟩)
  by_cases hzero : ∀ (f : Polynomial k) (hf : f ≠ 0), ν.value f hf = 0
  · exact Or.inl hzero
  have hx : 0 ≤ ν.xValue := by
    by_contra hx
    have hx' : ν.xValue < 0 := lt_of_not_ge hx
    apply hneg
    exact ⟨Polynomial.X, Polynomial.X_ne_zero, by
      simpa [PolynomialValuation.xValue] using hx'⟩
  obtain ⟨I, hIset, hIprime⟩ :=
    polynomial_valuation_positiveSet_is_prime ν hx
  obtain ⟨f, hf, hfne⟩ : ∃ (f : Polynomial k) (hf : f ≠ 0), ν.value f hf ≠ 0 := by
    rcases not_forall.mp hzero with ⟨f, hzero_f⟩
    rcases not_forall.mp hzero_f with ⟨hf, hfne⟩
    exact ⟨f, hf, hfne⟩
  have hfpos : 0 < ν.value f hf := lt_of_le_of_ne (hnonneg f hf) hfne.symm
  have hfI : f ∈ I := by
    change f ∈ (I : Set (Polynomial k))
    rw [hIset]
    exact Or.inr ⟨hf, hfpos⟩
  let p : Polynomial k := Submodule.IsPrincipal.generator I
  have hpI : Ideal.span ({p} : Set (Polynomial k)) = I := by
    change Ideal.span ({Submodule.IsPrincipal.generator I} : Set (Polynomial k)) = I
    exact Submodule.IsPrincipal.span_singleton_generator I
  have hIne : I ≠ (⊥ : Ideal (Polynomial k)) := by
    intro hbot
    apply hf
    have hmem : f ∈ (⊥ : Ideal (Polynomial k)) := hbot ▸ hfI
    simpa using hmem
  have hp0 : p ≠ 0 := by
    intro hp
    apply hIne
    rw [← hpI, hp]
    simp
  have hIp : (Ideal.span ({p} : Set (Polynomial k))).IsPrime := by
    rw [hpI]
    exact hIprime
  have hpprime : Prime p := (Ideal.span_singleton_prime hp0).mp hIp
  have hirr : Irreducible p := hpprime.irreducible
  have hpI_mem : p ∈ I := by
    rw [← hpI]
    exact Ideal.mem_span_singleton_self p
  have hpI' : p ∈ (I : Set (Polynomial k)) := hpI_mem
  rw [hIset] at hpI'
  change p = 0 ∨ ∃ h : p ≠ 0, 0 < ν.value p h at hpI'
  have hpvalpos : 0 < ν.value p hp0 := by
    rcases hpI' with hpz | ⟨hp', hpval⟩
    · exact (hp0 hpz).elim
    · exact hpval
  let n : ℕ := Int.toNat (ν.value p hp0)
  have hncast : (n : ℤ) = ν.value p hp0 := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (hnonneg p hp0)]
  have hnpos : 0 < n := by
    have hncastpos : (0 : ℤ) < (n : ℤ) := by
      rw [hncast]
      exact hpvalpos
    exact_mod_cast hncastpos
  right
  right
  refine ⟨p, n, hirr, hnpos, ?_⟩
  intro g hg
  have hfin : FiniteMultiplicity p g :=
    FiniteMultiplicity.of_prime_left hpprime hg
  obtain ⟨q, hfactor, hpq⟩ :=
    FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd hfin
  have hq : q ≠ 0 := by
    intro hq
    apply hg
    rw [hfactor, hq]
    simp
  have hqnotI : q ∉ I := by
    intro hqI
    apply hpq
    apply Ideal.mem_span_singleton.mp
    rw [hpI]
    exact hqI
  have hqzero : ν.value q hq = 0 := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hqpos
      have hqI : q ∈ I := by
        change q ∈ (I : Set (Polynomial k))
        rw [hIset]
        exact Or.inr ⟨hq, hqpos⟩
      exact hqnotI hqI
    · exact hnonneg q hq
  have hpow : ∀ r : ℕ,
      ν.value (p ^ r) (pow_ne_zero r hp0) = (r : ℤ) * ν.value p hp0 := by
    intro r
    induction r with
    | zero =>
        simpa [PolynomialValuation.value] using
          (ν.map_C' (c := (1 : k)) one_ne_zero)
    | succ r ih =>
        have hm := ν.map_mul' (f := p ^ r) (g := p)
          (pow_ne_zero r hp0) hp0
        change ν.value (p ^ r * p) _ =
          ν.value (p ^ r) _ + ν.value p _ at hm
        rw [ih] at hm
        calc
          ν.value (p ^ (r + 1)) _ =
              ν.value (p ^ r * p) _ := by rfl
          _ = (r : ℤ) * ν.value p hp0 + ν.value p hp0 := hm
          _ = ((r + 1 : ℕ) : ℤ) * ν.value p hp0 := by
            norm_num [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm,
              add_assoc, mul_add, add_mul]
  have hmul := ν.map_mul' (f := p ^ multiplicity p g) (g := q)
    (pow_ne_zero (multiplicity p g) hp0) hq
  calc
    ν.value g hg =
        ν.value (p ^ multiplicity p g * q)
          (mul_ne_zero (pow_ne_zero _ hp0) hq) := by
      simpa [PolynomialValuation.value] using congrArg ν.toFun (Subtype.ext hfactor)
    _ = ν.value (p ^ multiplicity p g) _ + ν.value q hq := hmul
    _ = (multiplicity p g : ℤ) * ν.value p hp0 := by
      rw [hpow, hqzero, add_zero]
    _ = (n : ℤ) * (multiplicity p g : ℤ) := by
      rw [hncast]
      ring

/-! ## Idempotents and products -/

/-- The canonical idempotent elements `0` and `1`. -/
theorem zero_one_are_idempotent {A : Type*} [MonoidWithZero A] :
    IsIdempotentElem (0 : A) ∧ IsIdempotentElem (1 : A) := by
  exact ⟨IsIdempotentElem.zero, IsIdempotentElem.one⟩

/-- The corrected nontrivial-idempotent predicate needed for a product decomposition. -/
def IsNontrivialIdempotent {A : Type*} [MonoidWithZero A] (e : A) : Prop :=
  IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1

/-- The pairwise notion of orthogonality is Mathlib's `OrthogonalIdempotents` on `Fin 2`. -/
theorem orthogonal_idempotents_pair_iff {A : Type*} [CommRing A] (e e' : A) :
    OrthogonalIdempotents ![e, e'] ↔
      IsIdempotentElem e ∧ IsIdempotentElem e' ∧ e * e' = 0 := by
  rw [orthogonalIdempotents_iff]
  constructor
  · intro h
    have he : IsIdempotentElem e := by simpa using h.1 0
    have he' : IsIdempotentElem e' := by simpa using h.1 1
    have hp : e * e' = 0 := by
      simpa using h.2 (show (0 : Fin 2) ≠ 1 by decide)
    exact ⟨he, he', hp⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using h.1
      · simpa using h.2.1
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [mul_comm]

/-- A commutative ring is a product of two nonzero rings. -/
def IsProductOfTwoNonzeroRings (A : CommRingCat.{u}) : Prop :=
  ∃ B C : CommRingCat.{u}, Nontrivial B ∧ Nontrivial C ∧ Nonempty (A ≃+* (B × C))

/-- A product decomposition is equivalent to a nontrivial idempotent. -/
theorem product_ring_iff_nontrivial_idempotent (A : CommRingCat.{u}) :
    IsProductOfTwoNonzeroRings A ↔ ∃ e : A, IsNontrivialIdempotent e := by
  constructor
  · rintro ⟨B, C, hB, hC, ⟨e⟩⟩
    let z : A := e.symm (1, 0)
    have hz : IsIdempotentElem z := by
      change z * z = z
      apply e.injective
      simp [z]
    have hz0 : z ≠ 0 := by
      intro h
      have h' : ((1, 0) : (B × C)) = (0, 0) := by
        have h'' := congrArg e h
        calc
          (1, 0) = e z := by simp [z]
          _ = e 0 := h''
          _ = (0, 0) := by
            rw [map_zero]
            change ((0 : B), (0 : C)) = (0, 0)
            rfl
      exact one_ne_zero (congrArg Prod.fst h')
    have hz1 : z ≠ 1 := by
      intro h
      have h' : ((1, 0) : (B × C)) = (1, 1) := by
        have h'' := congrArg e h
        calc
          (1, 0) = e z := by simp [z]
          _ = e 1 := h''
          _ = (1, 1) := by
            rw [map_one]
            change ((1 : B), (1 : C)) = (1, 1)
            rfl
      exact zero_ne_one (congrArg Prod.snd h')
    exact ⟨z, hz, hz0, hz1⟩
  · rintro ⟨e, he, he0, he1⟩
    have hunit_e : ¬ IsUnit e := by
      intro hunit
      exact he1 ((IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp he)
    have hunit_one_sub : ¬ IsUnit (1 - e) := by
      intro hunit
      have hsub : IsIdempotentElem (1 - e) := he.one_sub
      have heq : 1 - e = 1 :=
        (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp hsub
      apply he0
      calc
        e = 1 - (1 - e) := by abel
        _ = 1 - 1 := by rw [heq]
        _ = 0 := sub_self 1
    let B : CommRingCat := CommRingCat.of (A ⧸ Ideal.span ({e} : Set A))
    let C : CommRingCat := CommRingCat.of (A ⧸ Ideal.span ({1 - e} : Set A))
    have hB : Nontrivial B := by
      change Nontrivial (A ⧸ Ideal.span ({e} : Set A))
      exact Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top hunit_e)
    have hC : Nontrivial C := by
      change Nontrivial (A ⧸ Ideal.span ({1 - e} : Set A))
      exact Ideal.Quotient.nontrivial_iff.mpr
        (Ideal.span_singleton_ne_top hunit_one_sub)
    have hsub : IsIdempotentElem (1 - e) := he.one_sub
    have hsum : e + (1 - e) = 1 := by abel
    have hprod : e * (1 - e) = 0 := by simp [mul_sub, he.eq]
    let q : A →+* (A ⧸ Ideal.span ({e} : Set A)) ×
        (A ⧸ Ideal.span ({1 - e} : Set A)) :=
      (Ideal.Quotient.mk (Ideal.span ({e} : Set A))).prod
        (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A)))
    have hq : Function.Bijective q := by
      exact RingHom.prod_bijective_of_isIdempotentElem he hsub hsum hprod
    refine ⟨B, C, hB, hC, ?_⟩
    change Nonempty (A ≃+* (A ⧸ Ideal.span ({e} : Set A)) ×
      (A ⧸ Ideal.span ({1 - e} : Set A)))
    exact ⟨RingEquiv.ofBijective q hq⟩

/-! ## Lifting idempotents -/

/-- The quotient map on the subtypes of idempotents. -/
def quotientIdempotentMap {A : Type*} [CommRing A] (I : Ideal A) :
    {e : A // IsIdempotentElem e} → {e : A ⧸ I // IsIdempotentElem e} :=
  fun e => ⟨Ideal.Quotient.mk I e.1, e.2.map (Ideal.Quotient.mk I)⟩

/-- Locally nilpotent ideals do not change the set of idempotents. -/
theorem quotient_idempotent_map_bijective {A : Type*} [CommRing A] (I : Ideal A)
    (hI : ∀ x ∈ I, IsNilpotent x) :
    Function.Bijective (quotientIdempotentMap I) := by
  let q : A →+* A ⧸ I := Ideal.Quotient.mk I
  have hker : ∀ x ∈ RingHom.ker q, IsNilpotent x := by
    intro x hx
    apply hI x
    rw [← Ideal.mk_ker (I := I)]
    exact hx
  constructor
  · intro e e' he
    apply Subtype.ext
    apply eq_of_isNilpotent_sub_of_isIdempotentElem e.property e'.property
    apply hker
    rw [RingHom.mem_ker, map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val he)
  · intro e
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective e.1
    have heq : IsIdempotentElem (q x) := by
      rw [hx]
      exact e.2
    obtain ⟨y, hy, hqy⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
      q hker (q x) ⟨x, rfl⟩ heq
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    exact hqy.trans hx

end Formalization.Books.Exercises.Unit01
