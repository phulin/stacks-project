import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

set_option maxHeartbeats 20000000

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
open scoped TensorProduct ModuleCat.Algebra

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
  let R : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℕ → ZMod 2)
  refine ⟨R, ?_, ?_⟩
  · change ∀ I : Ideal (ULift.{u} ℕ → ZMod 2), I.FG →
      Module.FinitePresentation (ULift.{u} ℕ → ZMod 2) I
    intro I hI
    have hpoint : ∀ x : ULift.{u} ℕ → ZMod 2, IsIdempotentElem x := by
      intro x
      funext n
      let i : Fin 2 := (ZMod.finEquiv 2).symm (x n)
      have hi : ZMod.finEquiv 2 i = x n :=
        (ZMod.finEquiv 2).apply_symm_apply _
      change x n * x n = x n
      rw [← hi]
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with h | h
      · rw [h]
        simp
      · rw [h]
        simp
    have hIdem : IsIdempotentElem I := by
      rw [IsIdempotentElem]
      apply le_antisymm
      · exact Ideal.mul_le.mpr fun x hx y hy => I.mul_mem_left x hy
      · intro x hx
        convert Ideal.mul_mem_mul hx hx using 1
        exact (hpoint x).eq.symm
    obtain ⟨e, he, hIe⟩ := (I.isIdempotentElem_iff_of_fg hI).mp hIdem
    subst I
    change Module.FinitePresentation (ULift.{u} ℕ → ZMod 2)
      ((ULift.{u} ℕ → ZMod 2) ∙ e)
    have hspan : ((ULift.{u} ℕ → ZMod 2) ∙ e).FG := by
      exact hI
    let i : (ULift.{u} ℕ → ZMod 2) ∙ e →ₗ[ULift.{u} ℕ → ZMod 2]
        (ULift.{u} ℕ → ZMod 2) :=
      ((ULift.{u} ℕ → ZMod 2) ∙ e).subtype
    let p : (ULift.{u} ℕ → ZMod 2) →ₗ[ULift.{u} ℕ → ZMod 2]
        (ULift.{u} ℕ → ZMod 2) ∙ e :=
      { toFun := fun x =>
          ⟨x * e, Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩⟩
        map_add' := by
          intro x y
          apply Subtype.ext
          simp [add_mul]
        map_smul' := by
          intro r x
          apply Subtype.ext
          simp [smul_eq_mul, mul_assoc] }
    have hp : p.comp i = LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rcases Ideal.mem_span_singleton'.mp x.property with ⟨a, ha⟩
      change (x : ULift.{u} ℕ → ZMod 2) * e = (x : ULift.{u} ℕ → ZMod 2)
      rw [← ha, mul_assoc, he.eq]
    have hfinite : Module.Finite (ULift.{u} ℕ → ZMod 2)
        ((ULift.{u} ℕ → ZMod 2) ∙ e) :=
      Module.Finite.of_fg_top ((Submodule.fg_top _).mpr hspan)
    have hprojective : Module.Projective (ULift.{u} ℕ → ZMod 2)
        ((ULift.{u} ℕ → ZMod 2) ∙ e) :=
      Module.Projective.of_split i p hp
    exact @Module.finitePresentation_of_projective
      (ULift.{u} ℕ → ZMod 2) ((ULift.{u} ℕ → ZMod 2) ∙ e)
      _ _ _ hprojective hfinite
  · intro hN
    let K : Ideal (ULift.{u} ℕ → ZMod 2) :=
      { carrier := {x | (Function.support x).Finite}
        zero_mem' := by simp
        add_mem' := by
          intro x y hx hy
          apply (hx.union hy).subset
          intro n hn
          by_contra hzero
          have hxzero : x n = 0 := by
            by_contra hxzero
            exact hzero (Or.inl hxzero)
          have hyzero : y n = 0 := by
            by_contra hyzero
            exact hzero (Or.inr hyzero)
          simp [hxzero, hyzero] at hn
        smul_mem' := by
          intro r x hx
          exact hx.subset (Function.support_smul_subset_right r x) }
    let d : ℕ → (ULift.{u} ℕ → ZMod 2) := fun n m =>
      if m.down = n then 1 else 0
    have hd : ∀ n : ℕ, d n ∈ K := by
      intro n
      apply Set.Finite.subset (Set.finite_singleton (ULift.up n))
      intro m hm
      have hm' : m.down = n := by
        simpa [d, Function.mem_support] using hm
      exact Set.mem_singleton_iff.mpr (ULift.ext m (ULift.up n) hm')
    have hK : K.FG := (isNoetherianRing_iff_ideal_fg _).mp hN K
    obtain ⟨s, hs⟩ := hK
    have hsK : ∀ x ∈ s, x ∈ K := by
      intro x hx
      rw [← hs]
      exact Ideal.subset_span hx
    let T : Set (ULift.{u} ℕ) :=
      ⋃ x ∈ (s : Set (ULift.{u} ℕ → ZMod 2)), Function.support x
    have hT : T.Finite := by
      dsimp [T]
      apply Set.Finite.biUnion s.finite_toSet
      intro x hx
      exact hsK x hx
    obtain ⟨m, hm⟩ := hT.exists_notMem
    let n : ℕ := m.down
    have hs0 : ∀ x ∈ s, x m = 0 := by
      intro x hx
      by_contra hzero
      apply hm
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hzero⟩⟩
    let ev : (ULift.{u} ℕ → ZMod 2) →+* ZMod 2 :=
      Pi.evalRingHom (fun _ : ULift.{u} ℕ => ZMod 2) m
    have hker : Ideal.span (s : Set (ULift.{u} ℕ → ZMod 2)) ≤ RingHom.ker ev := by
      rw [Ideal.span_le]
      intro x hx
      exact RingHom.mem_ker.mpr (hs0 x hx)
    have hds : d n ∈ Ideal.span (s : Set (ULift.{u} ℕ → ZMod 2)) := by
      rw [hs]
      exact hd n
    have hz : ev (d n) = 0 := RingHom.mem_ker.mp (hker hds)
    have hone : ev (d n) = 1 := by
      simp [ev, d, n]
    rw [hone] at hz
    exact one_ne_zero hz

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

private theorem cotangent_atPrime_map_injective
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsMaximal] [p.IsPrime] :
    ∃ c : p.Cotangent →ₗ[R]
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)).Cotangent,
      Function.Injective c ∧
        ∀ x : p, c (p.toCotangent x) =
          (IsLocalRing.maximalIdeal (Localization.AtPrime p)).toCotangent
            ⟨algebraMap R (Localization.AtPrime p) x, by
              rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p
                (Localization.AtPrime p)]
              exact Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime p)) x.2⟩ := by
  let L := Localization.AtPrime p
  have hpmap : Ideal.map (algebraMap R L) p = IsLocalRing.maximalIdeal L :=
    IsLocalization.AtPrime.map_eq_maximalIdeal p L
  let c : p.Cotangent →ₗ[R] (IsLocalRing.maximalIdeal L).Cotangent :=
    Ideal.mapCotangent (R := R) (A := R) (B := L) p
      (IsLocalRing.maximalIdeal L) (Algebra.ofId R L) (by
        rw [← hpmap]
        exact Ideal.le_comap_map)
  refine ⟨c, ?_, ?_⟩
  intro x y hxy
  obtain ⟨x, rfl⟩ := p.toCotangent_surjective x
  obtain ⟨y, rfl⟩ := p.toCotangent_surjective y
  rw [Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent] at hxy
  have hxy' : algebraMap R L ((x : R) - (y : R)) ∈
      (IsLocalRing.maximalIdeal L) ^ 2 :=
    by
      simpa only [Algebra.ofId_apply, map_sub] using
        (Ideal.toCotangent_eq (IsLocalRing.maximalIdeal L)).mp hxy
  have hxy'' : (x : R) - (y : R) ∈ p ^ 2 := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal_pow p L 2, Ideal.mem_under]
    exact hxy'
  exact (Ideal.toCotangent_eq p).mpr hxy''
  · intro x
    exact Ideal.mapCotangent_toCotangent _ _ _ _ _

/-- The six-variable quadratic quotient is not a polynomial ring in five variables. -/
theorem sixVariableQuadratic_quotient_not_mvPolynomial_five
    {k : Type*} [Field k] :
    ¬ Nonempty
      ((MvPolynomial (Fin 6) k ⧸ Ideal.span {sixVariableQuadratic k}) ≃+*
        MvPolynomial (Fin 5) k) := by
  classical
  rintro ⟨e⟩
  let P := MvPolynomial (Fin 6) k
  let I : Ideal P := Ideal.span {sixVariableQuadratic k}
  let Q := P ⧸ I
  let φP : P →+* k := MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)
  let φQ : Q →+* k := Ideal.Quotient.lift I φP (by
    intro x hx
    change φP x = 0
    change x ∈ Ideal.span {sixVariableQuadratic k} at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with rfl
      change φP (MvPolynomial.X 0 * MvPolynomial.X 1 +
        MvPolynomial.X 2 * MvPolynomial.X 3 +
        MvPolynomial.X 4 * MvPolynomial.X 5) = 0
      rw [map_add, map_add, map_mul, map_mul, map_mul,
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      simp
    · exact map_zero φP
    · intro x y hx hy hxy hyy
      rw [map_add, hxy, hyy, add_zero]
    · intro a x hx hxy
      change φP (a * x) = 0
      rw [map_mul, hxy, mul_zero])
  let m : Ideal Q := RingHom.ker φQ
  letI : Algebra P k := φP.toAlgebra
  have hφC : φP.comp (MvPolynomial.C : k →+* P) = RingHom.id k := by
    exact MvPolynomial.eval₂Hom_comp_C _ _
  letI : IsScalarTower k P k :=
    IsScalarTower.of_algebraMap_eq' (by
      ext r
      change (RingHom.id k) r = φP (MvPolynomial.C r)
      exact (congrArg (fun h : k →+* k => h r) hφC).symm)
  let D : Fin 6 → Derivation k P k :=
    fun i => MvPolynomial.mkDerivation k (fun j => if i = j then 1 else 0)
  have hDX (i j : Fin 6) :
      D i (MvPolynomial.X j) = if i = j then 1 else 0 := by
    dsimp [D]
    rw [MvPolynomial.mkDerivation_X]
  have hD : ∀ i : Fin 6, D i (sixVariableQuadratic k) = 0 := by
    intro i
    change D i (MvPolynomial.X 0 * MvPolynomial.X 1 +
        MvPolynomial.X 2 * MvPolynomial.X 3 +
        MvPolynomial.X 4 * MvPolynomial.X 5) = 0
    rw [map_add, map_add, Derivation.leibniz, Derivation.leibniz, Derivation.leibniz,
      hDX i 0, hDX i 1, hDX i 2, hDX i 3, hDX i 4, hDX i 5]
    simp only [Algebra.smul_def]
    change φP (MvPolynomial.X 0) * (if i = 1 then 1 else 0) +
      φP (MvPolynomial.X 1) * (if i = 0 then 1 else 0) +
      (φP (MvPolynomial.X 2) * (if i = 3 then 1 else 0) +
        φP (MvPolynomial.X 3) * (if i = 2 then 1 else 0)) +
      (φP (MvPolynomial.X 4) * (if i = 5 then 1 else 0) +
        φP (MvPolynomial.X 5) * (if i = 4 then 1 else 0)) = 0
    dsimp [φP]
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
    simp
  have hIφ : ∀ x : P, x ∈ I → φP x = 0 := by
    intro x hx
    change x ∈ Ideal.span {sixVariableQuadratic k} at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with rfl
      change φP (MvPolynomial.X 0 * MvPolynomial.X 1 +
        MvPolynomial.X 2 * MvPolynomial.X 3 +
        MvPolynomial.X 4 * MvPolynomial.X 5) = 0
      rw [map_add, map_add, map_mul, map_mul, map_mul,
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      simp
    · exact map_zero φP
    · intro x y hx hy hxy hyy
      rw [map_add, hxy, hyy, add_zero]
    · intro a x hx hxy
      change φP (a * x) = 0
      rw [map_mul, hxy, mul_zero]
  have hIker (i : Fin 6) : I.restrictScalars k ≤ LinearMap.ker (D i).toLinearMap := by
    intro x hx
    change D i x = 0
    change x ∈ I.restrictScalars k at hx
    change x ∈ Ideal.span {sixVariableQuadratic k} at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with rfl
      exact hD i
    · exact (D i).map_zero
    · intro x y hx hy hxy hyy
      rw [map_add, hxy, hyy, add_zero]
    · intro a x hx hxy
      rw [smul_eq_mul, Derivation.leibniz, hxy]
      simp only [Algebra.smul_def, map_zero, zero_add]
      have hxI : x ∈ I := hx
      change φP a * 0 + φP x * (D i) a = 0
      rw [hIφ x hxI]
      simp
  let lD : Fin 6 → Q →ₗ[k] k :=
    fun i => (I.restrictScalars k).liftQ (D i).toLinearMap (hIker i)
  have hlD_mk (i : Fin 6) (x : P) : lD i (Ideal.Quotient.mk I x) = D i x := rfl
  have hlD_leibniz (i : Fin 6) (x y : Q) :
      lD i (x * y) = φQ x * lD i y + φQ y * lD i x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change D i (x * y) = φP x * D i y + φP y * D i x
    rw [Derivation.leibniz]
    simp only [Algebra.smul_def]
    change φP x * D i y + φP y * D i x = φP x * D i y + φP y * D i x
    rfl
  let li : Fin 6 → m →ₗ[k] k := fun i =>
    { toFun := fun x => lD i x.1
      map_add' := by intro x y; exact map_add (lD i) x.1 y.1
      map_smul' := by intro a x; exact map_smul (lD i) a x.1 }
  have hli_prod (i : Fin 6) (x y : m) : li i (x * y) = 0 := by
    rw [show li i (x * y) = lD i (x.1 * y.1) by rfl, hlD_leibniz]
    have hx : φQ x.1 = 0 := RingHom.mem_ker.mp x.2
    have hy : φQ y.1 = 0 := RingHom.mem_ker.mp y.2
    simp [hx, hy]
  let ci : Fin 6 → m.Cotangent →ₗ[k] k := fun i =>
    Ideal.Cotangent.lift (li i) (hli_prod i)
  let xi : Fin 6 → m := fun j =>
    ⟨Ideal.Quotient.mk I (MvPolynomial.X j), by
      apply RingHom.mem_ker.mpr
      change φP (MvPolynomial.X j) = 0
      dsimp [φP]
      rw [MvPolynomial.eval₂Hom_X']
      ⟩
  have hci (i j : Fin 6) :
      ci i (m.toCotangent (xi j)) = if i = j then 1 else 0 := by
    rw [Ideal.Cotangent.lift_toCotangent]
    exact hlD_mk i (MvPolynomial.X j) |>.trans (hDX i j)
  have hli_independent :
      LinearIndependent k (fun j => m.toCotangent (xi j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hgi := congrArg (ci i) hg
    simpa [map_sum, hci] using hgi
  have hφQ_alg : φQ.comp (algebraMap k Q) = RingHom.id k := by
    ext r
    change φP (MvPolynomial.C r) = r
    exact congrArg (fun h : k →+* k => h r) hφC
  have hφQ_surj : Function.Surjective φQ := by
    intro r
    refine ⟨Ideal.Quotient.mk I (MvPolynomial.C r), ?_⟩
    change φP (MvPolynomial.C r) = r
    exact congrArg (fun h : k →+* k => h r) hφC
  have hmmax : m.IsMaximal := RingHom.ker_isMaximal_of_surjective φQ hφQ_surj
  letI : m.IsMaximal := hmmax
  letI : m.IsPrime := hmmax.isPrime
  have hfin_bounds :
      6 ≤ Module.finrank k m.Cotangent ∧
        Module.finrank k m.Cotangent ≤ m.spanFinrank := by
    obtain ⟨s, hs_card, hs_span⟩ :=
      Submodule.FG.exists_span_finset_card_eq_spanFinrank
        (IsNoetherian.noetherian m)
    let v : s → m.Cotangent := fun x =>
      m.toCotangent ⟨x.1, by
        rw [← hs_span]
        exact Ideal.subset_span x.2⟩
    have hvspan : Submodule.span k (Set.range v) = ⊤ := by
      apply top_unique
      intro z hz
      obtain ⟨x, rfl⟩ := m.toCotangent_surjective z
      have hx : x.1 ∈ Ideal.span (s : Set Q) := by
        change x.1 ∈ Submodule.span Q (s : Set Q)
        rw [hs_span]
        exact x.2
      let p : ∀ q : Q, q ∈ Ideal.span (s : Set Q) → Prop := fun q hq =>
        m.toCotangent ⟨q, by
          rw [← hs_span]
          exact hq⟩ ∈ Submodule.span k (Set.range v)
      have hp : p x.1 hx := by
        refine Submodule.span_induction (p := p) ?_ ?_ ?_ ?_ hx
        · intro q hq
          have hmem : v ⟨q, hq⟩ ∈ Set.range v := ⟨⟨q, hq⟩, rfl⟩
          simpa [p, v] using
            (Submodule.subset_span hmem :
              v ⟨q, hq⟩ ∈ Submodule.span k (Set.range v))
        · simpa [p] using
            (show m.toCotangent ⟨0, by
              rw [← hs_span]
              exact Submodule.zero_mem _⟩ ∈
              Submodule.span k (Set.range v) from
              Submodule.zero_mem (Submodule.span k (Set.range v)))
        · intro q r hq hr hq' hr'
          dsimp [p] at hq' hr' ⊢
          have hmap :
              m.toCotangent ⟨q + r, by
                rw [← hs_span]
                exact add_mem hq hr⟩ =
                m.toCotangent ⟨q, by
                  rw [← hs_span]
                  exact hq⟩ +
                  m.toCotangent ⟨r, by
                    rw [← hs_span]
                    exact hr⟩ := by
            change m.toCotangent ((⟨q, by
              rw [← hs_span]
              exact hq⟩ : m) + ⟨r, by
                rw [← hs_span]
                exact hr⟩) = _
            rw [map_add]
          rw [hmap]
          exact add_mem hq' hr'
        · intro a q hq hq'
          have ha : a - algebraMap k Q (φQ a) ∈ m := by
            apply RingHom.mem_ker.mpr
            change φQ (a - algebraMap k Q (φQ a)) = 0
            rw [map_sub]
            have hqa := congrArg (fun h : k →+* k => h (φQ a)) hφQ_alg
            exact sub_eq_zero.mpr (by
              simpa only [RingHom.comp_apply, RingHom.id_apply] using hqa.symm)
          let y : m.Cotangent := m.toCotangent ⟨q, by
            rw [← hs_span]
            exact hq⟩
          have hy := Ideal.Cotangent.smul_eq_zero_of_mem ha y
          have hscalar : a • y = (φQ a) • y := by
            apply sub_eq_zero.mp
            calc
              a • y - (φQ a) • y =
                  a • y - algebraMap k Q (φQ a) • y := by
                exact congrArg (fun z => a • y - z)
                  (IsScalarTower.algebraMap_smul Q (φQ a) y).symm
              _ = (a - algebraMap k Q (φQ a)) • y :=
                (sub_smul a (algebraMap k Q (φQ a)) y).symm
              _ = 0 := hy
          dsimp [p] at hq' ⊢
          have hmap :
              m.toCotangent ⟨a * q, by
                rw [← hs_span]
                exact Ideal.mul_mem_left _ _ hq⟩ =
                a • m.toCotangent ⟨q, by
                  rw [← hs_span]
                  exact hq⟩ := by
            change m.toCotangent (a • (⟨q, by
              rw [← hs_span]
              exact hq⟩ : m)) = _
            rw [map_smul]
          rw [hmap]
          have hscalar' : a • m.toCotangent ⟨q, by
              rw [← hs_span]
              exact hq⟩ = (φQ a) • m.toCotangent ⟨q, by
                rw [← hs_span]
                exact hq⟩ := by
            simpa [y] using hscalar
          rw [hscalar']
          exact Submodule.smul_mem (Submodule.span k (Set.range v)) (φQ a) hq'
      simpa [p] using hp
    let fcomb : (s →₀ k) →ₗ[k] m.Cotangent := Finsupp.linearCombination k v
    have hfcomb : Function.Surjective fcomb := by
      rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
      exact hvspan
    letI : Module.Finite k m.Cotangent :=
      Module.Finite.of_surjective fcomb hfcomb
    constructor
    · simpa using hli_independent.fintype_card_le_finrank
    · simpa [hs_card] using
        (finrank_le_of_span_eq_top (R := k) (M := m.Cotangent)
          (v := v) hvspan)
  have hfin_ge := hfin_bounds.1
  have hfin_m_le := hfin_bounds.2
  have hm_ge : 6 ≤ m.spanFinrank := hfin_ge.trans hfin_m_le
  let L := Localization.AtPrime m
  obtain ⟨c, hc, hc_to⟩ := cotangent_atPrime_map_injective m
  let eQk : (Q ⧸ m) ≃+* k :=
    RingHom.quotientKerEquivOfSurjective hφQ_surj
  let eK : k ≃+* IsLocalRing.ResidueField L :=
    eQk.symm.trans (IsLocalization.AtPrime.equivQuotMaximalIdeal m L)
  letI : Algebra L (IsLocalRing.ResidueField L) :=
    IsLocalRing.ResidueField.algebra (R₀ := L) L
  have heK_alg (a : k) :
      eK a = Ideal.Quotient.mk (IsLocalRing.maximalIdeal L) (algebraMap k L a) := by
    have ha : φQ (algebraMap k Q a) = a := by
      simpa only [RingHom.comp_apply, RingHom.id_apply] using
        congrArg (fun h : k →+* k => h a) hφQ_alg
    change IsLocalization.AtPrime.equivQuotMaximalIdeal m L (eQk.symm a) = _
    rw [show eQk.symm a = eQk.symm (φQ (algebraMap k Q a)) by rw [ha]]
    rw [show eQk.symm (φQ (algebraMap k Q a)) =
      Ideal.Quotient.mk m (algebraMap k Q a) by
        exact RingHom.quotientKerEquivOfSurjective_symm_apply hφQ_surj _]
    rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
    rfl
  have hc_scalars (r : IsLocalRing.ResidueField L) (x : m.Cotangent) :
      c ((eK.symm r) • x) = r • c x := by
    obtain ⟨x, rfl⟩ := m.toCotangent_surjective x
    let a : k := eK.symm r
    have hxL : algebraMap Q L (x : Q) ∈ IsLocalRing.maximalIdeal L := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m L]
      exact Ideal.mem_map_of_mem (algebraMap Q L) x.2
    have hsource : a • m.toCotangent (⟨x, x.2⟩ : m) =
        algebraMap k Q a • m.toCotangent (⟨x, x.2⟩ : m) := by
      exact (IsScalarTower.algebraMap_smul Q a
        (m.toCotangent (⟨x, x.2⟩ : m))).symm
    have har : r = Ideal.Quotient.mk (IsLocalRing.maximalIdeal L)
        (algebraMap k L a) := by
      rw [← heK_alg a]
      exact (eK.apply_symm_apply r).symm
    calc
      c (a • m.toCotangent (⟨x, x.2⟩ : m)) =
          c (algebraMap k Q a • m.toCotangent (⟨x, x.2⟩ : m)) := by rw [hsource]
      _ = algebraMap k Q a • c (m.toCotangent (⟨x, x.2⟩ : m)) := by
        exact map_smul c (algebraMap k Q a) _
      _ = algebraMap k Q a •
          (IsLocalRing.maximalIdeal L).toCotangent
            ⟨algebraMap Q L (x : Q), hxL⟩ := by
        rw [hc_to]
      _ = algebraMap Q L (algebraMap k Q a) •
          (IsLocalRing.maximalIdeal L).toCotangent
            ⟨algebraMap Q L (x : Q), hxL⟩ := by
        exact (IsScalarTower.algebraMap_smul L _ _).symm
      _ = algebraMap k L a •
          (IsLocalRing.maximalIdeal L).toCotangent
            ⟨algebraMap Q L (x : Q), hxL⟩ := by
        rw [IsScalarTower.algebraMap_eq k Q L, RingHom.comp_apply]
      _ = (algebraMap L (IsLocalRing.ResidueField L) (algebraMap k L a)) •
          (IsLocalRing.maximalIdeal L).toCotangent
            ⟨algebraMap Q L (x : Q), hxL⟩ := by
        exact (IsScalarTower.algebraMap_smul L _ _).symm
      _ = r • c (m.toCotangent (⟨x, x.2⟩ : m)) := by
        rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_def, har, hc_to]
  have hlindependent : LinearIndependent
      (IsLocalRing.ResidueField L)
      (fun j => c (m.toCotangent (xi j))) := by
    apply hli_independent.map_of_injective_injective
      (eK.symm : IsLocalRing.ResidueField L →+* k) c.toAddMonoidHom
    · intro r hr
      apply eK.symm.injective
      simpa using hr
    · intro z hz
      exact hc (by simpa using hz)
    · intro r x
      exact hc_scalars r x
  letI : IsRegularRing Q := IsRegularRing.of_ringEquiv e.symm
  letI : IsRegularLocalRing L :=
    IsRegularRing.isRegularLocalRing_localization m
  have hreg := (IsRegularLocalRing.iff_finrank_cotangentSpace L).mp
    (inferInstance : IsRegularLocalRing L)
  have hdimL : ringKrullDim L ≤ 5 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m L]
    calc
      m.height ≤ ringKrullDim Q := Ideal.height_le_ringKrullDim_of_ne_top hmmax.ne_top
      _ = ringKrullDim (MvPolynomial (Fin 5) k) := ringKrullDim_eq_of_ringEquiv e
      _ = 5 := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
          ringKrullDim_eq_zero_of_field]
        norm_num
  have hfinL : 6 ≤ Module.finrank (IsLocalRing.ResidueField L)
      (IsLocalRing.CotangentSpace L) := by
    simpa using hlindependent.fintype_card_le_finrank
  have hfin_upper :
      (Module.finrank (IsLocalRing.ResidueField L)
        (IsLocalRing.CotangentSpace L) : WithBot ℕ∞) ≤ 5 := by
    rw [hreg]
    exact hdimL
  have hfin_upper_nat : Module.finrank (IsLocalRing.ResidueField L)
      (IsLocalRing.CotangentSpace L) ≤ 5 := by
    exact_mod_cast hfin_upper
  omega

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
/-
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
  let A₀ := ULift.{u} ℤ
  letI : IsNoetherianRing A₀ :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv : A₀ ≃+* ℤ).symm
  letI : IsDomain A₀ :=
    (ULift.ringEquiv : A₀ ≃+* ℤ).toMulEquiv.isDomain ℤ
  let L2 := Localization.Away (2 : A₀)
  let L3 := Localization.Away (3 : A₀)
  let B₀ := L2 × L3
  letI : Algebra A₀ L2 := by
    dsimp [L2]
    infer_instance
  letI : Algebra A₀ L3 := by
    dsimp [L3]
    infer_instance
  letI : Module A₀ L2 := Algebra.toModule
  letI : Module A₀ L3 := Algebra.toModule
  letI : Algebra A₀ B₀ := Prod.algebra A₀ L2 L3
  letI : Module A₀ B₀ := Algebra.toModule
  have hflatB : Module.Flat A₀ B₀ := by
    rw [Module.Flat.iff_lTensor_injectiveₛ]
    intro P _ _ N
    have hflat2 : Module.Flat A₀ L2 := by
      dsimp [L2]
      exact IsLocalization.flat (Localization.Away (2 : A₀))
        (Submonoid.powers (2 : A₀))
    have hflat3 : Module.Flat A₀ L3 := by
      dsimp [L3]
      exact IsLocalization.flat (Localization.Away (3 : A₀))
        (Submonoid.powers (3 : A₀))
    let eN : B₀ ⊗[A₀] N ≃ₗ[A₀] (L2 ⊗[A₀] N) × (L3 ⊗[A₀] N) :=
      TensorProduct.prodLeft A₀ A₀ L2 L3 N
    let eP : B₀ ⊗[A₀] P ≃ₗ[A₀] (L2 ⊗[A₀] P) × (L3 ⊗[A₀] P) :=
      TensorProduct.prodLeft A₀ A₀ L2 L3 P
    have hcomm : eP.toLinearMap.comp (N.subtype.lTensor B₀) =
        ((N.subtype.lTensor L2).prodMap (N.subtype.lTensor L3)).comp eN.toLinearMap := by
      apply LinearMap.ext
      intro z
      refine TensorProduct.induction_on z ?_ (fun x y => ?_) (fun x y hx hy => ?_)
      · simp only [map_zero]
      · rfl
      · simp only [map_add, hx, hy]
    intro x y hxy
    apply eN.injective
    have hxy' := congrArg eP hxy
    change (eP.toLinearMap.comp (N.subtype.lTensor B₀)) x =
      (eP.toLinearMap.comp (N.subtype.lTensor B₀)) y at hxy'
    rw [hcomm] at hxy'
    apply Prod.ext
    · apply (Module.Flat.iff_lTensor_injectiveₛ.mp hflat2 N)
      exact congrArg Prod.fst hxy'
    · apply (Module.Flat.iff_lTensor_injectiveₛ.mp hflat3 N)
      exact congrArg Prod.snd hxy'
  let f₀ : A₀ →+* B₀ :=
    (algebraMap A₀ L2).prod (algebraMap A₀ L3)
  have hflat₀ : f₀.Flat := by
    have hf₀ : f₀ = algebraMap A₀ B₀ := by
      ext x
      · rfl
      · change algebraMap A₀ L3 x = algebraMap A₀ L3 x
        rfl
    rw [hf₀, RingHom.flat_algebraMap_iff]
    exact hflatB
  have hcomap₀ : Function.Surjective (PrimeSpectrum.comap f₀) := by
    intro p
    by_cases hp2 : (2 : A₀) ∉ p.asIdeal
    · have hrange : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A₀ L2)) := by
        rw [PrimeSpectrum.localization_comap_range L2 (Submonoid.powers (2 : A₀))]
        exact (Ideal.disjoint_powers_iff_notMem_of_isPrime (2 : A₀)).mpr hp2
      obtain ⟨q, hq⟩ := hrange
      let r : PrimeSpectrum B₀ :=
        ⟨Ideal.prod q.asIdeal ⊤, Ideal.isPrime_ideal_prod_top⟩
      refine ⟨r, ?_⟩
      apply PrimeSpectrum.ext_iff.mpr
      rw [PrimeSpectrum.comap_asIdeal]
      ext z
      dsimp [r]
      have hqz : algebraMap A₀ L2 z ∈ q.asIdeal ↔ z ∈ p.asIdeal := by
        have hz := congrArg (fun t : PrimeSpectrum A₀ => z ∈ t.asIdeal) hq
        simpa [PrimeSpectrum.comap_asIdeal] using hz
      rw [Ideal.mem_comap, Ideal.mem_prod]
      change (algebraMap A₀ L2 z ∈ q.asIdeal ∧
        algebraMap A₀ L3 z ∈ (⊤ : Ideal L3)) ↔ z ∈ p.asIdeal
      simpa using hqz
    · have hp2' : (2 : A₀) ∈ p.asIdeal := by
        exact not_not.mp hp2
      have hp3 : (3 : A₀) ∉ p.asIdeal := by
        intro h3
        apply p.isPrime.one_notMem
        have h := p.asIdeal.sub_mem h3 hp2'
        norm_num at h ⊢
        exact h
      have hrange : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A₀ L3)) := by
        rw [PrimeSpectrum.localization_comap_range L3 (Submonoid.powers (3 : A₀))]
        exact (Ideal.disjoint_powers_iff_notMem_of_isPrime (3 : A₀)).mpr hp3
      obtain ⟨q, hq⟩ := hrange
      let r : PrimeSpectrum B₀ :=
        ⟨Ideal.prod ⊤ q.asIdeal, Ideal.isPrime_ideal_prod_top'⟩
      refine ⟨r, ?_⟩
      apply PrimeSpectrum.ext_iff.mpr
      rw [PrimeSpectrum.comap_asIdeal]
      ext z
      dsimp [r]
      have hqz : algebraMap A₀ L3 z ∈ q.asIdeal ↔ z ∈ p.asIdeal := by
        have hz := congrArg (fun t : PrimeSpectrum A₀ => z ∈ t.asIdeal) hq
        simpa [PrimeSpectrum.comap_asIdeal] using hz
      rw [Ideal.mem_comap, Ideal.mem_prod]
      change (algebraMap A₀ L2 z ∈ (⊤ : Ideal L2) ∧
        algebraMap A₀ L3 z ∈ q.asIdeal) ↔ z ∈ p.asIdeal
      simpa using hqz
  have hff₀ : f₀.FaithfullyFlat := by
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    exact ⟨hflat₀, hcomap₀⟩
  let i : A₀ →ₗ[A₀] B₀ := Algebra.linearMap A₀ B₀
  let C₀ := B₀ ⧸ LinearMap.range i
  letI : Module A₀ C₀ := Submodule.Quotient.module (LinearMap.range i)
  let q : B₀ →ₗ[A₀] C₀ := (LinearMap.range i).mkQ
  have hcomp : q.comp i = 0 := by
    apply LinearMap.ext
    intro x
    dsimp [q]
    change (LinearMap.range i).mkQ (i x) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact ⟨x, rfl⟩
  have hf₀ : f₀ = algebraMap A₀ B₀ := by
    ext x
    · rfl
    · change algebraMap A₀ L3 x = algebraMap A₀ L3 x
      rfl
  have hi : Function.Injective i := by
    intro x y hxy
    apply RingHom.FaithfullyFlat.injective hff₀
    simpa [i, hf₀] using hxy
  have hqsurj : Function.Surjective q := by
    simpa [q] using (Submodule.mkQ_surjective (LinearMap.range i))
  have hexact : Function.Exact i q := by
    intro x
    constructor
    · intro hx
      dsimp [q] at hx
      change (LinearMap.range i).mkQ x = 0 at hx
      exact (Submodule.Quotient.mk_eq_zero _).mp hx
    · rintro ⟨y, rfl⟩
      exact LinearMap.congr_fun hcomp y
  let A : CommRingCat.{u} := CommRingCat.of A₀
  let B : CommRingCat.{u} := CommRingCat.of B₀
  let f : A ⟶ B := CommRingCat.ofHom f₀
  let S₀ : ShortComplex (ModuleCat.{u} A) :=
    ShortComplex.moduleCatMk i q hcomp
  have hS₀ : S₀.ShortExact := ModuleCat.shortComplex_shortExact S₀ hexact hi hqsurj
  have hnonsplit₀ : ¬ Nonempty S₀.Splitting := by
    rintro ⟨s⟩
    dsimp [S₀, ShortComplex.moduleCatMk] at s
    have hret := ModuleCat.hom_ext_iff.mp s.f_r
    have hret1 := LinearMap.congr_fun hret (1 : A₀)
    change s.r.hom (i 1) = (1 : A₀) at hret1
    let a : A₀ := s.r.hom ((1 : L2), (0 : L3))
    let b : A₀ := s.r.hom ((0 : L2), (1 : L3))
    have hsum : a + b = 1 := by
      have hunit : (1 : B₀) = ((1 : L2), (1 : L3)) := by
        ext <;> simp
      have hret1' := hret1
      change s.r.hom (algebraMap A₀ B₀ 1) = (1 : A₀) at hret1'
      rw [map_one, hunit] at hret1'
      have hpair : ((1 : L2), (1 : L3)) =
          ((1 : L2), (0 : L3)) + ((0 : L2), (1 : L3)) := by
        ext <;> simp
      have hmapadd := s.r.hom.map_add
        ((1 : L2), (0 : L3)) ((0 : L2), (1 : L3))
      have hret1'' := hret1'
      rw [hpair] at hret1''
      change s.r.hom ((1 : L2), (0 : L3)) +
        s.r.hom ((0 : L2), (1 : L3)) = (1 : A₀)
      rw [← hmapadd]
      exact hret1''
    have ha_div (n : ℕ) : (2 : A₀) ^ n ∣ a := by
      letI : SMul A₀ B₀ := (inferInstance : Module A₀ B₀).toSMul
      letI : SMul A₀ A₀ := (inferInstance : Module A₀ A₀).toSMul
      have hu : IsUnit ((algebraMap A₀ L2 (2 : A₀)) ^ n) :=
        IsLocalization.Away.algebraMap_pow_isUnit (S := L2) (x := (2 : A₀)) n
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      let z : B₀ := (y, 0)
      have hz : (2 : A₀) ^ n • z = ((1 : L2), (0 : L3)) := by
        dsimp [z]
        rw [Algebra.smul_def]
        change
          (algebraMap A₀ L2 ((2 : A₀) ^ n) * y,
            algebraMap A₀ L3 ((2 : A₀) ^ n) * 0) = (1, 0)
        congr 1
        · rw [map_pow]
          exact hy
        · simp
      refine ⟨s.r.hom z, ?_⟩
      dsimp [a]
      rw [← hz, s.r.hom.map_smul, Algebra.smul_def]
      simp [A]
    have hb_div (n : ℕ) : (3 : A₀) ^ n ∣ b := by
      letI : SMul A₀ B₀ := (inferInstance : Module A₀ B₀).toSMul
      letI : SMul A₀ A₀ := (inferInstance : Module A₀ A₀).toSMul
      have hu : IsUnit ((algebraMap A₀ L3 (3 : A₀)) ^ n) :=
        IsLocalization.Away.algebraMap_pow_isUnit (S := L3) (x := (3 : A₀)) n
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      let z : B₀ := (0, y)
      have hz : (3 : A₀) ^ n • z = ((0 : L2), (1 : L3)) := by
        dsimp [z]
        rw [Algebra.smul_def]
        change
          (algebraMap A₀ L2 ((3 : A₀) ^ n) * 0,
            algebraMap A₀ L3 ((3 : A₀) ^ n) * y) = (0, 1)
        congr 1
        · simp
        · rw [map_pow]
          exact hy
      refine ⟨s.r.hom z, ?_⟩
      dsimp [b]
      rw [← hz, s.r.hom.map_smul, Algebra.smul_def]
      simp [A]
    have ha_zero : a = 0 := by
      let I : Ideal A₀ := Ideal.span {(2 : A₀)}
      have hI : I ≠ ⊤ := by
        apply Ideal.span_singleton_ne_top
        intro hu
        have hu' : IsUnit (2 : ℤ) :=
          IsUnit.map (ULift.ringEquiv : A₀ ≃+* ℤ).toRingHom hu
        norm_num [Int.isUnit_iff_abs_eq] at hu'
      have haI : a ∈ ⨅ n : ℕ, I ^ n := by
        rw [Ideal.mem_iInf]
        intro n
        rw [show I = Ideal.span {(2 : A₀)} by rfl,
          Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        exact ha_div n
      rw [Ideal.iInf_pow_eq_bot_of_isDomain I hI] at haI
      simpa using haI
    have hb_zero : b = 0 := by
      let I : Ideal A₀ := Ideal.span {(3 : A₀)}
      have hI : I ≠ ⊤ := by
        apply Ideal.span_singleton_ne_top
        intro hu
        have hu' : IsUnit (3 : ℤ) :=
          IsUnit.map (ULift.ringEquiv : A₀ ≃+* ℤ).toRingHom hu
        norm_num [Int.isUnit_iff_abs_eq] at hu'
      have hbI : b ∈ ⨅ n : ℕ, I ^ n := by
        rw [Ideal.mem_iInf]
        intro n
        rw [show I = Ideal.span {(3 : A₀)} by rfl,
          Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        exact hb_div n
      rw [Ideal.iInf_pow_eq_bot_of_isDomain I hI] at hbI
      simpa using hbI
    rw [ha_zero, hb_zero] at hsum
    exact zero_ne_one hsum
  let U_A := ModuleCat.uliftFunctor.{u_1, u, u} A₀
  let S : ShortComplex (ModuleCat.{max u u_1} A) := S₀.map U_A
  have hS : S.ShortExact := hS₀.map_of_exact U_A
  have hmap : (S.map (ModuleCat.extendScalars f.hom)).ShortExact := by
    letI : Algebra A₀ B₀ := f₀.toAlgebra
    letI : Module A₀ B₀ := Module.compHom B₀ f₀
    letI : Module.Flat A₀ B₀ := hflat₀
    have hexact' : Function.Exact S.f.hom S.g.hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
    have hinj' : Function.Injective S.f.hom :=
      (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
    have hsurj' : Function.Surjective S.g.hom :=
      (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
    apply ModuleCat.shortComplex_shortExact _
    · dsimp [S, f, A, B, ShortComplex.map, ModuleCat.extendScalars,
        ModuleCat.ExtendScalars.map', ModuleCat.ExtendScalars.obj']
      change Function.Exact (LinearMap.baseChange B₀ S.f.hom)
        (LinearMap.baseChange B₀ S.g.hom)
      exact Module.Flat.lTensor_exact B₀ hexact'
    · dsimp [S, f, A, B, ShortComplex.map, ModuleCat.extendScalars,
        ModuleCat.ExtendScalars.map', ModuleCat.ExtendScalars.obj']
      change Function.Injective (LinearMap.baseChange B₀ S.f.hom)
      exact Module.Flat.lTensor_preserves_injective_linearMap S.f.hom hinj'
    · dsimp [S, f, A, B, ShortComplex.map, ModuleCat.extendScalars,
        ModuleCat.ExtendScalars.map', ModuleCat.ExtendScalars.obj']
      change Function.Surjective (LinearMap.baseChange B₀ S.g.hom)
      exact LinearMap.baseChange_surjective B₀ hsurj'
  have hnonsplit : ¬ Nonempty S.Splitting := by
    rintro ⟨s⟩
    apply hnonsplit₀
    let FF := ModuleCat.fullyFaithfulUliftFunctor.{u, u, u_1} A₀
    let r : S₀.X₂ ⟶ S₀.X₁ := FF.preimage s.r
    let t : S₀.X₃ ⟶ S₀.X₂ := FF.preimage s.s
    have hr : U_A.map r = s.r := by
      exact FF.map_preimage s.r
    have ht : U_A.map t = s.s := by
      exact FF.map_preimage s.s
    refine ⟨{ r := r, s := t, f_r := ?_, s_g := ?_, id := ?_ }⟩
    · apply FF.map_injective
      simp only [Functor.map_comp]
      rw [hr]
      change (S₀.map U_A).f ≫ s.r = 𝟙 _
      exact s.f_r
    · apply FF.map_injective
      simp only [Functor.map_comp]
      rw [ht]
      change s.s ≫ (S₀.map U_A).g = 𝟙 _
      exact s.s_g
    · apply FF.map_injective
      simp only [Functor.map_add, Functor.map_comp]
      rw [hr, ht]
      change s.r ≫ (S₀.map U_A).f + (S₀.map U_A).g ≫ s.s = 𝟙 _
      exact s.id
  let T := S.map (ModuleCat.extendScalars f.hom)
  let r₁ : T.X₂ →ₗ[B] T.X₁ := by
    dsimp [T, S, U_A, f, A, B, ShortComplex.map, ModuleCat.extendScalars,
      ModuleCat.ExtendScalars.map', ModuleCat.ExtendScalars.obj']
    letI : Algebra A₀ B₀ := f₀.toAlgebra
    let M := (ModuleCat.restrictScalars f₀).obj (ModuleCat.of B₀ B₀)
    let N := (ModuleCat.uliftFunctor.{u_1, u, u} A₀).obj S₀.X₂
    let P := (ModuleCat.uliftFunctor.{u_1, u, u} A₀).obj S₀.X₁
    letI : Module B₀ M := (inferInstance : Module B₀ B₀)
    letI : Module A₀ M := M.isModule
    letI : SMul A₀ M := M.isModule.toSMul
    let htower : @IsScalarTower A₀ B₀ M
        (inferInstance : SMul A₀ B₀)
        (inferInstance : Module B₀ M).toSMul M.isModule.toSMul := {
      smul_assoc := by
        intro a b x
        rw [Algebra.smul_def, ModuleCat.restrictScalars.smul_def, ← hf₀]
        exact mul_smul _ _ _ }
    letI : @IsScalarTower A₀ B₀ M
        (inferInstance : SMul A₀ B₀)
        (inferInstance : Module B₀ M).toSMul M.isModule.toSMul := htower
    let hcomm : @SMulCommClass A₀ B₀ M
        M.isModule.toSMul (inferInstance : Module B₀ M).toSMul :=
      ModuleCat.sMulCommClass_mk f₀ (ModuleCat.of B₀ B₀)
    letI : Module B₀ (M ⊗[A₀] N) :=
      @TensorProduct.leftModule A₀ B₀ _ _ M N _ _ _ _ _ hcomm
    letI : Module B₀ (M ⊗[A₀] P) :=
      @TensorProduct.leftModule A₀ B₀ _ _ M P _ _ _ _ _ hcomm
    let hcommP : @SMulCommClass A₀ B₀ (M ⊗[A₀] P)
        (inferInstance : Module A₀ (M ⊗[A₀] P)).toSMul
        (inferInstance : Module B₀ (M ⊗[A₀] P)).toSMul := {
      smul_comm := by
        intro a b z
        refine TensorProduct.induction_on z ?_ (fun m p => ?_) (fun x y hx hy => ?_)
        · simp
        · change (a • (b • m)) ⊗ₜ[A₀] p = (b • (a • m)) ⊗ₜ[A₀] p
          exact congrArg (fun t => t ⊗ₜ[A₀] p) (hcomm.smul_comm a b m)
        · rw [TensorProduct.smul_add, TensorProduct.smul_add]
          simp only [hx, hy, smul_add] }
    letI : @SMulCommClass A₀ B₀ (M ⊗[A₀] P)
        (inferInstance : Module A₀ (M ⊗[A₀] P)).toSMul
        (inferInstance : Module B₀ (M ⊗[A₀] P)).toSMul := hcommP
    let htowerP : @IsScalarTower A₀ B₀ (M ⊗[A₀] P)
        (inferInstance : SMul A₀ B₀)
        (inferInstance : Module B₀ (M ⊗[A₀] P)).toSMul
        (inferInstance : Module A₀ (M ⊗[A₀] P)).toSMul := by
      constructor
      intro a b z
      refine TensorProduct.induction_on z ?_ (fun m p => ?_) (fun x y hx hy => ?_)
      · simp
      · change ((a • b) • m) ⊗ₜ[A₀] p = (a • (b • m)) ⊗ₜ[A₀] p
        rw [IsScalarTower.smul_assoc]
      · rw [TensorProduct.smul_add, TensorProduct.smul_add, hx, hy, smul_add]
    letI : @IsScalarTower A₀ B₀ (M ⊗[A₀] P)
        (inferInstance : SMul A₀ B₀)
        (inferInstance : Module B₀ (M ⊗[A₀] P)).toSMul
        (inferInstance : Module A₀ (M ⊗[A₀] P)).toSMul := htowerP
    change (M ⊗[A₀] N) →ₗ[B₀] (M ⊗[A₀] P)
    exact TensorProduct.AlgebraTensorModule.lift
      { toFun := fun b =>
          { toFun := fun x => ((b : B₀) * x.down) ⊗ₜ[A₀] ULift.up (1 : A₀)
            map_add' := by
              intro x y
              change (b * (x.down + y.down)) ⊗ₜ[A₀] ULift.up (1 : A₀) = _
              rw [mul_add, TensorProduct.add_tmul]
            map_smul' := by
              intro a x
              simp [Algebra.smul_def, TensorProduct.smul_tmul', mul_assoc,
                mul_comm] }
        map_add' := by
          intro b c
          apply LinearMap.ext
          intro x
          change ((b + c) * x.down) ⊗ₜ[A₀] ULift.up (1 : A₀) =
            (b * x.down) ⊗ₜ[A₀] ULift.up (1 : A₀) +
              (c * x.down) ⊗ₜ[A₀] ULift.up (1 : A₀)
          rw [add_mul, TensorProduct.add_tmul]
        map_smul' := by
          intro c b
          apply LinearMap.ext
          intro x
          simp [TensorProduct.smul_tmul', mul_assoc] }
  have hr₁ : r₁.comp T.f.hom = LinearMap.id := by
    apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ (fun b x => ?_) (fun x y hx hy => ?_)
    · simp
    · dsimp [r₁, T, S, U_A, f, A, B, ShortComplex.map, ModuleCat.extendScalars,
        ModuleCat.ExtendScalars.map', ModuleCat.ExtendScalars.obj']
      change (b * algebraMap A₀ B₀ x.down) ⊗ₜ[A₀] ULift.up (1 : A₀) =
        b ⊗ₜ[A₀] x
      apply (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl B₀ B₀)
        ULift.moduleEquiv).injective
      apply (TensorProduct.AlgebraTensorModule.rid A₀ B₀ B₀).injective
      simp [Algebra.smul_def, mul_comm]
    · simp only [map_add, hx, hy]
  have hsplit : Nonempty T.Splitting := by
    let r : T.X₂ ⟶ T.X₁ := ModuleCat.ofHom r₁
    have hfr : T.f ≫ r = 𝟙 T.X₁ := by
      apply ModuleCat.hom_ext
      simpa [r] using hr₁
    exact ⟨ShortComplex.Splitting.ofExactOfRetraction T hmap.exact r hfr hmap.epi_g⟩
  refine ⟨A, B, f, S, hS, hnonsplit, ?_⟩
  refine ⟨?_, hmap, ?_⟩
  · simpa [f] using hff₀
  · simpa [T] using hsplit
-/

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
