import Formalization.Books.Exercises.Unit18.Core

import Formalization.Books.Algebra.Unit105.CatenaryRings
import Formalization.Books.Topology.Unit20.DimensionFunctions
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Localization.Ideal

/-!
# Exercises, Chapter 18: Catenary rings

The declarations below follow the source definition and its four exercises
in order.  Proofs are deferred to the proving stage; the definitions and
interfaces use the canonical quotient, localization, prime-spectrum,
topological catenarity, and dimension-function APIs.
-/

noncomputable section

universe u

namespace Formalization.Books.Exercises.Unit18

private def iicInIciOrderIsoIciInIic
    {α : Type*} [Preorder α] {a b : α} (hab : a ≤ b) :
    Set.Iic (⟨b, hab⟩ : Set.Ici a) ≃o
      Set.Ici (⟨a, hab⟩ : Set.Iic b) where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private def zeroLocusIdealOrderIsoIci
    {A : Type u} [CommRing A] (q : PrimeSpectrum A) :
    PrimeSpectrum.zeroLocus (q.asIdeal : Set A) ≃o Set.Ici q where
  toFun p := ⟨p.1, p.2⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private noncomputable def quotientSpectrumOrderIsoIci
    {A : Type u} [CommRing A] (q : PrimeSpectrum A) :
    PrimeSpectrum (A ⧸ q.asIdeal) ≃o Set.Ici q :=
  q.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus.trans
    (zeroLocusIdealOrderIsoIci q)

private theorem quotientSpectrumOrderIsoIci_quotientPrime
    {A : Type u} [CommRing A]
    (p q : PrimeSpectrum A) (hqp : q ≤ p) :
    quotientSpectrumOrderIsoIci q (quotientPrime p q hqp) =
      (⟨p, hqp⟩ : Set.Ici q) := by
  apply Subtype.ext
  apply PrimeSpectrum.ext
  change (p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).comap
      (Ideal.Quotient.mk q.asIdeal) = p.asIdeal
  rw [Ideal.comap_map_quotientMk, sup_eq_right.mpr
    ((PrimeSpectrum.asIdeal_le_asIdeal q p).mpr hqp)]

private theorem relativeHeight_eq_intervalCoheight
    {A : Type u} [CommRing A]
    (p q : PrimeSpectrum A) (hqp : q ≤ p) :
    relativeHeight p.asIdeal q.asIdeal
        ((PrimeSpectrum.asIdeal_le_asIdeal q p).mpr hqp) =
      Order.coheight (⟨q, hqp⟩ : Set.Iic p) := by
  change (quotientPrime p q hqp).asIdeal.height = _
  rw [PrimeSpectrum.height_eq_orderHeight]
  rw [← Order.height_orderIso (quotientSpectrumOrderIsoIci q)
    (quotientPrime p q hqp)]
  rw [quotientSpectrumOrderIsoIci_quotientPrime p q hqp]
  apply WithBot.coe_injective
  calc
    (Order.height (⟨p, hqp⟩ : Set.Ici q) : WithBot ℕ∞) =
        Order.krullDim (Set.Iic (⟨p, hqp⟩ : Set.Ici q)) :=
      Order.height_eq_krullDim_Iic _
    _ = Order.krullDim (Set.Ici (⟨q, hqp⟩ : Set.Iic p)) :=
      Order.krullDim_eq_of_orderIso (iicInIciOrderIsoIciInIic hqp)
    _ = (Order.coheight (⟨q, hqp⟩ : Set.Iic p) : WithBot ℕ∞) :=
      (Order.coheight_eq_krullDim_Ici _).symm

private theorem relativeHeight_lt_top
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (p q : PrimeSpectrum A) (hqp : q ≤ p) :
    relativeHeight p.asIdeal q.asIdeal
        ((PrimeSpectrum.asIdeal_le_asIdeal q p).mpr hqp) < ⊤ := by
  change (quotientPrime p q hqp).asIdeal.height < ⊤
  exact Ideal.height_lt_top_of_isPrime

private theorem relativeHeight_self
    {A : Type u} [CommRing A] (p : PrimeSpectrum A) :
    relativeHeight p.asIdeal p.asIdeal le_rfl = 0 := by
  rw [relativeHeight_eq_intervalCoheight p p le_rfl]
  exact Order.coheight_top (Set.Iic p)

private theorem irreducibleClosed_le_of_prime_le
    {A : Type u} [CommRing A] {q p : PrimeSpectrum A} (hqp : q ≤ p) :
    OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds A p) ≤
      OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds A q) := by
  let e := PrimeSpectrum.pointsEquivIrreducibleCloseds A
  exact (e.monotone hqp).dual

private noncomputable def primeIntervalOrderIsoIrreducibleClosedIntervalDual
    {A : Type u} [CommRing A]
    (p q : PrimeSpectrum A) (hqp : q ≤ p) :
    Set.Ici (⟨q, hqp⟩ : Set.Iic p) ≃o
      (Set.Ici
        (⟨OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds A p),
            irreducibleClosed_le_of_prime_le (q := q) (p := p) hqp⟩ :
          Set.Iic
            (OrderDual.ofDual
              (PrimeSpectrum.pointsEquivIrreducibleCloseds A q))))ᵒᵈ := by
  let e := PrimeSpectrum.pointsEquivIrreducibleCloseds A
  refine
    { toFun := fun x => OrderDual.toDual
        ⟨⟨OrderDual.ofDual (e x.1.1), ?_⟩, ?_⟩
      invFun := fun x =>
        ⟨⟨e.symm (OrderDual.toDual
            (OrderDual.ofDual x).1.1), ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }
  · exact (e.monotone x.2).dual
  · exact (e.monotone x.1.2).dual
  · change e.symm (OrderDual.toDual (OrderDual.ofDual x).1.1) ≤ p
    calc
      _ ≤ e.symm (e p) := by
        simpa only [OrderDual.toDual_ofDual] using
          e.symm.monotone (OrderDual.ofDual x).2.dual
      _ = p := e.symm_apply_apply p
  · change q ≤ e.symm (OrderDual.toDual (OrderDual.ofDual x).1.1)
    calc
      q = e.symm (e q) := (e.symm_apply_apply q).symm
      _ ≤ _ := by
        simpa only [OrderDual.toDual_ofDual] using
          e.symm.monotone (OrderDual.ofDual x).1.2.dual
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    exact e.symm_apply_apply x.1.1
  · intro x
    apply OrderDual.ofDual.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg OrderDual.ofDual (e.apply_symm_apply
      (OrderDual.toDual (OrderDual.ofDual x).1.1))
  · intro x y
    exact e.le_iff_le

private theorem relativeCodimension_eq_relativeHeight
    {A : Type u} [CommRing A]
    (p q : PrimeSpectrum A) (hqp : q ≤ p) :
    Formalization.Books.Topology.Unit11.relativeCodimension
        (irreducibleClosed_le_of_prime_le (q := q) (p := p) hqp) =
      relativeHeight p.asIdeal q.asIdeal
        ((PrimeSpectrum.asIdeal_le_asIdeal q p).mpr hqp) := by
  unfold Formalization.Books.Topology.Unit11.relativeCodimension
  rw [relativeHeight_eq_intervalCoheight p q hqp]
  let cp : Set.Iic (OrderDual.ofDual
      (PrimeSpectrum.pointsEquivIrreducibleCloseds A q)) :=
    ⟨OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds A p),
      irreducibleClosed_le_of_prime_le (q := q) (p := p) hqp⟩
  let pq : Set.Iic p := ⟨q, hqp⟩
  change Order.coheight cp = Order.coheight pq
  apply WithBot.coe_injective
  calc
    (Order.coheight cp : WithBot ℕ∞) = Order.krullDim (Set.Ici cp) :=
      Order.coheight_eq_krullDim_Ici _
    _ = Order.krullDim ((Set.Ici cp)ᵒᵈ) :=
      Order.krullDim_orderDual.symm
    _ = Order.krullDim (Set.Ici pq) := (Order.krullDim_eq_of_orderIso
      (primeIntervalOrderIsoIrreducibleClosedIntervalDual p q hqp)).symm
    _ = (Order.coheight pq : WithBot ℕ∞) :=
      (Order.coheight_eq_krullDim_Ici _).symm

private theorem relativeCodimension_eq_relativeHeight_comap
    {A : Type u} [CommRing A]
    {Y Y' : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum A)}
    (hYY' : Y ≤ Y') :
    Formalization.Books.Topology.Unit11.relativeCodimension hYY' =
      relativeHeight
        ((PrimeSpectrum.pointsEquivIrreducibleCloseds A).symm
          (OrderDual.toDual Y)).asIdeal
        ((PrimeSpectrum.pointsEquivIrreducibleCloseds A).symm
          (OrderDual.toDual Y')).asIdeal
        ((PrimeSpectrum.asIdeal_le_asIdeal
          ((PrimeSpectrum.pointsEquivIrreducibleCloseds A).symm
            (OrderDual.toDual Y'))
          ((PrimeSpectrum.pointsEquivIrreducibleCloseds A).symm
            (OrderDual.toDual Y))).mpr
          ((PrimeSpectrum.pointsEquivIrreducibleCloseds A).symm.monotone
            (show OrderDual.toDual Y' ≤ OrderDual.toDual Y from hYY'))) := by
  let e := PrimeSpectrum.pointsEquivIrreducibleCloseds A
  let p : PrimeSpectrum A := e.symm (OrderDual.toDual Y)
  let q : PrimeSpectrum A := e.symm (OrderDual.toDual Y')
  have hqp : q ≤ p := e.symm.monotone
    (show OrderDual.toDual Y' ≤ OrderDual.toDual Y from hYY')
  convert relativeCodimension_eq_relativeHeight p q hqp using 1
  all_goals
    simp only [e, p, q, OrderIso.apply_symm_apply, OrderDual.ofDual_toDual]

private theorem isCatenaryRing_iff_topologicalCatenary
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    IsCatenaryRing A ↔
      Formalization.Books.Topology.Unit11.IsCatenary (PrimeSpectrum A) := by
  let e := PrimeSpectrum.pointsEquivIrreducibleCloseds A
  rw [Formalization.Books.Topology.Unit11.isCatenary_iff_finite_and_additive_relativeCodimension]
  constructor
  · intro h
    constructor
    · intro Y Y' hYY'
      let p : PrimeSpectrum A := e.symm (OrderDual.toDual Y)
      let q : PrimeSpectrum A := e.symm (OrderDual.toDual Y')
      have hqp : q ≤ p := e.symm.monotone hYY'.le
      rw [relativeCodimension_eq_relativeHeight_comap hYY'.le]
      exact relativeHeight_lt_top p q hqp
    · intro Y Y' Y'' hYY' hY'Y''
      let p₃ : PrimeSpectrum A := e.symm (OrderDual.toDual Y)
      let p₂ : PrimeSpectrum A := e.symm (OrderDual.toDual Y')
      let p₁ : PrimeSpectrum A := e.symm (OrderDual.toDual Y'')
      have h₁₂ : p₁ ≤ p₂ := e.symm.monotone hY'Y''.le
      have h₂₃ : p₂ ≤ p₃ := e.symm.monotone hYY'.le
      rw [relativeCodimension_eq_relativeHeight_comap,
        relativeCodimension_eq_relativeHeight_comap,
        relativeCodimension_eq_relativeHeight_comap]
      exact h h₁₂ h₂₃
  · rintro ⟨_, hadd⟩ p₁ p₂ p₃ h₁₂ h₂₃
    rcases h₁₂.eq_or_lt with h₁₂eq | h₁₂lt
    · subst p₂
      simp [relativeHeight_self]
    rcases h₂₃.eq_or_lt with h₂₃eq | h₂₃lt
    · subst p₃
      simp [relativeHeight_self]
    · let Y : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum A) :=
        OrderDual.ofDual (e p₃)
      let Y' : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum A) :=
        OrderDual.ofDual (e p₂)
      let Y'' : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum A) :=
        OrderDual.ofDual (e p₁)
      have hYY' : Y < Y' := e.lt_iff_lt.mpr h₂₃lt
      have hY'Y'' : Y' < Y'' := e.lt_iff_lt.mpr h₁₂lt
      have htop := hadd hYY' hY'Y''
      rw [relativeCodimension_eq_relativeHeight_comap,
        relativeCodimension_eq_relativeHeight_comap,
        relativeCodimension_eq_relativeHeight_comap] at htop
      simpa [Y, Y', Y'', e] using htop

private theorem isAlgebraCatenaryRing_iff_algebraUnit105
    (A : Type u) [CommRing A] :
    IsAlgebraCatenaryRing A ↔
      Formalization.Books.Algebra.Unit105.IsCatenaryRing A := by
  constructor
  · intro h p q hpq
    obtain ⟨n, hn, hmax⟩ := h p q hpq.le
    refine ⟨n, hn, ?_⟩
    intro c d hc hd
    exact hmax c d ⟨hc.1, hc.2.1⟩ ⟨hd.1, hd.2.1⟩ hc hd
  · intro h p q hpq
    rcases hpq.eq_or_lt with rfl | hpq
    · refine ⟨0, ?_, ?_⟩
      · intro c hc
        have hlen : c.length = 0 := by
          by_contra hne
          have hpos : 0 < c.length := Nat.pos_of_ne_zero hne
          have hlt : c.head < c.last := c.strictMono (by
            change 0 < c.length
            exact hpos)
          rw [hc.1, hc.2] at hlt
          exact (lt_irrefl _ hlt)
        simp [hlen]
      · intro c d hc hd _ _
        have hc0 : c.length = 0 := by
          by_contra hne
          have hpos : 0 < c.length := Nat.pos_of_ne_zero hne
          have hlt : c.head < c.last := c.strictMono (by
            change 0 < c.length
            exact hpos)
          rw [hc.1, hc.2] at hlt
          exact (lt_irrefl _ hlt)
        have hd0 : d.length = 0 := by
          by_contra hne
          have hpos : 0 < d.length := Nat.pos_of_ne_zero hne
          have hlt : d.head < d.last := d.strictMono (by
            change 0 < d.length
            exact hpos)
          rw [hd.1, hd.2] at hlt
          exact (lt_irrefl _ hlt)
        exact hc0.trans hd0.symm
    · obtain ⟨n, hn, hmax⟩ := h hpq
      refine ⟨n, hn, ?_⟩
      intro c d _ _ hc hd
      exact hmax c d hc hd

private theorem isCohenMacaulayRing_field (k : Type u) [Field k] :
    Formalization.Books.Algebra.Unit104.IsCohenMacaulayRing k := by
  intro p
  have hp : p.asIdeal = (⊥ : Ideal k) := by
    apply le_antisymm
    · intro x hx
      have hx0 : x = 0 := by
        by_contra hx0
        exact p.2.ne_top
          (p.asIdeal.eq_top_of_isUnit_mem hx (isUnit_iff_ne_zero.mpr hx0))
      simp [hx0]
    · exact bot_le
  let _ : Field (Localization.AtPrime p.asIdeal) := IsField.toField <| by
    simp [IsLocalRing.isField_iff_maximalIdeal_eq,
      ← Localization.AtPrime.map_eq_maximalIdeal, hp]
  apply (Formalization.Books.Algebra.Unit104.isCohenMacaulayLocalRing_iff_exists_regularSequence _).2
  refine ⟨[], by simp, ?_, ?_⟩
  · exact RingTheory.Sequence.IsRegular.nil _ _
  · rw [show Ideal.ofList ([] : List (Localization.AtPrime p.asIdeal)) = ⊥ by simp]
    rw [ringKrullDim_eq_of_ringEquiv
      (RingEquiv.quotientBot (Localization.AtPrime p.asIdeal))]
    exact ringKrullDim_eq_zero_of_field _

private theorem algebraUnit105_isCatenaryRing_finiteType_field
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] :
    Formalization.Books.Algebra.Unit105.IsCatenaryRing A := by
  let _ : IsNoetherianRing k := inferInstance
  have hk := Formalization.Books.Algebra.Unit105.isUniversallyCatenary_of_isCohenMacaulayRing k
      (isCohenMacaulayRing_field k)
  exact hk.2 A

/-! ## Definition `catenary` -/

/-
The source's four displayed descriptions of `ht(p / q)` are recorded here.
The first term is the relative height, the second is the dimension of
`Aₚ / qAₚ`, and the last term is the dimension of `(A / q)ₚ₋q`; the middle
notation `(A / q)ₚ` is represented by the same canonical quotient-localized
ring.
-/
theorem relativeHeight_eq_displayed_dimensions
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (p q : PrimeSpectrum A) (hpq : q ≤ p) :
    (relativeHeight p.asIdeal q.asIdeal
        ((PrimeSpectrum.asIdeal_le_asIdeal q p).mpr hpq) : WithBot ℕ∞) =
      ringKrullDim
        (Localization.AtPrime p.asIdeal ⧸
          q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal))) ∧
      ringKrullDim
        (Localization.AtPrime p.asIdeal ⧸
          q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal))) =
        ringKrullDim (Localization.AtPrime (quotientPrime p q hpq).asIdeal) := by
  let P : Ideal (A ⧸ q.asIdeal) := p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)
  have hP : P.IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime
      ((PrimeSpectrum.asIdeal_le_asIdeal q p).mpr hpq)
  let _ : P.IsPrime := hP
  have hPover : P.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change p.asIdeal = (p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).comap
      (Ideal.Quotient.mk q.asIdeal)
    rw [Ideal.comap_map_quotientMk]
    exact (sup_eq_right.mpr ((PrimeSpectrum.asIdeal_le_asIdeal q p).mpr hpq)).symm
  have hsub :
      Algebra.algebraMapSubmonoid (A ⧸ q.asIdeal) p.asIdeal.primeCompl = P.primeCompl := by
    exact Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective
      (p := p.asIdeal) (P := P) Ideal.Quotient.mk_surjective
  have hloc : IsLocalization P.primeCompl
      (Localization.AtPrime p.asIdeal ⧸
        q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal))) := by
    rw [← hsub]
    infer_instance
  let _ : IsLocalization.AtPrime
      (Localization.AtPrime p.asIdeal ⧸
        q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal))) P := hloc
  have hdimC :
      ringKrullDim (Localization.AtPrime p.asIdeal ⧸
        q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal))) =
        (P.height : WithBot ℕ∞) := by
    exact IsLocalization.AtPrime.ringKrullDim_eq_height P
      (Localization.AtPrime p.asIdeal ⧸
        q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal)))
  constructor
  · change (P.height : WithBot ℕ∞) = _
    exact hdimC.symm
  · have hdim := ringKrullDim_eq_of_ringEquiv
      (IsLocalization.algEquiv P.primeCompl
        (Localization.AtPrime p.asIdeal ⧸
          q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal)))
        (Localization.AtPrime P)).toRingEquiv
    change ringKrullDim (Localization.AtPrime p.asIdeal ⧸
        q.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal))) =
      ringKrullDim (Localization.AtPrime P)
    exact hdim

/-! ## Exercise `catenary-the-same` -/

/-- The height-additivity definition agrees with Algebra's chain definition
for Noetherian rings. -/
theorem catenary_iff_algebra_catenary
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    IsCatenaryRing A ↔ IsAlgebraCatenaryRing A := by
  exact (isCatenaryRing_iff_topologicalCatenary A).trans
    ((Formalization.Books.Algebra.Unit105.isCatenaryRing_iff_isCatenary_primeSpectrum A).symm.trans
      (isAlgebraCatenaryRing_iff_algebraUnit105 A).symm)

/-! ## Exercise `Noetherian-local-domain-dim-2-catenary` -/

/-- A Noetherian local domain of Krull dimension two is catenary. -/
theorem noetherian_local_domain_dimension_two_isCatenary
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (hA : ringKrullDim A = (2 : WithBot ℕ∞)) :
    IsCatenaryRing A := by
  sorry

/-! ## Exercise `finite-type-over-field-catenary` -/

/-- Every finite-type algebra over a field is catenary. -/
theorem finite_type_algebra_over_field_isCatenary
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] :
    IsCatenaryRing A := by
  let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  exact (catenary_iff_algebra_catenary A).2
    ((isAlgebraCatenaryRing_iff_algebraUnit105 A).2
      (algebraUnit105_isCatenaryRing_finiteType_field k A))

/-! ## Exercise `example-no-dim-function` -/

/-
The source writes the second dimension-function condition using an
intermediate point whenever the integer-valued function drops by at least
two.  The established `Topology.Unit20.IsDimensionFunction` uses the
equivalent immediate-specialization/equality-by-one formulation, so the
existence statement below reuses that canonical predicate.
-/
/-- There is a finite sober catenary space with no dimension function. -/
theorem exists_finite_sober_catenary_space_without_dimension_function :
    ∃ (X : Type u) (inst : TopologicalSpace X),
      @IsFiniteSoberCatenarySpace X inst ∧
        ¬ ∃ δ : X → ℤ,
          @Formalization.Books.Topology.Unit20.IsDimensionFunction X inst δ := by
  sorry

end Formalization.Books.Exercises.Unit18
