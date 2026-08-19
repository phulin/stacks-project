import Formalization.Books.MoreAlgebra.Unit05.FibreProductsOfRingsI
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# More on Algebra, Chapter 6: Fibre products of rings, II

The source fixes a pullback of commutative rings
`B → A ← A'` with `A' → A` surjective.  The ring pullback and its
projections are Mathlib's canonical `RingHom.pullback` construction.  For
modules, the category of triples and the compatible-pair pullback are the
canonical `ModuleGluingCategory` and `moduleFiberProduct` constructions from
the preceding chapter.
-/

namespace Formalization.Books.MoreAlgebra.Unit06

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Formalization.Books.MoreAlgebra.Unit05

universe u

noncomputable section

/-! ## The fibre-product situation -/

/-- The ring maps and surjectivity hypothesis in the source's situation. -/
structure FibreProductSituation (A A' B : Type u)
    [CommRing A] [CommRing A'] [CommRing B] where
  /-- The map `B → A`. -/
  toA : B →+* A
  /-- The surjective map `A' → A`. -/
  fromA' : A' →+* A
  /-- Surjectivity of `A' → A`. -/
  fromA'_surjective : Function.Surjective fromA'

/-- The kernel `I = ker(A' → A)` in the source's situation. -/
abbrev fibreProductIdeal
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) : Ideal A' :=
  RingHom.ker D.fromA'

/-- The ring `B' = B ×_A A'`, using Mathlib's canonical pullback subring. -/
abbrev fibreProductRing
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) : Type u :=
  RingHom.pullback D.toA D.fromA'

/-- The projection `B' → B`. -/
abbrev fibreProductToB
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) : fibreProductRing D →+* B :=
  RingHom.pullbackFst D.toA D.fromA'

/-- The projection `B' → A'`. -/
abbrev fibreProductToA'
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) : fibreProductRing D →+* A' :=
  RingHom.pullbackSnd D.toA D.fromA'

/-- The commutative square of rings attached to the source's situation. -/
def fibreProductRingSquare
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    RingSquare A A' B (fibreProductRing D) where
  t := D.fromA'
  s := D.toA
  u := fibreProductToB D
  v := fibreProductToA' D
  comm := RingHom.pullback_comm_sq D.toA D.fromA'

/-- The square defining `B'` is cartesian in `CommRingCat`. -/
theorem fibreProduct_isPullback
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    IsPullback
      (CommRingCat.ofHom (fibreProductToB D))
      (CommRingCat.ofHom (fibreProductToA' D))
      (CommRingCat.ofHom D.toA)
      (CommRingCat.ofHom D.fromA') := by
  exact IsPullback.of_isLimit
    (CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom D.toA)
      (CommRingCat.ofHom D.fromA'))

/-- The projection `B' → B` is surjective because `A' → A` is surjective. -/
theorem fibreProduct_toB_surjective
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Function.Surjective (fibreProductToB D) := by
  exact RingHom.surjective_pullbackFst_of_surjective D.toA D.fromA'
    D.fromA'_surjective

/-- The kernel of `B' → B` maps onto the kernel `I` of `A' → A`. -/
theorem fibreProduct_kernel_map
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Ideal.map (fibreProductToA' D) (RingHom.ker (fibreProductToB D)) =
      fibreProductIdeal D := by
  simpa [fibreProductIdeal] using
    (RingHom.map_pullbackSnd_ker_pullbackFst_eq D.toA D.fromA')

/-- The map on kernel elements induced by the projection `B' → A'`. -/
def fibreProduct_kernel_to_ideal
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    (RingHom.ker (fibreProductToB D) : Type u) →
      (fibreProductIdeal D : Type u) :=
  fun x => ⟨fibreProductToA' D x, by
    change D.fromA' (fibreProductToA' D x) = 0
    have hx : fibreProductToB D x = 0 := by
      simpa only [RingHom.mem_ker] using x.property
    have hcomm : D.toA (fibreProductToB D (x : fibreProductRing D)) =
        D.fromA' (fibreProductToA' D (x : fibreProductRing D)) :=
      DFunLike.congr_fun (RingHom.pullback_comm_sq D.toA D.fromA')
        (x : fibreProductRing D)
    rw [← hcomm]
    simp [hx]
  ⟩

/-- The source's assertion that the induced kernel map is bijective. -/
theorem fibreProduct_kernel_equiv_exists
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Nonempty
      {e : (RingHom.ker (fibreProductToB D) : Type u) ≃
          (fibreProductIdeal D : Type u) //
        ∀ x, e x = fibreProduct_kernel_to_ideal D x} := by
  let f := fibreProduct_kernel_to_ideal D
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · have hx : fibreProductToB D x = 0 := by
          simpa only [RingHom.mem_ker] using x.property
        have hy : fibreProductToB D y = 0 := by
          simpa only [RingHom.mem_ker] using y.property
        change ((x : fibreProductRing D).1).1 = ((y : fibreProductRing D).1).1
        simpa [fibreProductToB] using hx.trans hy.symm
      · simpa [f, fibreProduct_kernel_to_ideal, fibreProductToA'] using
          congrArg Subtype.val hxy
    · intro z
      rcases z with ⟨a', ha'⟩
      let x : (RingHom.ker (fibreProductToB D) : Type u) := by
        refine ⟨⟨(0, a'), ?_⟩, ?_⟩
        · change D.toA (0 : B) = D.fromA' a'
          simpa [fibreProductIdeal, RingHom.mem_ker] using ha'.symm
        · change (0 : B) = 0
          rfl
      refine ⟨x, ?_⟩
      apply Subtype.ext
      rfl
  exact ⟨⟨Equiv.ofBijective f hf, fun x => rfl⟩⟩

/-- A chosen equivalence for the induced map on kernel elements. -/
noncomputable def fibreProduct_kernel_equiv
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    (RingHom.ker (fibreProductToB D) : Type u) ≃
      (fibreProductIdeal D : Type u) :=
  (Classical.choice (fibreProduct_kernel_equiv_exists D)).1

theorem fibreProduct_kernel_equiv_apply
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) (x : RingHom.ker (fibreProductToB D)) :
    fibreProduct_kernel_equiv D x = fibreProduct_kernel_to_ideal D x :=
  (Classical.choice (fibreProduct_kernel_equiv_exists D)).2 x

/-- On spectra, the ring pullback square is a pushout square of topological
spaces.  `Spec.topMap` is Mathlib's canonical contravariant spectrum map. -/
theorem fibreProduct_spectrum_isPushout
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    IsPushout
      (Spec.topMap (CommRingCat.ofHom D.toA))
      (Spec.topMap (CommRingCat.ofHom D.fromA'))
      (Spec.topMap (CommRingCat.ofHom (fibreProductToB D)))
      (Spec.topMap (CommRingCat.ofHom (fibreProductToA' D))) := by
  have hpull :
      @CategoryTheory.IsPullback (Type u) _
        (PrimeSpectrum A) (PrimeSpectrum B) (PrimeSpectrum A') (PrimeSpectrum (fibreProductRing D))
        (↾PrimeSpectrum.comap D.toA)
        (↾PrimeSpectrum.comap D.fromA')
        (↾PrimeSpectrum.comap (fibreProductToB D))
        (↾PrimeSpectrum.comap (fibreProductToA' D)) := by
    rw [CategoryTheory.Limits.Types.isPullback_iff]
    constructor
    · apply ConcreteCategory.hom_ext
      intro x
      change PrimeSpectrum.comap (fibreProductToB D)
          (PrimeSpectrum.comap D.toA x) =
        PrimeSpectrum.comap (fibreProductToA' D)
          (PrimeSpectrum.comap D.fromA' x)
      rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
      rw [RingHom.pullback_comm_sq D.toA D.fromA']
    constructor
    · intro x y hxy
      apply PrimeSpectrum.ext
      apply Ideal.comap_injective_of_surjective D.fromA' D.fromA'_surjective
      exact congrArg PrimeSpectrum.asIdeal hxy.2
    · intro p q hpq
      have hpq' :
          PrimeSpectrum.comap (fibreProductToB D) p =
            PrimeSpectrum.comap (fibreProductToA' D) q := by
        simpa using hpq
      have hker : RingHom.ker D.fromA' ≤ q.asIdeal := by
        intro k hk
        let z : fibreProductRing D := ⟨(0, k), by
          change D.toA (0 : B) = D.fromA' k
          simpa only [map_zero, RingHom.mem_ker] using hk.symm⟩
        have hz : z ∈ (PrimeSpectrum.comap (fibreProductToB D) p).asIdeal := by
          change fibreProductToB D z ∈ p.asIdeal
          simp [z]
        have hmem := congrArg (fun P : PrimeSpectrum (fibreProductRing D) => z ∈ P.asIdeal) hpq'
        rw [hmem] at hz
        change fibreProductToA' D z ∈ q.asIdeal at hz
        simpa [z] using hz
      let x : PrimeSpectrum A :=
        ⟨q.asIdeal.map D.fromA',
          Ideal.map_isPrime_of_surjective D.fromA'_surjective hker⟩
      have hxq : PrimeSpectrum.comap D.fromA' x = q := by
        apply PrimeSpectrum.ext
        change (q.asIdeal.map D.fromA').comap D.fromA' = q.asIdeal
        rw [Ideal.comap_map_of_surjective D.fromA' D.fromA'_surjective,
          ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
      have hcomp :
          PrimeSpectrum.comap (fibreProductToB D)
              (PrimeSpectrum.comap D.toA x) =
            PrimeSpectrum.comap (fibreProductToA' D) q := by
        apply PrimeSpectrum.ext
        apply Ideal.ext
        intro z
        constructor
        · intro hz
          change D.toA (fibreProductToB D z) ∈ x.asIdeal at hz
          rw [Ideal.mem_map_iff_of_surjective D.fromA' D.fromA'_surjective] at hz
          rcases hz with ⟨a', ha', ha'eq⟩
          change fibreProductToA' D z ∈ q.asIdeal
          have hdiff : fibreProductToA' D z - a' ∈ RingHom.ker D.fromA' := by
            change D.fromA' (fibreProductToA' D z - a') = 0
            have hzcomp : D.fromA' (fibreProductToA' D z) =
                D.toA (fibreProductToB D z) := z.property.symm
            rw [map_sub, hzcomp, ha'eq]
            abel
          have hsum := q.asIdeal.add_mem (hker hdiff) ha'
          simpa only [sub_add_cancel] using hsum
        · intro hz
          change fibreProductToA' D z ∈ q.asIdeal at hz
          change D.toA (fibreProductToB D z) ∈ x.asIdeal
          rw [Ideal.mem_map_iff_of_surjective D.fromA' D.fromA'_surjective]
          exact ⟨fibreProductToA' D z, hz, (z.property).symm⟩
      have hxp : PrimeSpectrum.comap D.toA x = p :=
        (PrimeSpectrum.comap_injective_of_surjective (fibreProductToB D)
          (fibreProduct_toB_surjective D)) (hcomp.trans hpq'.symm)
      exact Exists.intro x (And.intro hxp hxq)
  have hrange :
      ∀ p : PrimeSpectrum (fibreProductRing D),
        ¬ RingHom.ker (fibreProductToB D) ≤ p.asIdeal →
          p ∈ Set.range (PrimeSpectrum.comap (fibreProductToA' D)) := by
    intro p hp
    apply (PrimeSpectrum.mem_range_comap_iff (fibreProductToA' D)).2
    apply le_antisymm
    · intro z hz
      change fibreProductToA' D z ∈ p.asIdeal.map (fibreProductToA' D) at hz
      have hw_exists : ∃ w, w ∈ RingHom.ker (fibreProductToB D) ∧
          w ∉ p.asIdeal := by
        by_contra h
        apply hp
        intro w hw
        by_contra hwne
        exact h ⟨w, hw, hwne⟩
      obtain ⟨w, hw, hwne⟩ := hw_exists
      have hwB : fibreProductToB D w = 0 := by
        simpa only [RingHom.mem_ker] using hw
      have hwA : D.fromA' (fibreProductToA' D w) = 0 := by
        have hcomm := DFunLike.congr_fun
          (RingHom.pullback_comm_sq D.toA D.fromA') w
        change D.toA (fibreProductToB D w) =
          D.fromA' (fibreProductToA' D w) at hcomm
        rw [hwB] at hcomm
        simpa using hcomm.symm
      let h := fibreProductToA' D w
      have hh : D.fromA' h = 0 := hwA
      let zh : A' → fibreProductRing D := fun c =>
        ⟨(0, h * c), by
          change D.toA (0 : B) = D.fromA' (h * c)
          simp [hh]⟩
      have hmul : ∀ a' ∈ p.asIdeal.map (fibreProductToA' D), ∀ c : A',
          zh (c * a') ∈ p.asIdeal := by
        intro a' ha'
        refine Submodule.span_induction (p := fun a' _ => ∀ c : A',
          zh (c * a') ∈ p.asIdeal) ?_ ?_ ?_ ?_ ha'
        · rintro _ ⟨w', hw', rfl⟩ c
          have hprod := p.asIdeal.mul_mem_left (zh c) hw'
          have heq : zh (c * fibreProductToA' D w') = zh c * w' := by
            rcases w' with ⟨⟨b', a'⟩, h'⟩
            apply Subtype.ext
            apply Prod.ext
            · change (0 : B) = 0 * b'
              simp
            · change h * (c * a') = (h * c) * a'
              rw [mul_assoc]
          rw [heq]
          exact hprod
        · intro c
          have heq : zh (c * 0) = 0 := by
            apply Subtype.ext
            apply Prod.ext
            · simp [zh]
            · change h * (c * 0) = 0
              simp
          rw [heq]
          exact p.asIdeal.zero_mem
        · intro a b _ _ ha hb c
          have heq : zh (c * (a + b)) = zh (c * a) + zh (c * b) := by
            apply Subtype.ext
            apply Prod.ext
            · change (0 : B) = 0 + 0
              simp
            · change h * (c * (a + b)) = h * (c * a) + h * (c * b)
              ring
          rw [heq]
          exact p.asIdeal.add_mem (ha c) (hb c)
        · intro c a _ ha d
          simpa only [smul_eq_mul, mul_assoc] using ha (d * c)
      have hprod : w * z ∈ p.asIdeal := by
        have hm := hmul (fibreProductToA' D z) hz 1
        have hw_eq : w = zh 1 := by
          apply Subtype.ext
          apply Prod.ext
          · simpa [zh, fibreProductToB] using hwB
          · simp [zh, h]
        rw [hw_eq]
        convert hm using 1
        apply Subtype.ext
        apply Prod.ext <;> simp [zh, fibreProductToA']
      exact (p.2.mem_or_mem hprod).resolve_left hwne
    · exact Ideal.le_comap_map
  have hjoint :
      Set.range (↾PrimeSpectrum.comap (fibreProductToB D)) ⊔
          Set.range (↾PrimeSpectrum.comap (fibreProductToA' D)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    by_cases hp : RingHom.ker (fibreProductToB D) ≤ p.asIdeal
    · left
      change p ∈ Set.range (PrimeSpectrum.comap (fibreProductToB D))
      rw [range_comap_of_surjective B (fibreProductToB D)
        (fibreProduct_toB_surjective D)]
      exact hp
    · right
      exact hrange p hp
  have hoff :
      ∀ (x y : PrimeSpectrum A')
        (hx : x ∉ Set.range (↾PrimeSpectrum.comap D.fromA'))
        (hy : y ∉ Set.range (↾PrimeSpectrum.comap D.fromA')),
        (↾PrimeSpectrum.comap (fibreProductToA' D)) x =
            (↾PrimeSpectrum.comap (fibreProductToA' D)) y → x = y := by
    intro x y hx hy hxy
    change x ∉ Set.range (PrimeSpectrum.comap D.fromA') at hx
    change y ∉ Set.range (PrimeSpectrum.comap D.fromA') at hy
    have hnotx : ¬ RingHom.ker D.fromA' ≤ x.asIdeal := by
      intro h
      apply hx
      rw [range_comap_of_surjective A D.fromA'
        D.fromA'_surjective]
      exact h
    have hnoty : ¬ RingHom.ker D.fromA' ≤ y.asIdeal := by
      intro h
      apply hy
      rw [range_comap_of_surjective A D.fromA'
        D.fromA'_surjective]
      exact h
    have hwx : ∃ w, w ∈ RingHom.ker D.fromA' ∧ w ∉ x.asIdeal := by
      by_contra h
      apply hnotx
      intro w hw
      by_contra hwn
      exact h ⟨w, hw, hwn⟩
    obtain ⟨w, hw, hwx⟩ := hwx
    have hxy' :
        PrimeSpectrum.comap (fibreProductToA' D) x =
          PrimeSpectrum.comap (fibreProductToA' D) y := by
      simpa using hxy
    have hwy : w ∉ y.asIdeal := by
      intro hwy
      apply hwx
      let z : fibreProductRing D := ⟨(0, w), by
        change D.toA (0 : B) = D.fromA' w
        simpa only [map_zero, RingHom.mem_ker] using hw.symm⟩
      have hz : z ∈ (PrimeSpectrum.comap (fibreProductToA' D) y).asIdeal := by
        change fibreProductToA' D z ∈ y.asIdeal
        simpa [z] using hwy
      have hz' : z ∈ (PrimeSpectrum.comap (fibreProductToA' D) x).asIdeal := by
        change z ∈ (PrimeSpectrum.comap (fibreProductToA' D) y).asIdeal at hz
        have hmem := congrArg
          (fun P : PrimeSpectrum (fibreProductRing D) => z ∈ P.asIdeal) hxy'
        exact hmem.mpr hz
      change fibreProductToA' D z ∈ x.asIdeal at hz'
      simpa [z] using hz'
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro a'
    constructor
    · intro ha'
      let z : fibreProductRing D := ⟨(0, w * a'), by
        change D.toA (0 : B) = D.fromA' (w * a')
        have hw0 : D.fromA' w = 0 := by
          simpa only [RingHom.mem_ker] using hw
        simp [hw0]⟩
      have hz : z ∈ (PrimeSpectrum.comap (fibreProductToA' D) x).asIdeal := by
        change fibreProductToA' D z ∈ x.asIdeal
        simpa [z] using x.asIdeal.mul_mem_left w ha'
      have hz' : z ∈ (PrimeSpectrum.comap (fibreProductToA' D) y).asIdeal := by
        change z ∈ (PrimeSpectrum.comap (fibreProductToA' D) x).asIdeal at hz
        have hmem := congrArg
          (fun P : PrimeSpectrum (fibreProductRing D) => z ∈ P.asIdeal) hxy'
        exact hmem.mp hz
      change fibreProductToA' D z ∈ y.asIdeal at hz'
      have hmul : w * a' ∈ y.asIdeal := by simpa [z] using hz'
      exact (y.2.mem_or_mem hmul).resolve_left hwy
    · intro ha'
      have hwy_exists : ∃ w, w ∈ RingHom.ker D.fromA' ∧ w ∉ y.asIdeal := by
        by_contra h
        apply hnoty
        intro w hw
        by_contra hwn
        exact h ⟨w, hw, hwn⟩
      obtain ⟨w, hw, hwy⟩ := hwy_exists
      let z : fibreProductRing D := ⟨(0, w), by
        change D.toA (0 : B) = D.fromA' w
        simpa only [map_zero, RingHom.mem_ker] using hw.symm⟩
      have hwx : w ∉ x.asIdeal := by
        intro hwx
        apply hwy
        have hz : z ∈ (PrimeSpectrum.comap (fibreProductToA' D) x).asIdeal := by
          change fibreProductToA' D z ∈ x.asIdeal
          simpa [z] using hwx
        have hz' : z ∈ (PrimeSpectrum.comap (fibreProductToA' D) y).asIdeal := by
          change z ∈ (PrimeSpectrum.comap (fibreProductToA' D) x).asIdeal at hz
          have hmem := congrArg
            (fun P : PrimeSpectrum (fibreProductRing D) => z ∈ P.asIdeal) hxy'
          exact hmem.mp hz
        change fibreProductToA' D z ∈ y.asIdeal at hz'
        simpa [z] using hz'
      let z' : fibreProductRing D := ⟨(0, w * a'), by
        change D.toA (0 : B) = D.fromA' (w * a')
        have hw0 : D.fromA' w = 0 := by
          simpa only [RingHom.mem_ker] using hw
        simp [hw0]⟩
      have hz : z' ∈ (PrimeSpectrum.comap (fibreProductToA' D) y).asIdeal := by
        change fibreProductToA' D z' ∈ y.asIdeal
        simpa [z'] using y.asIdeal.mul_mem_left w ha'
      have hz' : z' ∈ (PrimeSpectrum.comap (fibreProductToA' D) x).asIdeal := by
        change z' ∈ (PrimeSpectrum.comap (fibreProductToA' D) y).asIdeal at hz
        have hmem := congrArg
          (fun P : PrimeSpectrum (fibreProductRing D) => z' ∈ P.asIdeal) hxy'
        exact hmem.mpr hz
      change fibreProductToA' D z' ∈ x.asIdeal at hz'
      have hmul : w * a' ∈ x.asIdeal := by simpa [z'] using hz'
      exact (x.2.mem_or_mem hmul).resolve_left hwx
  have monoToB : Mono (↾PrimeSpectrum.comap (fibreProductToB D)) :=
    (mono_iff_injective _).2
    (PrimeSpectrum.comap_injective_of_surjective (fibreProductToB D)
        (fibreProduct_toB_surjective D))
  have htype :
      @CategoryTheory.IsPushout (Type u) _
        (PrimeSpectrum A) (PrimeSpectrum B) (PrimeSpectrum A')
          (PrimeSpectrum (fibreProductRing D))
        (↾PrimeSpectrum.comap D.toA)
        (↾PrimeSpectrum.comap D.fromA')
        (↾PrimeSpectrum.comap (fibreProductToB D))
        (↾PrimeSpectrum.comap (fibreProductToA' D)) := by
    exact @CategoryTheory.Limits.Types.isPushout_of_isPullback_of_mono'
      _ _ _ _ _ _ _ _ hpull monoToB hjoint hoff
  have hcomm :
      Spec.topMap (CommRingCat.ofHom D.toA) ≫
          Spec.topMap (CommRingCat.ofHom (fibreProductToB D)) =
        Spec.topMap (CommRingCat.ofHom D.fromA') ≫
          Spec.topMap (CommRingCat.ofHom (fibreProductToA' D)) := by
    rw [← Spec.topMap_comp, ← Spec.topMap_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.pullback_comm_sq D.toA D.fromA'
  let c : PushoutCocone
      (Spec.topMap (CommRingCat.ofHom D.toA))
      (Spec.topMap (CommRingCat.ofHom D.fromA')) :=
    PushoutCocone.mk _ _ hcomm
  have htoA :
      (forget TopCat).map (Spec.topMap (CommRingCat.ofHom D.toA)) =
        (↾PrimeSpectrum.comap D.toA) := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have hfromA' :
      (forget TopCat).map (Spec.topMap (CommRingCat.ofHom D.fromA')) =
        (↾PrimeSpectrum.comap D.fromA') := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have htoB :
      (forget TopCat).map (Spec.topMap (CommRingCat.ofHom (fibreProductToB D))) =
        (↾PrimeSpectrum.comap (fibreProductToB D)) := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have htoA' :
      (forget TopCat).map (Spec.topMap (CommRingCat.ofHom (fibreProductToA' D))) =
        (↾PrimeSpectrum.comap (fibreProductToA' D)) := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have htype' :
      @CategoryTheory.IsPushout (Type u) _
        (PrimeSpectrum A) (PrimeSpectrum B) (PrimeSpectrum A')
          (PrimeSpectrum (fibreProductRing D))
        ((forget TopCat).map (Spec.topMap (CommRingCat.ofHom D.toA)))
        ((forget TopCat).map (Spec.topMap (CommRingCat.ofHom D.fromA')))
        ((forget TopCat).map (Spec.topMap (CommRingCat.ofHom (fibreProductToB D))))
        ((forget TopCat).map (Spec.topMap (CommRingCat.ofHom (fibreProductToA' D)))) := by
    rw [htoA, hfromA', htoB, htoA']
    exact htype
  have hc : IsColimit ((forget TopCat).mapCocone c) := by
    refine (IsColimit.equivOfNatIsoOfIso
      (spanCompIso (forget TopCat)
        (Spec.topMap (CommRingCat.ofHom D.toA))
        (Spec.topMap (CommRingCat.ofHom D.fromA')))
      ((forget TopCat).mapCocone c) htype'.cocone
      (WalkingSpan.ext (Iso.refl _) ?_ ?_)).symm htype'.isColimit
    · change (forget TopCat).map c.inl = htype'.cocone.inl
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    · change (forget TopCat).map c.inr = htype'.cocone.inr
      apply ConcreteCategory.hom_ext
      intro x
      rfl
  refine ⟨⟨c.condition⟩, ?_⟩
  apply (TopCat.nonempty_isColimit_iff_eq_coinduced c hc).2
  apply le_antisymm
  · rw [TopologicalSpace.le_def]
    intro U hU
    rw [isOpen_iSup_iff] at hU
    rw [@isOpen_iff_forall_mem_open _ _ U]
    intro p hp
    have hB : IsOpen ((PrimeSpectrum.comap (fibreProductToB D)) ⁻¹' U) := by
      exact isOpen_coinduced.mp (hU WalkingSpan.left)
    have hA' : IsOpen ((PrimeSpectrum.comap (fibreProductToA' D)) ⁻¹' U) := by
      exact isOpen_coinduced.mp (hU WalkingSpan.right)
    by_cases hker : RingHom.ker (fibreProductToB D) ≤ p.asIdeal
    · have hpB : p ∈ Set.range (PrimeSpectrum.comap (fibreProductToB D)) := by
        rw [range_comap_of_surjective B (fibreProductToB D)
          (fibreProduct_toB_surjective D)]
        exact hker
      obtain ⟨q, rfl⟩ := hpB
      have hqU : q ∈ (PrimeSpectrum.comap (fibreProductToB D) ⁻¹' U) := hp
      obtain ⟨V, ⟨g, rfl⟩, hqg, hV⟩ :=
        PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqU hB
      obtain ⟨f', hf'⟩ := D.fromA'_surjective (D.toA g)
      obtain ⟨J, hJ⟩ := (PrimeSpectrum.isOpen_iff _).mp hA'
      have hVI : ∀ s : PrimeSpectrum A',
          s ∈ PrimeSpectrum.zeroLocus (fibreProductIdeal D) →
            s ∈ PrimeSpectrum.basicOpen f' →
              s ∈ (PrimeSpectrum.comap (fibreProductToA' D) ⁻¹' U) := by
        intro s hsI hsf
        have hsrange : s ∈ Set.range (PrimeSpectrum.comap D.fromA') := by
          rw [range_comap_of_surjective A D.fromA' D.fromA'_surjective]
          exact (PrimeSpectrum.mem_zeroLocus s _).mp hsI
        obtain ⟨x, hx⟩ := hsrange
        have hxf : D.toA g ∉ x.asIdeal := by
          intro hxf
          have hf'_not : f' ∉ s.asIdeal := by
            simpa only [PrimeSpectrum.mem_basicOpen] using hsf
          apply hf'_not
          rw [← hx]
          change D.fromA' f' ∈ x.asIdeal
          rw [hf']
          exact hxf
        have hxV : PrimeSpectrum.comap D.toA x ∈
            (PrimeSpectrum.comap (fibreProductToB D) ⁻¹' U) :=
          hV (by simpa [PrimeSpectrum.mem_basicOpen] using hxf)
        change PrimeSpectrum.comap (fibreProductToA' D) s ∈
          (U : Set (PrimeSpectrum (fibreProductRing D)))
        have hpoints :
            PrimeSpectrum.comap (fibreProductToA' D) s =
              PrimeSpectrum.comap (fibreProductToB D)
                (PrimeSpectrum.comap D.toA x) := by
          rw [← hx, ← PrimeSpectrum.comap_comp_apply,
            ← PrimeSpectrum.comap_comp_apply,
            RingHom.pullback_comm_sq D.toA D.fromA']
        have hxV' : PrimeSpectrum.comap D.toA x ∈
            (PrimeSpectrum.comap (fibreProductToB D) ⁻¹'
              (U : Set (PrimeSpectrum (fibreProductRing D)))) := hxV
        rw [hpoints]
        exact hxV'
      have hfrad :
          f' ∈ (fibreProductIdeal D ⊔ Ideal.span J).radical := by
        have hle : Ideal.span ({f'} : Set A') ≤
            (fibreProductIdeal D ⊔ Ideal.span J).radical := by
          rw [Ideal.radical_eq_sInf
            (fibreProductIdeal D ⊔ (Ideal.span J : Ideal A'))]
          refine le_sInf ?_
          intro K hK
          apply Ideal.span_le.2
          intro x hx
          have hxf' : x = f' := by
            simpa only [Set.mem_singleton_iff] using hx
          subst x
          by_contra hfK
          let sK : PrimeSpectrum A' := ⟨K, hK.2⟩
          have hsKI : sK ∈ PrimeSpectrum.zeroLocus (fibreProductIdeal D) := by
            apply (PrimeSpectrum.mem_zeroLocus sK _).2
            intro z hz
            exact hK.1 ((le_sup_left :
              fibreProductIdeal D ≤ fibreProductIdeal D ⊔ Ideal.span J) hz)
          have hsKf : sK ∈ PrimeSpectrum.basicOpen f' := by
            change f' ∉ K
            exact hfK
          have hsKU : sK ∈
              (PrimeSpectrum.comap (fibreProductToA' D) ⁻¹' U) :=
            hVI sK hsKI hsKf
          have hsKJ : sK ∈ PrimeSpectrum.zeroLocus J := by
            apply (PrimeSpectrum.mem_zeroLocus sK _).2
            intro j hj
            exact hK.1 ((le_sup_right :
              Ideal.span J ≤ fibreProductIdeal D ⊔ Ideal.span J)
              (Ideal.subset_span hj))
          have hsKc : sK ∈
              (PrimeSpectrum.comap (fibreProductToA' D) ⁻¹' U)ᶜ := by
            rw [hJ]
            exact hsKJ
          exact hsKc hsKU
        exact hle (Ideal.subset_span (by simp))
      obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hfrad
      rcases Submodule.mem_sup.mp hn with ⟨i, hi, a', ha', hsum⟩
      have hmap : D.fromA' a' = (D.toA g) ^ n := by
        have hsum' := congrArg D.fromA' hsum
        have hi0 : D.fromA' i = 0 := by
          simpa only [RingHom.mem_ker] using hi
        simpa only [map_add, hi0, map_pow, hf', zero_add] using hsum'
      let h : fibreProductRing D := ⟨(g ^ (n + 1), a' * f'), by
        change D.toA (g ^ (n + 1)) = D.fromA' (a' * f')
        rw [map_pow, map_mul, hmap, hf', pow_succ]⟩
      have hpbasic : PrimeSpectrum.comap (fibreProductToB D) q ∈
          PrimeSpectrum.basicOpen h := by
        change fibreProductToB D h ∉ q.asIdeal
        have hg : g ∉ q.asIdeal := by
          change g ∉ q.asIdeal at hqg
          exact hqg
        intro hh
        apply hg
        apply q.2.mem_of_pow_mem (n + 1)
        simpa [h] using hh
      refine ⟨(PrimeSpectrum.basicOpen h :
          Set (PrimeSpectrum (fibreProductRing D))), ?_,
        PrimeSpectrum.isOpen_basicOpen,
        hpbasic⟩
      intro z hz
      change (z : PrimeSpectrum (fibreProductRing D)) ∈
        (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum (fibreProductRing D))) at hz
      have hz' : (z : PrimeSpectrum (fibreProductRing D)) ∈
          (Set.range (PrimeSpectrum.comap (fibreProductToB D)) ⊔
            Set.range (PrimeSpectrum.comap (fibreProductToA' D))) := by
        change (z : PrimeSpectrum (fibreProductRing D)) ∈
          (Set.range (↾PrimeSpectrum.comap (fibreProductToB D)) ⊔
            Set.range (↾PrimeSpectrum.comap (fibreProductToA' D)))
        rw [hjoint]
        exact Set.mem_univ z
      rcases hz' with hzB | hzA'
      · obtain ⟨q', rfl⟩ := hzB
        have hpow : g ^ (n + 1) ∉ q'.asIdeal := by
          change fibreProductToB D h ∉ q'.asIdeal at hz
          simpa [h] using hz
        have hg' : g ∉ q'.asIdeal := by
          intro hg'
          apply hpow
          exact q'.asIdeal.pow_mem_of_mem hg' (n + 1) (by simp)
        apply hV
        change g ∉ q'.asIdeal
        exact hg'
      · obtain ⟨r, rfl⟩ := hzA'
        have hprod : a' * f' ∉ r.asIdeal := by
          change fibreProductToA' D h ∉ r.asIdeal at hz
          simpa [h] using hz
        have hrU : r ∈
            (PrimeSpectrum.comap (fibreProductToA' D) ⁻¹' U) := by
          by_contra hrnot
          have hrzero : r ∈ PrimeSpectrum.zeroLocus J := by
            rw [← hJ]
            exact hrnot
          have hspan : Ideal.span J ≤ r.asIdeal :=
            Ideal.span_le.2 ((PrimeSpectrum.mem_zeroLocus r _).mp hrzero)
          apply hprod
          simpa [mul_comm] using r.asIdeal.mul_mem_left f' (hspan ha')
        exact hrU
    · have hpA' := hrange p hker
      obtain ⟨r, hr⟩ := hpA'
      have hw_exists : ∃ w, w ∈ RingHom.ker (fibreProductToB D) ∧
          w ∉ p.asIdeal := by
        by_contra h
        apply hker
        intro w hw
        by_contra hwn
        exact h ⟨w, hw, hwn⟩
      obtain ⟨w, hw, hwp⟩ := hw_exists
      have hrU : r ∈
          (PrimeSpectrum.comap (fibreProductToA' D) ⁻¹'
            (U : Set (PrimeSpectrum (fibreProductRing D)))) := by
        change PrimeSpectrum.comap (fibreProductToA' D) r ∈
          (U : Set (PrimeSpectrum (fibreProductRing D)))
        rw [hr]
        exact hp
      obtain ⟨V, ⟨a', rfl⟩, hra, hV⟩ :=
        PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
          hrU hA'
      have hwA' : fibreProductToA' D w ∉ r.asIdeal := by
        intro hwA'
        apply hwp
        rw [← hr]
        change fibreProductToA' D w ∈ r.asIdeal
        exact hwA'
      have ha'_not : a' ∉ r.asIdeal := by
        change a' ∉ r.asIdeal at hra
        exact hra
      let h : fibreProductRing D :=
        ⟨(0, (fibreProductToA' D w) * a'), by
          change D.toA (0 : B) =
            D.fromA' ((fibreProductToA' D w) * a')
          have hw0 : D.fromA' (fibreProductToA' D w) = 0 := by
            have hcomm := DFunLike.congr_fun
              (RingHom.pullback_comm_sq D.toA D.fromA') w
            change D.toA (fibreProductToB D w) =
              D.fromA' (fibreProductToA' D w) at hcomm
            rw [show fibreProductToB D w = 0 by
              simpa only [RingHom.mem_ker] using hw] at hcomm
            simpa using hcomm.symm
          rw [map_zero, map_mul, hw0, zero_mul]⟩
      have hpbasic : p ∈ PrimeSpectrum.basicOpen h := by
        rw [← hr]
        change fibreProductToA' D h ∉ r.asIdeal
        intro hh
        have hprod : (fibreProductToA' D w) * a' ∈ r.asIdeal := by
          simpa [h] using hh
        exact (r.2.mem_or_mem hprod).elim hwA' ha'_not
      refine ⟨(PrimeSpectrum.basicOpen h :
          Set (PrimeSpectrum (fibreProductRing D))), ?_,
        PrimeSpectrum.isOpen_basicOpen,
        hpbasic⟩
      intro z hz
      change (z : PrimeSpectrum (fibreProductRing D)) ∈
        (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum (fibreProductRing D))) at hz
      have hz' : (z : PrimeSpectrum (fibreProductRing D)) ∈
          (Set.range (↾PrimeSpectrum.comap (fibreProductToB D)) ⊔
            Set.range (↾PrimeSpectrum.comap (fibreProductToA' D))) := by
        rw [hjoint]
        exact Set.mem_univ z
      rcases hz' with hzB | hzA'
      · obtain ⟨q', rfl⟩ := hzB
        exfalso
        apply hz
        change fibreProductToB D h ∈ q'.asIdeal
        simp [h]
      · obtain ⟨s, rfl⟩ := hzA'
        have has : a' ∉ s.asIdeal := by
          intro has
          apply hz
          change fibreProductToA' D h ∈ s.asIdeal
          simpa [h] using s.asIdeal.mul_mem_left (fibreProductToA' D w) has
        apply hV
        change a' ∉ s.asIdeal
        exact has
  · rw [iSup_le_iff]
    intro j
    exact (c.ι.app j).hom.continuous.coinduced_le

/-- Integrality descends across the surjective leg of the pullback square. -/
theorem fibreProduct_integral
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (h_integral : D.toA.IsIntegral) :
    (fibreProductToA' D).IsIntegral := by
  intro a'
  obtain ⟨p, hp, hpa⟩ := h_integral (D.fromA' a')
  let q := p * Polynomial.X
  have hq : q.Monic := hp.mul Polynomial.monic_X
  have hq_eval : Polynomial.eval₂ D.toA (D.fromA' a') q = 0 := by
    simp [q, hpa]
  obtain ⟨p', hpmap, hpdeg, hp'monic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic
      (f := fibreProductToB D)
      (Polynomial.mem_lifts_of_surjective (fibreProduct_toB_surjective D) q) hq
  let r : A' := p'.eval₂ (fibreProductToA' D) a'
  have hr : D.fromA' r = 0 := by
    dsimp [r]
    rw [Polynomial.hom_eval₂]
    have hcomp : D.fromA'.comp (fibreProductToA' D) =
        D.toA.comp (fibreProductToB D) :=
      (RingHom.pullback_comm_sq D.toA D.fromA').symm
    rw [hcomp, ← Polynomial.eval₂_map, hpmap]
    exact hq_eval
  let rI : fibreProductIdeal D := ⟨r, hr⟩
  obtain ⟨z, hz⟩ := (fibreProduct_kernel_equiv D).surjective rI
  have hz' : fibreProductToA' D z = r := by
    have hz'' := congrArg Subtype.val (fibreProduct_kernel_equiv_apply D z)
    rw [hz] at hz''
    simpa [fibreProduct_kernel_to_ideal] using hz''.symm
  rcases subsingleton_or_nontrivial B with hBtriv | hBnontriv
  · have hA01 : (0 : A) = 1 := by
      simpa using congrArg D.toA (hBtriv.elim (0 : B) 1)
    have hA_sub : Subsingleton A := by
      constructor
      intro x y
      calc
        x = x * 1 := by simp
        _ = x * 0 := by rw [hA01]
        _ = 0 := by simp
        _ = y * 0 := by simp
        _ = y * 1 := by rw [hA01]
        _ = y := by simp
    have ha'ker : D.fromA' a' = 0 := hA_sub.elim _ _
    let z : fibreProductRing D := ⟨(0, a'), by
      change D.toA (0 : B) = D.fromA' a'
      simp [ha'ker]⟩
    refine ⟨Polynomial.X - Polynomial.C (z : fibreProductRing D),
      Polynomial.monic_X_sub_C _, ?_⟩
    simp [z]
  · have hBzero : (0 : B) ≠ 1 := by
      intro h
      rcases hBnontriv.exists_pair_ne with ⟨x, y, hxy⟩
      apply hxy
      calc
        x = x * 1 := by simp
        _ = x * 0 := by rw [h]
        _ = 0 := by simp
        _ = y * 0 := by simp
        _ = y * 1 := by rw [h]
        _ = y := by simp
    have hFnontriv : Nontrivial (fibreProductRing D) := by
      rcases hBnontriv.exists_pair_ne with ⟨x, y, hxy⟩
      rcases fibreProduct_toB_surjective D x with ⟨x', rfl⟩
      rcases fibreProduct_toB_surjective D y with ⟨y', rfl⟩
      exact ⟨⟨x', y', by
        intro h'
        apply hxy
        simpa using congrArg (fibreProductToB D) h'⟩⟩
    have hFzero : (0 : fibreProductRing D) ≠ 1 := by
      intro h
      rcases hFnontriv.exists_pair_ne with ⟨x, y, hxy⟩
      apply hxy
      calc
        x = x * 1 := by simp
        _ = x * 0 := by rw [h]
        _ = 0 := by simp
        _ = y * 0 := by simp
        _ = y * 1 := by rw [h]
        _ = y := by simp
    have hp0 : p ≠ 0 := hp.ne_zero_of_ne hBzero
    have hX0 : (Polynomial.X : Polynomial B) ≠ 0 := by
      intro h
      apply hBzero
      have hcoeff := congrArg (fun f : Polynomial B => f.coeff 1) h
      simp at hcoeff
    have hqpos : 0 < q.natDegree := by
      dsimp [q]
      rw [Polynomial.natDegree_mul' (by simp [hp])]
      simp
    have hp'0 : p' ≠ 0 := by
      intro hp'0
      rw [hp'0, Polynomial.natDegree_zero] at hpdeg
      exact (Nat.ne_of_gt hqpos) hpdeg.symm
    let p'' := p' - Polynomial.C (z : fibreProductRing D)
    have hp''monic : p''.Monic := by
      apply hp'monic.sub_of_left
      apply Polynomial.degree_C_le.trans_lt
      rw [Polynomial.degree_eq_natDegree hp'0]
      apply WithBot.coe_lt_coe.mpr
      rw [hpdeg]
      exact hqpos
    refine ⟨p'', hp''monic, ?_⟩
    simp [p'', r, hz']

/-! ## Modules over the pullback -/

/-- The quotient `M'/IM'` used by the source to describe a gluing map. -/
abbrev fibreProductModuleReduction
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    {M' : Type u} [AddCommGroup M'] [Module A' M'] : Type u :=
  M' ⧸ (fibreProductIdeal D • (⊤ : Submodule A' M'))

/-- The category of module triples `(N, M', φ)` in the source, implemented by
the canonical full subcategory from Unit05. -/
abbrev fibreProductModuleGluingCategory
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :=
  ModuleGluingCategory (fibreProductRingSquare D)

/-- The source's functor `Mod(B') → Mod(B) ×_{Mod(A)} Mod(A')`. -/
noncomputable def fibreProductModuleFunctor
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    ModuleCat.{u} (fibreProductRing D) ⥤ fibreProductModuleGluingCategory D :=
  moduleBaseChangeFunctor (fibreProductRingSquare D)

/-- The compatible-pair module pullback attached to a module triple. -/
noncomputable abbrev fibreProductModule
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory D) :
    ModuleCat.{u} (fibreProductRing D) :=
  moduleFiberProduct (fibreProductRingSquare D) X

/-- The compatible-pair condition underlying `fibreProductModule`. -/
abbrev fibreProductModuleCompatiblePairs
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory D) :=
  moduleFiberCompatiblePairs (fibreProductRingSquare D) X

/-- The categorical module pullback and the source's compatible-pair
presentation have the same underlying elements. -/
noncomputable def fibreProductModuleCompatiblePairEquiv
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory D) :
    (fibreProductModule D X : Type u) ≃
      {p : (moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X) : Type u) ×
        (moduleGluingRightObj (D := fibreProductRingSquare D) (X := X) : Type u) //
        p ∈ fibreProductModuleCompatiblePairs D X} :=
  moduleFiberProduct_compatiblePairEquiv (fibreProductRingSquare D) X

/-- The projection from the compatible-pair module to its `B`-module
component. -/
def fibreProductModule_leftProjection
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (situation : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory situation) :
    fibreProductModule situation X →
      moduleGluingLeftObj (fibreProductRingSquare situation) X :=
  fun (x : fibreProductModule situation X) =>
    (moduleFiberProductPair (fibreProductRingSquare situation) X x).1

/-- In the source's module lemma, the compatible-pair projection to `N` is
surjective. -/
theorem fibreProductModule_leftProjection_surjective
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (situation : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory situation) :
    Function.Surjective (fibreProductModule_leftProjection situation X) := by
  intro x
  let _ : Algebra B A := RingHom.toAlgebra situation.toA
  let _ : Algebra A' A := RingHom.toAlgebra situation.fromA'
  obtain ⟨y, hy⟩ :=
    (TensorProduct.mk_surjective A' (X.obj.right : Type u) A
      situation.fromA'_surjective)
      (X.obj.hom (TensorProduct.tmul B (1 : A) x))
  have hxy :
      moduleFiberLeftMap (fibreProductRingSquare situation) X x =
        moduleFiberRightMap (fibreProductRingSquare situation) X y := by
    change X.obj.hom (TensorProduct.tmul B (1 : A) x) =
      TensorProduct.tmul A' (1 : A) y
    exact hy.symm
  refine ⟨Concrete.pullbackMk
      (moduleFiberLeftMap (fibreProductRingSquare situation) X)
      (moduleFiberRightMap (fibreProductRingSquare situation) X) x y hxy, ?_⟩
  change pullback.fst
      (moduleFiberLeftMap (fibreProductRingSquare situation) X)
      (moduleFiberRightMap (fibreProductRingSquare situation) X)
      (Concrete.pullbackMk
        (moduleFiberLeftMap (fibreProductRingSquare situation) X)
        (moduleFiberRightMap (fibreProductRingSquare situation) X) x y hxy) = x
  exact Concrete.pullbackMk_fst
    (moduleFiberLeftMap (fibreProductRingSquare situation) X)
    (moduleFiberRightMap (fibreProductRingSquare situation) X) x y hxy

/-- The right adjoint given by the compatible-pair module pullback. -/
noncomputable abbrev fibreProductModuleRightAdjoint
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    fibreProductModuleGluingCategory D ⥤ ModuleCat.{u} (fibreProductRing D) :=
  moduleFiberProductRightAdjointCanonical (fibreProductRingSquare D)

/-- The module functor has the source's compatible-pair right adjoint. -/
noncomputable def fibreProductModule_rightAdjoint
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    fibreProductModuleFunctor D ⊣ fibreProductModuleRightAdjoint D := by
  exact (moduleFiberProductAdjunctionData (fibreProductRingSquare D)).adjunction

/-- The source's assertion that applying the gluing functor to the right
adjoint recovers a module triple, expressed by a natural isomorphism. -/
/-
Proof roadmap (Stacks, Lemma 15.6.4).

* Work objectwise with `X = (N, M', φ)`, put
  `Bp := fibreProductRing D`, `J := RingHom.ker (fibreProductToB D)`,
  `I := fibreProductIdeal D`, and
  `L := (fibreProductModuleRightAdjoint D).obj X`.  Use
  `moduleFiberProduct_compatiblePairEquiv` and
  `moduleFiberProduct_pair_is_compatible` from
  `Unit05/FibreProductsOfRingsI.lean` to reason about `L` as compatible
  pairs.  Do not unfold `moduleFiberProductAdjunctionData`: it is selected by
  `Classical.choice` and is opaque.
* Let `p : L → N` be `pullback.fst (moduleFiberLeftMap _ X)
  (moduleFiberRightMap _ X)`.  Its underlying function is
  `fibreProductModule_leftProjection D X`, hence it is surjective by
  `fibreProductModule_leftProjection_surjective`.  Its kernel consists of
  pairs `(0, m')` with `m'` in `I • ⊤`.  Prove this in both directions by
  changing the compatibility equation to
  `X.obj.hom (1 ⊗ₜ 0) = 1 ⊗ₜ m'`; identify the latter kernel with
  `I • ⊤` using `TensorProduct.quotTensorEquivQuotSMul` and
  `TensorProduct.quotTensorEquivQuotSMul_comp_mk` from
  `Mathlib/LinearAlgebra/TensorProduct/Quotient.lean`.
* Show `J • ⊤ = LinearMap.ker p`.  The nontrivial inclusion uses the chosen
  bijection `fibreProduct_kernel_equiv D : J ≃ I` and its computation rule
  `fibreProduct_kernel_equiv_apply`: write an element of `I • ⊤` as a
  finite sum of `i • m'`, lift each `i` to `j : J`, and use that the
  image of the second projection `L → M'` generates `M'`.  Prove the latter
  first from generation modulo `I • ⊤` and the bijection between `ker p`
  and `I • ⊤`.  This is observations (4)--(7) in the source proof.
* The quotient description now gives a `B`-linear equivalence
  `(ModuleCat.extendScalars (fibreProductToB D)).obj L ≃ X.obj.left`.
  Build it from `TensorProduct.quotTensorEquivQuotSMul L J`, the quotient
  equivalence induced by `J • ⊤ = ker p`, and the first isomorphism theorem
  for the surjective linear map `p`.
* For the right component, define
  `γ : (ModuleCat.extendScalars (fibreProductToA' D)).obj L ⟶ X.obj.right`
  from the second pullback projection via
  `ModuleCat.extendRestrictScalarsAdj`.  Surjectivity follows because the
  image of `L → M'` generates `M'`; for injectivity reduce an element of
  `ker γ` modulo `I`.  Right exactness
  `lTensor_exact` and `LinearMap.lTensor_surjective` from
  `Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean` say that the
  remaining element is a sum of `l ⊗ 1` and `n ⊗ i`.  Replace each
  `i : I` by its `j : J` preimage and use `J • L = ker p`; the sum is
  `l ⊗ 1` and `γ` sends it to the same `l`, so it is zero.
* Turn the two bijective component maps into module isomorphisms with
  `ConcreteCategory.isIso_iff_bijective` (or
  `LinearEquiv.toModuleIso`).  Assemble an isomorphism in the comma category
  with `Comma.isoMk`, then lift it through the iso-property full subcategory
  with `ObjectProperty.isoMk`.  The maps are defined from the two pullback
  projections, so naturality is exactly
  `moduleFiberLeftMap_naturality`,
  `moduleFiberRightMap_naturality`, and the defining equations of
  `moduleFiberProductMap` in `Unit05/FibreProductsOfRingsI.lean`.
  `NatIso.ofComponents` gives the required natural isomorphism.
-/
theorem fibreProductModule_composition_isIdentity
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Nonempty
      (fibreProductModuleRightAdjoint D ⋙ fibreProductModuleFunctor D ≅
        𝟭 (fibreProductModuleGluingCategory D)) := by
  sorry

/-- A chosen natural isomorphism expressing the recovery of a module triple. -/
noncomputable def fibreProductModule_composition_iso
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    fibreProductModuleRightAdjoint D ⋙ fibreProductModuleFunctor D ≅
      𝟭 (fibreProductModuleGluingCategory D) :=
  Classical.choice (fibreProductModule_composition_isIdentity D)

/-- The componentwise base-change isomorphisms asserted in the source. -/
theorem fibreProductModule_recovery_exists
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory D) :
    Nonempty
      (((ModuleCat.extendScalars (fibreProductToB D)).obj
          ((fibreProductModuleRightAdjoint D).obj X) ≅
        moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X)) ×
        ((ModuleCat.extendScalars (fibreProductToA' D)).obj
          ((fibreProductModuleRightAdjoint D).obj X) ≅
        moduleGluingRightObj (D := fibreProductRingSquare D) (X := X))) := by
  let e := fibreProductModule_composition_iso D
  let eX := e.app X
  let leftIso :
      (ModuleCat.extendScalars (fibreProductToB D)).obj
          ((fibreProductModuleRightAdjoint D).obj X) ≅
        moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X) :=
    { hom := eX.hom.hom.left
      inv := eX.inv.hom.left
      hom_inv_id := by
        change eX.hom.hom.left ≫ eX.inv.hom.left = 𝟙 _
        have h := congrArg (fun f => f.hom.left) eX.hom_inv_id
        change eX.hom.hom.left ≫ eX.inv.hom.left = 𝟙 _ at h
        exact h
      inv_hom_id := by
        change eX.inv.hom.left ≫ eX.hom.hom.left = 𝟙 _
        have h := congrArg (fun f => f.hom.left) eX.inv_hom_id
        change eX.inv.hom.left ≫ eX.hom.hom.left = 𝟙 _ at h
        exact h }
  let rightIso :
      (ModuleCat.extendScalars (fibreProductToA' D)).obj
          ((fibreProductModuleRightAdjoint D).obj X) ≅
        moduleGluingRightObj (D := fibreProductRingSquare D) (X := X) :=
    { hom := eX.hom.hom.right
      inv := eX.inv.hom.right
      hom_inv_id := by
        change eX.hom.hom.right ≫ eX.inv.hom.right = 𝟙 _
        have h := congrArg (fun f => f.hom.right) eX.hom_inv_id
        change eX.hom.hom.right ≫ eX.inv.hom.right = 𝟙 _ at h
        exact h
      inv_hom_id := by
        change eX.inv.hom.right ≫ eX.hom.hom.right = 𝟙 _
        have h := congrArg (fun f => f.hom.right) eX.inv_hom_id
        change eX.inv.hom.right ≫ eX.hom.hom.right = 𝟙 _ at h
        exact h }
  exact ⟨leftIso, rightIso⟩

/-- A chosen pair of the source's componentwise recovery isomorphisms. -/
noncomputable def fibreProductModule_recovery
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory D) :
    (((ModuleCat.extendScalars (fibreProductToB D)).obj
        ((fibreProductModuleRightAdjoint D).obj X) ≅
      moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X)) ×
      ((ModuleCat.extendScalars (fibreProductToA' D)).obj
        ((fibreProductModuleRightAdjoint D).obj X) ≅
      moduleGluingRightObj (D := fibreProductRingSquare D) (X := X))) :=
  Classical.choice (fibreProductModule_recovery_exists D X)

/-- The unit of the module adjunction, i.e. the source's adjunction map. -/
noncomputable def fibreProductModuleAdjunctionMap
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) (L' : ModuleCat.{u} (fibreProductRing D)) :
    L' ⟶ (fibreProductModuleRightAdjoint D).obj ((fibreProductModuleFunctor D).obj L') :=
  (fibreProductModule_rightAdjoint D).unit.app L'

/-- The adjunction map is surjective. -/
/-
Proof roadmap (Stacks, Lemma 15.6.5, surjectivity).

* Put `J := RingHom.ker (fibreProductToB D)` and
  `I := fibreProductIdeal D`.  For a compatible pair in the target, first
  lift its left coordinate to `l : L'`.  The needed quotient description
  `L' ⊗[Bp] B ≃ L'/(J • ⊤)` is
  `TensorProduct.quotTensorEquivQuotSMul L' J`; alternatively use
  `TensorProduct.mk_surjective Bp L' B
  (fibreProduct_toB_surjective D)` and then quotient by the ambiguity.
  Subtract `fibreProductModuleAdjunctionMap D L' l`; it remains to lift a
  compatible pair of the form `(0, z)`.
* Compatibility says that `z` is in the kernel of base change
  `A' ⊗[Bp] L' → A ⊗[Bp] L'`.  Apply right exactness `lTensor_exact` to
  `I.subtype` and the quotient map `A' → A`
  (whose quotient model is again
  `TensorProduct.quotTensorEquivQuotSMul`) to write `z` as a finite sum
  of terms coming from `L' ⊗[Bp] I`.
* For every `i : I`, choose `j : J` with
  `fibreProduct_kernel_equiv D j = i`; rewrite the value in `A'` using
  `fibreProduct_kernel_equiv_apply`.  The source element `j • l` has zero
  left coordinate and the required right coordinate.  Add these preimages,
  transport back through
  `moduleFiberProduct_compatiblePairEquiv (fibreProductRingSquare D) _`,
  and finish by extensionality of the two pullback projections.

The later `fibreProduct_exact_sequence` packages the same diagram, but it is
declared after this theorem; using it here would violate source chronology.
-/
theorem fibreProductModuleAdjunctionMap_surjective
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) (L' : ModuleCat.{u} (fibreProductRing D)) :
    Function.Surjective (fun x => fibreProductModuleAdjunctionMap D L' x) := by
  sorry

/-! ## The concrete non-injectivity example -/

/-- The polynomial ring `k[x,y]` used in the source's example. -/
abbrev fibreProductExamplePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

/-- The ideal `(xy)` in `k[x,y]`. -/
def fibreProductExampleXYIdeal (k : Type u) [Field k] :
    Ideal (fibreProductExamplePolynomialRing k) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)} :
      Set (fibreProductExamplePolynomialRing k))

/-- The ring `B' = k[x,y]/(xy)` in the source's example. -/
abbrev fibreProductExampleBPrime (k : Type u) [Field k] :=
  fibreProductExamplePolynomialRing k ⧸ fibreProductExampleXYIdeal k

/-- The ideal `(x)` in `B'`. -/
def fibreProductExampleXIdeal (k : Type u) [Field k] :
    Ideal (fibreProductExampleBPrime k) :=
  Ideal.span
    ({Ideal.Quotient.mk (fibreProductExampleXYIdeal k)
        (MvPolynomial.X (0 : Fin 2))} : Set (fibreProductExampleBPrime k))

/-- The ideal `(y)` in `B'`. -/
def fibreProductExampleYIdeal (k : Type u) [Field k] :
    Ideal (fibreProductExampleBPrime k) :=
  Ideal.span
    ({Ideal.Quotient.mk (fibreProductExampleXYIdeal k)
        (MvPolynomial.X (1 : Fin 2))} : Set (fibreProductExampleBPrime k))

/-- The ideal `(x - y)` in `B'`. -/
def fibreProductExampleXYDifferenceIdeal (k : Type u) [Field k] :
    Ideal (fibreProductExampleBPrime k) :=
  Ideal.span
    ({Ideal.Quotient.mk (fibreProductExampleXYIdeal k)
        (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2))} :
      Set (fibreProductExampleBPrime k))

/-- The four quotient rings in the source's concrete example. -/
abbrev fibreProductExampleA' (k : Type u) [Field k] :=
  fibreProductExampleBPrime k ⧸ fibreProductExampleXIdeal k

abbrev fibreProductExampleB (k : Type u) [Field k] :=
  fibreProductExampleBPrime k ⧸ fibreProductExampleYIdeal k

abbrev fibreProductExampleA (k : Type u) [Field k] :=
  fibreProductExampleBPrime k ⧸
    (fibreProductExampleXIdeal k ⊔ fibreProductExampleYIdeal k)

/-- The quotient maps from `B'` in the source's example. -/
def fibreProductExampleBPrimeToB (k : Type u) [Field k] :
    fibreProductExampleBPrime k →+* fibreProductExampleB k :=
  Ideal.Quotient.mk (fibreProductExampleYIdeal k)

def fibreProductExampleBPrimeToA' (k : Type u) [Field k] :
    fibreProductExampleBPrime k →+* fibreProductExampleA' k :=
  Ideal.Quotient.mk (fibreProductExampleXIdeal k)

/-- The induced maps from `B` and `A'` to `A`. -/
def fibreProductExampleBToA (k : Type u) [Field k] :
    fibreProductExampleB k →+* fibreProductExampleA k :=
  Ideal.Quotient.factor le_sup_right

def fibreProductExampleA'ToA (k : Type u) [Field k] :
    fibreProductExampleA' k →+* fibreProductExampleA k :=
  Ideal.Quotient.factor le_sup_left

/-- The commutative square of quotient rings in the source's example. -/
def fibreProductExampleRingSquare (k : Type u) [Field k] :
    RingSquare (fibreProductExampleA k) (fibreProductExampleA' k)
      (fibreProductExampleB k) (fibreProductExampleBPrime k) where
  t := fibreProductExampleA'ToA k
  s := fibreProductExampleBToA k
  u := fibreProductExampleBPrimeToB k
  v := fibreProductExampleBPrimeToA' k
  comm := by
    simp [fibreProductExampleBToA, fibreProductExampleA'ToA,
      fibreProductExampleBPrimeToB, fibreProductExampleBPrimeToA']

/-- The module `L' = B'/(x-y)` in the source's example. -/
abbrev fibreProductExampleLPrime (k : Type u) [Field k] :=
  fibreProductExampleBPrime k ⧸ fibreProductExampleXYDifferenceIdeal k

noncomputable abbrev fibreProductExampleModule (k : Type u) [Field k] :
    ModuleCat.{u} (fibreProductExampleBPrime k) :=
  ModuleCat.of (fibreProductExampleBPrime k) (fibreProductExampleLPrime k)

/-- The class of `x` in `L'`. -/
def fibreProductExampleXClass (k : Type u) [Field k] :
    fibreProductExampleLPrime k :=
  Ideal.Quotient.mk (fibreProductExampleXYDifferenceIdeal k)
    (Ideal.Quotient.mk (fibreProductExampleXYIdeal k)
      (MvPolynomial.X (0 : Fin 2)))

/-- The source's concrete example has a nonzero class of `x` mapping to zero. -/
theorem fibreProductExample_x_nonzero_maps_zero (k : Type u) [Field k] :
    fibreProductExampleXClass k ≠ 0 ∧
      (moduleFiberProductAdjunctionData (fibreProductExampleRingSquare k)).adjunction.unit.app
          (fibreProductExampleModule k)
          (fibreProductExampleXClass k) = 0 := by
  let e : fibreProductExamplePolynomialRing k →ₐ[k] DualNumber k :=
    MvPolynomial.aeval (fun _ : Fin 2 => (DualNumber.eps : DualNumber k))
  have hXY : ∀ p ∈ fibreProductExampleXYIdeal k, e p = 0 := by
    intro p hp
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    simp [e]
  let eB : fibreProductExampleBPrime k →+* DualNumber k :=
    Ideal.Quotient.lift (fibreProductExampleXYIdeal k) e hXY
  have hdiff : ∀ p ∈ fibreProductExampleXYDifferenceIdeal k, eB p = 0 := by
    intro p hp
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [map_mul]
    have hxy : eB ((Ideal.Quotient.mk (fibreProductExampleXYIdeal k))
        (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2))) = 0 := by
      change e (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2)) = 0
      simp [e]
    rw [hxy, mul_zero]
  let eL : fibreProductExampleLPrime k →+* DualNumber k :=
    Ideal.Quotient.lift (fibreProductExampleXYDifferenceIdeal k) eB hdiff
  have hε : (DualNumber.eps : DualNumber k) ≠ 0 := by
    intro h
    have hs := congrArg (TrivSqZeroExt.snd : DualNumber k → k) h
    simp at hs
  have hx : fibreProductExampleXClass k ≠ 0 := by
    intro hx
    apply hε
    have he := congrArg eL hx
    have heps : eL (fibreProductExampleXClass k) = DualNumber.eps := by
      change e (MvPolynomial.X (0 : Fin 2)) = DualNumber.eps
      simp [e]
    rw [heps] at he
    simpa using he
  let r : fibreProductExampleBPrime k :=
    Ideal.Quotient.mk (fibreProductExampleXYIdeal k)
      (MvPolynomial.X (0 : Fin 2))
  let q : fibreProductExampleBPrime k :=
    Ideal.Quotient.mk (fibreProductExampleXYIdeal k)
      (MvPolynomial.X (1 : Fin 2))
  have hrq : r - q ∈ fibreProductExampleXYDifferenceIdeal k := by
    change Ideal.Quotient.mk (fibreProductExampleXYIdeal k)
        (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2)) ∈ _
    exact Ideal.mem_span_singleton'.mpr ⟨1, by simp⟩
  have hrel : ∀ z : fibreProductExampleLPrime k, (r - q) • z = 0 := by
    intro z
    have hz : Ideal.Quotient.mk (fibreProductExampleXYDifferenceIdeal k)
        (r - q) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hrq
    change (Ideal.Quotient.mk (fibreProductExampleXYDifferenceIdeal k)
        (r - q)) • z = 0
    rw [hz]
    change (0 : fibreProductExampleLPrime k) * z = 0
    exact zero_mul z
  have hqB : fibreProductExampleBPrimeToB k q = 0 := by
    change Ideal.Quotient.mk (fibreProductExampleYIdeal k) q = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.mpr ⟨1, by simp [q]⟩
  have hleft : ∀ z : TensorProduct (fibreProductExampleBPrime k)
      (fibreProductExampleB k) (fibreProductExampleLPrime k), r • z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b z =>
        rw [TensorProduct.smul_tmul']
        rw [← sub_add_cancel r q]
        rw [add_smul]
        rw [TensorProduct.add_tmul]
        rw [TensorProduct.smul_tmul]
        have hqsmul : q • b = 0 := by
          change (fibreProductExampleBPrimeToB k q) * b = 0
          rw [hqB]
          exact zero_mul b
        simp [hrel, hqsmul]
    | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]
  have hright : ∀ z : TensorProduct (fibreProductExampleBPrime k)
      (fibreProductExampleA' k) (fibreProductExampleLPrime k), r • z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b z =>
        rw [TensorProduct.smul_tmul']
        have hrA' : fibreProductExampleBPrimeToA' k r = 0 := by
          change Ideal.Quotient.mk (fibreProductExampleXIdeal k) r = 0
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_span_singleton'.mpr ⟨1, by simp [r]⟩
        change ((fibreProductExampleBPrimeToA' k r) • b) ⊗ₜ z = 0
        rw [hrA']
        change ((0 : fibreProductExampleA' k) * b) ⊗ₜ[fibreProductExampleBPrime k] z = 0
        calc
          ((0 : fibreProductExampleA' k) * b) ⊗ₜ[fibreProductExampleBPrime k] z =
              (0 : fibreProductExampleA' k) ⊗ₜ[fibreProductExampleBPrime k] z := by
            congr 1
            exact zero_mul b
          _ = 0 := TensorProduct.zero_tmul (fibreProductExampleA' k) z
    | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]
  let X0 := (moduleBaseChangeFunctor (fibreProductExampleRingSquare k)).obj
    (fibreProductExampleModule k)
  let f0 := moduleFiberLeftMap (fibreProductExampleRingSquare k) X0
  let g0 := moduleFiberRightMap (fibreProductExampleRingSquare k) X0
  have htarget : ∀ z : moduleFiberProduct (fibreProductExampleRingSquare k) X0,
      r • z = 0 := by
    intro z
    apply (Concrete.pullbackEquiv f0 g0).injective
    apply Subtype.ext
    apply Prod.ext
    · unfold Concrete.pullbackEquiv
      simp only [Iso.toEquiv, Equiv.coe_fn_mk, Iso.trans_hom,
        CategoryTheory.comp_apply]
      rw [Types.pullbackIsoPullback_hom_fst, Types.pullbackIsoPullback_hom_fst]
      have hcoord (w : moduleFiberProduct (fibreProductExampleRingSquare k) X0) :
          (ConcreteCategory.hom
              (pullback.fst (↾⇑(ConcreteCategory.hom f0))
                (↾⇑(ConcreteCategory.hom g0))))
              ((ConcreteCategory.hom
                (PreservesPullback.iso (forget (ModuleCat (fibreProductExampleBPrime k)))
                  f0 g0).hom) w) =
            (ConcreteCategory.hom (pullback.fst f0 g0)) w := by
        simpa [CategoryTheory.comp_apply] using
          congrArg (fun k => k.hom w)
            (PreservesPullback.iso_hom_fst
              (forget (ModuleCat (fibreProductExampleBPrime k))) f0 g0)
      rw [hcoord (r • z), hcoord 0]
      have hzero : r • (pullback.fst f0 g0 z) = 0 := by
        change r • (pullback.fst f0 g0 z) =
          (0 : TensorProduct (fibreProductExampleBPrime k)
            (fibreProductExampleB k) (fibreProductExampleLPrime k))
        exact hleft (pullback.fst f0 g0 z)
      simpa only [map_smul, map_zero] using hzero
    · have hpair (w : moduleFiberProduct (fibreProductExampleRingSquare k) X0) :
          ((Concrete.pullbackEquiv f0 g0 w).1.2) =
            (ConcreteCategory.hom
              (pullback.snd (↾⇑(ConcreteCategory.hom f0))
                (↾⇑(ConcreteCategory.hom g0))))
              ((ConcreteCategory.hom
                (PreservesPullback.iso (forget (ModuleCat (fibreProductExampleBPrime k)))
                  f0 g0).hom) w) := by
        simpa only [Concrete.pullbackEquiv, Iso.toEquiv, Equiv.coe_fn_mk,
          Iso.trans_hom, CategoryTheory.comp_apply] using
          Types.pullbackIsoPullback_hom_snd
            (↾⇑(ConcreteCategory.hom f0))
            (↾⇑(ConcreteCategory.hom g0))
            ((PreservesPullback.iso (forget (ModuleCat (fibreProductExampleBPrime k)))
              f0 g0).hom w)
      have hcoord (w : moduleFiberProduct (fibreProductExampleRingSquare k) X0) :
          (ConcreteCategory.hom
              (pullback.snd (↾⇑(ConcreteCategory.hom f0))
                (↾⇑(ConcreteCategory.hom g0))))
              ((ConcreteCategory.hom
                (PreservesPullback.iso (forget (ModuleCat (fibreProductExampleBPrime k)))
                  f0 g0).hom) w) =
            (ConcreteCategory.hom (pullback.snd f0 g0)) w := by
        simpa [CategoryTheory.comp_apply] using
          congrArg (fun k => k.hom w)
            (PreservesPullback.iso_hom_snd
              (forget (ModuleCat (fibreProductExampleBPrime k))) f0 g0)
      calc
        (Concrete.pullbackEquiv f0 g0 (r • z)).1.2 =
            (ConcreteCategory.hom (pullback.snd f0 g0)) (r • z) :=
          (hpair (r • z)).trans (hcoord (r • z))
        _ = r • (ConcreteCategory.hom (pullback.snd f0 g0)) z := by
          simp only [map_smul]
        _ = 0 := by
          have hzero : r • (pullback.snd f0 g0 z) = 0 := by
            change r • (pullback.snd f0 g0 z) =
              (0 : TensorProduct (fibreProductExampleBPrime k)
                (fibreProductExampleA' k) (fibreProductExampleLPrime k))
            exact hright (pullback.snd f0 g0 z)
          exact hzero
        _ = (ConcreteCategory.hom (pullback.snd f0 g0)) 0 := by
          simp only [map_zero]
        _ = (ConcreteCategory.hom
              (pullback.snd (↾⇑(ConcreteCategory.hom f0))
                (↾⇑(ConcreteCategory.hom g0))))
              ((ConcreteCategory.hom
                (PreservesPullback.iso (forget (ModuleCat (fibreProductExampleBPrime k)))
                  f0 g0).hom) 0) := (hcoord 0).symm
        _ = (Concrete.pullbackEquiv f0 g0 0).1.2 := (hpair 0).symm
  have hclass : fibreProductExampleXClass k = r • (1 : fibreProductExampleLPrime k) := by
    change Ideal.Quotient.mk (fibreProductExampleXYDifferenceIdeal k) r = r • 1
    change Ideal.Quotient.mk (fibreProductExampleXYDifferenceIdeal k) r =
      Ideal.Quotient.mk (fibreProductExampleXYDifferenceIdeal k) r * 1
    exact (mul_one (Ideal.Quotient.mk (fibreProductExampleXYDifferenceIdeal k) r)).symm
  constructor
  · exact hx
  · rw [hclass, map_smul]
    exact htarget _

/-- The compatible-pair adjunction map is not injective for arbitrary
commutative ring squares.  The source's concrete witness is the square above:
`B' = k[x, y]/(xy)`, `A' = B'/(x)`, `B = B'/(y)`,
`A = B'/(x, y)`, and `L' = B'/(x - y)`.

This statement is deliberately made at the `RingSquare` interface used by the
adjunction: the concrete square has lower-right ring `B'`, whereas the
specialized `FibreProductSituation` interface replaces it by a chosen
`RingHom.pullback` model.  No transport across an unrecorded ring equivalence
is therefore required. -/
theorem fibreProductModuleAdjunctionMap_not_injective_in_general :
    ¬ (∀ {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B]
        [CommRing B'] (D : RingSquare R R' B B') (L' : ModuleCat.{u} B'),
        Function.Injective (fun x =>
          (moduleFiberProductAdjunctionData D).adjunction.unit.app L' x)) := by
  /-
  Proof roadmap.

  Take `k := ULift.{u} ℚ` (the instance in
  `Mathlib/Algebra/Field/ULift.lean` supplies a field in the fixed universe
  `Type u`) and specialize the negated universal claim to
  `fibreProductExampleRingSquare k` and
  `fibreProductExampleModule k`.  From
  `fibreProductExample_x_nonzero_maps_zero k` obtain `hx : x ≠ 0` and
  `hmap : unit.app _ x = 0`.  If the specialized unit were injective, apply
  it to the equality `hmap.trans (map_zero _).symm`; this gives `x = 0`,
  contradicting `hx`.

  The theorem is intentionally below the witness and quantifies over
  `RingSquare`.  The previous formulation quantified over
  `FibreProductSituation`, whose lower-right ring is the chosen subtype
  `RingHom.pullback`; the concrete witness instead has lower-right ring
  `k[x,y]/(xy)`.  Reusing the witness there would require an unrecorded ring
  equivalence and transport of the module and adjunction, so that route is a
  known dead end.
  -/
  sorry

/-- The compatible-pair pullback is functorial for morphisms of triples. -/
/-
Proof roadmap (Stacks, Lemma 15.6.6).

* Convert the target element with
  `moduleFiberProduct_compatiblePairEquiv (fibreProductRingSquare D) Y`
  to a compatible pair `(x₂, y₂)`.  Choose `x₁` with
  `f.hom.left x₁ = x₂` using `hN`.
* The element
  `X.obj.hom (1 ⊗ₜ[B] x₁)` lies in the `A`-base change of `X.obj.right`.
  Use
  `TensorProduct.mk_surjective A' (X.obj.right : Type u) A
  D.fromA'_surjective` to choose `y₁` mapping to it.  Then `(x₁,y₁)` is
  compatible and maps to `(x₂,y₂')` for some `y₂'`.
* Compatibility of `(x₂,y₂)` and `(x₂,y₂')`, together with the comma
  relation `f.hom.w`, shows `δ := y₂ - y₂'` maps to zero in
  `A ⊗[A'] Y.obj.right`; hence `δ ∈ fibreProductIdeal D • ⊤`.  Prove this
  kernel statement through
  `TensorProduct.quotTensorEquivQuotSMul` from
  `Mathlib/LinearAlgebra/TensorProduct/Quotient.lean`.
* Write `δ = ∑ i_j • z_j` with `i_j : fibreProductIdeal D`.  Lift every
  `z_j` through `hM'`; then `∑ i_j • z'_j` is still in
  `fibreProductIdeal D • ⊤`, so `(0, ∑ i_j • z'_j)` is a compatible pair
  in `X` and maps to `(0,δ)`.  Add it to `(x₁,y₁)`.
* Return to the categorical pullback with the inverse of
  `moduleFiberProduct_compatiblePairEquiv`.  To identify its image under
  `(fibreProductModuleRightAdjoint D).map f`, apply
  `Concrete.pullbackEquiv` and use
  `moduleFiberProductMap`, `pullback.lift_fst`, and
  `pullback.lift_snd` from `Unit05/FibreProductsOfRingsI.lean`.
-/
theorem fibreProductModule_map_surjective
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    {X Y : fibreProductModuleGluingCategory D} (f : X ⟶ Y)
    (hN : Function.Surjective f.hom.left)
    (hM' : Function.Surjective f.hom.right) :
    Function.Surjective (fun x => (fibreProductModuleRightAdjoint D).map f x) := by
  sorry

/-- Finite modules on the two upper corners give a finite compatible-pair
module over the pullback ring. -/
/-
Proof roadmap (Stacks, Lemma 15.6.7).

* Write `L := (fibreProductModuleRightAdjoint D).obj X`,
  `N := X.obj.left`, and `Mp := X.obj.right`.  Extract finite generating
  sets using `Module.Finite.fg_top` (equivalently
  `Module.Finite.exists_fin'`) from
  `Mathlib/RingTheory/Finiteness/Basic.lean`.
* Lift the chosen generators of `N` to elements `u_i : L` with
  `fibreProductModule_leftProjection_surjective D X`.
  For each chosen generator of `Mp`, use the right isomorphism in
  `fibreProductModule_recovery D X`.  Its inverse lands in
  `A' ⊗[fibreProductRing D] L`; induction with
  `TensorProduct.induction_on` expresses the finitely many inverses using
  finitely many pure tensors.  Collect their second factors as a finite family
  `v_j : L`.  The images of the `v_j` generate `Mp` over `A'`.
* Let `S` be the `fibreProductRing D`-span of the `u_i` and `v_j`.
  For `ξ : L`, first match its left coordinate by a combination of the
  `u_i`; lift the coefficients from `B` with
  `fibreProduct_toB_surjective D`.  The remaining compatible pair has first
  coordinate zero, hence second coordinate in
  `fibreProductIdeal D • ⊤`.
* Express that second coordinate as `∑ i_j • image(v_j)`.  Lift each
  `i_j : fibreProductIdeal D` to
  `s_j : RingHom.ker (fibreProductToB D)` through
  `fibreProduct_kernel_equiv D`, and rewrite its `A'` coordinate with
  `fibreProduct_kernel_equiv_apply`.  Then the remaining element is exactly
  `∑ (s_j : fibreProductRing D) • v_j`, so `ξ ∈ S`.
* Conclude `S = ⊤` by `eq_top_iff`; the finite union of the two finite
  families supplies `Module.Finite` via `Module.finite_def`.
-/
theorem fibreProduct_finite_module
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory D)
    [Module.Finite B
      (moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X) : Type u)]
    [Module.Finite A'
      (moduleGluingRightObj (D := fibreProductRingSquare D) (X := X) : Type u)] :
    Module.Finite (fibreProductRing D)
      ((fibreProductModuleRightAdjoint D).obj X : Type u) := by
  sorry

/-! ## The exact sequence and flat modules -/

/-- The first map in the source's exact sequence
`0 → B' → B ⊕ A' → A → 0`. -/
def fibreProductExactLeft
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) : fibreProductRing D → B × A' :=
  fun x => (fibreProductToB D x, fibreProductToA' D x)

/-- The second map in the source's exact sequence
`0 → B' → B ⊕ A' → A → 0`. -/
def fibreProductExactRight
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) : B × A' → A :=
  fun x => D.toA x.1 - D.fromA' x.2

/-- The source object in the `B'`-linear short exact sequence. -/
noncomputable abbrev fibreProductExactSource
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) : ModuleCat.{u} (fibreProductRing D) :=
  ModuleCat.of (fibreProductRing D) (fibreProductRing D)

/-- The middle object `B ⊕ A'`, with the componentwise `B'`-module
structure induced by the two pullback projections. -/
noncomputable def fibreProductExactMiddle
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) : ModuleCat.{u} (fibreProductRing D) :=
  letI : Module (fibreProductRing D) B :=
    Module.compHom B (fibreProductToB D)
  letI : Module (fibreProductRing D) A' :=
    Module.compHom A' (fibreProductToA' D)
  ModuleCat.of (fibreProductRing D) (B × A')

/-- The target `A`, regarded as a `B'`-module through `B' → B → A`. -/
noncomputable def fibreProductExactTarget
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) : ModuleCat.{u} (fibreProductRing D) :=
  letI : Module (fibreProductRing D) A :=
    Module.compHom A (D.toA.comp (fibreProductToB D))
  ModuleCat.of (fibreProductRing D) A

/-- The first map in the short exact sequence, bundled as a `B'`-linear map.
This is the interface needed to tensor the sequence in the flatness proof. -/
noncomputable def fibreProductExactLeftLinear
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    fibreProductExactSource D ⟶ fibreProductExactMiddle D :=
  ConcreteCategory.ofHom (C := ModuleCat (fibreProductRing D))
    { toFun := fibreProductExactLeft D
      map_add' := by
        intro x y
        change (fibreProductExactLeft D (x + y) : B × A') =
          ((fibreProductExactLeft D x).1 + (fibreProductExactLeft D y).1,
            (fibreProductExactLeft D x).2 + (fibreProductExactLeft D y).2)
        ext <;> rfl
      map_smul' := by
        intro r x
        change (fibreProductExactLeft D (r * x) : B × A') =
          (fibreProductToB D r * (fibreProductExactLeft D x).1,
            fibreProductToA' D r * (fibreProductExactLeft D x).2)
        ext <;> rfl }

/-- The second map in the short exact sequence, bundled as a `B'`-linear map. -/
noncomputable def fibreProductExactRightLinear
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    fibreProductExactMiddle D ⟶ fibreProductExactTarget D :=
  ConcreteCategory.ofHom (C := ModuleCat (fibreProductRing D))
    { toFun := fun x =>
        show (fibreProductExactTarget D : Type u) from
          D.toA x.1 - D.fromA' x.2
      map_add' := by
        intro x y
        change B × A' at x y
        change D.toA (x.1 + y.1) - D.fromA' (x.2 + y.2) =
          (D.toA x.1 - D.fromA' x.2) + (D.toA y.1 - D.fromA' y.2)
        simp only [map_add]
        abel
      map_smul' := by
        intro r x
        change B × A' at x
        change D.toA (fibreProductToB D r * x.1) -
            D.fromA' (fibreProductToA' D r * x.2) =
          D.toA (fibreProductToB D r) *
            (D.toA x.1 - D.fromA' x.2)
        rw [map_mul, map_mul]
        have hr := RingSquare.comm_apply (fibreProductRingSquare D) r
        change D.toA (fibreProductToB D r) =
          D.fromA' (fibreProductToA' D r) at hr
        rw [← hr, mul_sub] }

@[simp]
theorem fibreProductExactLeftLinear_apply
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) (x : fibreProductRing D) :
    fibreProductExactLeftLinear D x = fibreProductExactLeft D x := rfl

@[simp]
theorem fibreProductExactRightLinear_apply
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) (x : B × A') :
    fibreProductExactRightLinear D x = fibreProductExactRight D x := by
  change D.toA x.1 - D.fromA' x.2 = D.toA x.1 - D.fromA' x.2
  rfl

/-- Exactness, injectivity on the left, and surjectivity on the right of the
source's short exact sequence, at the `B'`-linear interface required by
`Module.Flat.lTensor_exact`. -/
/-
Proof roadmap.

The new bundled maps are definitionally the displayed functions by
`fibreProductExactLeftLinear_apply` and
`fibreProductExactRightLinear_apply`.

* Injectivity: if the two coordinates of
  `fibreProductExactLeftLinear D x` and
  `fibreProductExactLeftLinear D y` agree, use `Subtype.ext` followed by
  `Prod.ext`; the two coordinate equalities are exactly the goal.
* Exactness: apply `LinearMap.exact_of_comp_of_mem_range` from
  `Mathlib/Algebra/Exact/Basic.lean`.  The composite is zero by
  `RingSquare.comm_apply (fibreProductRingSquare D)`.  Conversely, if
  `D.toA b - D.fromA' a' = 0`, use `sub_eq_zero.mp` to form the pullback
  element `x : fibreProductRing D := ⟨(b,a'), equality⟩`; then
  `fibreProductExactLeftLinear D x = (b,a')`.
* Surjectivity: for `a : A`, choose `a' : A'` with
  `D.fromA' a' = -a` using `D.fromA'_surjective (-a)`.  The pair
  `(0,a')` maps to `a`; finish with `map_zero` and `sub_neg_eq_add`.

Keep the result in terms of the linear maps.  Reverting it to the old plain
function interface prevents its use by `Module.Flat.lTensor_exact` and
`lTensor_exact`.
-/
theorem fibreProduct_exact_sequence
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Function.Injective (fibreProductExactLeftLinear D) ∧
      Function.Exact (fibreProductExactLeftLinear D)
        (fibreProductExactRightLinear D) ∧
      Function.Surjective (fibreProductExactRightLinear D) := by
  sorry

/-- The full subcategory of module triples whose two displayed components are
flat. -/
def fibreProductFlatGluingProperty
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    ObjectProperty (fibreProductModuleGluingCategory D) :=
  fun X =>
    Module.Flat B
        (moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X) : Type u) ∧
      Module.Flat A'
        (moduleGluingRightObj (D := fibreProductRingSquare D) (X := X) : Type u)

abbrev fibreProductFlatGluingCategory
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :=
  ObjectProperty.FullSubcategory (fibreProductFlatGluingProperty D)

/-- The category of flat modules over the pullback ring. -/
def fibreProductFlatModuleProperty
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    ObjectProperty (ModuleCat.{u} (fibreProductRing D)) :=
  fun L' => Module.Flat (fibreProductRing D) (L' : Type u)

abbrev fibreProductFlatModuleCategory
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :=
  ObjectProperty.FullSubcategory (fibreProductFlatModuleProperty D)

/-- If both components of a triple are flat, its compatible-pair module is
flat over the pullback ring. -/
/-
Proof roadmap (Stacks, Lemma 15.6.8(1)).

Let `Bp := fibreProductRing D`, `J := RingHom.ker (fibreProductToB D)`,
`I := fibreProductIdeal D`, and
`L := (fibreProductModuleRightAdjoint D).obj X`.

* Apply `Module.Flat.iff_lTensor_injective'` from
  `Mathlib/RingTheory/Flat/Tensor.lean`.  For an ideal `q : Ideal Bp`,
  the goal is injectivity of `q.subtype.lTensor L`.
* First record the two recovery identifications supplied by
  `fibreProductModule_recovery D X`: `L/JL ≃ₗ[B] X.obj.left` and
  `A' ⊗[Bp] L ≃ₗ[A'] X.obj.right`.  Also construct the multiplication map
  `J ⊗[Bp] L →ₗ[Bp] L`.  Using
  `fibreProduct_kernel_equiv`/`fibreProduct_kernel_equiv_apply`, tensor
  associativity, and the right recovery equivalence, identify it with
  `I.subtype.lTensor X.obj.right`.  It is injective by
  `Module.Flat.lTensor_preserves_injective_linearMap` for the flat
  `A'`-module `X.obj.right`.
* Put `qJ := q ⊓ J`.  The quotient `q/qJ` is killed by `J`, hence is a
  `B = Bp/J`-module.  Tensor the exact pair
  `qJ.subtype → q → q/qJ` with `L` using the right-exact theorem
  `lTensor_exact` and `LinearMap.lTensor_surjective` from
  `Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean`.
  Via `TensorProduct.quotTensorEquivQuotSMul L J` and the left recovery
  equivalence, flatness of `X.obj.left` over `B` shows that a kernel
  element comes from `qJ ⊗ L`.  Thus it suffices to handle `q ≤ J`.
* For `q ≤ J`, let `q''` be its `A'`-saturation after transporting
  `J ≃ I`; concretely it is the preimage in `J` of the `A'`-submodule
  spanned by the image of `q`.  Then `q''/q` is killed by `J`.  Establish
  the local change-of-rings claim that
  `(Submodule.inclusion hqq'').lTensor L : q ⊗ L → q'' ⊗ L` is injective
  whenever
  `J ⊗ L → L` is injective, `L/(J • ⊤)` is flat over `Bp/J`, and
  `q''/q` is killed by `J`.  For the proof, use
  `LinearMap.exact_subtype_mkQ`, `Submodule.mkQ_surjective`, and
  `lTensor_exact` for the submodule
  `q.comap q''.subtype : Submodule Bp q''`; transport its subtype back to
  `Submodule.inclusion hqq''`.  Identify tensors of the quotient with
  tensors over `Bp/J` by
  `TensorProduct.quotTensorEquivQuotSMul`, and apply
  `Module.Flat.lTensor_preserves_injective_linearMap` to the recovered
  left component `X.obj.left`; injectivity of `J ⊗ L → L` removes the
  remaining lift.  This is the source's change-of-rings/Tor-vanishing
  step, and both hypotheses are essential.  Replace `q` by `q''`.
* Now `q` is an `A'`-submodule of `I`.  Identify
  `q ⊗[Bp] L` with `q ⊗[A'] X.obj.right`; under this equivalence the map
  to `L` followed by the right pullback projection is
  `q.subtype.lTensor X.obj.right`, injective by flatness over `A'`.
  Hence the original map is injective.

Universe note: all rings, ideals, and modules here live in `Type u`, so use
`iff_lTensor_injective'` (the unrestricted-ideal version) without an
`ULift`.  Do not invoke `Module.Flat.lTensor_exact` with tensor factor `L`
in the saturation step: flatness of `L` is the conclusion and that would be
circular.
-/
theorem fibreProduct_flat_module
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory D)
    [Module.Flat B
      (moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X) : Type u)]
    [Module.Flat A'
      (moduleGluingRightObj (D := fibreProductRingSquare D) (X := X) : Type u)] :
    Module.Flat (fibreProductRing D)
      ((fibreProductModuleRightAdjoint D).obj X : Type u) := by
  sorry

/-- For a flat pullback module, the adjunction map back to the compatible-pair
module is an isomorphism. -/
/-
Proof roadmap (Stacks, Lemma 15.6.8(2)).

* Let `f := fibreProductExactLeftLinear D` and
  `g := fibreProductExactRightLinear D`.  From
  `fibreProduct_exact_sequence D` obtain injectivity of `f`, exactness
  `Function.Exact f g`, and surjectivity of `g`.
* Tensor on the left by `L'`.  Flatness gives injectivity of
  `f.lTensor L'` via
  `Module.Flat.lTensor_preserves_injective_linearMap`; exactness follows
  from `Module.Flat.lTensor_exact`.  (The non-flat right-exact theorem
  `lTensor_exact` plus `LinearMap.lTensor_surjective` is also available.)
* Conjugate this tensored sequence by:
  `TensorProduct.lid (fibreProductRing D) L'` for the source,
  `TensorProduct.prodRight` from
  `Mathlib/LinearAlgebra/TensorProduct/Prod.lean` followed by
  `TensorProduct.comm` for the middle, and the standard
  `ModuleCat.extendScalarsComp` isomorphisms for the target.  Under these
  equivalences, `f.lTensor L'` is the pair of base-change maps appearing in
  `fibreProductModuleAdjunctionMap D L'`, while `g.lTensor L'` is the
  difference of the two maps to the common `A`-base change.
* Use `moduleFiberProduct_compatiblePairEquiv` to identify the target of the
  adjunction map with the kernel of that difference.  Exactness makes the
  adjunction map surjective; injectivity of `f.lTensor L'` makes it
  injective.  Prove equality of the conjugated maps on pure tensors with
  `TensorProduct.ext'`, `TensorProduct.prodRight_tmul`,
  `ModuleCat.extendScalarsComp_hom_app_one_tmul`, and
  `ModuleCat.extendRestrictScalarsAdj_unit_app_apply`.
* Apply `ConcreteCategory.isIso_iff_bijective` to the resulting bijectivity
  of the `ModuleCat` morphism.
-/
theorem fibreProduct_flat_module_recovery
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (L' : ModuleCat.{u} (fibreProductRing D))
    [Module.Flat (fibreProductRing D) (L' : Type u)] :
    IsIso (fibreProductModuleAdjunctionMap D L') := by
  sorry

/-- A chosen isomorphism expressing the source's recovery statement for flat
modules. -/
noncomputable def fibreProduct_flat_module_recoveryIso
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (L' : ModuleCat.{u} (fibreProductRing D))
    [Module.Flat (fibreProductRing D) (L' : Type u)] :
    L' ≅ (fibreProductModuleRightAdjoint D).obj ((fibreProductModuleFunctor D).obj L') := by
  letI := fibreProduct_flat_module_recovery D L'
  exact asIso (fibreProductModuleAdjunctionMap D L')

/-- Flat modules over the pullback ring are equivalent to flat module triples. -/
/-
Proof roadmap (Stacks, Lemma 15.6.8(3)).

* Define the forward functor with
  `(fibreProductFlatGluingProperty D).lift
    ((fibreProductFlatModuleProperty D).ι ⋙ fibreProductModuleFunctor D) _`.
  For an object `L'`, turn its property into a local
  `Module.Flat (fibreProductRing D) L'` instance.  Each component is an
  extension of scalars, so `Module.Flat.baseChange` from
  `Mathlib/RingTheory/Flat/Stability.lean` proves the two required flatness
  statements (use `Module.Flat.of_linearEquiv` if unfolding
  `ModuleCat.extendScalars` leaves a definitional mismatch).
* Define the inverse with
  `(fibreProductFlatModuleProperty D).lift
    ((fibreProductFlatGluingProperty D).ι ⋙
      fibreProductModuleRightAdjoint D) _`.
  Install the two conjuncts of the source object's property as local
  `Module.Flat` instances and apply `fibreProduct_flat_module D X`.
* Lift `fibreProduct_flat_module_recoveryIso D L'` to an isomorphism in the
  flat full subcategory using `ObjectProperty.isoMk`; these components form
  the unit natural isomorphism.  Lift
  `fibreProductModule_composition_iso D` similarly for the counit.  Prove
  naturality after applying the faithful inclusions; it then reduces to
  naturality of the underlying adjunction unit and of
  `fibreProductModule_composition_iso D`.
* Assemble `e` with `CategoryTheory.Equivalence.mk forward inverse unitIso
  counitIso`.  Return the subtype witness together with
  `⟨Iso.refl _⟩`: by construction
  `e.functor ⋙ (fibreProductFlatGluingProperty D).ι` is definitionally the
  requested restricted `fibreProductModuleFunctor D`.

The last functor-identification is part of the repaired interface; an
unrelated abstract equivalence between the two full subcategories would not
formalize the book's base-change equivalence.
-/
theorem fibreProduct_flat_module_equivalence_exists
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Nonempty
      {e : fibreProductFlatModuleCategory D ≌ fibreProductFlatGluingCategory D //
        Nonempty
          (e.functor ⋙ (fibreProductFlatGluingProperty D).ι ≅
            (fibreProductFlatModuleProperty D).ι ⋙
              fibreProductModuleFunctor D)} := by
  sorry

noncomputable def fibreProduct_flat_module_equivalence
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    fibreProductFlatModuleCategory D ≌ fibreProductFlatGluingCategory D :=
  (Classical.choice (fibreProduct_flat_module_equivalence_exists D)).1

/-! ## Finite projective modules -/

/-- The full subcategory of finite projective modules over a ring. -/
def fibreProductFiniteProjectiveProperty
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    ObjectProperty (ModuleCat.{u} (fibreProductRing D)) :=
  fun L' =>
    Module.Finite (fibreProductRing D) (L' : Type u) ∧
      Module.Projective (fibreProductRing D) (L' : Type u)

abbrev fibreProductFiniteProjectiveModuleCategory
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :=
  ObjectProperty.FullSubcategory (fibreProductFiniteProjectiveProperty D)

/-- The full subcategory of triples with finite projective components. -/
def fibreProductFiniteProjectiveGluingProperty
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    ObjectProperty (fibreProductModuleGluingCategory D) :=
  fun X =>
    (Module.Finite B
        (moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X) : Type u) ∧
      Module.Projective B
        (moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X) : Type u)) ∧
    (Module.Finite A'
        (moduleGluingRightObj (D := fibreProductRingSquare D) (X := X) : Type u) ∧
      Module.Projective A'
        (moduleGluingRightObj (D := fibreProductRingSquare D) (X := X) : Type u))

abbrev fibreProductFiniteProjectiveGluingCategory
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :=
  ObjectProperty.FullSubcategory (fibreProductFiniteProjectiveGluingProperty D)

/-- Finite projective modules over the pullback ring are equivalent to triples
with finite projective components. -/
/-
Proof roadmap (Stacks, Lemma 15.6.9).

First prove that the compatible-pair module of a finite-projective triple is
finite projective.

* From the two projectivity hypotheses get component flatness through the
  instance `Module.Flat.of_projective`; apply
  `fibreProduct_flat_module D X`.  Finiteness is exactly
  `fibreProduct_finite_module D X`.
* A finite flat module is not directly an instance of `Module.Projective`
  in this Mathlib version.  Prove finite presentation as in the source.
  Choose a finite free surjection
  `p : (Fin n → fibreProductRing D) →ₗ[fibreProductRing D] L` using
  `Module.Finite.exists_fin'`, and put `Kp := LinearMap.ker p`.
* Base-change `p` to `B` and `A'`, then conjugate the targets by the two
  isomorphisms `fibreProductModule_recovery D X`.  Call the resulting
  kernels `KB` and `KA'`.  Because `N` and `M'` are projective, the
  surjections split by `Module.projective_lifting_property`; their kernels
  are ranges of idempotents on finite free modules.  They are finite by
  `Module.Finite.range` (or by
  `Module.Finite.exists_comp_eq_id_of_projective`) from
  `Mathlib/RingTheory/Finiteness/Projective.lean`.
* The comparison over `A` makes `(KB, KA')` an object of
  `fibreProductModuleGluingCategory D`.  Exactness after base change uses
  component projectivity through `Module.Flat.lTensor_exact`.  Construct a
  `fibreProductRing D`-linear equivalence
  `Kp ≃ₗ[fibreProductRing D]
    (fibreProductModuleRightAdjoint D).obj kernelTriple` by mapping a kernel
  element to its two base changes.  Prove inverse laws with
  `moduleFiberProduct_compatiblePairEquiv` and the exactness of the two
  base-changed kernel sequences.
* Apply `fibreProduct_finite_module D kernelTriple` to obtain finiteness of
  the right-hand side and transport it across the linear equivalence with
  `Module.Finite.equiv`.  Thus `Kp` is finitely generated.
  `Module.FinitePresentation.fg_ker_iff p p_surjective` from
  `Mathlib/Algebra/Module/FinitePresentation.lean` now gives
  `Module.FinitePresentation (fibreProductRing D) L`.
  Finish with `Module.Flat.projective_of_finitePresentation` from
  `Mathlib/RingTheory/Flat/EquationalCriterion.lean`.

Then build the categorical equivalence.

* Lift `fibreProductModuleFunctor D` to the finite-projective full
  subcategories.  Finiteness of each base change is
  `Module.Finite.base_change`; projectivity follows from
  `Module.Projective.tensorProduct` after unfolding
  `ModuleCat.extendScalars` (the scalar ring is projective over itself).
* Lift `fibreProductModuleRightAdjoint D` using the finite-projective result
  above.  Lift `fibreProduct_flat_module_recoveryIso` for the unit and
  `fibreProductModule_composition_iso D` for the counit with
  `ObjectProperty.isoMk`, then use `CategoryTheory.Equivalence.mk`.
* Package the equivalence with the required `Nonempty` functor isomorphism.
  As in the flat case it is `⟨Iso.refl _⟩` because the forward functor was
  defined with `ObjectProperty.lift`.

Do not replace the finite-presentation argument by “finite + flat implies
projective”: that implication is the missing step here, and Mathlib only
provides the finitely-presented-flat theorem named above.
-/
theorem fibreProduct_finite_projective_equivalence_exists
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Nonempty
      {e : fibreProductFiniteProjectiveModuleCategory D ≌
          fibreProductFiniteProjectiveGluingCategory D //
        Nonempty
          (e.functor ⋙ (fibreProductFiniteProjectiveGluingProperty D).ι ≅
            (fibreProductFiniteProjectiveProperty D).ι ⋙
              fibreProductModuleFunctor D)} := by
  sorry

noncomputable def fibreProduct_finite_projective_equivalence
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    fibreProductFiniteProjectiveModuleCategory D ≌
      fibreProductFiniteProjectiveGluingCategory D :=
  (Classical.choice (fibreProduct_finite_projective_equivalence_exists D)).1

end

end Formalization.Books.MoreAlgebra.Unit06
