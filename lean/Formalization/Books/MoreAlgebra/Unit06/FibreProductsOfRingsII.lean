import Formalization.Books.MoreAlgebra.Unit05.FibreProductsOfRingsI
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.RingTheory.Flat.Basic
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
        change z ∈ (PrimeSpectrum.comap (fibreProductToA' D) x).asIdeal
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
        change z ∈ (PrimeSpectrum.comap (fibreProductToA' D) y).asIdeal
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
          change z ∈ (PrimeSpectrum.comap (fibreProductToA' D) y).asIdeal
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
        change z' ∈ (PrimeSpectrum.comap (fibreProductToA' D) x).asIdeal
        change z' ∈ (PrimeSpectrum.comap (fibreProductToA' D) y).asIdeal at hz
        have hmem := congrArg
          (fun P : PrimeSpectrum (fibreProductRing D) => z' ∈ P.asIdeal) hxy'
        exact hmem.mpr hz
      change fibreProductToA' D z' ∈ x.asIdeal at hz'
      have hmul : w * a' ∈ x.asIdeal := by simpa [z'] using hz'
      exact (x.2.mem_or_mem hmul).resolve_left hwx
  letI : Mono (↾PrimeSpectrum.comap (fibreProductToB D)) :=
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
    apply CategoryTheory.Limits.Types.isPushout_of_isPullback_of_mono' hpull
    · exact hjoint
    · exact hoff
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
        change p ∈ Set.range (PrimeSpectrum.comap (fibreProductToB D))
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
        (U : Set (PrimeSpectrum (fibreProductRing D)))
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
        (U : Set (PrimeSpectrum (fibreProductRing D)))
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
      rw [Polynomial.natDegree_mul' (by simp [hp, hBzero])]
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
  sorry

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
  sorry

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
theorem fibreProductModuleAdjunctionMap_surjective
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) (L' : ModuleCat.{u} (fibreProductRing D)) :
    Function.Surjective (fun x => fibreProductModuleAdjunctionMap D L' x) := by
  sorry

/-- The displayed adjunction map is not injective for arbitrary pullback
diagrams.  The source's concrete witness is
`B' = k[x, y]/(xy)`, `A' = B'/(x)`, `B = B'/(y)`,
`A = B'/(x, y)`, and `L' = B'/(x - y)`. -/
theorem fibreProductModuleAdjunctionMap_not_injective_in_general :
    ¬ (∀ {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
        (D : FibreProductSituation A A' B)
        (L' : ModuleCat.{u} (fibreProductRing D)),
        Function.Injective (fun x => fibreProductModuleAdjunctionMap D L' x)) := by
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
  sorry

/-- The compatible-pair pullback is functorial for morphisms of triples. -/
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

/-- Exactness, injectivity on the left, and surjectivity on the right of the
source's short exact sequence. -/
theorem fibreProduct_exact_sequence
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Function.Injective (fibreProductExactLeft D) ∧
      Function.Exact (fibreProductExactLeft D) (fibreProductExactRight D) ∧
      Function.Surjective (fibreProductExactRight D) := by
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
theorem fibreProduct_flat_module_equivalence_exists
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Nonempty (fibreProductFlatModuleCategory D ≌ fibreProductFlatGluingCategory D) := by
  sorry

noncomputable def fibreProduct_flat_module_equivalence
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    fibreProductFlatModuleCategory D ≌ fibreProductFlatGluingCategory D :=
  Classical.choice (fibreProduct_flat_module_equivalence_exists D)

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
theorem fibreProduct_finite_projective_equivalence_exists
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Nonempty
      (fibreProductFiniteProjectiveModuleCategory D ≌
        fibreProductFiniteProjectiveGluingCategory D) := by
  sorry

noncomputable def fibreProduct_finite_projective_equivalence
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    fibreProductFiniteProjectiveModuleCategory D ≌
      fibreProductFiniteProjectiveGluingCategory D :=
  Classical.choice (fibreProduct_finite_projective_equivalence_exists D)

end

end Formalization.Books.MoreAlgebra.Unit06
