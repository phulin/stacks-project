import Formalization.Books.Categories.Unit31.TwoFibreProducts
import Formalization.Books.Algebra.Unit09.Localization
import Formalization.Books.Algebra.Unit51.MoreNoetherianRings
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Exact.Basic
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# More on Algebra, Chapter 5: Fibre products of rings, I

This file uses Mathlib's canonical pullback subrings and subalgebras.  The
category of triples of modules is the canonical full subcategory of a comma
category used by the earlier chapter's `IsoComma` construction, and the
module fibre product is the categorical pullback in `ModuleCat`; the source's
compatible-pair description is recorded alongside that construction.
-/

namespace Formalization.Books.MoreAlgebra.Unit05

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit31
open scoped ChangeOfRings

universe u

noncomputable section

/-! ## Finite type and finite-index fibre products -/

/-- The exact sequence underlying the first displayed fibre-product diagram.

The source uses this exactness in its proof; the canonical equalizer
presentation of `AlgHom.pullback` is used for the object itself. -/
theorem algebraPullback_exact
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) :
    Function.Exact
      (fun x : AlgHom.pullback f g => (x : A × C))
      (fun x : A × C => f x.1 - g x.2) := by
  change ∀ x : A × C, f x.1 - g x.2 = 0 ↔
    x ∈ Set.range (fun x : AlgHom.pullback f g => (x : A × C))
  intro x
  constructor
  · intro h
    exact Set.mem_range.mpr ⟨⟨x, sub_eq_zero.mp h⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact sub_eq_zero.mpr y.property

/- The proof's two exact rows use the kernel `I = ker(A → B)` and the
canonical projections of the algebra pullback. -/

/-- The ideal `I` used in the exact-row diagram in the proof of
`finiteType_algHom_pullback`. -/
abbrev algebraPullbackKernel
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) : Ideal A :=
  RingHom.ker f.toRingHom

/-- The inclusion of the proof's kernel `I` into `A`. -/
def algebraPullbackKernelToA
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    algebraPullbackKernel f → A :=
  fun x => x

/-- The inclusion of `I` into the algebra pullback `A ×_B C`. -/
def algebraPullbackKernelToPullback
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) :
    algebraPullbackKernel f → AlgHom.pullback f g :=
  fun x => ⟨((x : A), 0), by
    change f (x : A) = g 0
    rw [show f (x : A) = 0 by simpa [algebraPullbackKernel] using x.property]
    simp⟩

/-- The map from the fibre product to the product used in the Artin--Tate
argument. -/
def algebraPullbackToProduct
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) :
    AlgHom.pullback f g →+* A × C :=
  (AlgHom.pullbackFst f g).toRingHom.prod (AlgHom.pullbackSnd f g).toRingHom

/-- The map from the fibre product to the product is injective. -/
theorem algebraPullback_to_product_injective
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) :
    Function.Injective (algebraPullbackToProduct f g) := by
  intro x y hxy
  exact Subtype.ext hxy

private noncomputable def algebraPullback_product_finite_aux
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B)
    (hf : Function.Surjective f)
    (hg : RingHom.Finite g.toRingHom) :
    Unit × PLift (@Module.Finite (AlgHom.pullback f g) (A × C) _ _
      (@Algebra.toModule (AlgHom.pullback f g) (A × C) _ _
        (algebraPullbackToProduct f g).toAlgebra)) := by
  classical
  letI : Algebra (AlgHom.pullback f g) A :=
    (AlgHom.pullbackFst f g).toRingHom.toAlgebra
  letI : Algebra (AlgHom.pullback f g) C :=
    (AlgHom.pullbackSnd f g).toRingHom.toAlgebra
  letI : Algebra C B := g.toRingHom.toAlgebra
  letI : Algebra (AlgHom.pullback f g) (A × C) :=
    (algebraPullbackToProduct f g).toAlgebra
  letI : Module.Finite C B := by
    simpa only [RingHom.Finite] using hg
  let D := AlgHom.pullback f g
  let hfin := Module.Finite.exists_fin' C B
  let n := Classical.choose hfin
  let hfin' : ∃ l : (Fin n → C) →ₗ[C] B, Function.Surjective l :=
    Classical.choose_spec hfin
  let l := Classical.choose hfin'
  have hl : Function.Surjective l := Classical.choose_spec hfin'
  choose x hx using fun i : Fin n => hf (l (Pi.single i 1))
  let q : (D × (Fin n → D)) →ₗ[D] A :=
    { toFun := fun z =>
        (AlgHom.pullbackFst f g) z.1 +
          ∑ i, (AlgHom.pullbackFst f g) (z.2 i) * x i
      map_add' := by
        intro z w
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, Finset.sum_add_distrib,
          add_mul]
        abel
      map_smul' := by
        intro d z
        change
          (AlgHom.pullbackFst f g) (d * z.1) +
              ∑ i, (AlgHom.pullbackFst f g) (d * z.2 i) * x i =
            (AlgHom.pullbackFst f g) d *
              ((AlgHom.pullbackFst f g) z.1 +
                ∑ i, (AlgHom.pullbackFst f g) (z.2 i) * x i)
        simp only [map_mul]
        rw [mul_add, Finset.mul_sum]
        ring_nf }
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨v, hv⟩ := hl (f a)
    choose d hd using fun i : Fin n =>
      AlgHom.surjective_pullbackSnd_of_surjective f g hf (v i)
    have hsum : f (∑ i, (AlgHom.pullbackFst f g) (d i) * x i) = l v := by
      calc
        f (∑ i, (AlgHom.pullbackFst f g) (d i) * x i) =
            ∑ i, g (v i) * l (Pi.single i 1) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro i hi
              have hdi :
                  f ((AlgHom.pullbackFst f g) (d i)) = g (v i) := by
                calc
                  f ((AlgHom.pullbackFst f g) (d i)) =
                      g ((AlgHom.pullbackSnd f g) (d i)) := (d i).property
                  _ = g (v i) := by rw [hd i]
              rw [map_mul, hdi, hx i]
        _ = ∑ i, l (Pi.single i (v i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hsingle :
                  (algebraMap C (Fin n → C)) (v i) * Pi.single i 1 =
                    Pi.single i (v i) := by
                ext j
                by_cases hji : i = j <;> simp [hji]
              have hm := (l.map_smul (v i) (Pi.single i 1)).symm
              have hm' :
                  (algebraMap C B) (v i) * l (Pi.single i 1) =
                    l ((algebraMap C (Fin n → C)) (v i) * Pi.single i 1) := by
                simpa only [Algebra.smul_def] using hm
              rw [hsingle] at hm'
              simpa [RingHom.algebraMap_toAlgebra] using hm'
        _ = l (∑ i, Pi.single i (v i)) := by rw [map_sum]
        _ = l v := by rw [Finset.univ_sum_single]
    let k : D :=
      ⟨(a - ∑ i, (AlgHom.pullbackFst f g) (d i) * x i, 0), by
        change f (a - ∑ i, (AlgHom.pullbackFst f g) (d i) * x i) = g 0
        rw [map_sub, hsum, hv]
        simp⟩
    refine ⟨(k, d), ?_⟩
    change (a - ∑ i, (AlgHom.pullbackFst f g) (d i) * x i) +
      ∑ i, (AlgHom.pullbackFst f g) (d i) * x i = a
    exact sub_add_cancel _ _
  let s : D →ₗ[D] C :=
    { toFun := AlgHom.pullbackSnd f g
      map_add' := by simp
      map_smul' := by
        intro d z
        change (d : A × C).2 * (z : A × C).2 =
          (d : A × C).2 * (z : A × C).2
        rfl }
  let qp : (D × (Fin n → D)) × D →ₗ[D] (A × C) :=
    { toFun := fun z => (q z.1, s z.2)
      map_add' := by
        intro z w
        change (q (z.1 + w.1), s (z.2 + w.2)) =
          (q z.1 + q w.1, s z.2 + s w.2)
        exact Prod.ext (q.map_add _ _) (s.map_add _ _)
      map_smul' := by
        intro d z
        change (q (d • z.1), s (d • z.2)) =
          ((AlgHom.pullbackFst f g) d * q z.1,
            (AlgHom.pullbackSnd f g) d * s z.2)
        exact Prod.ext (q.map_smul _ _) (s.map_smul _ _) }
  have hqp : Function.Surjective qp := by
    intro z
    obtain ⟨u, hu⟩ := hq z.1
    obtain ⟨v, hv⟩ :=
      AlgHom.surjective_pullbackSnd_of_surjective f g hf z.2
    refine ⟨(u, v), ?_⟩
    apply Prod.ext
    · exact hu
    · change s v = z.2
      simpa [s] using hv
  exact ⟨(), ⟨Module.Finite.of_surjective qp hqp⟩⟩

/-- The product ring is finite as a module over the fibre product, as used
in the Artin--Tate argument. -/
theorem algebraPullback_product_finite
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B)
    (hf : Function.Surjective f)
    (hg : RingHom.Finite g.toRingHom) :
    (algebraPullbackToProduct f g).Finite := by
  change Module.Finite (AlgHom.pullback f g) (A × C)
  exact (algebraPullback_product_finite_aux f g hf hg).2.down

/-- The exact rows in the proof of the finite-type fibre-product lemma,
with `I` represented by the canonical kernel ideal. -/
theorem algebraPullback_exact_rows
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) (hf : Function.Surjective f) :
    Function.Exact (algebraPullbackKernelToA f) f ∧
      Function.Surjective f ∧
      Function.Exact (algebraPullbackKernelToPullback f g)
        (AlgHom.pullbackSnd f g) ∧
      Function.Surjective (AlgHom.pullbackSnd f g) := by
  refine ⟨?_, hf, ?_, ?_⟩
  · change ∀ a : A, f a = 0 ↔
      a ∈ Set.range (algebraPullbackKernelToA f)
    intro a
    constructor
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      change f (x : A) = 0
      simpa [algebraPullbackKernel] using x.property
  · change ∀ y : AlgHom.pullback f g,
      (AlgHom.pullbackSnd f g) y = 0 ↔
        y ∈ Set.range (algebraPullbackKernelToPullback f g)
    intro y
    constructor
    · intro hy
      change y.1.2 = 0 at hy
      have ha : f ((AlgHom.pullbackFst f g) y) = 0 := by
        change f y.1.1 = 0
        calc
          f y.1.1 = g y.1.2 := y.property
          _ = 0 := by rw [hy]; simp
      refine ⟨⟨(AlgHom.pullbackFst f g) y, ha⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hy.symm
    · rintro ⟨x, rfl⟩
      simp [algebraPullbackKernelToPullback]
  · exact AlgHom.surjective_pullbackSnd_of_surjective f g hf

/-! The source-facing finite-type lemma follows the proof-support interfaces
above, which makes the Artin--Tate route available when its body is filled. -/

private noncomputable def finiteType_algHom_pullback_aux
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B)
    (hR : IsNoetherianRing R)
    (hA : Algebra.FiniteType R A)
    (hB : Algebra.FiniteType R B)
    (hC : Algebra.FiniteType R C)
    (hf : Function.Surjective f)
    (hg : RingHom.Finite g.toRingHom) :
    PLift (Algebra.FiniteType R B ∧ Algebra.FiniteType R (AlgHom.pullback f g)) := by
  letI : Algebra (AlgHom.pullback f g) (A × C) :=
    (algebraPullbackToProduct f g).toAlgebra
  let tower : IsScalarTower R (AlgHom.pullback f g) (A × C) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext r <;> simp [RingHom.algebraMap_toAlgebra, algebraPullbackToProduct])
  letI : IsScalarTower R (AlgHom.pullback f g) (A × C) := tower
  letI : Algebra.FiniteType R A := hA
  letI : Algebra.FiniteType R B := hB
  letI : Algebra.FiniteType R C := hC
  have hfinite : Module.Finite (AlgHom.pullback f g) (A × C) :=
    algebraPullback_product_finite f g hf hg
  have hprod : (⊤ : Subalgebra R (A × C)).FG :=
    (inferInstance : Algebra.FiniteType R (A × C)).out
  have hmodule : (⊤ : Submodule (AlgHom.pullback f g) (A × C)).FG :=
    hfinite.fg_top
  have hinjective :
      Function.Injective (algebraMap (AlgHom.pullback f g) (A × C)) := by
    simpa [RingHom.algebraMap_toAlgebra] using
      (algebraPullback_to_product_injective f g)
  exact ⟨⟨hB, ⟨@fg_of_fg_of_fg R (AlgHom.pullback f g) (A × C) _ _ _ _ _ _
    tower hR hprod hmodule hinjective⟩⟩⟩

/-- A finite-type fibre product of algebras in the hypotheses of the source
lemma.  `AlgHom.pullback` is Mathlib's canonical fibre-product algebra, and
`RingHom.Finite` is the established finite-module condition for `C → B`. -/
theorem finiteType_algHom_pullback
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B)
    (hR : IsNoetherianRing R)
    (hA : Algebra.FiniteType R A)
    (hB : Algebra.FiniteType R B)
    (hC : Algebra.FiniteType R C)
    (hf : Function.Surjective f)
    (hg : RingHom.Finite g.toRingHom) :
    Algebra.FiniteType R (AlgHom.pullback f g) := by
  exact (finiteType_algHom_pullback_aux f g hR hA hB hC hf hg).down.2

/-- The product of a family of algebra maps with varying codomains.  Mathlib
provides `AlgHom.pi` for a common domain; this small componentwise map is the
corresponding canonical construction needed for the finite-index diagram. -/
def piAlgHomMap
    {R I : Type*} {A B : I → Type*}
    [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)]
    (f : ∀ i, A i →ₐ[R] B i) :
    (∀ i, A i) →ₐ[R] (∀ i, B i) :=
  { toRingHom :=
      { toFun := fun x i => f i (x i)
        map_one' := by
          funext i
          simp
        map_mul' := by
          intro x y
          funext i
          simp
        map_zero' := by
          funext i
          simp
        map_add' := by
          intro x y
          funext i
          simp }
    commutes' := by
      intro r
      funext i
      simp }

private theorem finiteType_pi_of_finite
    {R I : Type u} {A : I → Type u}
    [CommRing R] [∀ i, CommRing (A i)]
    [∀ i, Algebra R (A i)] [Finite I]
    (hA : ∀ i, Algebra.FiniteType R (A i)) :
    Algebra.FiniteType R (∀ i, A i) := by
  classical
  revert A
  apply Finite.induction_empty_option
    (P := fun I => ∀ {A : I → Type u} [∀ i, CommRing (A i)]
      [∀ i, Algebra R (A i)],
      (∀ i, Algebra.FiniteType R (A i)) →
        Algebra.FiniteType R (∀ i, A i))
  · intro I J e ih A _ _ hA
    exact Algebra.FiniteType.equiv
      (ih (A := fun i => A (e i)) (fun i => hA (e i)))
      (AlgEquiv.piCongrLeft R A e)
  · intro A _ _ hA
    let : Subsingleton (∀ i : PEmpty, A i) :=
      ⟨fun x y => funext fun i => PEmpty.elim i⟩
    exact Algebra.FiniteType.of_surjective (Algebra.ofId R _)
      (fun x => ⟨0, Subsingleton.elim _ _⟩)
  · intro I _ ih A _ _ hA
    let : ∀ i : I, CommRing (A (some i)) := fun i => inferInstance
    let : ∀ i : I, Algebra R (A (some i)) := fun i => inferInstance
    have hprod : Algebra.FiniteType R
        (A none × (∀ i : I, A (some i))) := by
      let : Algebra.FiniteType R (∀ i : I, A (some i)) :=
        ih (A := fun i => A (some i)) (fun i => hA (some i))
      infer_instance
    exact Algebra.FiniteType.equiv hprod
      (AlgEquiv.ofRingEquiv
        (f := (RingEquiv.piOptionEquivProd (R := A)).symm) (by
        intro r
        ext i
        cases i <;> simp [RingEquiv.piOptionEquivProd,
          Equiv.piOptionEquivProd]))

/-- The finite-index cartesian-product consequence of the first lemma. -/
theorem finiteType_of_finite_cartesian_product
    {R P Q I : Type u} {A B : I → Type u}
    [CommRing R] [CommRing P] [CommRing Q]
    [Algebra R P] [Algebra R Q]
    [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
    [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)]
    [Finite I]
    (φ : ∀ i, A i →ₐ[R] B i)
    (ψ : ∀ i, Q →ₐ[R] B i)
    (pA : P →ₐ[R] (∀ i, A i))
    (pQ : P →ₐ[R] Q)
    (hcart :
      IsPullback
        (CommRingCat.ofHom pA.toRingHom)
        (CommRingCat.ofHom pQ.toRingHom)
        (CommRingCat.ofHom (piAlgHomMap φ).toRingHom)
        (CommRingCat.ofHom (AlgHom.pi ψ).toRingHom))
    (hR : IsNoetherianRing R)
    (hQ : Algebra.FiniteType R Q)
    (hA : ∀ i, Algebra.FiniteType R (A i))
    (hB : ∀ i, Algebra.FiniteType R (B i))
    (hφ : ∀ i, Function.Surjective (φ i))
    (hψ : ∀ i, Function.Surjective (ψ i)) :
    Algebra.FiniteType R P := by
  let : Algebra.FiniteType R (∀ i, A i) := finiteType_pi_of_finite hA
  let : Algebra.FiniteType R (∀ i, B i) := finiteType_pi_of_finite hB
  have hφ' : Function.Surjective (piAlgHomMap φ) := by
    intro y
    choose x hx using fun i => hφ i (y i)
    exact ⟨x, funext fun i => hx i⟩
  have hfiniteψ : RingHom.Finite (AlgHom.pi ψ).toRingHom := by
    let : ∀ i, Algebra Q (B i) := fun i => (ψ i).toRingHom.toAlgebra
    let : ∀ i, Module.Finite Q (B i) := fun i =>
      Module.Finite.of_surjective (Algebra.linearMap Q (B i)) (hψ i)
    change Module.Finite Q (∀ i, B i)
    infer_instance
  have hpull : Algebra.FiniteType R (AlgHom.pullback (piAlgHomMap φ) (AlgHom.pi ψ)) :=
    finiteType_algHom_pullback (piAlgHomMap φ) (AlgHom.pi ψ) hR
      (finiteType_pi_of_finite hA) (finiteType_pi_of_finite hB) hQ hφ' hfiniteψ
  let u : P →ₐ[R] AlgHom.pullback (piAlgHomMap φ) (AlgHom.pi ψ) :=
    (pA.prod pQ).codRestrict _ (by
      intro x
      change (piAlgHomMap φ) (pA x) = (AlgHom.pi ψ) (pQ x)
      simpa using congrArg (fun k => k.hom x) hcart.w)
  have w :
      CommRingCat.ofHom (AlgHom.pullbackFst (piAlgHomMap φ) (AlgHom.pi ψ)).toRingHom ≫
          CommRingCat.ofHom (piAlgHomMap φ).toRingHom =
        CommRingCat.ofHom (AlgHom.pullbackSnd (piAlgHomMap φ) (AlgHom.pi ψ)).toRingHom ≫
          CommRingCat.ofHom (AlgHom.pi ψ).toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom]
    exact congrArg (fun k => k x)
      (AlgHom.pullback_comm_sq (piAlgHomMap φ) (AlgHom.pi ψ))
  let vRing : AlgHom.pullback (piAlgHomMap φ) (AlgHom.pi ψ) →+* P :=
    (hcart.lift
      (CommRingCat.ofHom (AlgHom.pullbackFst (piAlgHomMap φ) (AlgHom.pi ψ)).toRingHom)
      (CommRingCat.ofHom (AlgHom.pullbackSnd (piAlgHomMap φ) (AlgHom.pi ψ)).toRingHom)
      w).hom
  have hvA :
      pA.toRingHom.comp vRing =
        (AlgHom.pullbackFst (piAlgHomMap φ) (AlgHom.pi ψ)).toRingHom := by
    have hh := congrArg CommRingCat.Hom.hom (hcart.lift_fst _ _ w)
    dsimp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hh
    exact hh
  have hvB :
      pQ.toRingHom.comp vRing =
        (AlgHom.pullbackSnd (piAlgHomMap φ) (AlgHom.pi ψ)).toRingHom := by
    have hh := congrArg CommRingCat.Hom.hom (hcart.lift_snd _ _ w)
    dsimp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hh
    exact hh
  let v : AlgHom.pullback (piAlgHomMap φ) (AlgHom.pi ψ) →ₐ[R] P :=
    { vRing with
      commutes' := by
        intro r
        have heq :
            CommRingCat.ofHom (vRing.comp (algebraMap R
              (AlgHom.pullback (piAlgHomMap φ) (AlgHom.pi ψ)))) =
              CommRingCat.ofHom (algebraMap R P) := by
          apply hcart.hom_ext
          · ext x
            simp [vRing, CategoryTheory.Category.assoc]
          · ext x
            simp [vRing, CategoryTheory.Category.assoc]
        exact congrArg (fun k => k.hom r) heq }
  have huv : vRing.comp u.toRingHom = RingHom.id P := by
    apply RingHom.ext
    intro x
    have heq :
        CommRingCat.ofHom (vRing.comp u.toRingHom) =
          CommRingCat.ofHom (RingHom.id P) := by
      apply hcart.hom_ext
      · apply CommRingCat.hom_ext
        apply RingHom.ext
        intro y
        dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
          CommRingCat.hom_ofHom]
        change pA (vRing (u y)) = pA y
        have hh := DFunLike.congr_fun hvA (u y)
        change pA (vRing (u y)) = pA y at hh
        exact hh
      · apply CommRingCat.hom_ext
        apply RingHom.ext
        intro y
        dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
          CommRingCat.hom_ofHom]
        change pQ (vRing (u y)) = pQ y
        have hh := DFunLike.congr_fun hvB (u y)
        change pQ (vRing (u y)) = pQ y at hh
        exact hh
    exact congrArg (fun k => k.hom x) heq
  have hvu : u.toRingHom.comp vRing =
      RingHom.id (AlgHom.pullback (piAlgHomMap φ) (AlgHom.pi ψ)) := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · change pA (vRing x) = (AlgHom.pullbackFst (piAlgHomMap φ) (AlgHom.pi ψ)) x
      exact DFunLike.congr_fun hvA x
    · change pQ (vRing x) = (AlgHom.pullbackSnd (piAlgHomMap φ) (AlgHom.pi ψ)) x
      exact DFunLike.congr_fun hvB x
  let e : P ≃+* AlgHom.pullback (piAlgHomMap φ) (AlgHom.pi ψ) :=
    RingEquiv.ofRingHom u.toRingHom vRing hvu huv
  exact Algebra.FiniteType.equiv hpull
    (AlgEquiv.ofRingEquiv (f := e.symm) (by
      intro r
      change v (algebraMap R
        (AlgHom.pullback (piAlgHomMap φ) (AlgHom.pi ψ)) r) = algebraMap R P r
      exact v.commutes r))

/-! ## Localization -/

/-- The element of a ring pullback corresponding to compatible elements on
the two lower-right corners of the source diagram. -/
def ringPullbackElement
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (g : B) (f : R')
    (h : s g = t f) : RingHom.pullback s t :=
  ⟨(g, f), h⟩

/-- The localized first projection from the canonical ring pullback. -/
noncomputable def localizedPullbackFst
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (g : B) (f : R')
    (h : s g = t f) :
    Localization.Away (ringPullbackElement s t g f h) →+*
      Localization.Away
        ((RingHom.pullbackFst s t) (ringPullbackElement s t g f h)) :=
  Localization.awayMap (RingHom.pullbackFst s t)
    (ringPullbackElement s t g f h)

/-- The localized second projection from the canonical ring pullback. -/
noncomputable def localizedPullbackSnd
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (g : B) (f : R')
    (h : s g = t f) :
    Localization.Away (ringPullbackElement s t g f h) →+*
      Localization.Away
        ((RingHom.pullbackSnd s t) (ringPullbackElement s t g f h)) :=
  Localization.awayMap (RingHom.pullbackSnd s t)
    (ringPullbackElement s t g f h)

/-- The localized map from `B_g` to the common localization of `R`. -/
noncomputable def localizedPullbackBaseLeft
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (g : B) (f : R')
    (_h : s g = t f) :
    Localization.Away g →+* Localization.Away (s g) :=
  Localization.awayMap s g

/-- The localized map from `R'_f` to the same chosen common localization. -/
noncomputable def localizedPullbackBaseRight
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (g : B) (f : R')
    (h : s g = t f) :
    Localization.Away f →+* Localization.Away (s g) := by
  rw [h]
  exact Localization.awayMap t f

private theorem ringPullback_exact_aux
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) :
    Function.Exact
      (fun x : RingHom.pullback s t => (x : B × R'))
      (fun x : B × R' => s x.1 - t x.2) := by
  change ∀ x : B × R', s x.1 - t x.2 = 0 ↔
    x ∈ Set.range (fun x : RingHom.pullback s t => (x : B × R'))
  intro x
  constructor
  · intro hx
    exact Set.mem_range.mpr ⟨⟨x, sub_eq_zero.mp hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact sub_eq_zero.mpr y.property

/-- Localization preserves the ring pullback diagram from the source. -/
theorem localized_ring_pullback_isPullback
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (g : B) (f : R')
    (h : s g = t f) :
    IsPullback
      (CommRingCat.ofHom (localizedPullbackFst s t g f h))
      (CommRingCat.ofHom (localizedPullbackSnd s t g f h))
      (CommRingCat.ofHom (localizedPullbackBaseLeft s t g f h))
      (CommRingCat.ofHom (localizedPullbackBaseRight s t g f h)) := by
  let P := RingHom.pullback s t
  let hp : P := ringPullbackElement s t g f h
  let : Algebra P B := (RingHom.pullbackFst s t).toAlgebra
  let : Algebra P R' := (RingHom.pullbackSnd s t).toAlgebra
  let : Algebra P R := (s.comp (RingHom.pullbackFst s t)).toAlgebra
  let : Module P (Localization.Away g) :=
    Module.compHom (Localization.Away g)
      ((algebraMap B (Localization.Away g)).comp (RingHom.pullbackFst s t))
  let : Module P (Localization.Away f) :=
    Module.compHom (Localization.Away f)
      ((algebraMap R' (Localization.Away f)).comp (RingHom.pullbackSnd s t))
  let : Module P (Localization.Away (s g)) :=
    Module.compHom (Localization.Away (s g))
      ((algebraMap R (Localization.Away (s g))).comp
        (s.comp (RingHom.pullbackFst s t)))
  let : SMul P (Localization.Away g) :=
    ⟨fun x y => ((algebraMap B (Localization.Away g)).comp
      (RingHom.pullbackFst s t)) x * y⟩
  let : SMul P (Localization.Away f) :=
    ⟨fun x y => ((algebraMap R' (Localization.Away f)).comp
      (RingHom.pullbackSnd s t)) x * y⟩
  let : SMul P (Localization.Away (s g)) :=
    ⟨fun x y => ((algebraMap R (Localization.Away (s g))).comp
      (s.comp (RingHom.pullbackFst s t))) x * y⟩
  let : IsScalarTower P B (Localization.Away g) :=
    IsScalarTower.of_algebraMap_smul (by
      intro x y
      rw [RingHom.algebraMap_toAlgebra]
      rw [Algebra.smul_def]
      rfl)
  let : IsScalarTower P R' (Localization.Away f) :=
    IsScalarTower.of_algebraMap_smul (by
      intro x y
      rw [RingHom.algebraMap_toAlgebra]
      rw [Algebra.smul_def]
      rfl)
  let : IsLocalizedModule (.powers ((algebraMap P B) hp))
      (Algebra.linearMap B (Localization.Away g)) := by
    simpa [RingHom.algebraMap_toAlgebra, hp, ringPullbackElement] using
      (inferInstance : IsLocalizedModule (.powers g)
        (Algebra.linearMap B (Localization.Away g)))
  let : IsLocalizedModule (.powers ((algebraMap P R') hp))
      (Algebra.linearMap R' (Localization.Away f)) := by
    simpa [RingHom.algebraMap_toAlgebra, hp, ringPullbackElement] using
      (inferInstance : IsLocalizedModule (.powers f)
        (Algebra.linearMap R' (Localization.Away f)))
  have hB_loc : IsLocalizedModule (.powers hp)
      ((Algebra.linearMap B (Localization.Away g)).restrictScalars P) := by
    exact IsLocalizedModule.restrictScalars_powers hp
      (Algebra.linearMap B (Localization.Away g))
  have hR'_loc : IsLocalizedModule (.powers hp)
      ((Algebra.linearMap R' (Localization.Away f)).restrictScalars P) := by
    exact IsLocalizedModule.restrictScalars_powers hp
      (Algebra.linearMap R' (Localization.Away f))
  let : Algebra P (B × R') :=
    ((RingHom.pullbackFst s t).prod (RingHom.pullbackSnd s t)).toAlgebra
  let : Algebra P (Localization.Away (s g)) :=
    ((algebraMap R (Localization.Away (s g))).comp
      (s.comp (RingHom.pullbackFst s t))).toAlgebra
  let : IsScalarTower P R (Localization.Away (s g)) :=
    IsScalarTower.of_algebraMap_smul (by
      intro x y
      rw [RingHom.algebraMap_toAlgebra]
      rw [Algebra.smul_def]
      rfl)
  let i : P →ₗ[P] B × R' := Algebra.linearMap P (B × R')
  let d : (B × R') →ₗ[P] R :=
    { toFun := fun x => s x.1 - t x.2
      map_add' := by
        intro x y
        simp only [Prod.fst_add, Prod.snd_add, map_add, sub_add_sub_comm]
      map_smul' := by
        intro x y
        change s (x.1.1 * y.1) - t (x.1.2 * y.2) =
          s x.1.1 * (s y.1 - t y.2)
        have hx : s (x : B × R').1 = t (x : B × R').2 := x.property
        rw [map_mul, map_mul, hx]
        ring }
  let f1 : (B × R') →ₗ[P]
      (Localization.Away g × Localization.Away f) :=
    { toFun := fun x =>
        ((Algebra.linearMap B (Localization.Away g)) x.1,
          (Algebra.linearMap R' (Localization.Away f)) x.2)
      map_add' := by
        intro x y
        ext <;> simp
      map_smul' := by
        intro x y
        ext
        · change (algebraMap B (Localization.Away g))
              ((algebraMap P B x) * y.1) =
            (algebraMap B (Localization.Away g)) (algebraMap P B x) *
              (algebraMap B (Localization.Away g) y.1)
          rw [map_mul]
        · change (algebraMap R' (Localization.Away f))
              ((algebraMap P R' x) * y.2) =
            (algebraMap R' (Localization.Away f)) (algebraMap P R' x) *
              (algebraMap R' (Localization.Away f) y.2)
          rw [map_mul] }
  let f2 : R →ₗ[P] Localization.Away (s g) :=
    (Algebra.linearMap R (Localization.Away (s g))).restrictScalars P
  have hP_loc : IsLocalizedModule (.powers hp)
      (Algebra.linearMap P (Localization.Away hp)) := by
    infer_instance
  let : IsLocalizedModule (.powers ((algebraMap P R) hp))
      (Algebra.linearMap R (Localization.Away (s g))) := by
    simpa [RingHom.algebraMap_toAlgebra, hp, ringPullbackElement] using
      (inferInstance : IsLocalizedModule (.powers (s g))
        (Algebra.linearMap R (Localization.Away (s g))))
  have hbase_loc : IsLocalizedModule (.powers hp) f2 := by
    exact IsLocalizedModule.restrictScalars_powers hp
      (Algebra.linearMap R (Localization.Away (s g)))
  have hprod_loc : IsLocalizedModule (.powers hp) f1 := by
    constructor
    · intro c
      rw [Module.End.isUnit_iff]
      constructor
      · intro x y hxy
        apply Prod.ext
        · apply ((Module.End.isUnit_iff _).mp (hB_loc.map_units c)).1
          exact congrArg Prod.fst hxy
        · apply ((Module.End.isUnit_iff _).mp (hR'_loc.map_units c)).1
          exact congrArg Prod.snd hxy
      · intro x
        obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).mp (hB_loc.map_units c)).2 x.1
        obtain ⟨z, hz⟩ := ((Module.End.isUnit_iff _).mp (hR'_loc.map_units c)).2 x.2
        change c • y = x.1 at hy
        change c • z = x.2 at hz
        exact ⟨(y, z), by
          change (c • y, c • z) = x
          exact Prod.ext hy hz⟩
    · intro x
      rcases hB_loc.surj x.1 with ⟨⟨y, c₁⟩, hy⟩
      rcases hR'_loc.surj x.2 with ⟨⟨z, c₂⟩, hz⟩
      change c₁ • x.1 = (Algebra.linearMap B (Localization.Away g)) y at hy
      change c₂ • x.2 = (Algebra.linearMap R' (Localization.Away f)) z at hz
      refine ⟨((c₂ • y, c₁ • z), c₁ * c₂), ?_⟩
      apply Prod.ext
      · change (c₁ * c₂) • x.1 =
          (Algebra.linearMap B (Localization.Away g)) (c₂ • y)
        calc
          (c₁ * c₂) • x.1 = c₂ • (c₁ • x.1) := by
            change
              (algebraMap B (Localization.Away g))
                  ((RingHom.pullbackFst s t) (c₁ * c₂)) * x.1 =
                (algebraMap B (Localization.Away g))
                  ((RingHom.pullbackFst s t) c₂) *
                  ((algebraMap B (Localization.Away g))
                    ((RingHom.pullbackFst s t) c₁) * x.1)
            simp only [map_mul]
            ring
          _ = c₂ • (Algebra.linearMap B (Localization.Away g) y) := by rw [hy]
          _ = (Algebra.linearMap B (Localization.Away g)) (c₂ • y) := by
            exact (LinearMap.map_smul_of_tower
              (Algebra.linearMap B (Localization.Away g)) c₂ y).symm
      · change (c₁ * c₂) • x.2 =
          (Algebra.linearMap R' (Localization.Away f)) (c₁ • z)
        calc
          (c₁ * c₂) • x.2 = c₁ • (c₂ • x.2) := by
            change
              (algebraMap R' (Localization.Away f))
                  ((RingHom.pullbackSnd s t) (c₁ * c₂)) * x.2 =
                (algebraMap R' (Localization.Away f))
                  ((RingHom.pullbackSnd s t) c₁) *
                  ((algebraMap R' (Localization.Away f))
                    ((RingHom.pullbackSnd s t) c₂) * x.2)
            simp only [map_mul]
            ring
          _ = c₁ • (Algebra.linearMap R' (Localization.Away f) z) := by rw [hz]
          _ = (Algebra.linearMap R' (Localization.Away f)) (c₁ • z) := by
            exact (LinearMap.map_smul_of_tower
              (Algebra.linearMap R' (Localization.Away f)) c₁ z).symm
    · intro x y hxy
      rcases hB_loc.exists_of_eq (congrArg Prod.fst hxy) with ⟨c₁, hc₁⟩
      rcases hR'_loc.exists_of_eq (congrArg Prod.snd hxy) with ⟨c₂, hc₂⟩
      refine ⟨c₁ * c₂, ?_⟩
      apply Prod.ext
      · change (c₁ * c₂) • x.1 = (c₁ * c₂) • y.1
        calc
          (c₁ * c₂) • x.1 = c₂ • (c₁ • x.1) := by
            change
              (algebraMap P B) (c₁ * c₂ : P) * x.1 =
                (algebraMap P B)
                  (c₂ : P) *
                  ((algebraMap P B) (c₁ : P) * x.1)
            simp only [map_mul]
            ring
          _ = c₂ • (c₁ • y.1) := by rw [hc₁]
          _ = (c₁ * c₂) • y.1 := by
            change
              (algebraMap P B) (c₂ : P) *
                  ((algebraMap P B)
                    (c₁ : P) * y.1) =
                (algebraMap P B)
                  (c₁ * c₂ : P) * y.1
            simp only [map_mul]
            ring
      · change (c₁ * c₂) • x.2 = (c₁ * c₂) • y.2
        calc
          (c₁ * c₂) • x.2 = c₁ • (c₂ • x.2) := by
            change
              (algebraMap P R')
                  (c₁ * c₂ : P) * x.2 =
                (algebraMap P R')
                  (c₁ : P) *
                  ((algebraMap P R')
                    (c₂ : P) * x.2)
            simp only [map_mul]
            ring
          _ = c₁ • (c₂ • y.2) := by rw [hc₂]
          _ = (c₁ * c₂) • y.2 := by
            change
              (algebraMap P R')
                  (c₁ : P) *
                  ((algebraMap P R')
                    (c₂ : P) * y.2) =
                (algebraMap P R')
                  (c₁ * c₂ : P) * y.2
            simp only [map_mul]
            ring
  let : IsLocalizedModule (.powers hp)
      (Algebra.linearMap P (Localization.Away hp)) := hP_loc
  let : IsLocalizedModule (.powers hp) f1 := hprod_loc
  let : IsLocalizedModule (.powers hp) f2 := hbase_loc
  have hPD : Function.Exact i d := by
    change ∀ x : B × R', d x = 0 ↔ x ∈ Set.range i
    intro x
    constructor
    · intro hx
      refine Set.mem_range.mpr ⟨⟨x, sub_eq_zero.mp hx⟩, ?_⟩
      rfl
    · rintro ⟨y, rfl⟩
      exact sub_eq_zero.mpr y.property
  have hloc_exact : Function.Exact
      (IsLocalizedModule.map (.powers hp) (Algebra.linearMap P (Localization.Away hp)) f1 i)
      (IsLocalizedModule.map (.powers hp) f1 f2 d) := by
    exact IsLocalizedModule.map_exact (.powers hp)
      (Algebra.linearMap P (Localization.Away hp)) f1 f2 i d hPD
  let qLinear : Localization.Away hp →ₗ[P]
      (Localization.Away g × Localization.Away f) :=
    { toFun := fun x =>
        (Localization.awayMap (RingHom.pullbackFst s t) hp x,
          Localization.awayMap (RingHom.pullbackSnd s t) hp x)
      map_add' := by
        intro x y
        ext
        · exact (Localization.awayMap (RingHom.pullbackFst s t) hp).map_add x y
        · exact (Localization.awayMap (RingHom.pullbackSnd s t) hp).map_add x y
      map_smul' := by
        intro x y
        ext
        · dsimp
          rw [Algebra.smul_def]
          change
            (Localization.awayMap (RingHom.pullbackFst s t) hp)
                ((algebraMap P (Localization.Away hp)) x * y) =
              (algebraMap B
                (Localization.Away ((RingHom.pullbackFst s t) hp)))
                  ((RingHom.pullbackFst s t) x) *
                (Localization.awayMap (RingHom.pullbackFst s t) hp) y
          rw [(Localization.awayMap (RingHom.pullbackFst s t) hp).map_mul]
          change
            (IsLocalization.map (Localization.Away ((RingHom.pullbackFst s t) hp))
              (RingHom.pullbackFst s t) _
                ((algebraMap P (Localization.Away hp)) x)) * _ = _
          rw [IsLocalization.map_eq]
        · dsimp
          rw [Algebra.smul_def]
          change
            (Localization.awayMap (RingHom.pullbackSnd s t) hp)
                ((algebraMap P (Localization.Away hp)) x * y) =
              (algebraMap R'
                (Localization.Away ((RingHom.pullbackSnd s t) hp)))
                  ((RingHom.pullbackSnd s t) x) *
                (Localization.awayMap (RingHom.pullbackSnd s t) hp) y
          rw [(Localization.awayMap (RingHom.pullbackSnd s t) hp).map_mul]
          change
            (IsLocalization.map (Localization.Away ((RingHom.pullbackSnd s t) hp))
              (RingHom.pullbackSnd s t) _
                ((algebraMap P (Localization.Away hp)) x)) * _ = _
          rw [IsLocalization.map_eq] }
  have hql : qLinear =
      IsLocalizedModule.map (.powers hp)
        (Algebra.linearMap P (Localization.Away hp)) f1 i := by
    apply IsLocalizedModule.linearMap_ext (.powers hp)
      (Algebra.linearMap P (Localization.Away hp)) f1
    apply LinearMap.ext
    intro x
    simp only [LinearMap.coe_comp, Function.comp_apply,
      IsLocalizedModule.map_apply]
    apply Prod.ext
    · change
        (Localization.awayMap (RingHom.pullbackFst s t) hp)
            ((algebraMap P (Localization.Away hp)) x) =
          (algebraMap B (Localization.Away g))
            ((RingHom.pullbackFst s t) x)
      change
        (IsLocalization.map (Localization.Away ((RingHom.pullbackFst s t) hp))
          (RingHom.pullbackFst s t) _
            ((algebraMap P (Localization.Away hp)) x)) = _
      rw [IsLocalization.map_eq]
      rfl
    · change
        (Localization.awayMap (RingHom.pullbackSnd s t) hp)
            ((algebraMap P (Localization.Away hp)) x) =
          (algebraMap R' (Localization.Away f))
            ((RingHom.pullbackSnd s t) x)
      change
        (IsLocalization.map (Localization.Away ((RingHom.pullbackSnd s t) hp))
          (RingHom.pullbackSnd s t) _
            ((algebraMap P (Localization.Away hp)) x)) = _
      rw [IsLocalization.map_eq]
      rfl
  let bLeft : Localization.Away g →+* Localization.Away (s g) :=
    Localization.awayMap s g
  let bRight : Localization.Away f →+* Localization.Away (s g) := by
    exact IsLocalization.map (Localization.Away (s g)) t (show
      Submonoid.powers f ≤ (Submonoid.powers (s g)).comap t by
      rintro x ⟨n, rfl⟩
      use n
      rw [map_pow, h])
  have hleft (x : P) :
      bLeft ((algebraMap B (Localization.Away g))
        ((algebraMap P B) x)) = (algebraMap P (Localization.Away (s g))) x := by
    simp [bLeft, IsLocalization.Away.map, IsLocalization.map_eq,
      RingHom.algebraMap_toAlgebra]
  have hright (x : P) :
      bRight ((algebraMap R' (Localization.Away f))
        ((algebraMap P R') x)) = (algebraMap P (Localization.Away (s g))) x := by
    simp [bRight, IsLocalization.map_eq, RingHom.algebraMap_toAlgebra]
    exact congrArg (algebraMap R (Localization.Away (s g))) x.property.symm
  let dWanted : (Localization.Away g × Localization.Away f) →ₗ[P]
      Localization.Away (s g) :=
    { toFun := fun x => bLeft x.1 - bRight x.2
      map_add' := by
        intro x y
        simp only [Prod.fst_add, Prod.snd_add, map_add, sub_add_sub_comm]
      map_smul' := by
        intro x y
        change bLeft ((algebraMap B (Localization.Away g) ((algebraMap P B) x)) * y.1) -
            bRight ((algebraMap R' (Localization.Away f) ((algebraMap P R') x)) * y.2) =
          (algebraMap P (Localization.Away (s g)) x) *
            (bLeft y.1 - bRight y.2)
        rw [map_mul, map_mul, hleft, hright]
        ring }
  have hd : dWanted =
      IsLocalizedModule.map (.powers hp) f1 f2 d := by
    apply IsLocalizedModule.linearMap_ext (.powers hp) f1 f2
    apply LinearMap.ext
    intro x
    simp only [LinearMap.coe_comp, Function.comp_apply,
      IsLocalizedModule.map_apply]
    simp [dWanted, d, f1, f2, bLeft, bRight,
      IsLocalization.Away.map, IsLocalization.map_eq]
  have hi : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    exact hxy
  have hq_inj : Function.Injective qLinear := by
    rw [hql]
    exact IsLocalizedModule.map_injective (.powers hp)
      (Algebra.linearMap P (Localization.Away hp)) f1 i hi
  let K := RingHom.pullback bLeft bRight
  let qRing : Localization.Away hp →+* K :=
    ((Localization.awayMap (RingHom.pullbackFst s t) hp).prod
      (Localization.awayMap (RingHom.pullbackSnd s t) hp)).codRestrict K (by
        intro x
        have heq :
            bLeft.comp (Localization.awayMap (RingHom.pullbackFst s t) hp) =
              bRight.comp (Localization.awayMap (RingHom.pullbackSnd s t) hp) := by
          apply IsLocalization.ringHom_ext (.powers hp)
          apply RingHom.ext
          intro z
          change
            bLeft ((Localization.awayMap (RingHom.pullbackFst s t) hp)
              ((algebraMap P (Localization.Away hp)) z)) =
              bRight ((Localization.awayMap (RingHom.pullbackSnd s t) hp)
                ((algebraMap P (Localization.Away hp)) z))
          have hfst :
              Localization.awayMap (RingHom.pullbackFst s t) hp
                  ((algebraMap P (Localization.Away hp)) z) =
                (algebraMap B (Localization.Away g))
                  ((RingHom.pullbackFst s t) z) := by
            change
              (IsLocalization.map
                (Localization.Away ((RingHom.pullbackFst s t) hp))
                (RingHom.pullbackFst s t) _
                  ((algebraMap P (Localization.Away hp)) z)) = _
            rw [IsLocalization.map_eq]
            rfl
          have hsnd :
              Localization.awayMap (RingHom.pullbackSnd s t) hp
                  ((algebraMap P (Localization.Away hp)) z) =
                (algebraMap R' (Localization.Away f))
                  ((RingHom.pullbackSnd s t) z) := by
            change
              (IsLocalization.map
                (Localization.Away ((RingHom.pullbackSnd s t) hp))
                (RingHom.pullbackSnd s t) _
                  ((algebraMap P (Localization.Away hp)) z)) = _
            rw [IsLocalization.map_eq]
            rfl
          calc
            bLeft ((Localization.awayMap (RingHom.pullbackFst s t) hp)
                ((algebraMap P (Localization.Away hp)) z)) =
                bLeft ((algebraMap B (Localization.Away g))
                  ((RingHom.pullbackFst s t) z)) := by rw [hfst]
            _ = bLeft ((algebraMap B (Localization.Away g))
                  ((algebraMap P B) z)) := by rfl
            _ = (algebraMap P (Localization.Away (s g))) z := hleft z
            _ = bRight ((algebraMap R' (Localization.Away f))
                  ((algebraMap P R') z)) := (hright z).symm
            _ = bRight ((algebraMap R' (Localization.Away f))
                  ((RingHom.pullbackSnd s t) z)) := by rfl
            _ = bRight ((Localization.awayMap (RingHom.pullbackSnd s t) hp)
                  ((algebraMap P (Localization.Away hp)) z)) := by rw [hsnd]
        exact DFunLike.congr_fun heq x)
  have hqRing_inj : Function.Injective qRing := by
    intro x y hxy
    apply hq_inj
    exact congrArg Subtype.val hxy
  have hqRing_surj : Function.Surjective qRing := by
    intro z
    have hzker : dWanted z.1 = 0 := by
      exact sub_eq_zero.mpr z.property
    have hzker' :
        (IsLocalizedModule.map (.powers hp) f1 f2 d) z.1 = 0 := by
      rw [← hd]
      exact hzker
    rcases (hloc_exact z.1).mp hzker' with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change qLinear x = z.1
    rw [hql]
    exact hx
  have hK :
      IsPullback
        (CommRingCat.ofHom (RingHom.pullbackFst bLeft bRight))
        (CommRingCat.ofHom (RingHom.pullbackSnd bLeft bRight))
        (CommRingCat.ofHom bLeft)
        (CommRingCat.ofHom bRight) := by
    exact IsPullback.of_isLimit
      (CommRingCat.pullbackConeIsLimit
        (CommRingCat.ofHom bLeft) (CommRingCat.ofHom bRight))
  let e : Localization.Away hp ≃+* K :=
    RingEquiv.ofBijective qRing ⟨hqRing_inj, hqRing_surj⟩
  have hbRight :
      bRight = localizedPullbackBaseRight s t g f h := by
    apply IsLocalization.ringHom_ext (.powers f)
    apply RingHom.ext
    intro x
    change bRight (algebraMap R' (Localization.Away f) x) =
      localizedPullbackBaseRight s t g f h
        (algebraMap R' (Localization.Away f) x)
    let he : Localization.Away (t f) = Localization.Away (s g) :=
      congrArg Localization.Away h.symm
    have hm :
        (Localization.awayMap t f)
            (algebraMap R' (Localization.Away f) x) =
          (algebraMap R (Localization.Away (t f))) (t x) := by
      simp [Localization.awayMap, IsLocalization.Away.map,
        IsLocalization.map_eq]
    have hm' := congrArg (fun z : Localization.Away (t f) => cast he z) hm
    have cast_algebraMap (a b : R) (e' : a = b) (y : R) :
        cast (congrArg (fun z : R => Localization.Away z) e')
            ((algebraMap R (Localization.Away a)) y) =
          (algebraMap R (Localization.Away b)) y := by
      cases e'
      rfl
    have cast_ringHom_apply (a b : R) (e' : a = b)
        (φ : Localization.Away f →+* Localization.Away a)
        (y : Localization.Away f) :
        (cast
            (congrArg (fun z : R => Localization.Away f →+* Localization.Away z) e')
            φ) y =
          cast (congrArg (fun z : R => Localization.Away z) e') (φ y) := by
      cases e'
      rfl
    convert hm'.symm using 1
    · symm
      calc
        cast he ((algebraMap R (Localization.Away (t f))) (t x)) =
            (algebraMap R (Localization.Away (s g))) (t x) :=
          cast_algebraMap (t f) (s g) h.symm (t x)
        _ = bRight (algebraMap R' (Localization.Away f) x) := by
          simp [bRight, IsLocalization.map_eq]
    · simpa [bRight, localizedPullbackBaseRight, he] using
        cast_ringHom_apply (t f) (s g) h.symm
          (Localization.awayMap t f) (algebraMap R' (Localization.Away f) x)
  let e₂ : Localization.Away
      ((RingHom.pullbackFst s t) hp) ≃+*
      Localization.Away g :=
    RingEquiv.cast (show
      (RingHom.pullbackFst s t) hp = g by
        change (ringPullbackElement s t g f h).1.1 = g
        rfl)
  let e₃ : Localization.Away
      ((RingHom.pullbackSnd s t) hp) ≃+*
      Localization.Away f :=
    RingEquiv.cast (show
      (RingHom.pullbackSnd s t) hp = f by
        change (ringPullbackElement s t g f h).1.2 = f
        rfl)
  have hfst :
      (RingHom.pullbackFst bLeft bRight).comp qRing =
        e₂.toRingHom.comp (localizedPullbackFst s t g f h) := by
    ext x
    rfl
  have hsnd :
      (RingHom.pullbackSnd bLeft bRight).comp qRing =
        e₃.toRingHom.comp (localizedPullbackSnd s t g f h) := by
    ext x
    rfl
  have hbLeft :
      bLeft = localizedPullbackBaseLeft s t g f h := by
    rfl
  apply hK.of_iso' e.toCommRingCatIso e₂.toCommRingCatIso
    e₃.toCommRingCatIso (Iso.refl _)
  · apply CommRingCat.hom_ext
    exact hfst
  · apply CommRingCat.hom_ext
    exact hsnd
  · apply CommRingCat.hom_ext
    rw [hbLeft]
    rfl
  · apply CommRingCat.hom_ext
    rw [hbRight]
    rfl

/-- The exact sequence displayed in the localization proof, before
localization: it is the equalizer sequence for the canonical pullback. -/
theorem ringPullback_exact
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) :
    Function.Exact
      (fun x : RingHom.pullback s t => (x : B × R'))
      (fun x : B × R' => s x.1 - t x.2) := by
  exact ringPullback_exact_aux s t

/-- The two component maps in the localized exact sequence, stated directly
for an arbitrary element of the canonical pullback subring. -/
noncomputable def localizedPullbackFstCanonical
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (h : RingHom.pullback s t) :
    Localization.Away h →+*
      Localization.Away ((RingHom.pullbackFst s t) h) :=
  Localization.awayMap (RingHom.pullbackFst s t) h

noncomputable def localizedPullbackSndCanonical
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (h : RingHom.pullback s t) :
    Localization.Away h →+*
      Localization.Away ((RingHom.pullbackSnd s t) h) :=
  Localization.awayMap (RingHom.pullbackSnd s t) h

noncomputable def localizedPullbackBaseRightCanonical
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (h : RingHom.pullback s t) :
      Localization.Away ((RingHom.pullbackSnd s t) h) →+*
      Localization.Away (s ((RingHom.pullbackFst s t) h)) := by
  have hst : s ((RingHom.pullbackFst s t) h) =
      t ((RingHom.pullbackSnd s t) h) := by
    exact h.property
  rw [hst]
  exact Localization.awayMap t ((RingHom.pullbackSnd s t) h)

/-- The localized exact sequence used in the proof of the localization
lemma. -/
theorem localized_ringPullback_exact
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (h : RingHom.pullback s t) :
    Function.Exact
      (fun x : Localization.Away h =>
        (localizedPullbackFstCanonical s t h x,
          localizedPullbackSndCanonical s t h x))
      (fun p : Localization.Away ((RingHom.pullbackFst s t) h) ×
          Localization.Away ((RingHom.pullbackSnd s t) h) =>
        Localization.awayMap s ((RingHom.pullbackFst s t) h) p.1 -
          localizedPullbackBaseRightCanonical s t h p.2) := by
  let F : Localization.Away h →
      Localization.Away ((RingHom.pullbackFst s t) h) ×
        Localization.Away ((RingHom.pullbackSnd s t) h) :=
    fun x =>
      (localizedPullbackFstCanonical s t h x,
        localizedPullbackSndCanonical s t h x)
  let G : Localization.Away ((RingHom.pullbackFst s t) h) ×
      Localization.Away ((RingHom.pullbackSnd s t) h) →
      Localization.Away (s ((RingHom.pullbackFst s t) h)) :=
    fun p =>
      Localization.awayMap s ((RingHom.pullbackFst s t) h) p.1 -
        localizedPullbackBaseRightCanonical s t h p.2
  change Function.Exact F G
  have hEq :
      ringPullbackElement s t ((RingHom.pullbackFst s t) h)
          ((RingHom.pullbackSnd s t) h) h.property = h := by
    apply Subtype.ext
    rfl
  have hpull :
      IsPullback
        (CommRingCat.ofHom (localizedPullbackFstCanonical s t h))
        (CommRingCat.ofHom (localizedPullbackSndCanonical s t h))
        (CommRingCat.ofHom (Localization.awayMap s
          ((RingHom.pullbackFst s t) h)))
        (CommRingCat.ofHom (localizedPullbackBaseRightCanonical s t h)) := by
    rw [← hEq]
    exact localized_ring_pullback_isPullback s t
      ((RingHom.pullbackFst s t) h) ((RingHom.pullbackSnd s t) h)
      h.property
  intro p
  constructor
  · intro hp
    have hz :
        Localization.awayMap s ((RingHom.pullbackFst s t) h) p.1 =
          localizedPullbackBaseRightCanonical s t h p.2 := by
      apply sub_eq_zero.mp
      simpa [G] using hp
    let l₁ : MvPolynomial (ULift Unit) ℤ →+*
        Localization.Away ((RingHom.pullbackFst s t) h) :=
      MvPolynomial.eval₂Hom (algebraMap ℤ _) (fun _ => p.1)
    let l₂ : MvPolynomial (ULift Unit) ℤ →+*
        Localization.Away ((RingHom.pullbackSnd s t) h) :=
      MvPolynomial.eval₂Hom (algebraMap ℤ _) (fun _ => p.2)
    have hl :
        (localizedPullbackBaseRightCanonical s t h).comp l₂ =
          (Localization.awayMap s ((RingHom.pullbackFst s t) h)).comp l₁ := by
      rw [MvPolynomial.comp_eval₂Hom, MvPolynomial.comp_eval₂Hom]
      apply DFunLike.ext _ _
      intro q
      apply MvPolynomial.hom_congr_vars
      · exact RingHom.ext_int _ _
      · intro i hi₁ hi₂
        simpa only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] using hz.symm
      · rfl
    have hl' :
        CommRingCat.ofHom l₂ ≫
            CommRingCat.ofHom (localizedPullbackBaseRightCanonical s t h) =
          CommRingCat.ofHom l₁ ≫
            CommRingCat.ofHom (Localization.awayMap s
              ((RingHom.pullbackFst s t) h)) := by
      apply CommRingCat.hom_ext
      exact hl
    rcases hpull.exists_lift (CommRingCat.ofHom l₁) (CommRingCat.ofHom l₂)
        hl'.symm with ⟨q, hq₁, hq₂⟩
    refine ⟨q.hom (MvPolynomial.X (ULift.up ())), ?_⟩
    apply Prod.ext
    · have hq₁' := congrArg
          (fun k => k.hom (MvPolynomial.X (ULift.up ()))) hq₁
      change localizedPullbackFstCanonical s t h
          (q.hom (MvPolynomial.X (ULift.up ()))) = p.1
      change localizedPullbackFstCanonical s t h
          (q.hom (MvPolynomial.X (ULift.up ()))) =
        l₁ (MvPolynomial.X (ULift.up ())) at hq₁'
      simpa only [l₁, MvPolynomial.eval₂Hom_X'] using hq₁'
    · have hq₂' := congrArg (fun k => k.hom (MvPolynomial.X (ULift.up ()))) hq₂
      change localizedPullbackSndCanonical s t h
          (q.hom (MvPolynomial.X (ULift.up ()))) = p.2
      change localizedPullbackSndCanonical s t h
          (q.hom (MvPolynomial.X (ULift.up ()))) =
        l₂ (MvPolynomial.X (ULift.up ())) at hq₂'
      simpa only [l₂, MvPolynomial.eval₂Hom_X'] using hq₂'
  · rintro ⟨q, rfl⟩
    have hw' :
        (Localization.awayMap s ((RingHom.pullbackFst s t) h)).comp
            (localizedPullbackFstCanonical s t h) =
          (localizedPullbackBaseRightCanonical s t h).comp
            (localizedPullbackSndCanonical s t h) := by
      exact congrArg CommRingCat.Hom.hom hpull.w
    have hw := congrArg (fun k : Localization.Away h →+*
        Localization.Away (s ((RingHom.pullbackFst s t) h)) => k q) hw'
    change (Localization.awayMap s ((RingHom.pullbackFst s t) h))
          (localizedPullbackFstCanonical s t h q) -
        localizedPullbackBaseRightCanonical s t h
          (localizedPullbackSndCanonical s t h q) = 0
    exact sub_eq_zero.mpr hw

/-! ## Modules over a commutative square -/

/-- A commutative square of rings.

The module functor in the source only assumes commutativity of the square;
cartesianness is needed for the preceding localization statement, but not for
this construction. -/
structure RingSquare (R R' B B' : Type u)
    [CommRing R] [CommRing R'] [CommRing B] [CommRing B'] where
  /-- The upper horizontal map `R' → R`. -/
  t : R' →+* R
  /-- The left vertical map `B → R`. -/
  s : B →+* R
  /-- The lower horizontal map `B' → B`. -/
  u : B' →+* B
  /-- The right vertical map `B' → R'`. -/
  v : B' →+* R'
  /-- Commutativity of the square. -/
  comm : s.comp u = t.comp v

@[simp]
theorem RingSquare.comm_apply
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (x : B') :
    D.s (D.u x) = D.t (D.v x) :=
  DFunLike.congr_fun D.comm x

/-- The category of module triples `(N, M', φ)` over a commutative square.
This is the canonical full subcategory of the comma category on isomorphisms,
the underlying implementation of the earlier Categories construction. -/
abbrev ModuleGluingCategory
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') :=
  IsoComma (ModuleCat.extendScalars D.s) (ModuleCat.extendScalars D.t)

/-- The two module components of an object of `ModuleGluingCategory`.  These
abbreviations keep projections out of binder positions, where Lean parses a
dotted projection as a binder name. -/
abbrev moduleGluingLeftObj
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) : ModuleCat.{u} B :=
  (isoCommaLeft (ModuleCat.extendScalars D.s) (ModuleCat.extendScalars D.t)).obj X

abbrev moduleGluingRightObj
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) : ModuleCat.{u} R' :=
  (isoCommaRight (ModuleCat.extendScalars D.s) (ModuleCat.extendScalars D.t)).obj X

abbrev moduleGluingComparison
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    (ModuleCat.extendScalars D.s).obj
        (moduleGluingLeftObj (D := D) (X := X)) ⟶
      (ModuleCat.extendScalars D.t).obj
        (moduleGluingRightObj (D := D) (X := X)) :=
  (isoCommaComparison (ModuleCat.extendScalars D.s) (ModuleCat.extendScalars D.t)).app X

theorem moduleGluingComparison_isIso
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    IsIso (moduleGluingComparison D X) := by
  exact isoComma_isIso_hom X

/-- The canonical comparison between the two iterated extensions of scalars
along a commutative square. -/
noncomputable def moduleBaseChangeComparison
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') :
    (ModuleCat.extendScalars D.u ⋙ ModuleCat.extendScalars D.s) ≅
      (ModuleCat.extendScalars D.v ⋙ ModuleCat.extendScalars D.t) := by
  let ecomm : ModuleCat.extendScalars (D.s.comp D.u) ≅
      ModuleCat.extendScalars (D.t.comp D.v) :=
    eqToIso (congrArg (fun f => ModuleCat.extendScalars f) D.comm)
  exact (ModuleCat.extendScalarsComp D.u D.s).symm ≪≫ ecomm ≪≫
    ModuleCat.extendScalarsComp D.v D.t

/-- The source's functor from modules over the lower-right ring to triples of
modules.  Its two components are extension of scalars, and its comparison is
the canonical iterated-extension isomorphism. -/
noncomputable def moduleBaseChangeFunctor
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') :
    ModuleCat.{u} B' ⥤ ModuleGluingCategory D where
  obj L :=
    { obj :=
        { left := (ModuleCat.extendScalars D.u).obj L
          right := (ModuleCat.extendScalars D.v).obj L
          hom := (moduleBaseChangeComparison D).hom.app L }
      property := by
        change IsIso ((moduleBaseChangeComparison D).hom.app L)
        infer_instance }
  map f :=
    ObjectProperty.homMk
      { left := (ModuleCat.extendScalars D.u).map f
        right := (ModuleCat.extendScalars D.v).map f
        w := (moduleBaseChangeComparison D).hom.naturality f }
  map_id := by
    intro L
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp
  map_comp := by
    intro L M N f g
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp

noncomputable abbrev moduleBaseChange
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') :
    ModuleCat.{u} B' ⥤ ModuleGluingCategory D :=
  moduleBaseChangeFunctor D

/-- The common target used to compare the two canonical maps defining the
module pullback. -/
abbrev moduleFiberCommonTarget
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) : ModuleCat.{u} B' :=
  (ModuleCat.restrictScalars (D.s.comp D.u)).obj
    ((ModuleCat.extendScalars D.t).obj X.obj.right)

/-- The map from the `B`-module component to the common target. -/
noncomputable def moduleFiberLeftMap
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    (ModuleCat.restrictScalars D.u).obj X.obj.left ⟶
      moduleFiberCommonTarget D X := by
  let K : ModuleCat.{u} R := (ModuleCat.extendScalars D.t).obj X.obj.right
  let e := ModuleCat.restrictScalarsComp'App D.u D.s (D.s.comp D.u) rfl K
  exact
    (ModuleCat.restrictScalars D.u).map
        ((ModuleCat.extendRestrictScalarsAdj D.s).unit.app X.obj.left ≫
          (ModuleCat.restrictScalars D.s).map X.obj.hom) ≫
      e.inv

/-- The map from the `R'`-module component to the common target. -/
noncomputable def moduleFiberRightMap
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    (ModuleCat.restrictScalars D.v).obj X.obj.right ⟶
      moduleFiberCommonTarget D X := by
  let K : ModuleCat.{u} R := (ModuleCat.extendScalars D.t).obj X.obj.right
  let e := ModuleCat.restrictScalarsComp'App D.v D.t (D.t.comp D.v) rfl K
  exact
    (ModuleCat.restrictScalars D.v).map
        ((ModuleCat.extendRestrictScalarsAdj D.t).unit.app X.obj.right) ≫
      e.inv ≫
      (ModuleCat.restrictScalarsCongr D.comm).inv.app K

/-- The map on the common target induced by a morphism of module triples. -/
def moduleFiberCommonMap
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') {X Y : ModuleGluingCategory D}
    (f : X ⟶ Y) :
    moduleFiberCommonTarget D X ⟶ moduleFiberCommonTarget D Y :=
  (ModuleCat.restrictScalars (D.s.comp D.u)).map
    ((ModuleCat.extendScalars D.t).map f.hom.right)

/-- Naturality of the first map in the categorical module pullback. -/
theorem moduleFiberLeftMap_naturality
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') {X Y : ModuleGluingCategory D}
    (f : X ⟶ Y) :
    (ModuleCat.restrictScalars D.u).map f.hom.left ≫ moduleFiberLeftMap D Y =
      moduleFiberLeftMap D X ≫ moduleFiberCommonMap D f := by
  have hunit : f.hom.left ≫ (ModuleCat.extendRestrictScalarsAdj D.s).unit.app Y.obj.left =
      (ModuleCat.extendRestrictScalarsAdj D.s).unit.app X.obj.left ≫
        (ModuleCat.restrictScalars D.s).map ((ModuleCat.extendScalars D.s).map f.hom.left) := by
    simp
  have hw : (ModuleCat.extendScalars D.s).map f.hom.left ≫ Y.obj.hom =
      X.obj.hom ≫ (ModuleCat.extendScalars D.t).map f.hom.right := by
    simp
  simp only [moduleFiberLeftMap, moduleFiberCommonMap, ← Functor.map_comp, ← Category.assoc]
  rw [hunit]
  rw [Category.assoc]
  rw [← (ModuleCat.restrictScalars D.s).map_comp]
  rw [hw]
  simp only [Functor.map_comp, Category.assoc]
  rw [ModuleCat.restrictScalarsComp'App_inv_naturality]

/-- Naturality of the second map in the categorical module pullback. -/
theorem moduleFiberRightMap_naturality
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') {X Y : ModuleGluingCategory D}
    (f : X ⟶ Y) :
    (ModuleCat.restrictScalars D.v).map f.hom.right ≫ moduleFiberRightMap D Y =
      moduleFiberRightMap D X ≫ moduleFiberCommonMap D f := by
  have hunit : f.hom.right ≫ (ModuleCat.extendRestrictScalarsAdj D.t).unit.app Y.obj.right =
      (ModuleCat.extendRestrictScalarsAdj D.t).unit.app X.obj.right ≫
        (ModuleCat.restrictScalars D.t).map ((ModuleCat.extendScalars D.t).map f.hom.right) := by
    simp
  simp only [moduleFiberRightMap, moduleFiberCommonMap, ← Functor.map_comp, ← Category.assoc]
  rw [hunit]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc
    ((ModuleCat.restrictScalars D.v).map ((ModuleCat.restrictScalars D.t).map
      ((ModuleCat.extendScalars D.t).map f.hom.right)))
    (ModuleCat.restrictScalarsComp'App D.v D.t (D.t.comp D.v) rfl
      ((ModuleCat.extendScalars D.t).obj Y.obj.right)).inv
    ((ModuleCat.restrictScalarsCongr D.comm).inv.app
      ((ModuleCat.extendScalars D.t).obj Y.obj.right))]
  rw [ModuleCat.restrictScalarsComp'App_inv_naturality]
  simp only [Category.assoc]
  rw [(ModuleCat.restrictScalarsCongr D.comm).inv.naturality]

/-- The source's compatible-pair set, written in terms of the canonical
tensor base-change elements. -/
def moduleFiberCompatiblePairs
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    Set ((moduleGluingLeftObj (D := D) (X := X) : Type u) ×
      (moduleGluingRightObj (D := D) (X := X) : Type u)) :=
  {p |
    X.obj.hom ((1 : R) ⊗ₜ[B, D.s] p.1) =
      (1 : R) ⊗ₜ[R', D.t] p.2}

/-- The module fibre product is the categorical pullback of the two maps
whose elementwise condition is `moduleFiberCompatiblePairs`. -/
noncomputable abbrev moduleFiberProduct
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) : ModuleCat.{u} B' :=
  limit (cospan (moduleFiberLeftMap D X) (moduleFiberRightMap D X))

/-- The two coordinate maps of the categorical module fibre product. -/
def moduleFiberProductPair
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D)
    (x : moduleFiberProduct D X) :
    (moduleGluingLeftObj (D := D) (X := X) : Type u) ×
      (moduleGluingRightObj (D := D) (X := X) : Type u) :=
  (limit.π (cospan (moduleFiberLeftMap D X) (moduleFiberRightMap D X))
      WalkingCospan.left x,
    limit.π (cospan (moduleFiberLeftMap D X) (moduleFiberRightMap D X))
      WalkingCospan.right x)

/-- The map between the two categorical module pullbacks induced by a morphism
of triples. -/
noncomputable def moduleFiberProductMap
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') {X Y : ModuleGluingCategory D}
    (f : X ⟶ Y) : moduleFiberProduct D X ⟶ moduleFiberProduct D Y :=
  pullback.lift
    (pullback.fst (moduleFiberLeftMap D X) (moduleFiberRightMap D X) ≫
      (ModuleCat.restrictScalars D.u).map f.hom.left)
    (pullback.snd (moduleFiberLeftMap D X) (moduleFiberRightMap D X) ≫
      (ModuleCat.restrictScalars D.v).map f.hom.right) (by
        simp only [Category.assoc]
        rw [moduleFiberLeftMap_naturality D f, moduleFiberRightMap_naturality D f]
        exact congrArg (fun k => k ≫ moduleFiberCommonMap D f)
          (PullbackCone.condition (limit.cone
            (cospan (moduleFiberLeftMap D X) (moduleFiberRightMap D X)))) )

/-- The compatible-pair pullback is functorial in the module triple. -/
noncomputable def moduleFiberProductRightAdjointCanonical
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') :
    ModuleGluingCategory D ⥤ ModuleCat.{u} B' where
  obj X := moduleFiberProduct D X
  map f := moduleFiberProductMap D f
  map_id := by
    intro X
    apply pullback.hom_ext
    · simp [moduleFiberProductMap]
    · simp [moduleFiberProductMap]
  map_comp := by
    intro X Y Z f g
    apply pullback.hom_ext
    · simp only [moduleFiberProductMap, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.assoc]
      simp
    · simp only [moduleFiberProductMap, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.assoc]
      simp

/-- The categorical pullback and the source's compatible-pair presentation
have the same underlying elements. -/
theorem moduleFiberProduct_pair_is_compatible
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D)
    (x : moduleFiberProduct D X) :
    moduleFiberProductPair D X x ∈ moduleFiberCompatiblePairs D X := by
  have h := congrArg (fun k => k x)
    (PullbackCone.condition (limit.cone
      (cospan (moduleFiberLeftMap D X) (moduleFiberRightMap D X))))
  change (moduleFiberLeftMap D X) (moduleFiberProductPair D X x).1 =
      (moduleFiberRightMap D X) (moduleFiberProductPair D X x).2 at h
  change X.obj.hom ((1 : R) ⊗ₜ[B, D.s] (moduleFiberProductPair D X x).1) =
      (1 : R) ⊗ₜ[R', D.t] (moduleFiberProductPair D X x).2 at h
  exact h

/-- The compatible-pair presentation is equivalent to the underlying set of
the categorical module pullback. -/
theorem moduleFiberProduct_compatiblePairEquiv_exists
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    Nonempty
      ((moduleFiberProduct D X : Type u) ≃
        {p : (moduleGluingLeftObj (D := D) (X := X) : Type u) ×
          (moduleGluingRightObj (D := D) (X := X) : Type u) //
          p ∈ moduleFiberCompatiblePairs D X}) := by
  have hforward :
      ∀ p : (moduleGluingLeftObj (D := D) (X := X) : Type u) ×
        (moduleGluingRightObj (D := D) (X := X) : Type u),
        (moduleFiberLeftMap D X) p.1 = (moduleFiberRightMap D X) p.2 →
          p ∈ moduleFiberCompatiblePairs D X := by
    intro p h
    change X.obj.hom ((1 : R) ⊗ₜ[B, D.s] p.1) =
        (1 : R) ⊗ₜ[R', D.t] p.2 at h
    exact h
  have hbackward :
      ∀ p : (moduleGluingLeftObj (D := D) (X := X) : Type u) ×
        (moduleGluingRightObj (D := D) (X := X) : Type u),
        p ∈ moduleFiberCompatiblePairs D X →
          (moduleFiberLeftMap D X) p.1 = (moduleFiberRightMap D X) p.2 := by
    intro p h
    change X.obj.hom ((1 : R) ⊗ₜ[B, D.s] p.1) =
        (1 : R) ⊗ₜ[R', D.t] p.2 at h
    exact h
  let c :
      {p : (moduleGluingLeftObj (D := D) (X := X) : Type u) ×
          (moduleGluingRightObj (D := D) (X := X) : Type u) //
        (moduleFiberLeftMap D X) p.1 = (moduleFiberRightMap D X) p.2} ≃
        {p : (moduleGluingLeftObj (D := D) (X := X) : Type u) ×
          (moduleGluingRightObj (D := D) (X := X) : Type u) //
          p ∈ moduleFiberCompatiblePairs D X} :=
    { toFun := fun p => ⟨p.1, hforward p.1 p.2⟩
      invFun := fun p => ⟨p.1, hbackward p.1 p.2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  exact ⟨(Concrete.pullbackEquiv (moduleFiberLeftMap D X) (moduleFiberRightMap D X)).trans c⟩

/-- Source-facing chosen equivalence between the categorical pullback and its
compatible-pair presentation. -/
noncomputable def moduleFiberProduct_compatiblePairEquiv
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    (moduleFiberProduct D X : Type u) ≃
      {p : (moduleGluingLeftObj (D := D) (X := X) : Type u) ×
        (moduleGluingRightObj (D := D) (X := X) : Type u) //
        p ∈ moduleFiberCompatiblePairs D X} :=
  Classical.choice (moduleFiberProduct_compatiblePairEquiv_exists D X)

/-! ## Base change and the right adjoint -/

/-- The adjunction data asserting that the compatible-pair fibre product is a
right adjoint of the source's module functor. -/
structure ModuleFiberProductAdjunctionData
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') where
  adjunction : moduleBaseChangeFunctor D ⊣ moduleFiberProductRightAdjointCanonical D

private theorem moduleFiberProduct_hcompat
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    ∀ (p : (ModuleCat.extendScalars D.u).obj L ⟶ X.obj.left)
      (q : (ModuleCat.extendScalars D.v).obj L ⟶ X.obj.right),
      (moduleBaseChangeComparison D).hom.app L ≫
            (ModuleCat.extendScalars D.t).map q =
          (ModuleCat.extendScalars D.s).map p ≫
            moduleGluingComparison (D := D) (X := X) ↔
        (ModuleCat.extendRestrictScalarsAdj D.u).homEquiv _ _ p ≫
              moduleFiberLeftMap D X =
          (ModuleCat.extendRestrictScalarsAdj D.v).homEquiv _ _ q ≫
            moduleFiberRightMap D X := by
  intro p q
  constructor
  · intro h
    apply ModuleCat.hom_ext
    ext x
    have hleft :
        ((ModuleCat.extendRestrictScalarsAdj D.u).homEquiv L
            X.obj.left p ≫
            moduleFiberLeftMap D X) x =
          X.obj.hom ((1 : R) ⊗ₜ[B, D.s]
            (p ((1 : B) ⊗ₜ[B', D.u] x))) := by
      dsimp [moduleFiberLeftMap]
      simp [
        ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
        ModuleCat.restrictScalarsComp'App_inv_apply]
      rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
      rfl
    have hright :
        ((ModuleCat.extendRestrictScalarsAdj D.v).homEquiv L
            X.obj.right q ≫
            moduleFiberRightMap D X) x =
          (1 : R) ⊗ₜ[R', D.t]
            (q ((1 : R') ⊗ₜ[B', D.v] x)) := by
      dsimp [moduleFiberRightMap]
      simp [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
      rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
      rfl
    rw [hleft, hright]
    let z0 : (ModuleCat.extendScalars (D.s.comp D.u)).obj L :=
      ((1 : R) ⊗ₜ[B'] x)
    let z : (ModuleCat.extendScalars D.u ⋙ ModuleCat.extendScalars D.s).obj L :=
      (ModuleCat.extendScalarsComp D.u D.s).hom.app L z0
    have hcancel :
        (ModuleCat.extendScalarsComp D.u D.s).inv.app L
            ((ModuleCat.extendScalarsComp D.u D.s).hom.app L z0) = z0 := by
      -- Prior attempt:
      -- simpa [ModuleCat.hom_comp, LinearMap.coe_comp] using
      --   congrArg (fun f => f z0)
      --     ((ModuleCat.extendScalarsComp D.u D.s).hom_inv_id_app L)
      simp
    have heq {f g : B' →+* R} (hfg : f = g) :
        ((eqToHom (congrArg (fun k => ModuleCat.extendScalars k) hfg)).app L).hom
            ((1 : R) ⊗ₜ[B', f] x) =
          (1 : R) ⊗ₜ[B', g] x := by
      subst g
      rfl
    have heq' :
        ((eqToHom (congrArg (fun k => ModuleCat.extendScalars k) D.comm)).app L).hom z0 =
          (1 : R) ⊗ₜ[B', D.t.comp D.v] x := by
      dsimp [z0]
      exact heq D.comm
    have hbase_z :
        (moduleBaseChangeComparison D).hom.app L z =
          (ModuleCat.extendScalarsComp D.v D.t).hom.app L
            ((1 : R) ⊗ₜ[B', D.t.comp D.v] x) := by
      dsimp [z, moduleBaseChangeComparison]
      rw [hcancel]
      dsimp [z0]
      rw [heq']
      rfl
    have hx := congrArg (fun k => k.hom z) h
    simp only [ModuleCat.hom_comp] at hx
    simp only [LinearMap.comp_apply] at hx
    rw [hbase_z] at hx
    dsimp only [z, z0] at hx
    have hut := ModuleCat.extendScalarsComp_hom_app_one_tmul D.u D.s L x
    have hvt := ModuleCat.extendScalarsComp_hom_app_one_tmul D.v D.t L x
    rw [hut] at hx
    erw [hvt] at hx
    change
      X.obj.hom ((1 : R) ⊗ₜ[B, D.s]
        (p ((1 : B) ⊗ₜ[B', D.u] x))) =
        (1 : R) ⊗ₜ[R', D.t]
        (q ((1 : R') ⊗ₜ[B', D.v] x))
    change
      ((ModuleCat.extendScalars D.t).map q).hom'
          ((1 : R) ⊗ₜ[R', D.t] ((1 : R') ⊗ₜ[B', D.v] x)) =
        X.obj.hom.hom'
          (((ModuleCat.extendScalars D.s).map p).hom'
            ((1 : R) ⊗ₜ[B, D.s] ((1 : B) ⊗ₜ[B', D.u] x))) at hx
    exact hx.symm
  · intro h
    apply ModuleCat.ExtendScalars.hom_ext
    intro y
    have hmap :
        (ModuleCat.extendRestrictScalarsAdj D.s).homEquiv _ _
            ((moduleBaseChangeComparison D).hom.app L ≫
              (ModuleCat.extendScalars D.t).map q) =
          (ModuleCat.extendRestrictScalarsAdj D.s).homEquiv _ _
            ((ModuleCat.extendScalars D.s).map p ≫
              moduleGluingComparison D X) := by
      apply ModuleCat.ExtendScalars.hom_ext
      intro l
      have hleft :
          ((ModuleCat.extendRestrictScalarsAdj D.u).homEquiv L
              X.obj.left p ≫ moduleFiberLeftMap D X) l =
            X.obj.hom ((1 : R) ⊗ₜ[B, D.s]
              (p ((1 : B) ⊗ₜ[B', D.u] l))) := by
        dsimp [moduleFiberLeftMap]
        simp [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
          ModuleCat.restrictScalarsComp'App_inv_apply]
        rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
        rfl
      have hright :
          ((ModuleCat.extendRestrictScalarsAdj D.v).homEquiv L
              X.obj.right q ≫ moduleFiberRightMap D X) l =
            (1 : R) ⊗ₜ[R', D.t]
              (q ((1 : R') ⊗ₜ[B', D.v] l)) := by
        dsimp [moduleFiberRightMap]
        simp [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
        rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
        rfl
      have hdesired :
          X.obj.hom ((1 : R) ⊗ₜ[B, D.s]
            (p ((1 : B) ⊗ₜ[B', D.u] l))) =
            (1 : R) ⊗ₜ[R', D.t]
              (q ((1 : R') ⊗ₜ[B', D.v] l)) := by
        rw [← hleft, ← hright]
        exact congrArg (fun k => k l) h
      let z0 : (ModuleCat.extendScalars (D.s.comp D.u)).obj L :=
        ((1 : R) ⊗ₜ[B'] l)
      let z : (ModuleCat.extendScalars D.u ⋙ ModuleCat.extendScalars D.s).obj L :=
        (ModuleCat.extendScalarsComp D.u D.s).hom.app L z0
      have hcancel :
          (ModuleCat.extendScalarsComp D.u D.s).inv.app L
              ((ModuleCat.extendScalarsComp D.u D.s).hom.app L z0) = z0 := by
        simp
      have heq {f g : B' →+* R} (hfg : f = g) :
          ((eqToHom (congrArg (fun k => ModuleCat.extendScalars k) hfg)).app L).hom
              ((1 : R) ⊗ₜ[B', f] l) =
            (1 : R) ⊗ₜ[B', g] l := by
        subst g
        rfl
      have heq' :
          ((eqToHom (congrArg (fun k => ModuleCat.extendScalars k) D.comm)).app L).hom z0 =
            (1 : R) ⊗ₜ[B', D.t.comp D.v] l := by
        dsimp [z0]
        exact heq D.comm
      have hbase_z :
          (moduleBaseChangeComparison D).hom.app L z =
            (ModuleCat.extendScalarsComp D.v D.t).hom.app L
              ((1 : R) ⊗ₜ[B', D.t.comp D.v] l) := by
        dsimp [z, moduleBaseChangeComparison]
        rw [hcancel]
        dsimp [z0]
        rw [heq']
        rfl
      have hF :
          ((moduleBaseChangeComparison D).hom.app L ≫
            (ModuleCat.extendScalars D.t).map q).hom z =
            ((ModuleCat.extendScalars D.s).map p ≫
              moduleGluingComparison D X).hom z := by
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        rw [hbase_z]
        dsimp [z]
        have hvt := ModuleCat.extendScalarsComp_hom_app_one_tmul D.v D.t L l
        erw [hvt]
        dsimp [z0]
        have hut := ModuleCat.extendScalarsComp_hom_app_one_tmul D.u D.s L l
        rw [hut]
        change
          ((ModuleCat.extendScalars D.t).map q).hom'
              ((1 : R) ⊗ₜ[R', D.t]
                ((1 : R') ⊗ₜ[B', D.v] l)) =
            X.obj.hom.hom'
              (((ModuleCat.extendScalars D.s).map p).hom'
                ((1 : R) ⊗ₜ[B, D.s]
                  ((1 : B) ⊗ₜ[B', D.u] l)))
        exact hdesired.symm
      change
        ((moduleBaseChangeComparison D).hom.app L ≫
          (ModuleCat.extendScalars D.t).map q).hom
            ((1 : R) ⊗ₜ[B, D.s] ((1 : B) ⊗ₜ[B', D.u] l)) =
          ((ModuleCat.extendScalars D.s).map p ≫
            moduleGluingComparison D X).hom
            ((1 : R) ⊗ₜ[B, D.s] ((1 : B) ⊗ₜ[B', D.u] l))
      have hz : z =
          ((1 : R) ⊗ₜ[B, D.s] ((1 : B) ⊗ₜ[B', D.u] l) :
            (ModuleCat.extendScalars D.u ⋙ ModuleCat.extendScalars D.s).obj L) := by
        dsimp [z, z0]
        exact ModuleCat.extendScalarsComp_hom_app_one_tmul D.u D.s L l
      rw [← hz]
      exact hF
    have hmap_y := congrArg (fun k => k y) hmap
    exact hmap_y

/-- The source's module functor has the compatible-pair fibre product as a
right adjoint. -/
theorem moduleFiberProduct_rightAdjoint_exists
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') :
    Nonempty (ModuleFiberProductAdjunctionData D) := by
  let e : ∀ (L : ModuleCat B') (X : ModuleGluingCategory D),
      ((moduleBaseChange D).obj L ⟶ X) ≃
        (L ⟶ (moduleFiberProductRightAdjointCanonical D).obj X) :=
    fun L X =>
      { toFun := fun f =>
          pullback.lift
            ((ModuleCat.extendRestrictScalarsAdj D.u).homEquiv _ _ f.hom.left)
            ((ModuleCat.extendRestrictScalarsAdj D.v).homEquiv _ _ f.hom.right)
            ((moduleFiberProduct_hcompat D L X _ _).mp f.hom.w.symm)
        invFun := fun g =>
          ObjectProperty.homMk
            { left := ((ModuleCat.extendRestrictScalarsAdj D.u).homEquiv _ _).symm
                (g ≫ pullback.fst (moduleFiberLeftMap D X) (moduleFiberRightMap D X))
              right := ((ModuleCat.extendRestrictScalarsAdj D.v).homEquiv _ _).symm
                (g ≫ pullback.snd (moduleFiberLeftMap D X) (moduleFiberRightMap D X))
              w := by
                change L ⟶ moduleFiberProduct D X at g
                symm
                apply (moduleFiberProduct_hcompat D L X _ _).mpr
                simp only [Equiv.apply_symm_apply]
                change
                  (g ≫ pullback.fst (moduleFiberLeftMap D X) (moduleFiberRightMap D X)) ≫
                      moduleFiberLeftMap D X =
                    (g ≫ pullback.snd (moduleFiberLeftMap D X) (moduleFiberRightMap D X)) ≫
                      moduleFiberRightMap D X
                simp only [Category.assoc]
                rw [pullback.condition] }
        left_inv := by
          intro f
          apply ObjectProperty.hom_ext
          apply Comma.hom_ext
          · change ((ModuleCat.extendRestrictScalarsAdj D.u).homEquiv _ _).symm
                (((pullback.lift _ _ _) ≫
                  pullback.fst (moduleFiberLeftMap D X) (moduleFiberRightMap D X))) =
              f.hom.left
            rw [pullback.lift_fst]
            exact ((ModuleCat.extendRestrictScalarsAdj D.u).homEquiv _ _).symm_apply_apply _
          · change ((ModuleCat.extendRestrictScalarsAdj D.v).homEquiv _ _).symm
                (((pullback.lift _ _ _) ≫
                  pullback.snd (moduleFiberLeftMap D X) (moduleFiberRightMap D X))) =
              f.hom.right
            rw [pullback.lift_snd]
            exact ((ModuleCat.extendRestrictScalarsAdj D.v).homEquiv _ _).symm_apply_apply _
        right_inv := by
          intro g
          apply pullback.hom_ext
          · change
              (pullback.lift _ _ _) ≫
                  pullback.fst (moduleFiberLeftMap D X) (moduleFiberRightMap D X) =
                g ≫ pullback.fst (moduleFiberLeftMap D X) (moduleFiberRightMap D X)
            rw [pullback.lift_fst]
            exact ((ModuleCat.extendRestrictScalarsAdj D.u).homEquiv _ _).apply_symm_apply _
          · change
              (pullback.lift _ _ _) ≫
                  pullback.snd (moduleFiberLeftMap D X) (moduleFiberRightMap D X) =
                g ≫ pullback.snd (moduleFiberLeftMap D X) (moduleFiberRightMap D X)
            rw [pullback.lift_snd]
            exact ((ModuleCat.extendRestrictScalarsAdj D.v).homEquiv _ _).apply_symm_apply _ }
  have e_toFun (L : ModuleCat B') (X : ModuleGluingCategory D)
      (f : (moduleBaseChange D).obj L ⟶ X) :
      e L X f =
        pullback.lift
          ((ModuleCat.extendRestrictScalarsAdj D.u).homEquiv _ _ f.hom.left)
          ((ModuleCat.extendRestrictScalarsAdj D.v).homEquiv _ _ f.hom.right)
          ((moduleFiberProduct_hcompat D L X _ _).mp f.hom.w.symm) := rfl
  let adj : moduleBaseChangeFunctor D ⊣ moduleFiberProductRightAdjointCanonical D :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun L X => e L X
        homEquiv_naturality_left_symm := by
          intro L' L X f g
          change L ⟶ moduleFiberProduct D X at g
          apply ObjectProperty.hom_ext
          apply Comma.hom_ext
          · change
              ((ModuleCat.extendRestrictScalarsAdj D.u).homEquiv _ _).symm
                  ((f ≫ g) ≫
                    pullback.fst (moduleFiberLeftMap D X) (moduleFiberRightMap D X)) =
                (ModuleCat.extendScalars D.u).map f ≫
                  ((ModuleCat.extendRestrictScalarsAdj D.u).homEquiv _ _).symm
                    (g ≫ pullback.fst (moduleFiberLeftMap D X)
                      (moduleFiberRightMap D X))
            rw [Category.assoc]
            rw [(ModuleCat.extendRestrictScalarsAdj D.u).homEquiv_naturality_left_symm]
          · change
              ((ModuleCat.extendRestrictScalarsAdj D.v).homEquiv _ _).symm
                  ((f ≫ g) ≫
                    pullback.snd (moduleFiberLeftMap D X) (moduleFiberRightMap D X)) =
                (ModuleCat.extendScalars D.v).map f ≫
                  ((ModuleCat.extendRestrictScalarsAdj D.v).homEquiv _ _).symm
                    (g ≫ pullback.snd (moduleFiberLeftMap D X)
                      (moduleFiberRightMap D X))
            rw [Category.assoc]
            rw [(ModuleCat.extendRestrictScalarsAdj D.v).homEquiv_naturality_left_symm]
        homEquiv_naturality_right := by
          intro L X Y f g
          apply pullback.hom_ext
          · rw [e_toFun, e_toFun]
            dsimp [moduleFiberProductRightAdjointCanonical]
            simp only [moduleFiberProductMap, pullback.lift_fst, pullback.lift_fst_assoc,
              Category.assoc]
            change
              (ModuleCat.extendRestrictScalarsAdj D.u).homEquiv _ _
                  (f.hom.left ≫ g.hom.left) =
                (ModuleCat.extendRestrictScalarsAdj D.u).homEquiv _ _ f.hom.left ≫
                  (ModuleCat.restrictScalars D.u).map g.hom.left
            erw [(ModuleCat.extendRestrictScalarsAdj D.u).homEquiv_naturality_right]
          · rw [e_toFun, e_toFun]
            dsimp [moduleFiberProductRightAdjointCanonical]
            simp only [moduleFiberProductMap, pullback.lift_snd, pullback.lift_snd_assoc,
              Category.assoc]
            change
              (ModuleCat.extendRestrictScalarsAdj D.v).homEquiv _ _
                  (f.hom.right ≫ g.hom.right) =
                (ModuleCat.extendRestrictScalarsAdj D.v).homEquiv _ _ f.hom.right ≫
                  (ModuleCat.restrictScalars D.v).map g.hom.right
            erw [(ModuleCat.extendRestrictScalarsAdj D.v).homEquiv_naturality_right] }
  exact ⟨{ adjunction := adj }⟩

noncomputable def moduleFiberProductAdjunctionData
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') : ModuleFiberProductAdjunctionData D :=
  Classical.choice (moduleFiberProduct_rightAdjoint_exists D)

noncomputable abbrev moduleFiberProductRightAdjoint
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') : ModuleGluingCategory D ⥤ ModuleCat.{u} B' :=
  moduleFiberProductRightAdjointCanonical D

/-- The source-facing adjunction Hom equivalence. -/
noncomputable def moduleFiberProductHomEquiv
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    ((moduleBaseChange D).obj L ⟶ X) ≃
      (L ⟶ (moduleFiberProductRightAdjoint D).obj X) :=
  (moduleFiberProductAdjunctionData D).adjunction.homEquiv L X

/-- The compatible pairs of component maps appearing on the right-hand side
of the source's displayed Hom identity. -/
def moduleCompatibleHomPairs
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    Set (((ModuleCat.extendScalars D.u).obj L ⟶
          moduleGluingLeftObj (D := D) (X := X)) ×
      ((ModuleCat.extendScalars D.v).obj L ⟶
        moduleGluingRightObj (D := D) (X := X))) :=
  {p |
    (moduleBaseChangeComparison D).hom.app L ≫
          (ModuleCat.extendScalars D.t).map p.2 =
    (ModuleCat.extendScalars D.s).map p.1 ≫
        moduleGluingComparison (D := D) (X := X)}

/- The second displayed Hom fibre product in the source, after applying the
tensor--restriction adjunctions, is the ordinary pullback Hom description
for the categorical module pullback. -/
def moduleCompatibleHomPairsAdjoint
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    Set (((L ⟶ (ModuleCat.restrictScalars D.u).obj
          (moduleGluingLeftObj (D := D) (X := X))) ×
      (L ⟶ (ModuleCat.restrictScalars D.v).obj
        (moduleGluingRightObj (D := D) (X := X))))) :=
  {p |
    p.1 ≫ moduleFiberLeftMap D X =
      p.2 ≫ moduleFiberRightMap D X}

/-- The displayed Hom fibre product is equivalent to the adjunction Hom set.
The subtype is the ordinary Lean realization of the fibre product of the two
component Hom sets over the common `R`-Hom set. -/
theorem moduleFiberProductHomPairEquiv_exists
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    Nonempty
      ((L ⟶ moduleFiberProduct D X) ≃
        {p : ((ModuleCat.extendScalars D.u).obj L ⟶
              moduleGluingLeftObj (D := D) (X := X)) ×
          ((ModuleCat.extendScalars D.v).obj L ⟶
            moduleGluingRightObj (D := D) (X := X)) //
          p ∈ moduleCompatibleHomPairs D L X}) := by
  sorry
/- Prior attempt retained for later completion:
  have hcompat :
      ∀ (p : (ModuleCat.extendScalars D.u).obj L ⟶ X.obj.left)
        (q : (ModuleCat.extendScalars D.v).obj L ⟶ X.obj.right),
        (moduleBaseChangeComparison D).hom.app L ≫
              (ModuleCat.extendScalars D.t).map q =
            (ModuleCat.extendScalars D.s).map p ≫
              moduleGluingComparison (D := D) (X := X) ↔
          (ModuleCat.extendRestrictScalarsAdj D.u).homEquiv _ _ p ≫
                moduleFiberLeftMap D X =
            (ModuleCat.extendRestrictScalarsAdj D.v).homEquiv _ _ q ≫
                moduleFiberRightMap D X := by
    intro p q
    constructor
    · intro h
      apply ModuleCat.hom_ext
      ext x
      have hleft :
          ((ModuleCat.extendRestrictScalarsAdj D.u).homEquiv L
              X.obj.left p ≫
              moduleFiberLeftMap D X) x =
            X.obj.hom ((1 : R) ⊗ₜ[B, D.s]
              (p ((1 : B) ⊗ₜ[B', D.u] x))) := by
        dsimp [moduleFiberLeftMap]
        simp [ModuleCat.comp_apply,
          ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
          ModuleCat.restrictScalarsComp'App_inv_apply]
        rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
        rfl
      have hright :
          ((ModuleCat.extendRestrictScalarsAdj D.v).homEquiv L
              X.obj.right q ≫
              moduleFiberRightMap D X) x =
            (1 : R) ⊗ₜ[R', D.t]
              (q ((1 : R') ⊗ₜ[B', D.v] x)) := by
        dsimp [moduleFiberRightMap]
        simp [ModuleCat.comp_apply,
          ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
          ModuleCat.restrictScalarsComp'App_inv_apply]
        rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
        rfl
      rw [hleft, hright]
      let z0 : (ModuleCat.extendScalars (D.s.comp D.u)).obj L :=
        ((1 : R) ⊗ₜ[B'] x)
      let z : (ModuleCat.extendScalars D.u ⋙ ModuleCat.extendScalars D.s).obj L :=
        (ModuleCat.extendScalarsComp D.u D.s).hom.app L z0
      have hcancel :
          (ModuleCat.extendScalarsComp D.u D.s).inv.app L
              ((ModuleCat.extendScalarsComp D.u D.s).hom.app L z0) = z0 := by
        simpa [ModuleCat.hom_comp, LinearMap.coe_comp] using
          congrArg (fun f => f z0)
            ((ModuleCat.extendScalarsComp D.u D.s).hom_inv_id_app L)
      have heq {f g : B' →+* R} (hfg : f = g) :
          ((eqToHom (congrArg (fun k => ModuleCat.extendScalars k) hfg)).app L).hom
              ((1 : R) ⊗ₜ[B', f] x) =
            (1 : R) ⊗ₜ[B', g] x := by
        subst g
        rfl
      have heq' :
          ((eqToHom (congrArg (fun k => ModuleCat.extendScalars k) D.comm)).app L).hom z0 =
            (1 : R) ⊗ₜ[B', D.t.comp D.v] x := by
        dsimp [z0]
        exact heq D.comm
      have hbase_z :
          (moduleBaseChangeComparison D).hom.app L z =
            (ModuleCat.extendScalarsComp D.v D.t).hom.app L
              ((1 : R) ⊗ₜ[B', D.t.comp D.v] x) := by
        dsimp [z, moduleBaseChangeComparison]
        rw [hcancel]
        dsimp [z0]
        rw [heq']
        rfl
      have hx := congrArg (fun k => k.hom z) h
      simp only [ModuleCat.hom_comp] at hx
      simp only [LinearMap.comp_apply] at hx
      rw [hbase_z] at hx
      have hvt := ModuleCat.extendScalarsComp_hom_app_one_tmul D.v D.t L x
      erw [hvt] at hx
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hx
      change
        X.obj.hom ((1 : R) ⊗ₜ[B, D.s]
          (p ((1 : B) ⊗ₜ[B', D.u] x))) =
          (1 : R) ⊗ₜ[R', D.t]
          (q ((1 : R') ⊗ₜ[B', D.v] x))
      change
        ((ModuleCat.extendScalars D.t).map q).hom'
            ((1 : R) ⊗ₜ[R', D.t] ((1 : R') ⊗ₜ[B', D.v] x)) =
          X.obj.hom.hom'
            (((ModuleCat.extendScalars D.s).map p).hom'
              ((1 : R) ⊗ₜ[B, D.s] ((1 : B) ⊗ₜ[B', D.u] x))) at hx
      exact hx.symm
    · intro h
      apply ModuleCat.hom_ext
      ext x
      simp [moduleFiberLeftMap, moduleFiberRightMap,
        ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] at *
  let P :=
      {p : ((L ⟶ (ModuleCat.restrictScalars D.u).obj
              (moduleGluingLeftObj (D := D) (X := X))) ×
          (L ⟶ (ModuleCat.restrictScalars D.v).obj
            (moduleGluingRightObj (D := D) (X := X)))) //
        p ∈ moduleCompatibleHomPairsAdjoint D L X}
  let e0 : (L ⟶ moduleFiberProduct D X) ≃ P :=
    Equiv.mk
      (fun f =>
        ⟨(f ≫ pullback.fst (moduleFiberLeftMap D X) (moduleFiberRightMap D X),
          f ≫ pullback.snd (moduleFiberLeftMap D X) (moduleFiberRightMap D X)), by
          change (f ≫ pullback.fst (moduleFiberLeftMap D X) (moduleFiberRightMap D X)) ≫
              moduleFiberLeftMap D X =
            (f ≫ pullback.snd (moduleFiberLeftMap D X) (moduleFiberRightMap D X)) ≫
              moduleFiberRightMap D X
          simp only [Category.assoc]
          rw [pullback.condition]⟩)
      (fun p => pullback.lift p.1.1 p.1.2 (by
        change p.1.1 ≫ moduleFiberLeftMap D X =
          p.1.2 ≫ moduleFiberRightMap D X
        exact p.2))
      (by
        intro f
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
        · rw [pullback.lift_snd])
      (by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · change pullback.lift p.1.1 p.1.2 _ ≫
            pullback.fst (moduleFiberLeftMap D X) (moduleFiberRightMap D X) = p.1.1
          rw [pullback.lift_fst]
        · change pullback.lift p.1.1 p.1.2 _ ≫
            pullback.snd (moduleFiberLeftMap D X) (moduleFiberRightMap D X) = p.1.2
          rw [pullback.lift_snd])
  let e1 : P ≃
      {p : ((ModuleCat.extendScalars D.u).obj L ⟶
              moduleGluingLeftObj (D := D) (X := X)) ×
          ((ModuleCat.extendScalars D.v).obj L ⟶
            moduleGluingRightObj (D := D) (X := X)) //
          p ∈ moduleCompatibleHomPairs D L X} :=
    { toFun := fun p =>
        ⟨((ModuleCat.extendRestrictScalarsAdj D.u).homEquiv _ _).symm p.1.1,
          ((ModuleCat.extendRestrictScalarsAdj D.v).homEquiv _ _).symm p.1.2,
          (hcompat _ _).mpr p.2⟩
      invFun := fun p =>
        ⟨((ModuleCat.extendRestrictScalarsAdj D.u).homEquiv _ _ p.1),
          ((ModuleCat.extendRestrictScalarsAdj D.v).homEquiv _ _ p.2),
          (hcompat _ _).mp p.2⟩
      left_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · exact (ModuleCat.extendRestrictScalarsAdj D.u).homEquiv.apply_symm_apply _
        · exact (ModuleCat.extendRestrictScalarsAdj D.v).homEquiv.apply_symm_apply _
      right_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · exact (ModuleCat.extendRestrictScalarsAdj D.u).homEquiv.symm_apply_apply _
        · exact (ModuleCat.extendRestrictScalarsAdj D.v).homEquiv.symm_apply_apply _ }
  exact ⟨e0.trans e1⟩
-/
/- Original nontrivial proof retained for later completion:
  have hcompat :
      ∀ (p : (ModuleCat.extendScalars D.u).obj L ⟶ X.obj.left)
        (q : (ModuleCat.extendScalars D.v).obj L ⟶ X.obj.right),
        (moduleBaseChangeComparison D).hom.app L ≫
              (ModuleCat.extendScalars D.t).map q =
            (ModuleCat.extendScalars D.s).map p ≫
              moduleGluingComparison (D := D) (X := X) ↔
          (ModuleCat.extendRestrictScalarsAdj D.u).homEquiv _ _ p ≫
                moduleFiberLeftMap D X =
            (ModuleCat.extendRestrictScalarsAdj D.v).homEquiv _ _ q ≫
                moduleFiberRightMap D X := by
    intro p q
    constructor
    · intro h
      apply ModuleCat.hom_ext
      ext x
      have hleft :
          ((ModuleCat.extendRestrictScalarsAdj D.u).homEquiv L
              X.obj.left p ≫
              moduleFiberLeftMap D X) x =
            X.obj.hom ((1 : R) ⊗ₜ[B, D.s]
              (p ((1 : B) ⊗ₜ[B', D.u] x))) := by
        dsimp [moduleFiberLeftMap]
        simp [ModuleCat.comp_apply,
          ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
          ModuleCat.restrictScalarsComp'App_inv_apply]
        rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
        rfl
      have hright :
          ((ModuleCat.extendRestrictScalarsAdj D.v).homEquiv L
              X.obj.right q ≫
              moduleFiberRightMap D X) x =
            (1 : R) ⊗ₜ[R', D.t]
              (q ((1 : R') ⊗ₜ[B', D.v] x)) := by
        dsimp [moduleFiberRightMap]
        simp [ModuleCat.comp_apply,
          ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
          ModuleCat.restrictScalarsComp'App_inv_apply]
        rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
        rfl
      rw [hleft, hright]
      let z0 : (ModuleCat.extendScalars (D.s.comp D.u)).obj L :=
        ((1 : R) ⊗ₜ[B'] x)
      let z : (ModuleCat.extendScalars D.u ⋙ ModuleCat.extendScalars D.s).obj L :=
        (ModuleCat.extendScalarsComp D.u D.s).hom.app L z0
      have hcancel :
          (ModuleCat.extendScalarsComp D.u D.s).inv.app L
              ((ModuleCat.extendScalarsComp D.u D.s).hom.app L z0) = z0 := by
        simpa [ModuleCat.hom_comp, LinearMap.coe_comp] using
          congrArg (fun f => f z0)
            ((ModuleCat.extendScalarsComp D.u D.s).hom_inv_id_app L)
      have heq {f g : B' →+* R} (hfg : f = g) :
          ((eqToHom (congrArg (fun k => ModuleCat.extendScalars k) hfg)).app L).hom
              ((1 : R) ⊗ₜ[B', f] x) =
            (1 : R) ⊗ₜ[B', g] x := by
        subst g
        rfl
      have heq' :
          ((eqToHom (congrArg (fun k => ModuleCat.extendScalars k) D.comm)).app L).hom z0 =
            (1 : R) ⊗ₜ[B', D.t.comp D.v] x := by
        dsimp [z0]
        exact heq D.comm
      have hbase_z :
          (moduleBaseChangeComparison D).hom.app L z =
            (ModuleCat.extendScalarsComp D.v D.t).hom.app L
              ((1 : R) ⊗ₜ[B', D.t.comp D.v] x) := by
        dsimp [z, moduleBaseChangeComparison]
        rw [hcancel]
        dsimp [z0]
        rw [heq']
        rfl
      have hx := congrArg (fun k => k.hom z) h
      simp only [ModuleCat.hom_comp] at hx
      simp only [LinearMap.comp_apply] at hx
      rw [hbase_z] at hx
      have hvt := ModuleCat.extendScalarsComp_hom_app_one_tmul D.v D.t L x
      erw [hvt] at hx
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hx
      change
        X.obj.hom ((1 : R) ⊗ₜ[B, D.s]
          (p ((1 : B) ⊗ₜ[B', D.u] x))) =
          (1 : R) ⊗ₜ[R', D.t]
          (q ((1 : R') ⊗ₜ[B', D.v] x))
      change
        ((ModuleCat.extendScalars D.t).map q).hom'
            ((1 : R) ⊗ₜ[R', D.t] ((1 : R') ⊗ₜ[B', D.v] x)) =
          X.obj.hom.hom'
            (((ModuleCat.extendScalars D.s).map p).hom'
              ((1 : R) ⊗ₜ[B, D.s] ((1 : B) ⊗ₜ[B', D.u] x))) at hx
      exact hx.symm
    · intro h
      apply ModuleCat.hom_ext
      ext x
      simp [moduleFiberLeftMap, moduleFiberRightMap,
        ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] at *
  sorry
-/

/-- The second displayed Hom fibre product is equivalent to maps into the
categorical module pullback. -/
theorem moduleFiberProductHomAdjointPairEquiv_exists
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    Nonempty
      ((L ⟶ moduleFiberProduct D X) ≃
        {p : ((L ⟶ (ModuleCat.restrictScalars D.u).obj
                (moduleGluingLeftObj (D := D) (X := X))) ×
            (L ⟶ (ModuleCat.restrictScalars D.v).obj
              (moduleGluingRightObj (D := D) (X := X)))) //
          p ∈ moduleCompatibleHomPairsAdjoint D L X}) := by
  let P :=
      {p : ((L ⟶ (ModuleCat.restrictScalars D.u).obj
              (moduleGluingLeftObj (D := D) (X := X))) ×
          (L ⟶ (ModuleCat.restrictScalars D.v).obj
            (moduleGluingRightObj (D := D) (X := X)))) //
        p ∈ moduleCompatibleHomPairsAdjoint D L X}
  let left : ∀ p : P,
      L ⟶ (ModuleCat.restrictScalars D.u).obj X.obj.left :=
    fun p => by
      simpa only [moduleGluingLeftObj, isoCommaLeft_obj] using p.1.1
  let right : ∀ p : P,
      L ⟶ (ModuleCat.restrictScalars D.v).obj X.obj.right :=
    fun p => by
      simpa only [moduleGluingRightObj, isoCommaRight_obj] using p.1.2
  have hforward :
      ∀ f : L ⟶ moduleFiberProduct D X,
        (f ≫ pullback.fst (moduleFiberLeftMap D X) (moduleFiberRightMap D X),
          f ≫ pullback.snd (moduleFiberLeftMap D X) (moduleFiberRightMap D X)) ∈
          moduleCompatibleHomPairsAdjoint D L X := by
    intro f
    change (f ≫ pullback.fst (moduleFiberLeftMap D X) (moduleFiberRightMap D X)) ≫
        moduleFiberLeftMap D X =
      (f ≫ pullback.snd (moduleFiberLeftMap D X) (moduleFiberRightMap D X)) ≫
        moduleFiberRightMap D X
    simp only [Category.assoc]
    rw [pullback.condition]
  let e : (L ⟶ moduleFiberProduct D X) ≃ P :=
    Equiv.mk
      (fun f =>
        ⟨(f ≫ pullback.fst (moduleFiberLeftMap D X) (moduleFiberRightMap D X),
          f ≫ pullback.snd (moduleFiberLeftMap D X) (moduleFiberRightMap D X)),
          hforward f⟩)
      (fun p => pullback.lift (left p) (right p) (by
        change (p.1.1 ≫ moduleFiberLeftMap D X) =
          (p.1.2 ≫ moduleFiberRightMap D X)
        exact p.2))
      (by
        intro f
        dsimp [left, right]
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
        · rw [pullback.lift_snd])
      (by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · change pullback.lift (left p) (right p) _ ≫
            pullback.fst (moduleFiberLeftMap D X) (moduleFiberRightMap D X) = p.1.1
          rw [pullback.lift_fst]
        · change pullback.lift (left p) (right p) _ ≫
            pullback.snd (moduleFiberLeftMap D X) (moduleFiberRightMap D X) = p.1.2
          rw [pullback.lift_snd])
  exact Nonempty.intro e

noncomputable def moduleFiberProductHomAdjointPairEquiv
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    (L ⟶ moduleFiberProduct D X) ≃
      {p : ((L ⟶ (ModuleCat.restrictScalars D.u).obj
              (moduleGluingLeftObj (D := D) (X := X))) ×
          (L ⟶ (ModuleCat.restrictScalars D.v).obj
            (moduleGluingRightObj (D := D) (X := X)))) //
        p ∈ moduleCompatibleHomPairsAdjoint D L X} :=
  Classical.choice (moduleFiberProductHomAdjointPairEquiv_exists D L X)

/-- A chosen source-facing equivalence for the Hom identity. -/
noncomputable def moduleFiberProductHomPairEquiv
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    (L ⟶ moduleFiberProduct D X) ≃
      {p : ((ModuleCat.extendScalars D.u).obj L ⟶
            moduleGluingLeftObj (D := D) (X := X)) ×
        ((ModuleCat.extendScalars D.v).obj L ⟶
          moduleGluingRightObj (D := D) (X := X)) //
        p ∈ moduleCompatibleHomPairs D L X} :=
  Classical.choice (moduleFiberProductHomPairEquiv_exists D L X)

end

end Formalization.Books.MoreAlgebra.Unit05
