import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-!
# More on Algebra, Chapter 3: Stably free modules

The source's stable-freeness predicate is Mathlib's canonical
`Module.IsStablyFree`.  The source-facing stable-isomorphism relation is
recorded separately using finite free modules `Fin n → R`; quotient modules
`M / IM` use Mathlib's canonical `M ⧸ (I • ⊤)` construction.
-/

namespace Formalization.Books.MoreAlgebra.Unit03

open CategoryTheory
open scoped Pointwise

universe u

/-! ## The definition of stable freeness -/

/-- Two modules are stably isomorphic when they become linearly equivalent
after adjoining finite free summands.  The type `Fin n → R` represents the
finite direct sum `R^{⊕ n}`. -/
def StablyIsomorphic (R M N : Type u) [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] : Prop :=
  ∃ m n : ℕ,
    Nonempty ((M × (Fin m → R)) ≃ₗ[R] (N × (Fin n → R)))

/-- The source's notion of a stably free module, delegated to Mathlib's
canonical predicate. -/
abbrev StablyFree (R M : Type u) [Ring R]
    [AddCommGroup M] [Module R M] : Prop :=
  Module.IsStablyFree R M

/-- Mathlib's canonical stably-free predicate expresses the source's second
definition: being stably isomorphic to a free module. -/
theorem stablyFree_iff_stablyIsomorphic_free
    {R M : Type u} [Ring R] [AddCommGroup M] [Module R M] :
    StablyFree R M ↔
      ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module R F)
        (_ : Module.Free R F), StablyIsomorphic R M F := by
  constructor
  · intro h
    let : Module.IsStablyFree R M := h
    obtain ⟨N, hNadd, hNmod, hNfin, hNfree, hMNfree⟩ :=
      Module.IsStablyFree.exist_free_prod R M
    let : AddCommGroup N := hNadd
    let : Module R N := hNmod
    let : Module.Finite R N := hNfin
    let : Module.Free R N := hNfree
    let ι := Module.Free.ChooseBasisIndex R N
    let : Fintype ι := Module.Free.ChooseBasisIndex.fintype R N
    let b := Module.Free.chooseBasis R N
    let m := Fintype.card ι
    let eN : N ≃ₗ[R] (Fin m → R) :=
      (b.reindex (Fintype.equivFin ι)).equivFun
    refine ⟨M × N, inferInstance, inferInstance, hMNfree, ?_⟩
    refine ⟨m, 0, ?_⟩
    exact ⟨((LinearEquiv.refl R M).prodCongr eN.symm) ≪≫ₗ
      (LinearEquiv.prodUnique (R := R) (M := M × N) (M₂ := Fin 0 → R)).symm⟩
  · rintro ⟨F, hFadd, hFmod, hFfree, ⟨m, n, ⟨e⟩⟩⟩
    let : AddCommGroup F := hFadd
    let : Module R F := hFmod
    let : Module.Free R F := hFfree
    let : Module.Free R (F × (Fin n → R)) := inferInstance
    let : Module.Finite R (Fin m → R) := inferInstance
    have hfree : Module.Free R (M × (Fin m → R)) :=
      Module.Free.of_equiv e.symm
    let : Module.Free R (M × (Fin m → R)) := hfree
    exact Module.IsStablyFree.of_free_prod R M (Fin m → R)

/-- A stably free module is projective.  This is Mathlib's existing
`Module.IsStablyFree` instance, exposed under the source-facing name. -/
theorem stablyFree_projective
    {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]
    [StablyFree R M] : Module.Projective R M :=
  inferInstance

/-! ## The split exact sequence lemma -/

/-- The split direct-sum decomposition used in the proof of the source
two-out-of-three lemma.  It combines Mathlib's canonical splitting of a
short exact sequence with its module biproduct/product equivalence. -/
noncomputable def shortExact_middle_linearEquiv_prod
    {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Projective R S.X₃] :
    S.X₂ ≃ₗ[R] (S.X₁ × S.X₃) :=
  ((ShortComplex.ShortExact.splittingOfProjective hS).isoBinaryBiproduct ≪≫
    ModuleCat.biprodIsoProd S.X₁ S.X₃).toLinearEquiv

/-- In a short exact sequence of finite projective modules, stable freeness
has the two-out-of-three property. -/
theorem shortExact_isStablyFree_two_of_three
    {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.Projective R S.X₁]
    [Module.Finite R S.X₂] [Module.Projective R S.X₂]
    [Module.Finite R S.X₃] [Module.Projective R S.X₃] :
    (StablyFree R S.X₁ ∧ StablyFree R S.X₂ → StablyFree R S.X₃) ∧
      (StablyFree R S.X₁ ∧ StablyFree R S.X₃ → StablyFree R S.X₂) ∧
        (StablyFree R S.X₂ ∧ StablyFree R S.X₃ → StablyFree R S.X₁) := by
  have hsplit := shortExact_middle_linearEquiv_prod S hS
  have hprod :
      ∀ (A C : Type u) [AddCommGroup A] [Module R A]
        [AddCommGroup C] [Module R C],
        StablyFree R A → StablyFree R C → StablyFree R (A × C) := by
    intro A C _ _ _ _ hA hC
    let : Module.IsStablyFree R A := hA
    let : Module.IsStablyFree R C := hC
    obtain ⟨N₁, hN₁add, hN₁mod, hN₁fin, hN₁free, hAfree⟩ :=
      Module.IsStablyFree.exist_free_prod R A
    obtain ⟨N₂, hN₂add, hN₂mod, hN₂fin, hN₂free, hCfree⟩ :=
      Module.IsStablyFree.exist_free_prod R C
    let : AddCommGroup N₁ := hN₁add
    let : Module R N₁ := hN₁mod
    let : Module.Finite R N₁ := hN₁fin
    let : Module.Free R N₁ := hN₁free
    let : AddCommGroup N₂ := hN₂add
    let : Module R N₂ := hN₂mod
    let : Module.Finite R N₂ := hN₂fin
    let : Module.Free R N₂ := hN₂free
    let : Module.Free R (A × N₁) := hAfree
    let : Module.Free R (C × N₂) := hCfree
    have hfree : Module.Free R ((A × C) × (N₁ × N₂)) := by
      exact Module.Free.of_equiv
        (LinearEquiv.prodProdProdComm R A C N₁ N₂).symm
    let : Module.Free R ((A × C) × (N₁ × N₂)) := hfree
    exact Module.IsStablyFree.of_free_prod R (A × C) (N₁ × N₂)
  have hcancel :
      ∀ (A B C : Type u) [AddCommGroup A] [Module R A] [Module.Finite R A]
        [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C],
        (B ≃ₗ[R] A × C) → StablyFree R A → StablyFree R B →
          StablyFree R C := by
    intro A B C _ _ _ _ _ _ _ e hA hB
    let : Module.IsStablyFree R A := hA
    let : Module.IsStablyFree R B := hB
    obtain ⟨N₁, hN₁add, hN₁mod, hN₁fin, hN₁free, hAfree⟩ :=
      Module.IsStablyFree.exist_free_prod R A
    obtain ⟨N₂, hN₂add, hN₂mod, hN₂fin, hN₂free, hBfree⟩ :=
      Module.IsStablyFree.exist_free_prod R B
    let : AddCommGroup N₁ := hN₁add
    let : Module R N₁ := hN₁mod
    let : Module.Finite R N₁ := hN₁fin
    let : Module.Free R N₁ := hN₁free
    let : AddCommGroup N₂ := hN₂add
    let : Module R N₂ := hN₂mod
    let : Module.Finite R N₂ := hN₂fin
    let : Module.Free R N₂ := hN₂free
    let : Module.Free R (A × N₁) := hAfree
    let : Module.Free R (B × N₂) := hBfree
    let equivC : (C × ((A × N₁) × N₂)) ≃ₗ[R] ((B × N₂) × N₁) :=
      { toFun := fun x =>
          ((e.symm (x.2.1.1, x.1), x.2.2), x.2.1.2)
        invFun := fun y =>
          ((e y.1.1).2, (((e y.1.1).1, y.2), y.1.2))
        left_inv := by
          rintro ⟨c, ⟨⟨a, n₁⟩, n₂⟩⟩
          simp
        right_inv := by
          rintro ⟨⟨b, n₂⟩, n₁⟩
          simp
        map_add' := by
          intro x y
          apply Prod.ext
          · apply Prod.ext
            · simpa using e.symm.map_add (x.2.1.1, x.1) (y.2.1.1, y.1)
            · rfl
          · rfl
        map_smul' := by
          intro r x
          apply Prod.ext
          · apply Prod.ext
            · simpa using e.symm.map_smul r (x.2.1.1, x.1)
            · rfl
          · rfl }
    have hfree : Module.Free R (C × ((A × N₁) × N₂)) := by
      exact Module.Free.of_equiv (LinearEquiv.symm equivC)
    let : Module.Free R (C × ((A × N₁) × N₂)) := hfree
    exact Module.IsStablyFree.of_free_prod R C ((A × N₁) × N₂)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hcancel S.X₁ S.X₂ S.X₃ hsplit h.1 h.2
  · intro h
    let : Module.IsStablyFree R (S.X₁ × S.X₃) := hprod S.X₁ S.X₃ h.1 h.2
    exact Module.IsStablyFree.equiv hsplit.symm
  · intro h
    exact hcancel S.X₃ S.X₂ S.X₁
      (hsplit ≪≫ₗ LinearEquiv.prodComm R S.X₁ S.X₃) h.2 h.1

/- The displayed chain of direct sums in the source proof is an informal use
of associativity and commutativity of finite products.  The preceding
decomposition together with Mathlib's `LinearEquiv.prodAssoc` and
`LinearEquiv.prodComm` is the source-faithful interface, so no artificial
equality between differently parenthesized products is introduced. -/

/-! ## Lifting across a Jacobson-radical ideal -/

/- The source phrases the hypothesis as "every element of `1 + I` is a unit".
We use the canonical equivalent condition `I ≤ Ring.jacobson R`; the earlier
Jacobson-radical API records the equivalence with the elementwise formulation.
-/

/-- Every finite stably free module over `R ⧸ I` lifts to a finite stably free
module over `R` when `I` is contained in the Jacobson radical. -/
theorem exists_finite_stablyFree_lift
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ring.jacobson R)
    (E : ModuleCat.{u} (R ⧸ I))
    [Module.Finite (R ⧸ I) E] [StablyFree (R ⧸ I) E] :
    ∃ M : ModuleCat.{u} R,
        Module.Finite R M ∧ StablyFree R M ∧
        Nonempty ((M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I] E) := by sorry
/-
  classical
  let A := R ⧸ I
  letI : Module.IsStablyFree A E := ‹StablyFree A E›
  obtain ⟨N, hNadd, hNmod, hNfin, hNfree, hENfree⟩ :=
    Module.IsStablyFree.exist_free_prod A E
  letI : AddCommGroup N := hNadd
  letI : Module A N := hNmod
  letI : Module.Finite A N := hNfin
  letI : Module.Free A N := hNfree
  let ιN := Module.Free.ChooseBasisIndex A N
  letI : Fintype ιN := Module.Free.ChooseBasisIndex.fintype A N
  let eN : N ≃ₗ[A] (Fin (Fintype.card ιN) → A) :=
    (Module.Free.chooseBasis A N).reindex (Fintype.equivFin ιN) |>.equivFun
  letI : Module.Free A (E × N) := hENfree
  let ιF := Module.Free.ChooseBasisIndex A (E × N)
  letI : Fintype ιF := Module.Free.ChooseBasisIndex.fintype A (E × N)
  let eF : (E × N) ≃ₗ[A] (Fin (Fintype.card ιF) → A) :=
    (Module.Free.chooseBasis A (E × N)).reindex (Fintype.equivFin ιF) |>.equivFun
  let n := Fintype.card ιN
  let m := Fintype.card ιF
  let e : (E × (Fin n → A)) ≃ₗ[A] (Fin m → A) :=
    ((LinearEquiv.refl A E).prodCongr eN.symm) ≪≫ₗ eF
  let F : Type u := Fin m → R
  let G : Type u := Fin n → R
  let Fbar : Type u := Fin m → A
  let Gbar : Type u := Fin n → A
  let qF : F →ₗ[R] Fbar :=
    LinearMap.piMap (fun _ : Fin m => (I.mkQ : R →ₗ[R] A))
  let qG : G →ₗ[R] Gbar :=
    LinearMap.piMap (fun _ : Fin n => (I.mkQ : R →ₗ[R] A))
  have hqF : Function.Surjective qF := by
    intro y
    choose x hx using fun i : Fin m => I.mkQ_surjective (y i)
    refine ⟨x, ?_⟩
    ext i
    exact hx i
  have hqG : Function.Surjective qG := by
    intro y
    choose x hx using fun i : Fin n => I.mkQ_surjective (y i)
    refine ⟨x, ?_⟩
    ext i
    exact hx i
  let pbar : Fbar →ₗ[A] Gbar :=
    (LinearMap.snd A E Gbar).comp e.symm.toLinearMap
  let ibar : Gbar →ₗ[A] Fbar :=
    e.toLinearMap.comp (LinearMap.inr A E Gbar)
  have hpibar : pbar.comp ibar = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (e.symm (e (0, x))).2 = x
    rw [e.symm_apply_apply]
  let pbarR : Fbar →ₗ[R] Gbar := pbar.restrictScalars R
  let ibarR : Gbar →ₗ[R] Fbar := ibar.restrictScalars R
  obtain ⟨p, hp⟩ :=
    Module.projective_lifting_property qG (pbarR.comp qF) hqG
  obtain ⟨i, hi⟩ :=
    Module.projective_lifting_property qF (ibarR.comp qG) hqF
  let a : G →ₗ[R] G := p.comp i
  have hqa : qG.comp a = qG := by
    apply LinearMap.ext
    intro x
    change qG (p (i x)) = qG x
    have hp' := congrArg (fun f : F →ₗ[R] Gbar => f (i x)) hp
    have hi' := congrArg (fun f : G →ₗ[R] Fbar => f x) hi
    rw [show qG (p (i x)) = pbarR (qF (i x)) by
      simpa [LinearMap.comp_apply] using hp']
    rw [show qF (i x) = ibarR (qG x) by
      simpa [LinearMap.comp_apply] using hi']
    simpa [pbarR, ibarR, LinearMap.comp_apply] using
      congrArg (fun z => z (qG x)) hpibar
  have hI' : I ≤ Ideal.jacobson (⊥ : Ideal R) := by
    simpa only [Ideal.jacobson_bot] using hI
  have hrange : LinearMap.range a = ⊤ := by
    apply top_unique
    apply Submodule.le_of_le_smul_of_le_jacobson_bot
      (N' := (⊤ : Submodule R G)) Module.Finite.fg_top hI'
    intro x hx
    have hxy : qG (x - a x) = 0 := by
      rw [map_sub]
      have hqa' := congrArg (fun f : G →ₗ[R] Gbar => f x) hqa
      rw [show qG (a x) = qG x by simpa [LinearMap.comp_apply] using hqa']
      exact sub_self _
    have hmem : x - a x ∈ I • (⊤ : Submodule R G) := by
      rw [show x - a x = (∑ j : Fin n, (x - a x) j • Pi.single j 1) by
        ext k
        simp [Finset.sum_apply, Pi.single_apply]]
      apply Submodule.sum_mem
      intro j hj
      have hj' := congrFun hxy j
      change I.mkQ ((x - a x) j) = 0 at hj'
      exact Submodule.smul_mem_smul
        ((Submodule.Quotient.mk_eq_zero I).mp hj') Submodule.mem_top
    rw [← sub_add_cancel x (a x)]
    exact Submodule.add_mem _
      ((le_sup_right : I • (⊤ : Submodule R G) ≤
        LinearMap.range a ⊔ I • (⊤ : Submodule R G)) hmem)
      ((le_sup_left : LinearMap.range a ≤
        LinearMap.range a ⊔ I • (⊤ : Submodule R G)) ⟨x, rfl⟩)
  have ha_surj : Function.Surjective a := LinearMap.range_eq_top.mp hrange
  have ha : Function.Bijective a := ⟨Module.End.injective_of_surjective_fin ha_surj, ha_surj⟩
  let ae : G ≃ₗ[R] G := LinearEquiv.ofBijective a ha
  let i' : G →ₗ[R] F := i.comp ae.symm.toLinearMap
  have hi' : p.comp i' = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change p (i (ae.symm x)) = x
    have h := ae.apply_symm_apply x
    change a (ae.symm x) = x at h
    change p (i (ae.symm x)) = x at h
    exact h
  let K : Type u := LinearMap.ker p
  let eK : (K × G) ≃ₗ[R] F :=
    { toFun := fun x => (x.1 : F) + i' x.2
      invFun := fun x =>
        (⟨x - i' (p x), by
          change p (x - i' (p x)) = 0
          rw [map_sub]
          have h := congrArg (fun f : G →ₗ[R] G => f (p x)) hi'
          change p (i' (p x)) = p x at h
          rw [h, sub_self]⟩, p x)
      left_inv := by
        rintro ⟨x, y⟩
        apply Prod.ext
        · apply Subtype.ext
          change (x : F) + i' y - i' (p ((x : F) + i' y)) = (x : F)
          rw [map_add, x.property]
          have h := congrArg (fun f : G →ₗ[R] G => f y) hi'
          change p (i' y) = y at h
          rw [h]
          simp
          simp
        · change p ((x : F) + i' y) = y
          rw [map_add, x.property]
          have h := congrArg (fun f : G →ₗ[R] G => f y) hi'
          change p (i' y) = y at h
          rw [h]
      right_inv := by
        intro x
        simp [i', hi']
      map_add' := by
        rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
        change (x₁ : F) + (x₂ : F) + i' (y₁ + y₂) =
          ((x₁ : F) + i' y₁) + ((x₂ : F) + i' y₂)
        rw [map_add]
        abel
      map_smul' := by
        intro r x
        change r • (x.1 : F) + i' (r • x.2) = r • ((x.1 : F) + i' x.2)
        rw [map_smul, smul_add] }
  letI : Module.Finite R (K × G) := Module.Finite.equiv eK.symm
  letI : Module.Finite R K := by
    apply Module.Finite.of_surjective (LinearMap.fst R K G)
    intro x
    exact ⟨(x, 0), rfl⟩
  letI : Module R E := Module.compHom E (Ideal.Quotient.mk I)
  letI : IsScalarTower R A E :=
    ⟨fun r a x => by
      change (r • a) • x = r • (a • x)
      rw [Algebra.smul_def, smul_smul, Ideal.Quotient.algebraMap_eq]
      rfl⟩
  letI : Module.Free R (K × G) := Module.Free.of_equiv eK.symm
  have hstable : StablyFree R K := Module.IsStablyFree.of_free_prod R K G
  let IK : Submodule R K := I • (⊤ : Submodule R K)
  let fbar : Fbar →ₗ[A] E :=
    (LinearMap.fst A E Gbar).comp e.symm.toLinearMap
  let fbarR : Fbar →ₗ[R] E :=
    { toFun := fbar
      map_add' := by intro x y; exact fbar.map_add x y
      map_smul' := by
        intro r x
        change fbar (r • x) = r • fbar x
        rw [← IsScalarTower.algebraMap_smul A r,
          ← IsScalarTower.algebraMap_smul A r, Ideal.Quotient.algebraMap_eq]
        exact fbar.map_smul (Ideal.Quotient.mk I r) x }
  let f0 : K →ₗ[R] E := fbarR.comp (qF.comp (LinearMap.ker p).subtype)
  have hf0 : IK ≤ LinearMap.ker f0 := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun x y hx hy => ?_)
    · change fbarR (qF ((LinearMap.ker p).subtype (r • y))) = 0
      rw [(LinearMap.ker p).subtype.map_smul, qF.map_smul, fbarR.map_smul]
      have hr0 : Ideal.Quotient.mk I r = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hr
      change (Ideal.Quotient.mk I r) • fbarR (qF ((LinearMap.ker p).subtype y)) = 0
      rw [hr0, zero_smul]
    · simp only [LinearMap.mem_ker, map_add]
      rw [LinearMap.mem_ker.mp hx, LinearMap.mem_ker.mp hy, add_zero]
  let φ0 : (K ⧸ IK) →ₗ[R] E :=
    ((⊥ : Submodule R E).quotEquivOfEqBot rfl).toLinearMap.comp
      (IK.mapQ (⊥ : Submodule R E) f0 hf0)
  let φ : (K ⧸ IK) →ₗ[A] E :=
    LinearMap.extendScalarsOfSurjective I.mkQ_surjective φ0
  have hφ_mk (x : K) : φ (Submodule.Quotient.mk x) = f0 x := by
    rfl
  have hker_q (x : K) : pbar (qF (x : F)) = 0 := by
    have hp' := congrArg (fun f : F →ₗ[R] Gbar => f (x : F)) hp
    simpa [LinearMap.mem_ker.mp x.property, pbarR, LinearMap.comp_apply] using hp'.symm
  let ret : F →ₗ[R] K :=
    (LinearMap.fst R K G).comp eK.symm.toLinearMap
  have hret : ret.comp (LinearMap.ker p).subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    change ((eK.symm ((LinearMap.ker p).subtype x))).1 = x
    simp [ret, eK, x.property]
  have hret_mem {x : F} (hx : x ∈ I • (⊤ : Submodule R F)) :
      ret x ∈ IK := by
    refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · rw [map_add]
      exact Submodule.add_mem _ hx hy
  have hker_component (x : K) :
      e.symm (qF (x : F)) = (fbar (qF (x : F)), 0) := by
    apply Prod.ext
    · rfl
    · simpa [pbar, LinearMap.comp_apply] using hker_q x
  have hqae (y : G) : qG (ae.symm y) = qG y := by
    have h := congrArg (fun f : G →ₗ[R] Gbar => f (ae.symm y)) hqa
    have h' : a (ae.symm y) = y := by
      exact ae.apply_symm_apply y
    have h'' : qG y = qG (ae.symm y) := by
      simpa [a, LinearMap.comp_apply] using h
    exact h''.symm
  have hqi' (y : G) : qF (i' y) = ibar (qG y) := by
    change qF (i (ae.symm y)) = ibar (qG y)
    have h := congrArg (fun f : G →ₗ[R] Fbar => f (ae.symm y)) hi
    simpa [ibarR, LinearMap.comp_apply, hqae y] using h
  have hcompat (x : K) (y : G) :
      e.symm (qF (eK (x, y))) = (fbar (qF (x : F)), qG y) := by
    change e.symm (qF ((x : F) + i' y)) = _
    rw [qF.map_add, e.symm.map_add, hker_component x]
    have hi_bar : e.symm (ibar (qG y)) = (0, qG y) := by
      change e.symm (e (0, qG y)) = _
      rw [e.symm_apply_apply]
    rw [hqi', hi_bar]
    rfl
  have hφ_surj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := hqF (e (y, 0))
    let z : K × G := eK.symm x
    refine ⟨Submodule.Quotient.mk z.1, ?_⟩
    have hz : e.symm (qF (eK z)) = (y, 0) := by
      rw [show eK z = x by simp [z], hx, e.symm_apply_apply]
    have hfirst := congrArg Prod.fst (hcompat z.1 z.2 |>.trans hz.symm)
    rw [hφ_mk]
    simpa [f0, fbarR] using hfirst
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    obtain ⟨x', rfl⟩ := Submodule.Quotient.mk_surjective IK x
    obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective IK y
    have hxy' : fbar (qF (x' : F)) = fbar (qF (y' : F)) := by
      have h := hxy
      rw [hφ_mk, hφ_mk] at h
      simpa [f0, fbarR] using h
    have hqxy : qF (x' : F) = qF (y' : F) := by
      apply e.symm.injective
      rw [hker_component x', hker_component y', hxy']
    have hqzero : qF ((x' : F) - (y' : F)) = 0 := by
      rw [map_sub, hqxy, sub_self]
    have hmemF : (x' : F) - (y' : F) ∈ I • (⊤ : Submodule R F) := by
      rw [show (x' : F) - (y' : F) =
        (∑ j : Fin m, ((x' : F) - (y' : F)) j • Pi.single j 1) by
          ext k
          simp [Finset.sum_apply, Pi.single_apply]]
      apply Submodule.sum_mem
      intro j hj
      have hj' := congrFun hqzero j
      change I.mkQ (((x' : F) - (y' : F)) j) = 0 at hj'
      exact Submodule.smul_mem_smul
        ((Submodule.Quotient.mk_eq_zero I).mp hj') Submodule.mem_top
    have hmemK : x' - y' ∈ IK := by
      have h := hret_mem hmemF
      have hret' : ret ((x' : F) - (y' : F)) = x' - y' := by
        simpa [ret, LinearMap.comp_apply] using
          congrArg (fun f => f (x' - y')) hret
      rw [hret'] at h
      exact h
    rw [← sub_eq_zero]
    exact (Submodule.Quotient.mk_eq_zero IK).2 hmemK
  exact ⟨ModuleCat.of R K, inferInstance, hstable,
    ⟨LinearEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩⟩⟩

 -/
/-! ## Lifting finite projectivity -/

/-- A finite flat module whose reduction modulo a Jacobson-radical ideal is
projective is projective. -/
theorem finiteProjective_of_finiteFlat_of_projective_quotient
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ring.jacobson R) (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Flat R M]
    (hM : Module.Projective (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Projective R M := by
  sorry

/-! ## Uniqueness of finite-projective lifts -/

/-- A quotient linear equivalence is induced by an `R`-linear map when it
commutes with the canonical quotient maps. -/
def InducesQuotientEquiv
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (φ : M →ₗ[R] N)
    (e : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I]
      (N ⧸ (I • (⊤ : Submodule R N)))) : Prop :=
  ∀ x : M,
    e ((I • (⊤ : Submodule R M)).mkQ x) =
      (I • (⊤ : Submodule R N)).mkQ (φ x)

/-- A map between finite projective modules that induces an isomorphism after
reduction modulo a Jacobson-radical ideal is already an isomorphism. -/
theorem finiteProjective_map_isIso_of_inducesQuotientEquiv
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ring.jacobson R)
    {P P' : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup P'] [Module R P']
    [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R P'] [Module.Projective R P']
    (φ : P →ₗ[R] P')
    (hφ : ∃ e : (P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R ⧸ I]
        (P' ⧸ (I • (⊤ : Submodule R P'))),
      InducesQuotientEquiv I φ e) :
    ∃ e : P ≃ₗ[R] P', e.toLinearMap = φ := by sorry
/-
  classical
  obtain ⟨e, he⟩ := hφ
  let q : P →ₗ[R] (P ⧸ (I • (⊤ : Submodule R P))) :=
    (I • (⊤ : Submodule R P)).mkQ
  let q' : P' →ₗ[R] (P' ⧸ (I • (⊤ : Submodule R P'))) :=
    (I • (⊤ : Submodule R P')).mkQ
  let eR : (P' ⧸ (I • (⊤ : Submodule R P'))) →ₗ[R]
      (P ⧸ (I • (⊤ : Submodule R P))) :=
    e.symm.toLinearMap.restrictScalars R
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property q
    (eR.comp q') (Submodule.mkQ_surjective _)
  have hI' : I ≤ Ideal.jacobson (⊥ : Ideal R) := by
    simpa only [Ideal.jacobson_bot] using hI
  have surj_of_quotient_eq :
      ∀ {X : Type u} [AddCommGroup X] [Module R X]
        [Module.Finite R X] (f : X →ₗ[R] X),
        (∀ x : X, (I • (⊤ : Submodule R X)).mkQ (f x) =
          (I • (⊤ : Submodule R X)).mkQ x) → Function.Surjective f := by
    intro X _ _ _ f hf
    apply LinearMap.range_eq_top.mp
    apply Submodule.le_of_le_smul_of_le_jacobson_bot
      Module.Finite.fg_top hI'
    intro x hx
    have hzero : (I • (⊤ : Submodule R X)).mkQ (x - f x) = 0 := by
      rw [map_sub, hf x, sub_self]
    have hmem : x - f x ∈ I • (⊤ : Submodule R X) := by
      exact (Submodule.Quotient.mk_eq_zero I).mp hzero
    rw [← sub_add_cancel x (f x)]
    exact Submodule.add_mem _
      ((le_sup_right : I • (⊤ : Submodule R X) ≤
        LinearMap.range f ⊔ I • (⊤ : Submodule R X)) hmem)
      ((le_sup_left : LinearMap.range f ≤
        LinearMap.range f ⊔ I • (⊤ : Submodule R X)) ⟨f x, rfl⟩)
  have hleft (x : P) : q (ψ (φ x)) = q x := by
    calc
      q (ψ (φ x)) = e.symm (q' (φ x)) := by
        simpa [q, q', eR, LinearMap.comp_apply] using
          congrArg (fun f => f (φ x)) hψ
      _ = e.symm (e (q x)) := by rw [← he x]
      _ = q x := e.symm_apply_apply _
  have hright (y : P') : q' (φ (ψ y)) = q' y := by
    calc
      q' (φ (ψ y)) = e (q (ψ y)) := (he (ψ y)).symm
      _ = e (e.symm (q' y)) := by
        have h := congrArg (fun f => f y) hψ
        simpa [q, q', eR, LinearMap.comp_apply] using h
      _ = q' y := e.apply_symm_apply _
  have hleft_surj : Function.Surjective (ψ.comp φ) :=
    surj_of_quotient_eq (ψ.comp φ) hleft
  have hright_surj : Function.Surjective (φ.comp ψ) :=
    surj_of_quotient_eq (φ.comp ψ) hright
  have hleft_bij : Function.Bijective (ψ.comp φ) :=
    OrzechProperty.bijective_of_surjective_endomorphism _ hleft_surj
  have hright_bij : Function.Bijective (φ.comp ψ) :=
    OrzechProperty.bijective_of_surjective_endomorphism _ hright_surj
  have hφ_bij : Function.Bijective φ := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply hleft_bij.1
      simpa [LinearMap.comp_apply, hxy]
    · intro y
      obtain ⟨x, hx⟩ := hright_surj y
      exact ⟨ψ x, by simpa [LinearMap.comp_apply] using hx⟩
  exact ⟨LinearEquiv.ofBijective φ hφ_bij, rfl⟩
 -/

/-- Finite projective modules with isomorphic reductions modulo a
Jacobson-radical ideal are isomorphic. -/
theorem finiteProjective_quotientEquiv_imp_isomorphic
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ring.jacobson R)
    {P P' : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup P'] [Module R P']
    [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R P'] [Module.Projective R P']
    (h : Nonempty ((P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R ⧸ I]
      (P' ⧸ (I • (⊤ : Submodule R P'))))) :
    Nonempty (P ≃ₗ[R] P') := by sorry
/-
  classical
  obtain ⟨e⟩ := h
  let q' : P' →ₗ[R] (P' ⧸ (I • (⊤ : Submodule R P'))) :=
    (I • (⊤ : Submodule R P')).mkQ
  let eR : (P ⧸ (I • (⊤ : Submodule R P))) →ₗ[R]
      (P' ⧸ (I • (⊤ : Submodule R P'))) :=
    e.toLinearMap.restrictScalars R
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property q' (eR.comp
    ((I • (⊤ : Submodule R P)).mkQ)) (Submodule.mkQ_surjective _)
  have hφ' : InducesQuotientEquiv I φ e := by
    intro x
    have h := congrArg (fun f => f x) hφ
    simpa [eR, q', LinearMap.comp_apply] using h
  obtain ⟨e', _⟩ := finiteProjective_map_isIso_of_inducesQuotientEquiv
    I hI φ ⟨e, hφ'⟩
  exact ⟨e'⟩
-/

end Formalization.Books.MoreAlgebra.Unit03
