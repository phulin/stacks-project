/-
# More on Algebra, Chapter 121: Determinants of endomorphisms of finite length modules
-/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Noetherian
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
This file records the category of finite-length endomorphisms and the linear-algebraic
constructions used in the rest of the chapter.  The filtration and Jordan--Hölder arguments
are kept as interfaces: their proofs belong to the proving stage, while the definitions below
use Mathlib's module, quotient, composition-series, and linear-map APIs.
-/

namespace Formalization.Books.MoreAlgebra.Unit121

noncomputable section

open CategoryTheory
open scoped BigOperators Polynomial

universe u v

/-! ## The category of finite-length endomorphisms -/

/-- A finite-length `R`-module equipped with an endomorphism. -/
structure FiniteLengthEndomorphism (R : Type u) [CommRing R] where
  carrier : ModuleCat.{v} R
  finite_length : IsFiniteLength R carrier
  endomorphism : carrier ⟶ carrier

namespace FiniteLengthEndomorphism

variable {R : Type u} [CommRing R]

/-- A morphism of pairs is a module map commuting with the specified endomorphisms. -/
structure Morph (X Y : FiniteLengthEndomorphism.{u, v} R) where
  hom : X.carrier ⟶ Y.carrier
  comm : X.endomorphism ≫ hom = hom ≫ Y.endomorphism

@[ext]
theorem Morph.ext {X Y : FiniteLengthEndomorphism.{u, v} R} {f g : Morph X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f with
  | mk fhom fcomm =>
    cases g with
    | mk ghom gcomm =>
      cases h
      rfl

instance : Category (FiniteLengthEndomorphism.{u, v} R) where
  Hom X Y := Morph X Y
  id X :=
    { hom := 𝟙 X.carrier
      comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm := by
        rw [← Category.assoc, f.comm, Category.assoc, g.comm]
        exact (Category.assoc _ _ _).symm }
  id_comp f := by
    apply Morph.ext
    simp
  comp_id f := by
    apply Morph.ext
    simp
  assoc f g h := by
    apply Morph.ext
    simp

/-- The pair category is abelian; kernels and cokernels are inherited from modules and
preserve finite length. -/
noncomputable instance : Abelian (FiniteLengthEndomorphism.{u, v} R) := by
  sorry

theorem isNoetherian_and_isArtinian (X : FiniteLengthEndomorphism.{u, v} R) :
    IsNoetherian R X.carrier ∧ IsArtinian R X.carrier :=
  isFiniteLength_iff_isNoetherian_isArtinian.mp X.finite_length

/-- Every finite-length pair is Noetherian and Artinian in the pair category. -/
theorem isNoetherianObject_and_isArtinianObject
    (X : FiniteLengthEndomorphism.{u, v} R) :
    IsNoetherianObject X ∧ IsArtinianObject X := by
  have underlying_injective {A B : FiniteLengthEndomorphism.{u, v} R}
      (f : A ⟶ B)
      (hf : ∀ {Z : FiniteLengthEndomorphism.{u, v} R} (g h : Z ⟶ A),
        g ≫ f = h ≫ f → g = h) : Function.Injective f.hom.hom := by
    intro x y hxy
    let K : Submodule R A.carrier := LinearMap.ker f.hom.hom
    have hcomm : ∀ z : A.carrier,
        f.hom.hom (A.endomorphism.hom z) =
          B.endomorphism.hom (f.hom.hom z) := by
      intro z
      have hz := congrArg (fun g : A.carrier ⟶ B.carrier => g z) f.comm
      simpa [ModuleCat.comp_apply] using hz
    have hstable : ∀ z : A.carrier, z ∈ K → A.endomorphism.hom z ∈ K := by
      intro z hz
      change f.hom.hom (A.endomorphism.hom z) = 0
      rw [hcomm, hz, map_zero]
    let phiK : Module.End R K :=
      A.endomorphism.hom.restrict hstable
    let A' : FiniteLengthEndomorphism.{u, v} R :=
      { carrier := ModuleCat.of R K
        finite_length := A.finite_length.of_injective K.injective_subtype
        endomorphism := ModuleCat.ofHom phiK }
    let i : A' ⟶ A :=
      { hom := ModuleCat.ofHom K.subtype
        comm := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          rfl }
    let z : A' ⟶ A :=
      { hom := ModuleCat.ofHom 0
        comm := by
          apply ModuleCat.hom_ext
          simp }
    have hcomp : i ≫ f = z ≫ f := by
      apply Morph.ext
      change i.hom ≫ f.hom = z.hom ≫ f.hom
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      change (i.hom ≫ f.hom).hom w = (z.hom ≫ f.hom).hom w
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
      change f.hom.hom (K.subtype w) = f.hom.hom 0
      rw [show K.subtype w = (w : A.carrier) by rfl, w.property, map_zero]
    have hiz : i = z := hf i z hcomp
    have hxy' : f.hom.hom (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    let w : K := ⟨x - y, hxy'⟩
    have hw := congrArg (fun k : A' ⟶ A => k.hom.hom w) hiz
    have hzero : x - y = 0 := by
      change x - y = 0 at hw
      exact hw
    exact sub_eq_zero.mp hzero
  let rangeMap : Subobject X → Submodule R X.carrier :=
    fun P => LinearMap.range P.arrow.hom.hom
  have hrange_mono {P Q : Subobject X} (hPQ : P ≤ Q) :
      rangeMap P ≤ rangeMap Q := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    refine ⟨(Subobject.ofLE P Q hPQ).hom.hom y, ?_⟩
    have hw := congrArg
      (fun k : (P : FiniteLengthEndomorphism.{u, v} R) ⟶ X => k.hom.hom y)
      (Subobject.ofLE_arrow hPQ)
    change Q.arrow.hom.hom ((Subobject.ofLE P Q hPQ).hom.hom y) =
      P.arrow.hom.hom y at hw
    exact hw
  have hpair_morphism {P Q : Subobject X}
      (hPQ : rangeMap P = rangeMap Q) :
      ∃ i : (P : FiniteLengthEndomorphism.{u, v} R) ⟶
          (Q : FiniteLengthEndomorphism.{u, v} R), i ≫ Q.arrow = P.arrow := by
    let pToRange :=
      P.arrow.hom.hom.codRestrict (rangeMap P)
        (fun y => LinearMap.mem_range_self P.arrow.hom.hom y)
    let qToRange :=
      Q.arrow.hom.hom.codRestrict (rangeMap Q)
        (fun y => LinearMap.mem_range_self Q.arrow.hom.hom y)
    have hp_inj : Function.Injective pToRange := by
      intro a b hab
      apply underlying_injective P.arrow
        (fun g h hgh => (cancel_mono P.arrow).mp hgh)
      exact congrArg Subtype.val hab
    have hq_inj : Function.Injective qToRange := by
      intro a b hab
      apply underlying_injective Q.arrow
        (fun g h hgh => (cancel_mono Q.arrow).mp hgh)
      exact congrArg Subtype.val hab
    have hp_surj : Function.Surjective pToRange := by
      intro y
      exact ⟨Classical.choose y.property,
        Subtype.ext (Classical.choose_spec y.property)⟩
    have hq_surj : Function.Surjective qToRange := by
      intro y
      exact ⟨Classical.choose y.property,
        Subtype.ext (Classical.choose_spec y.property)⟩
    let eP := LinearEquiv.ofBijective pToRange ⟨hp_inj, hp_surj⟩
    let eQ := LinearEquiv.ofBijective qToRange ⟨hq_inj, hq_surj⟩
    let e :=
      eP.trans ((LinearEquiv.ofEq (rangeMap P) (rangeMap Q) hPQ).trans eQ.symm)
    have he (y : (P : FiniteLengthEndomorphism.{u, v} R).carrier) :
        Q.arrow.hom.hom (e y) = P.arrow.hom.hom y := by
      change (eQ (eQ.symm
        ((LinearEquiv.ofEq (rangeMap P) (rangeMap Q) hPQ) (eP y)))).val =
        (eP y).val
      rw [eQ.apply_symm_apply]
      rfl
    have hPcomm (y : (P : FiniteLengthEndomorphism.{u, v} R).carrier) :
        P.arrow.hom.hom ((P : FiniteLengthEndomorphism.{u, v} R).endomorphism.hom y) =
          X.endomorphism.hom (P.arrow.hom.hom y) := by
      have hw := congrArg
        (fun k : (P : FiniteLengthEndomorphism.{u, v} R).carrier ⟶ X.carrier => k.hom y)
        P.arrow.comm
      simpa [ModuleCat.comp_apply] using hw
    have hQcomm (y : (Q : FiniteLengthEndomorphism.{u, v} R).carrier) :
        Q.arrow.hom.hom ((Q : FiniteLengthEndomorphism.{u, v} R).endomorphism.hom y) =
          X.endomorphism.hom (Q.arrow.hom.hom y) := by
      have hw := congrArg
        (fun k : (Q : FiniteLengthEndomorphism.{u, v} R).carrier ⟶ X.carrier => k.hom y)
        Q.arrow.comm
      simpa [ModuleCat.comp_apply] using hw
    let i : (P : FiniteLengthEndomorphism.{u, v} R) ⟶
        (Q : FiniteLengthEndomorphism.{u, v} R) :=
      { hom := ModuleCat.ofHom e.toLinearMap
        comm := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro y
          change e ((P : FiniteLengthEndomorphism.{u, v} R).endomorphism.hom y) =
            (Q : FiniteLengthEndomorphism.{u, v} R).endomorphism.hom (e y)
          apply underlying_injective Q.arrow
            (fun g h hgh => (cancel_mono Q.arrow).mp hgh)
          rw [he, hQcomm, he]
          exact hPcomm y }
    refine ⟨i, ?_⟩
    apply Morph.ext
    change i.hom ≫ Q.arrow.hom = P.arrow.hom
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rw [ModuleCat.comp_apply]
    change Q.arrow.hom.hom (e y) = P.arrow.hom.hom y
    exact he y
  have hrange_inj : Function.Injective rangeMap := by
    intro P Q hPQ
    obtain ⟨i, hi⟩ := hpair_morphism hPQ
    obtain ⟨j, hj⟩ := hpair_morphism hPQ.symm
    exact le_antisymm (Subobject.le_of_comm i hi) (Subobject.le_of_comm j hj)
  have hmodule := isNoetherian_and_isArtinian X
  constructor
  · rw [isNoetherianObject_iff_monotone_chain_condition]
    intro f
    let g : ℕ →o Submodule R X.carrier :=
      ⟨fun n => rangeMap (f n), fun n m hnm => hrange_mono (f.2 hnm)⟩
    obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr hmodule.1 g
    exact ⟨n, fun m hnm => hrange_inj (hn m hnm)⟩
  · rw [isArtinianObject_iff_antitone_chain_condition]
    intro f
    let g : ℕ →o (Submodule R X.carrier)ᵒᵈ :=
      ⟨fun n => rangeMap (f n), fun n m hnm => hrange_mono (f.2 hnm)⟩
    obtain ⟨n, hn⟩ := monotone_stabilizes_iff_artinian.mpr hmodule.2 g
    exact ⟨n, fun m hnm => hrange_inj (hn m hnm)⟩

end FiniteLengthEndomorphism

/-! ## Simple pairs and residue-field linear algebra -/

/-- An endomorphism has no nonzero proper invariant submodule. -/
def IsSimplePair {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (φ : Module.End R M) : Prop :=
  Nontrivial M ∧
    ∀ N : Submodule R M, Submodule.map φ N ≤ N → N = ⊥ ∨ N = ⊤

/-- The simple-object predicate on a bundled finite-length endomorphism. -/
def PairSimple {R : Type*} [CommRing R]
    (X : FiniteLengthEndomorphism R) : Prop :=
  IsSimplePair X.endomorphism.hom

/-- The maximal ideal kills the underlying module of a simple pair. -/
theorem IsSimplePair.annihilated_by_maximalIdeal
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    (φ : Module.End R M) (hφ : IsSimplePair φ) :
    Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R) := by
  have hNoeth : IsNoetherian R M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  let N : Submodule R M := IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)
  have hN : Submodule.map φ N ≤ N := by
    change Submodule.map φ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) ≤ _
    rw [Submodule.map_smul'']
    exact smul_mono_right _ le_top
  exact (hφ.2 N hN).elim
    (fun hNbot x a => by
      have hx : (a : R) • x ∈ N :=
        Submodule.smul_mem_smul a.property (Submodule.mem_top)
      have hxbot : (a : R) • x ∈ (⊥ : Submodule R M) := hNbot ▸ hx
      exact (Submodule.mem_bot R).mp hxbot)
    (fun hNtop => by
      have hIN : (⊤ : Submodule R M) ≤
          IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
        intro x hx
        have hxN : x ∈ N := hNtop.symm ▸ hx
        simpa [N] using hxN
      have hbot : (⊤ : Submodule R M) = ⊥ :=
        Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
          (IsLocalRing.maximalIdeal R) (⊤ : Submodule R M)
          (hNoeth.noetherian ⊤) hIN
          (IsLocalRing.maximalIdeal_le_jacobson ⊥)
      exact False.elim ((not_nontrivial_iff_subsingleton.mpr
        ⟨fun x y =>
          ((Submodule.mem_bot R).mp
            (hbot ▸ (Submodule.mem_top : x ∈ (⊤ : Submodule R M)))).trans
            ((Submodule.mem_bot R).mp
              (hbot ▸ (Submodule.mem_top : y ∈ (⊤ : Submodule R M)))).symm⟩) hφ.1))

/-- The residue-field vector space attached to a simple pair.  The explicit fields make the
source's finiteness and annihilation assertions available to later constructions. -/
structure SimplePairData (R M : Type*) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (φ : Module.End R M) where
  simple : IsSimplePair φ
  annihilated : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)
  residue_endomorphism :
    @Module.End (IsLocalRing.ResidueField R) M _ _ annihilated.module
  finite_dimensional :
    @Module.Finite (IsLocalRing.ResidueField R) M _ _ annihilated.module
  residue_endomorphism_apply : ∀ x, residue_endomorphism.toFun x = φ x

theorem exists_simplePairData
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    (φ : Module.End R M) (hφ : IsSimplePair φ) :
    Nonempty (SimplePairData R M φ) := by
  have hNoeth : IsNoetherian R M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  let hAnn : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R) :=
    IsSimplePair.annihilated_by_maximalIdeal hM φ hφ
  let hFinite : Module.Finite R M := ⟨hNoeth.noetherian ⊤⟩
  let _ : Module.Finite R M := hFinite
  let _ : Module (R ⧸ IsLocalRing.maximalIdeal R) M := hAnn.module
  let ψ : @Module.End (R ⧸ IsLocalRing.maximalIdeal R) M _ _ hAnn.module :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := by
        intro a x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        simpa only [RingHom.id_apply, hAnn.mk_smul] using φ.map_smul r x }
  have hFiniteK :
      @Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) M _ _ hAnn.module :=
    Module.Finite.of_restrictScalars_finite R _ _
  refine ⟨{
    simple := hφ
    annihilated := hAnn
    residue_endomorphism := ψ
    finite_dimensional := hFiniteK
    residue_endomorphism_apply := ?_
  }⟩
  intro x
  rfl

noncomputable def simplePairData
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    (φ : Module.End R M) (hφ : IsSimplePair φ) :
    SimplePairData R M φ :=
  Classical.choice (exists_simplePairData hM φ hφ)

/-- The endomorphism induced on a residue-field vector space. -/
noncomputable def simpleDeterminant
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {φ : Module.End R M}
    (D : SimplePairData R M φ) : IsLocalRing.ResidueField R :=
  letI : Module (IsLocalRing.ResidueField R) M := D.annihilated.module
  letI : Module.Finite (IsLocalRing.ResidueField R) M := D.finite_dimensional
  D.residue_endomorphism.det

noncomputable def simpleTrace
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {φ : Module.End R M}
    (D : SimplePairData R M φ) : IsLocalRing.ResidueField R :=
  letI : Module (IsLocalRing.ResidueField R) M := D.annihilated.module
  letI : Module.Finite (IsLocalRing.ResidueField R) M := D.finite_dimensional
  LinearMap.trace (IsLocalRing.ResidueField R) M D.residue_endomorphism

noncomputable def simpleCharacteristicPolynomial
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {φ : Module.End R M}
    (D : SimplePairData R M φ) :
    Polynomial (IsLocalRing.ResidueField R) :=
  letI : Module (IsLocalRing.ResidueField R) M := D.annihilated.module
  letI : Module.Finite (IsLocalRing.ResidueField R) M := D.finite_dimensional
  letI : Module.Free (IsLocalRing.ResidueField R) M :=
    Module.Free.of_divisionRing (IsLocalRing.ResidueField R) M
  D.residue_endomorphism.charpoly

/-! ## Stable filtrations and the three invariants -/

/-- A submodule which is stable under a specified endomorphism. -/
structure StableSubmodule {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (φ : Module.End R M) where
  carrier : Submodule R M
  stable : Submodule.map φ carrier ≤ carrier

/-- A finite strictly increasing filtration by submodules stable under `φ`. -/
abbrev StableSubmoduleSeries {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (φ : Module.End R M) : Type _ :=
  RelSeries {(P, Q) : StableSubmodule φ × StableSubmodule φ | P.carrier < Q.carrier}

/-- The quotient module belonging to a step of a stable filtration. -/
abbrev factorModule {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {φ : Module.End R M} (s : StableSubmoduleSeries φ) (i : Fin s.length) : Type _ :=
  (s (Fin.succ i)).carrier ⧸
    Submodule.comap (s (Fin.succ i)).carrier.subtype (s (Fin.castSucc i)).carrier

/-- Restrict an endomorphism to an invariant submodule. -/
def restrictToStableSubmodule
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (φ : Module.End R M) (N : Submodule R M)
    (hN : Submodule.map φ N ≤ N) : Module.End R N :=
  φ.restrict (fun x hx => hN ⟨x, hx, rfl⟩)

/-- The endomorphism induced on a composition factor. -/
def factorEnd
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {φ : Module.End R M} (s : StableSubmoduleSeries φ) (i : Fin s.length) :
    Module.End R (factorModule s i) := by
  let U := (s (Fin.succ i)).carrier
  let L : Submodule R U :=
    Submodule.comap U.subtype (s (Fin.castSucc i)).carrier
  let fU : Module.End R U :=
    restrictToStableSubmodule φ U (s (Fin.succ i)).stable
  let hL : L ≤ L.comap fU := by
    intro x hx
    change φ (x : M) ∈ (s (Fin.castSucc i)).carrier
    exact (s (Fin.castSucc i)).stable ⟨x, hx, rfl⟩
  exact L.mapQ L fU hL

/-- A stable composition series together with the simple pair carried by every factor. -/
structure StableCompositionSeries
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) where
  series : StableSubmoduleSeries X.endomorphism.hom
  head_eq_bot : series.head.carrier = ⊥
  last_eq_top : series.last.carrier = ⊤
  simple_factor :
    ∀ i, SimplePairData R (factorModule series i)
      (factorEnd series i)

theorem exists_stableCompositionSeries
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) :
    Nonempty (StableCompositionSeries X) := by
  sorry

noncomputable def stableCompositionSeries
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) : StableCompositionSeries X :=
  Classical.choice (exists_stableCompositionSeries X)

noncomputable def determinant
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) : IsLocalRing.ResidueField R :=
  let s := stableCompositionSeries X
  ∏ i, simpleDeterminant (s.simple_factor i)

noncomputable def trace
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) : IsLocalRing.ResidueField R :=
  let s := stableCompositionSeries X
  ∑ i, simpleTrace (s.simple_factor i)

noncomputable def characteristicPolynomial
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) :
    Polynomial (IsLocalRing.ResidueField R) :=
  let s := stableCompositionSeries X
  ∏ i, simpleCharacteristicPolynomial (s.simple_factor i)

/-! ## Lengths used in the base-change statements -/

noncomputable def finiteLengthNat
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (_hM : IsFiniteLength R M) : ℕ :=
  (Module.length R M).toNat

/-- The finite residue-field dimension of a simple factor. -/
noncomputable def residueFinrank
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {φ : Module.End R M}
    (D : SimplePairData R M φ) : ℕ :=
  letI : Module (IsLocalRing.ResidueField R) M := D.annihilated.module
  Module.finrank (IsLocalRing.ResidueField R) M

/-- For a simple pair, the residue-field dimension is its `R`-length. -/
theorem simplePair_residueFinrank_eq_length
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    {φ : Module.End R M} (D : SimplePairData R M φ) :
    residueFinrank D = finiteLengthNat R M hM := by
  sorry

/-! The following three interfaces record the Jordan--Hölder independence of the definitions. -/

theorem determinant_eq_stableCompositionSeries_product
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) (s : StableCompositionSeries X) :
    determinant X =
      ∏ i : Fin s.series.length, simpleDeterminant (s.simple_factor i) := by
  sorry

theorem trace_eq_stableCompositionSeries_sum
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) (s : StableCompositionSeries X) :
    trace X =
      ∑ i : Fin s.series.length, simpleTrace (s.simple_factor i) := by
  sorry

theorem characteristicPolynomial_eq_stableCompositionSeries_product
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) (s : StableCompositionSeries X) :
    characteristicPolynomial X =
      ∏ i : Fin s.series.length, simpleCharacteristicPolynomial (s.simple_factor i) := by
  sorry

/-- Package a module endomorphism as a finite-length pair. -/
def ofModule
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (φ : Module.End R M) :
    FiniteLengthEndomorphism R :=
  { carrier := ModuleCat.of R M
    finite_length := hM
    endomorphism := ModuleCat.ofHom φ }

noncomputable def determinantOf
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    (φ : Module.End R M) : IsLocalRing.ResidueField R :=
  determinant (ofModule hM φ)

noncomputable def traceOf
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    (φ : Module.End R M) : IsLocalRing.ResidueField R :=
  trace (ofModule hM φ)

noncomputable def characteristicPolynomialOf
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    (φ : Module.End R M) : Polynomial (IsLocalRing.ResidueField R) :=
  characteristicPolynomial (ofModule hM φ)

end
