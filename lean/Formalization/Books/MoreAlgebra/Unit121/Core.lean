/-
# More on Algebra, Chapter 121: Determinants of endomorphisms of finite length modules
-/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Noetherian
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
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
  let φ := X.endomorphism.hom
  let _ : IsNoetherian R X.carrier :=
    (FiniteLengthEndomorphism.isNoetherian_and_isArtinian X).1
  let _ : IsArtinian R X.carrier :=
    (FiniteLengthEndomorphism.isNoetherian_and_isArtinian X).2
  let _ : PartialOrder (StableSubmodule φ) :=
    PartialOrder.lift StableSubmodule.carrier (by
      intro P Q h
      cases P
      cases Q
      cases h
      rfl)
  let _ : OrderBot (StableSubmodule φ) :=
    { bot := { carrier := (⊥ : Submodule R X.carrier), stable := by simp }
      bot_le := by intro P; exact (show (⊥ : Submodule R X.carrier) ≤ P.carrier from bot_le) }
  let _ : OrderTop (StableSubmodule φ) :=
    { top := { carrier := (⊤ : Submodule R X.carrier), stable := by simp }
      le_top := by intro P; exact (show P.carrier ≤ (⊤ : Submodule R X.carrier) from le_top) }
  let e : StableSubmodule φ ↪o Submodule R X.carrier :=
    OrderEmbedding.ofMapLEIff StableSubmodule.carrier (fun _ _ => Iff.rfl)
  let _ : WellFoundedLT (StableSubmodule φ) := e.wellFoundedLT
  let _ : WellFoundedGT (StableSubmodule φ) := e.dual.wellFoundedLT
  obtain ⟨f, hf, n, hn, hstep⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (StableSubmodule φ)
  let s : StableSubmoduleSeries φ :=
    { length := n
      toFun := fun i => f i
      step := fun i => (hstep i i.2).1 }
  have hs_head : s.head.carrier = (⊥ : Submodule R X.carrier) := by
    change (f 0).carrier = (⊥ : Submodule R X.carrier)
    exact congrArg StableSubmodule.carrier hf.eq_bot
  have hs_last : s.last.carrier = (⊤ : Submodule R X.carrier) := by
    change (f n).carrier = (⊤ : Submodule R X.carrier)
    exact congrArg StableSubmodule.carrier hn.eq_top
  have hsimple (i : Fin s.length) :
      IsSimplePair (factorEnd s i) := by
    let P := (s (Fin.castSucc i)).carrier
    let U := (s (Fin.succ i)).carrier
    let L : Submodule R U := Submodule.comap U.subtype P
    have hPU : P ≤ U := le_of_lt (by simpa [P, U] using s.step i)
    have hPUs : P < U := by
      have hi := (hstep i (by simp [s])).1
      change P < U at hi
      exact hi
    have hL_ne : L ≠ ⊤ := by
      intro hL
      apply hPUs.2
      intro x hx
      let y : U := ⟨x, hx⟩
      have hyL : y ∈ L := by rw [hL]; exact Submodule.mem_top
      exact hyL
    obtain ⟨y, hy⟩ : ∃ y : U, y ∉ L := by
      by_contra h
      apply hL_ne
      apply top_unique
      intro y hy'
      by_contra hyL
      exact h ⟨y, hyL⟩
    let _ : Nontrivial (U ⧸ L) :=
      ⟨⟨L.mkQ y, 0, by
        intro hzero
        exact hy ((Submodule.Quotient.mk_eq_zero _).mp hzero)⟩⟩
    have hstable (N : Submodule R (U ⧸ L))
        (hN : Submodule.map (factorEnd s i) N ≤ N) :
        ∀ z : U, z ∈ Submodule.comap (L.mkQ) N →
          restrictToStableSubmodule φ U (s (Fin.succ i)).stable z ∈
            Submodule.comap (L.mkQ) N := by
      intro z hz
      change L.mkQ (restrictToStableSubmodule φ U (s (Fin.succ i)).stable z) ∈ N
      apply hN
      exact ⟨L.mkQ z, hz, by
        change factorEnd s i (L.mkQ z) = L.mkQ
          (restrictToStableSubmodule φ U (s (Fin.succ i)).stable z)
        rfl⟩
    unfold IsSimplePair
    refine ⟨inferInstance, ?_⟩
    intro N hN
    let WU : Submodule R U := Submodule.comap (L.mkQ) N
    let W : Submodule R X.carrier := Submodule.map U.subtype WU
    have hWstable : Submodule.map φ W ≤ W := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hx
      obtain ⟨z, hz, hyz⟩ := hy
      refine ⟨restrictToStableSubmodule φ U (s (Fin.succ i)).stable z,
        hstable N hN z hz, ?_⟩
      calc
        U.subtype (restrictToStableSubmodule φ U (s (Fin.succ i)).stable z) =
            φ (U.subtype z) := by rfl
        _ = φ y := by rw [hyz]
        _ = x := hxy
    let W' : StableSubmodule φ := ⟨W, hWstable⟩
    have hPW : P ≤ W := by
      intro x hx
      let z : U := ⟨x, hPU hx⟩
      refine ⟨z, ?_, rfl⟩
      change L.mkQ z ∈ N
      have hzL : z ∈ L := by
        change (z : X.carrier) ∈ P
        exact hx
      rw [show L.mkQ z = 0 by
        exact (Submodule.Quotient.mk_eq_zero _).mpr hzL]
      exact N.zero_mem
    have hWU : W ≤ U := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := hx
      exact z.property
    have hcases := (covBy_iff_lt_and_eq_or_eq.mp (hstep i i.2)).2 W'
      hPW hWU
    rcases hcases with hWP | hWUQ
    · have hpre : WU = L := by
        ext z
        constructor
        · intro hz
          have hzW : (z : X.carrier) ∈ W := ⟨z, hz, rfl⟩
          have hcar : W = P := congrArg StableSubmodule.carrier hWP
          rw [hcar] at hzW
          exact hzW
        · intro hz
          change L.mkQ z ∈ N
          rw [show L.mkQ z = 0 by
            apply (Submodule.Quotient.mk_eq_zero _).mpr
            exact hz]
          exact N.zero_mem
      left
      apply eq_bot_iff.mpr
      intro q hq
      obtain ⟨z, rfl⟩ := L.mkQ_surjective q
      have hz : z ∈ WU := by
        change L.mkQ z ∈ N
        exact hq
      rw [hpre] at hz
      have : z ∈ L := hz
      rw [Submodule.mem_bot]
      exact (Submodule.Quotient.mk_eq_zero _).mpr this
    · have hpre : WU = ⊤ := by
        apply top_unique
        intro z hz
        have hzW : (z : X.carrier) ∈ W := by
          have hcar : W = U := congrArg StableSubmodule.carrier hWUQ
          rw [hcar]
          exact z.property
        obtain ⟨z', hz', hzz'⟩ := hzW
        have hz_eq : z' = z := Subtype.ext hzz'
        exact hz_eq ▸ hz'
      right
      apply top_unique
      intro q hq
      obtain ⟨z, rfl⟩ := L.mkQ_surjective q
      change L.mkQ z ∈ N
      change z ∈ WU
      exact hpre ▸ Submodule.mem_top
  exact ⟨{
    series := s
    head_eq_bot := hs_head
    last_eq_top := hs_last
    simple_factor := fun i =>
      simplePairData
        ((X.finite_length.of_injective
          (Submodule.injective_subtype _)).of_surjective
            (Submodule.mkQ_surjective _))
        (factorEnd s i)
        (hsimple i)
  }⟩

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
  have hNoeth : IsNoetherian R M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  let _ : Module.Finite R M := ⟨hNoeth.noetherian ⊤⟩
  let _ : Module (R ⧸ IsLocalRing.maximalIdeal R) M := D.annihilated.module
  let _ : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) M :=
    Module.Finite.of_restrictScalars_finite R _ _
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  change Module.finrank (R ⧸ IsLocalRing.maximalIdeal R) M =
    (Module.length R M).toNat
  have hlen : Module.length R M =
      Module.length (R ⧸ IsLocalRing.maximalIdeal R) M :=
    Module.length_eq_of_surjective (R := R ⧸ IsLocalRing.maximalIdeal R)
      (S := R) (M := M) (IsLocalRing.maximalIdeal R).mkQ_surjective
  have hlenQ : Module.length (R ⧸ IsLocalRing.maximalIdeal R) M =
      (Module.finrank (R ⧸ IsLocalRing.maximalIdeal R) M : ℕ∞) :=
    Module.length_eq_finrank _ _
  rw [hlen, hlenQ]
  simp

private theorem simplePair_invariant
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    {φ : Module.End R M} {ψ : Module.End R N}
    (D : SimplePairData R M φ) (E : SimplePairData R N ψ)
    (e : M ≃ₗ[R] N)
    (he : ∀ x, e (φ x) = ψ (e x)) :
    simpleDeterminant D = simpleDeterminant E ∧
      simpleTrace D = simpleTrace E := by
  let _ : Module (IsLocalRing.ResidueField R) M := D.annihilated.module
  let _ : Module (IsLocalRing.ResidueField R) N := E.annihilated.module
  let _ : Module.Finite (IsLocalRing.ResidueField R) M := D.finite_dimensional
  let _ : Module.Finite (IsLocalRing.ResidueField R) N := E.finite_dimensional
  let eK : M ≃ₗ[IsLocalRing.ResidueField R] N :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro c x
        obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (R := R) c
        rw [← hr]
        change e (IsLocalRing.residue R r • x) =
          IsLocalRing.residue R r • e x
        have hM : IsLocalRing.residue R r • x = r • x :=
          D.annihilated.mk_smul r x
        have hN : IsLocalRing.residue R r • e x = r • e x :=
          E.annihilated.mk_smul r (e x)
        rw [hM, hN]
        exact e.map_smul r x }
  have heK :
      (eK : M →ₗ[IsLocalRing.ResidueField R] N) ∘ₗ
          (D.residue_endomorphism ∘ₗ
            (eK.symm : N →ₗ[IsLocalRing.ResidueField R] M)) =
        E.residue_endomorphism := by
    apply LinearMap.ext
    intro x
    change eK (D.residue_endomorphism.toFun (eK.symm x)) =
      E.residue_endomorphism.toFun x
    rw [D.residue_endomorphism_apply, E.residue_endomorphism_apply]
    simpa [eK] using he (e.symm x)
  have hdet := LinearMap.det_conj D.residue_endomorphism eK
  rw [heK] at hdet
  have heK' : eK.conj D.residue_endomorphism =
      E.residue_endomorphism := by
    apply LinearMap.ext
    intro x
    change eK (D.residue_endomorphism.toFun (eK.symm x)) =
      E.residue_endomorphism.toFun x
    rw [D.residue_endomorphism_apply, E.residue_endomorphism_apply]
    simpa [eK] using he (e.symm x)
  have htrace := LinearMap.trace_conj' D.residue_endomorphism eK
  rw [heK'] at htrace
  constructor
  · exact hdet.symm
  · exact htrace.symm

private theorem simplePair_characteristicPolynomial_invariant
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    {φ : Module.End R M} {ψ : Module.End R N}
    (D : SimplePairData R M φ) (E : SimplePairData R N ψ)
    (e : M ≃ₗ[R] N)
    (he : ∀ x, e (φ x) = ψ (e x)) :
    simpleCharacteristicPolynomial D = simpleCharacteristicPolynomial E := by
  let _ : Module (IsLocalRing.ResidueField R) M := D.annihilated.module
  let _ : Module (IsLocalRing.ResidueField R) N := E.annihilated.module
  let _ : Module.Finite (IsLocalRing.ResidueField R) M := D.finite_dimensional
  let _ : Module.Finite (IsLocalRing.ResidueField R) N := E.finite_dimensional
  let eK : M ≃ₗ[IsLocalRing.ResidueField R] N :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro c x
        obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (R := R) c
        rw [← hr]
        change e (IsLocalRing.residue R r • x) =
          IsLocalRing.residue R r • e x
        have hM : IsLocalRing.residue R r • x = r • x :=
          D.annihilated.mk_smul r x
        have hN : IsLocalRing.residue R r • e x = r • e x :=
          E.annihilated.mk_smul r (e x)
        rw [hM, hN]
        exact e.map_smul r x }
  have heK :
      eK.conj D.residue_endomorphism = E.residue_endomorphism := by
    apply LinearMap.ext
    intro x
    change eK (D.residue_endomorphism.toFun (eK.symm x)) =
      E.residue_endomorphism.toFun x
    rw [D.residue_endomorphism_apply, E.residue_endomorphism_apply]
    simpa [eK] using he (e.symm x)
  have hchar := LinearEquiv.charpoly_conj eK D.residue_endomorphism
  rw [heK] at hchar
  exact hchar.symm

private theorem stableCompositionSeries_invariant
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R)
    (s t : StableCompositionSeries X) :
    (∏ i, simpleDeterminant (s.simple_factor i)) =
        ∏ i, simpleDeterminant (t.simple_factor i) ∧
      (∑ i, simpleTrace (s.simple_factor i)) =
        ∑ i, simpleTrace (t.simple_factor i) := by
  let φ : Module.End R X.carrier := X.endomorphism.hom
  let _ : PartialOrder (StableSubmodule φ) :=
    PartialOrder.lift StableSubmodule.carrier (by
      intro P Q h
      cases P
      cases Q
      cases h
      rfl)
  let supInst : SemilatticeSup (StableSubmodule φ) :=
    { __ := (inferInstance : PartialOrder (StableSubmodule φ))
      sup := fun P Q =>
        { carrier := P.carrier ⊔ Q.carrier
          stable := by
            rw [Submodule.map_sup]
            exact sup_le (P.stable.trans le_sup_left) (Q.stable.trans le_sup_right) }
      le_sup_left := by
        intro P Q
        change P.carrier ≤ P.carrier ⊔ Q.carrier
        exact le_sup_left
      le_sup_right := by
        intro P Q
        change Q.carrier ≤ P.carrier ⊔ Q.carrier
        exact le_sup_right
      sup_le := by
        intro P Q S hP hQ
        change P.carrier ⊔ Q.carrier ≤ S.carrier
        exact sup_le hP hQ }
  let infInst : SemilatticeInf (StableSubmodule φ) :=
    { __ := (inferInstance : PartialOrder (StableSubmodule φ))
      inf := fun P Q =>
        { carrier := P.carrier ⊓ Q.carrier
          stable := by
            exact le_inf
              ((Submodule.map_mono inf_le_left).trans P.stable)
              ((Submodule.map_mono inf_le_right).trans Q.stable) }
      le_inf := by
        intro S P Q hP hQ
        change S.carrier ≤ P.carrier ⊓ Q.carrier
        exact le_inf hP hQ
      inf_le_left := by
        intro P Q
        change P.carrier ⊓ Q.carrier ≤ P.carrier
        exact inf_le_left
      inf_le_right := by
        intro P Q
        change P.carrier ⊓ Q.carrier ≤ Q.carrier
        exact inf_le_right }
  let _ : Lattice (StableSubmodule φ) := { __ := supInst, __ := infInst }
  let _ : IsModularLattice (StableSubmodule φ) :=
    ⟨by
      intro x y z h
      change (x.carrier ⊔ y.carrier) ⊓ z.carrier ≤
        x.carrier ⊔ (y.carrier ⊓ z.carrier)
      exact IsModularLattice.sup_inf_le_assoc_of_le y.carrier
        (show x.carrier ≤ z.carrier from h)⟩
  let intervalFactor (P Q : StableSubmodule φ) : Type v :=
    Q.carrier ⧸ Submodule.comap Q.carrier.subtype P.carrier
  let intervalEnd (P Q : StableSubmodule φ) :
      Module.End R (intervalFactor P Q) := by
    let L : Submodule R Q.carrier :=
      Submodule.comap Q.carrier.subtype P.carrier
    let fQ : Module.End R Q.carrier :=
      restrictToStableSubmodule φ Q.carrier Q.stable
    let hL : L ≤ L.comap fQ := by
      intro z hz
      change φ (z : X.carrier) ∈ P.carrier
      exact P.stable ⟨z, hz, rfl⟩
    exact L.mapQ L fQ hL
  let E : (StableSubmodule φ × StableSubmodule φ) →
      (StableSubmodule φ × StableSubmodule φ) → Prop :=
    fun a b =>
      ∃ e : intervalFactor a.1 a.2 ≃ₗ[R] intervalFactor b.1 b.2,
        ∀ x, e (intervalEnd a.1 a.2 x) =
          intervalEnd b.1 b.2 (e x)
  have hE_refl : ∀ {a}, E a a := by
    intro a
    refine ⟨LinearEquiv.refl R _, ?_⟩
    intro x
    rfl
  have hE_symm : ∀ {a b}, E a b → E b a := by
    rintro a b ⟨e, he⟩
    refine ⟨e.symm, ?_⟩
    intro x
    calc
      e.symm (intervalEnd b.1 b.2 x) =
          e.symm (intervalEnd b.1 b.2 (e (e.symm x))) := by
            rw [e.apply_symm_apply]
      _ = e.symm (e (intervalEnd a.1 a.2 (e.symm x))) :=
        congrArg e.symm (he (e.symm x)).symm
      _ = intervalEnd a.1 a.2 (e.symm x) := e.symm_apply_apply _
  have hE_trans : ∀ {a b c}, E a b → E b c → E a c := by
    rintro a b c ⟨e, he⟩ ⟨f, hf⟩
    refine ⟨e.trans f, ?_⟩
    intro x
    change f (e (intervalEnd a.1 a.2 x)) =
      intervalEnd c.1 c.2 (f (e x))
    calc
      f (e (intervalEnd a.1 a.2 x)) =
          f (intervalEnd b.1 b.2 (e x)) := by rw [he]
      _ = intervalEnd c.1 c.2 (f (e x)) := hf (e x)
  have hE_diamond : ∀ {x y : StableSubmodule φ},
      x ⋖ x ⊔ y → E (x, x ⊔ y) (x ⊓ y, y) := by
    intro x y hxy
    let U : Submodule R X.carrier := (x ⊔ y).carrier
    let I : Submodule R X.carrier := (x ⊓ y).carrier
    let K : Submodule R U := Submodule.comap U.subtype x.carrier
    let L : Submodule R y.carrier := Submodule.comap y.carrier.subtype I
    let inc : y.carrier →ₗ[R] U :=
      { toFun := fun z => ⟨z, by
          change (z : X.carrier) ∈ (x ⊔ y).carrier
          exact Submodule.mem_sup_right z.property⟩
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    have hL : L ≤ K.comap inc := by
      intro z hz
      change (z : X.carrier) ∈ x.carrier
      change (z : X.carrier) ∈ I at hz
      exact (show I ≤ x.carrier by
        change x.carrier ⊓ y.carrier ≤ x.carrier
        exact inf_le_left) hz
    let qMap : intervalFactor (x ⊓ y) y →ₗ[R]
        intervalFactor x (x ⊔ y) := by
      change (y.carrier ⧸ L) →ₗ[R] (U ⧸ K)
      exact L.mapQ K inc hL
    have qMap_injective : Function.Injective qMap := by
      intro a b hab
      obtain ⟨a0, ha0⟩ := L.mkQ_surjective a
      obtain ⟨b0, hb0⟩ := L.mkQ_surjective b
      rw [← ha0, ← hb0] at hab ⊢
      change (L.mapQ K inc hL) (Submodule.Quotient.mk a0) =
        (L.mapQ K inc hL) (Submodule.Quotient.mk b0) at hab
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply] at hab
      apply (Submodule.Quotient.eq L).2
      have hab' : ((inc a0 : U) : X.carrier) - (inc b0 : U) ∈ x.carrier := by
        have := (Submodule.Quotient.eq K).1 hab
        exact this
      change (a0 : X.carrier) - b0 ∈ I
      exact ⟨hab', sub_mem a0.property b0.property⟩
    have qMap_surjective : Function.Surjective qMap := by
      intro z
      obtain ⟨z, rfl⟩ := K.mkQ_surjective z
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp z.property
      let b' : y.carrier := ⟨b, hb⟩
      refine ⟨Submodule.Quotient.mk b', ?_⟩
      change (L.mapQ K inc hL) (Submodule.Quotient.mk b') = K.mkQ z
      rw [Submodule.mapQ_apply]
      apply (Submodule.Quotient.eq K).2
      change (inc b' : X.carrier) - z ∈ x.carrier
      rw [show (inc b' : X.carrier) = b by rfl, ← hab]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (sub_mem x.carrier.zero_mem ha)
    let e0 : intervalFactor (x ⊓ y) y ≃ₗ[R]
        intervalFactor x (x ⊔ y) :=
      LinearEquiv.ofBijective qMap ⟨qMap_injective, qMap_surjective⟩
    have qMap_comm : ∀ w : intervalFactor (x ⊓ y) y,
        qMap (intervalEnd (x ⊓ y) y w) =
          intervalEnd x (x ⊔ y) (qMap w) := by
      intro w
      refine Submodule.Quotient.induction_on _ w ?_
      intro w
      rfl
    refine ⟨e0.symm, ?_⟩
    intro z
    apply qMap_injective
    change e0 (e0.symm (intervalEnd x (x ⊔ y) z)) =
      qMap (intervalEnd (x ⊓ y) y (e0.symm z))
    rw [e0.apply_symm_apply, qMap_comm]
    have he0q : qMap (e0.symm z) = z := by
      change e0 (e0.symm z) = z
      exact e0.apply_symm_apply z
    rw [he0q]
  have stable_ext {P Q : StableSubmodule φ} (h : P.carrier = Q.carrier) : P = Q := by
    cases P
    cases Q
    cases h
    rfl
  have stable_cov (r : StableCompositionSeries X) (i : Fin r.series.length) :
      r.series (Fin.castSucc i) ⋖ r.series (Fin.succ i) := by
    apply covBy_iff_lt_and_eq_or_eq.mpr
    refine ⟨?_, ?_⟩
    · change (r.series (Fin.castSucc i)).carrier <
        (r.series (Fin.succ i)).carrier
      exact r.series.step i
    · intro W hP hU
      let P := (r.series (Fin.castSucc i)).carrier
      let U := (r.series (Fin.succ i)).carrier
      let L : Submodule R U := Submodule.comap U.subtype P
      let WU : Submodule R U := Submodule.comap U.subtype W.carrier
      let fU : Module.End R U :=
        restrictToStableSubmodule φ U (r.series (Fin.succ i)).stable
      let N : Submodule R (U ⧸ L) := WU.map L.mkQ
      have hWUstable : ∀ z : U, z ∈ WU → fU z ∈ WU := by
        intro z hz
        change φ (z : X.carrier) ∈ W.carrier
        apply W.stable
        exact ⟨z, hz, rfl⟩
      have hN : Submodule.map (factorEnd r.series i) N ≤ N := by
        intro q hq
        obtain ⟨q, hq, rfl⟩ := hq
        obtain ⟨z, hz, rfl⟩ := hq
        change L.mkQ (fU z) ∈ N
        exact ⟨fU z, hWUstable z hz, rfl⟩
      rcases (r.simple_factor i).simple.2 N hN with hNbot | hNtop
      · have hWU : WU = L := by
          apply le_antisymm
          · intro z hz
            have hzq : L.mkQ z ∈ N := ⟨z, hz, rfl⟩
            rw [hNbot] at hzq
            exact (Submodule.Quotient.mk_eq_zero _).mp hzq
          · intro z hz
            change (z : X.carrier) ∈ W.carrier
            exact hP hz
        left
        apply stable_ext
        apply le_antisymm
        · intro x hx
          let z : U := ⟨x, hU hx⟩
          have hz : z ∈ WU := by
            change (z : X.carrier) ∈ W.carrier
            exact hx
          rw [hWU] at hz
          exact hz
        · intro x hx
          exact hP hx
      · have hmap : WU.map L.mkQ = ⊤ := by
          change WU.map L.mkQ = ⊤ at hNtop
          exact hNtop
        have htop : L ⊔ WU = ⊤ :=
          (Submodule.map_mkQ_eq_top L WU).mp hmap
        have hWU : WU = ⊤ := by
          apply top_unique
          rw [← htop]
          exact sup_le (fun z hz => by
            change (z : X.carrier) ∈ W.carrier
            exact hP hz) le_rfl
        right
        apply stable_ext
        apply le_antisymm
        · intro x hx
          exact hU hx
        · intro x hx
          let z : U := ⟨x, hx⟩
          have hz : z ∈ WU := by rw [hWU]; exact Submodule.mem_top
          exact hz
  let toCompositionSeries (r : StableCompositionSeries X) :
      CompositionSeries (StableSubmodule φ) :=
    { length := r.series.length
      toFun := r.series
      step := fun i => stable_cov r i }
  have hhead : (toCompositionSeries s).head = (toCompositionSeries t).head := by
    apply stable_ext
    change (s.series.head).carrier = (t.series.head).carrier
    rw [s.head_eq_bot, t.head_eq_bot]
  have hlast : (toCompositionSeries s).last = (toCompositionSeries t).last := by
    apply stable_ext
    change (s.series.last).carrier = (t.series.last).carrier
    rw [s.last_eq_top, t.last_eq_top]
  have hJH : CompositionSeries.Equivalent (toCompositionSeries s) (toCompositionSeries t) :=
    CompositionSeries.jordan_holder (toCompositionSeries s) (toCompositionSeries t)
      hhead hlast
  have hterm_det : ∀ i : Fin s.series.length,
      simpleDeterminant (s.simple_factor i) =
        simpleDeterminant (t.simple_factor (hJH.choose i)) := by
    intro i
    have hIso := JordanHolderLattice.Iso.rel E hE_refl hE_symm hE_trans
      hE_diamond (hJH.choose_spec i)
    rcases hIso with ⟨e, he⟩
    have hcomm : ∀ x, e (factorEnd s.series i x) =
        factorEnd t.series (hJH.choose i) (e x) := by
      intro x
      exact he x
    exact (simplePair_invariant (s.simple_factor i)
      (t.simple_factor (hJH.choose i)) e hcomm).1
  have hterm_trace : ∀ i : Fin s.series.length,
      simpleTrace (s.simple_factor i) =
        simpleTrace (t.simple_factor (hJH.choose i)) := by
    intro i
    have hIso := JordanHolderLattice.Iso.rel E hE_refl hE_symm hE_trans
      hE_diamond (hJH.choose_spec i)
    rcases hIso with ⟨e, he⟩
    have hcomm : ∀ x, e (factorEnd s.series i x) =
        factorEnd t.series (hJH.choose i) (e x) := by
      intro x
      exact he x
    exact (simplePair_invariant (s.simple_factor i)
      (t.simple_factor (hJH.choose i)) e hcomm).2
  refine ⟨?_, ?_⟩
  · exact Fintype.prod_equiv hJH.choose
      (fun i => simpleDeterminant (s.simple_factor i))
      (fun i => simpleDeterminant (t.simple_factor i)) hterm_det
  · exact Fintype.sum_equiv hJH.choose
      (fun i => simpleTrace (s.simple_factor i))
      (fun i => simpleTrace (t.simple_factor i)) hterm_trace

private theorem stableCompositionSeries_characteristicPolynomial_invariant
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R)
    (s t : StableCompositionSeries X) :
    (∏ i, simpleCharacteristicPolynomial (s.simple_factor i)) =
        ∏ i, simpleCharacteristicPolynomial (t.simple_factor i) := by
  let φ : Module.End R X.carrier := X.endomorphism.hom
  let _ : PartialOrder (StableSubmodule φ) :=
    PartialOrder.lift StableSubmodule.carrier (by
      intro P Q h
      cases P
      cases Q
      cases h
      rfl)
  let supInst : SemilatticeSup (StableSubmodule φ) :=
    { __ := (inferInstance : PartialOrder (StableSubmodule φ))
      sup := fun P Q =>
        { carrier := P.carrier ⊔ Q.carrier
          stable := by
            rw [Submodule.map_sup]
            exact sup_le (P.stable.trans le_sup_left) (Q.stable.trans le_sup_right) }
      le_sup_left := by
        intro P Q
        change P.carrier ≤ P.carrier ⊔ Q.carrier
        exact le_sup_left
      le_sup_right := by
        intro P Q
        change Q.carrier ≤ P.carrier ⊔ Q.carrier
        exact le_sup_right
      sup_le := by
        intro P Q S hP hQ
        change P.carrier ⊔ Q.carrier ≤ S.carrier
        exact sup_le hP hQ }
  let infInst : SemilatticeInf (StableSubmodule φ) :=
    { __ := (inferInstance : PartialOrder (StableSubmodule φ))
      inf := fun P Q =>
        { carrier := P.carrier ⊓ Q.carrier
          stable := by
            exact le_inf
              ((Submodule.map_mono inf_le_left).trans P.stable)
              ((Submodule.map_mono inf_le_right).trans Q.stable) }
      le_inf := by
        intro S P Q hP hQ
        change S.carrier ≤ P.carrier ⊓ Q.carrier
        exact le_inf hP hQ
      inf_le_left := by
        intro P Q
        change P.carrier ⊓ Q.carrier ≤ P.carrier
        exact inf_le_left
      inf_le_right := by
        intro P Q
        change P.carrier ⊓ Q.carrier ≤ Q.carrier
        exact inf_le_right }
  let _ : Lattice (StableSubmodule φ) := { __ := supInst, __ := infInst }
  let _ : IsModularLattice (StableSubmodule φ) :=
    ⟨by
      intro x y z h
      change (x.carrier ⊔ y.carrier) ⊓ z.carrier ≤
        x.carrier ⊔ (y.carrier ⊓ z.carrier)
      exact IsModularLattice.sup_inf_le_assoc_of_le y.carrier
        (show x.carrier ≤ z.carrier from h)⟩
  let intervalFactor (P Q : StableSubmodule φ) : Type v :=
    Q.carrier ⧸ Submodule.comap Q.carrier.subtype P.carrier
  let intervalEnd (P Q : StableSubmodule φ) :
      Module.End R (intervalFactor P Q) := by
    let L : Submodule R Q.carrier :=
      Submodule.comap Q.carrier.subtype P.carrier
    let fQ : Module.End R Q.carrier :=
      restrictToStableSubmodule φ Q.carrier Q.stable
    let hL : L ≤ L.comap fQ := by
      intro z hz
      change φ (z : X.carrier) ∈ P.carrier
      exact P.stable ⟨z, hz, rfl⟩
    exact L.mapQ L fQ hL
  let E : (StableSubmodule φ × StableSubmodule φ) →
      (StableSubmodule φ × StableSubmodule φ) → Prop :=
    fun a b =>
      ∃ e : intervalFactor a.1 a.2 ≃ₗ[R] intervalFactor b.1 b.2,
        ∀ x, e (intervalEnd a.1 a.2 x) =
          intervalEnd b.1 b.2 (e x)
  have hE_refl : ∀ {a}, E a a := by
    intro a
    refine ⟨LinearEquiv.refl R _, ?_⟩
    intro x
    rfl
  have hE_symm : ∀ {a b}, E a b → E b a := by
    rintro a b ⟨e, he⟩
    refine ⟨e.symm, ?_⟩
    intro x
    calc
      e.symm (intervalEnd b.1 b.2 x) =
          e.symm (intervalEnd b.1 b.2 (e (e.symm x))) := by
            rw [e.apply_symm_apply]
      _ = e.symm (e (intervalEnd a.1 a.2 (e.symm x))) :=
        congrArg e.symm (he (e.symm x)).symm
      _ = intervalEnd a.1 a.2 (e.symm x) := e.symm_apply_apply _
  have hE_trans : ∀ {a b c}, E a b → E b c → E a c := by
    rintro a b c ⟨e, he⟩ ⟨f, hf⟩
    refine ⟨e.trans f, ?_⟩
    intro x
    change f (e (intervalEnd a.1 a.2 x)) =
      intervalEnd c.1 c.2 (f (e x))
    calc
      f (e (intervalEnd a.1 a.2 x)) =
          f (intervalEnd b.1 b.2 (e x)) := by rw [he]
      _ = intervalEnd c.1 c.2 (f (e x)) := hf (e x)
  have hE_diamond : ∀ {x y : StableSubmodule φ},
      x ⋖ x ⊔ y → E (x, x ⊔ y) (x ⊓ y, y) := by
    intro x y hxy
    let U : Submodule R X.carrier := (x ⊔ y).carrier
    let I : Submodule R X.carrier := (x ⊓ y).carrier
    let K : Submodule R U := Submodule.comap U.subtype x.carrier
    let L : Submodule R y.carrier := Submodule.comap y.carrier.subtype I
    let inc : y.carrier →ₗ[R] U :=
      { toFun := fun z => ⟨z, by
          change (z : X.carrier) ∈ (x ⊔ y).carrier
          exact Submodule.mem_sup_right z.property⟩
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    have hL : L ≤ K.comap inc := by
      intro z hz
      change (z : X.carrier) ∈ x.carrier
      change (z : X.carrier) ∈ I at hz
      exact (show I ≤ x.carrier by
        change x.carrier ⊓ y.carrier ≤ x.carrier
        exact inf_le_left) hz
    let qMap : intervalFactor (x ⊓ y) y →ₗ[R]
        intervalFactor x (x ⊔ y) := by
      change (y.carrier ⧸ L) →ₗ[R] (U ⧸ K)
      exact L.mapQ K inc hL
    have qMap_injective : Function.Injective qMap := by
      intro a b hab
      obtain ⟨a0, ha0⟩ := L.mkQ_surjective a
      obtain ⟨b0, hb0⟩ := L.mkQ_surjective b
      rw [← ha0, ← hb0] at hab ⊢
      change (L.mapQ K inc hL) (Submodule.Quotient.mk a0) =
        (L.mapQ K inc hL) (Submodule.Quotient.mk b0) at hab
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply] at hab
      apply (Submodule.Quotient.eq L).2
      have hab' : ((inc a0 : U) : X.carrier) - (inc b0 : U) ∈ x.carrier := by
        have := (Submodule.Quotient.eq K).1 hab
        exact this
      change (a0 : X.carrier) - b0 ∈ I
      exact ⟨hab', sub_mem a0.property b0.property⟩
    have qMap_surjective : Function.Surjective qMap := by
      intro z
      obtain ⟨z, rfl⟩ := K.mkQ_surjective z
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp z.property
      let b' : y.carrier := ⟨b, hb⟩
      refine ⟨Submodule.Quotient.mk b', ?_⟩
      change (L.mapQ K inc hL) (Submodule.Quotient.mk b') = K.mkQ z
      rw [Submodule.mapQ_apply]
      apply (Submodule.Quotient.eq K).2
      change (inc b' : X.carrier) - z ∈ x.carrier
      rw [show (inc b' : X.carrier) = b by rfl, ← hab]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (sub_mem x.carrier.zero_mem ha)
    let e0 : intervalFactor (x ⊓ y) y ≃ₗ[R]
        intervalFactor x (x ⊔ y) :=
      LinearEquiv.ofBijective qMap ⟨qMap_injective, qMap_surjective⟩
    have qMap_comm : ∀ w : intervalFactor (x ⊓ y) y,
        qMap (intervalEnd (x ⊓ y) y w) =
          intervalEnd x (x ⊔ y) (qMap w) := by
      intro w
      refine Submodule.Quotient.induction_on _ w ?_
      intro w
      rfl
    refine ⟨e0.symm, ?_⟩
    intro z
    apply qMap_injective
    change e0 (e0.symm (intervalEnd x (x ⊔ y) z)) =
      qMap (intervalEnd (x ⊓ y) y (e0.symm z))
    rw [e0.apply_symm_apply, qMap_comm]
    have he0q : qMap (e0.symm z) = z := by
      change e0 (e0.symm z) = z
      exact e0.apply_symm_apply z
    rw [he0q]
  have stable_ext {P Q : StableSubmodule φ} (h : P.carrier = Q.carrier) : P = Q := by
    cases P
    cases Q
    cases h
    rfl
  have stable_cov (r : StableCompositionSeries X) (i : Fin r.series.length) :
      r.series (Fin.castSucc i) ⋖ r.series (Fin.succ i) := by
    apply covBy_iff_lt_and_eq_or_eq.mpr
    refine ⟨?_, ?_⟩
    · change (r.series (Fin.castSucc i)).carrier <
        (r.series (Fin.succ i)).carrier
      exact r.series.step i
    · intro W hP hU
      let P := (r.series (Fin.castSucc i)).carrier
      let U := (r.series (Fin.succ i)).carrier
      let L : Submodule R U := Submodule.comap U.subtype P
      let WU : Submodule R U := Submodule.comap U.subtype W.carrier
      let fU : Module.End R U :=
        restrictToStableSubmodule φ U (r.series (Fin.succ i)).stable
      let N : Submodule R (U ⧸ L) := WU.map L.mkQ
      have hWUstable : ∀ z : U, z ∈ WU → fU z ∈ WU := by
        intro z hz
        change φ (z : X.carrier) ∈ W.carrier
        apply W.stable
        exact ⟨z, hz, rfl⟩
      have hN : Submodule.map (factorEnd r.series i) N ≤ N := by
        intro q hq
        obtain ⟨q, hq, rfl⟩ := hq
        obtain ⟨z, hz, rfl⟩ := hq
        change L.mkQ (fU z) ∈ N
        exact ⟨fU z, hWUstable z hz, rfl⟩
      rcases (r.simple_factor i).simple.2 N hN with hNbot | hNtop
      · have hWU : WU = L := by
          apply le_antisymm
          · intro z hz
            have hzq : L.mkQ z ∈ N := ⟨z, hz, rfl⟩
            rw [hNbot] at hzq
            exact (Submodule.Quotient.mk_eq_zero _).mp hzq
          · intro z hz
            change (z : X.carrier) ∈ W.carrier
            exact hP hz
        left
        apply stable_ext
        apply le_antisymm
        · intro x hx
          let z : U := ⟨x, hU hx⟩
          have hz : z ∈ WU := by
            change (z : X.carrier) ∈ W.carrier
            exact hx
          rw [hWU] at hz
          exact hz
        · intro x hx
          exact hP hx
      · have hmap : WU.map L.mkQ = ⊤ := by
          change WU.map L.mkQ = ⊤ at hNtop
          exact hNtop
        have htop : L ⊔ WU = ⊤ :=
          (Submodule.map_mkQ_eq_top L WU).mp hmap
        have hWU : WU = ⊤ := by
          apply top_unique
          rw [← htop]
          exact sup_le (fun z hz => by
            change (z : X.carrier) ∈ W.carrier
            exact hP hz) le_rfl
        right
        apply stable_ext
        apply le_antisymm
        · intro x hx
          exact hU hx
        · intro x hx
          let z : U := ⟨x, hx⟩
          have hz : z ∈ WU := by rw [hWU]; exact Submodule.mem_top
          exact hz
  let toCompositionSeries (r : StableCompositionSeries X) :
      CompositionSeries (StableSubmodule φ) :=
    { length := r.series.length
      toFun := r.series
      step := fun i => stable_cov r i }
  have hhead : (toCompositionSeries s).head = (toCompositionSeries t).head := by
    apply stable_ext
    change (s.series.head).carrier = (t.series.head).carrier
    rw [s.head_eq_bot, t.head_eq_bot]
  have hlast : (toCompositionSeries s).last = (toCompositionSeries t).last := by
    apply stable_ext
    change (s.series.last).carrier = (t.series.last).carrier
    rw [s.last_eq_top, t.last_eq_top]
  have hJH : CompositionSeries.Equivalent (toCompositionSeries s) (toCompositionSeries t) :=
    CompositionSeries.jordan_holder (toCompositionSeries s) (toCompositionSeries t)
      hhead hlast
  have hterm_charpoly : ∀ i : Fin s.series.length,
      simpleCharacteristicPolynomial (s.simple_factor i) =
        simpleCharacteristicPolynomial (t.simple_factor (hJH.choose i)) := by
    intro i
    have hIso := JordanHolderLattice.Iso.rel E hE_refl hE_symm hE_trans
      hE_diamond (hJH.choose_spec i)
    rcases hIso with ⟨e, he⟩
    have hcomm : ∀ x, e (factorEnd s.series i x) =
        factorEnd t.series (hJH.choose i) (e x) := by
      intro x
      exact he x
    exact simplePair_characteristicPolynomial_invariant
      (s.simple_factor i) (t.simple_factor (hJH.choose i)) e hcomm
  exact Fintype.prod_equiv hJH.choose
    (fun i => simpleCharacteristicPolynomial (s.simple_factor i))
    (fun i => simpleCharacteristicPolynomial (t.simple_factor i)) hterm_charpoly

/-! The following three interfaces record the Jordan--Hölder independence of the definitions. -/

theorem determinant_eq_stableCompositionSeries_product
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) (s : StableCompositionSeries X) :
    determinant X =
      ∏ i : Fin s.series.length, simpleDeterminant (s.simple_factor i) := by
  change (∏ i, simpleDeterminant ((stableCompositionSeries X).simple_factor i)) = _
  exact (stableCompositionSeries_invariant X (stableCompositionSeries X) s).1

theorem trace_eq_stableCompositionSeries_sum
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) (s : StableCompositionSeries X) :
    trace X =
      ∑ i : Fin s.series.length, simpleTrace (s.simple_factor i) := by
  change (∑ i, simpleTrace ((stableCompositionSeries X).simple_factor i)) = _
  exact (stableCompositionSeries_invariant X (stableCompositionSeries X) s).2

theorem characteristicPolynomial_eq_stableCompositionSeries_product
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) (s : StableCompositionSeries X) :
    characteristicPolynomial X =
      ∏ i : Fin s.series.length, simpleCharacteristicPolynomial (s.simple_factor i) := by
  change (∏ i, simpleCharacteristicPolynomial ((stableCompositionSeries X).simple_factor i)) = _
  exact stableCompositionSeries_characteristicPolynomial_invariant
    X (stableCompositionSeries X) s

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
