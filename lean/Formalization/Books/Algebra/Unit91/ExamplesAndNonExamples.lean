import Formalization.Books.Algebra.Unit90.CoherentRings
import Formalization.Books.Algebra.Unit81.CharacterizingFlatness
import Formalization.Books.Algebra.Unit84.TransfiniteDevissage
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.RingHom.FinitePresentation

/-!
# Commutative Algebra, Chapter 91: Examples and non-examples of Mittag-Leffler modules

This file records the examples and non-examples at the end of the source
section.  The Mittag-Leffler predicate and the tensor-product APIs are the
canonical interfaces from Chapters 88 and 89.
-/

namespace Formalization.Books.Algebra.Unit91

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit84
open Formalization.Books.Algebra.Unit81
open Formalization.Books.Categories.Unit21
open Formalization.Books.Algebra.Unit88
open Formalization.Books.Algebra.Unit89
open scoped DirectSum TensorProduct

universe u v w

noncomputable section

/-! ## Mittag-Leffler modules -/

/- The assertion that finitely presented modules are Mittag-Leffler is already
   `isMittagLefflerModule_of_finitePresentation` from Chapter 88. -/

/-- A finitely generated module is Mittag-Leffler exactly when it is finitely
presented (the first example in the source). -/
theorem finite_isMittagLeffler_iff_finitePresentation
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (hM : Module.Finite R (M : Type v)) :
    IsMittagLefflerModule M ↔ Module.FinitePresentation R (M : Type v) := by
  constructor
  · intro hML
    have hsurj :=
      (finite_generation_tensor_iff M).out 0 1 |>.mp hM
    have hinj : ∀ (A : Type v) (Q : A → ModuleCat.{v} R),
        Function.Injective (productTensorMap M Q) :=
      (mittagLeffler_tensor_iff M).out 0 1 |>.mp hML
    apply (finite_presentation_tensor_iff M).out 0 1 |>.mpr
    intro A Q
    exact ⟨hinj A Q, hsurj A Q⟩
  · intro hFP
    exact isMittagLefflerModule_of_finitePresentation M hFP

/-- A free module is Mittag-Leffler. -/
theorem isMittagLefflerModule_of_free
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (hM : Module.Free R (M : Type v)) :
    IsMittagLefflerModule M := by
  let _freeM := hM
  classical
  obtain ⟨ι, b⟩ := (Module.free_iff_set R (M : Type v)).mp hM
  let b : Module.Basis ι R (M : Type v) := b.some
  intro P hP f
  let _finiteP : Module.Finite R (P : Type v) := inferInstance
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R (P : Type v)
  let T : Finset ι :=
    Finset.univ.biUnion (fun i => (b.repr (f (p (Pi.single i 1)))).support)
  let Q : Submodule R (M : Type v) :=
    Submodule.span R (Set.range (fun i : T => b i))
  have hQset : Set.range (fun i : T => b i) = b '' (T : Set ι) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hlin : LinearIndependent R (fun i : T => b i) :=
    b.linearIndependent.comp (fun i : T => (i : ι)) Subtype.val_injective
  let bQ : Module.Basis T R (Q : Type v) := Module.Basis.span hlin
  let _freeQ : Module.Free R (Q : Type v) := Module.Free.of_basis bQ
  let _finiteQ : Module.Finite R (Q : Type v) := Module.Finite.of_basis bQ
  have hQ : Module.FinitePresentation R (Q : Type v) :=
    Module.finitePresentation_of_projective R (Q : Type v)
  have hgen : ∀ i : Fin n, f (p (Pi.single i 1)) ∈ Q := by
    intro i
    have hm : f (p (Pi.single i 1)) ∈
        Submodule.span R (b '' (T : Set ι)) := by
      apply (b.mem_span_image).mpr
      intro j hj
      have hj' : j ∈ T := by
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hj⟩
      simpa only [Finset.mem_coe] using hj'
    simpa [Q, hQset] using hm
  have hmem : ∀ x : (P : Type v), f x ∈ Q := by
    intro x
    obtain ⟨c, rfl⟩ := hp x
    have hc : c = ∑ i, c i • Pi.single i (1 : R) := by
      calc
        c = ∑ i, Pi.single i (c i) := (Finset.univ_sum_single c).symm
        _ = ∑ i, c i • Pi.single i (1 : R) := by
          apply Finset.sum_congr rfl
          intro i hi
          ext j
          by_cases hij : i = j <;> simp [hij]
    rw [hc]
    simp only [map_sum, map_smul]
    exact Submodule.sum_mem Q (fun i _ => Q.smul_mem _ (hgen i))
  let g : (P : Type v) →ₗ[R] (Q : Type v) := f.codRestrict Q hmem
  have hfactor : Q.subtype.comp g = f := by
    ext x
    rfl
  let r : (M : Type v) →ₗ[R] (Q : Type v) :=
    b.constr R (fun i => if hi : i ∈ T then
      ⟨b i, by
        apply Submodule.subset_span
        exact ⟨⟨i, hi⟩, rfl⟩⟩ else 0)
  have hsplit : r.comp Q.subtype = LinearMap.id := by
    apply bQ.ext
    intro i
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    have hi_eq : Q.subtype (bQ i) = b (i : ι) := by
      dsimp [bQ]
      exact Module.Basis.coe_span_apply hlin i
    rw [hi_eq]
    simp only [r, Module.Basis.constr_basis, dif_pos i.property]
    apply Subtype.ext
    dsimp [bQ]
    exact (Module.Basis.coe_span_apply hlin i).symm
  refine ⟨ModuleCat.of R (Q : Type v), hQ, g, ?_⟩
  constructor
  · intro V _ _ x hx
    apply LinearMap.mem_ker.mpr
    have hcomp : (r.rTensor V).comp (f.rTensor V) = g.rTensor V := by
      calc
        (r.rTensor V).comp (f.rTensor V) =
            (r.rTensor V).comp ((Q.subtype.comp g).rTensor V) := by
              rw [hfactor]
        _ = (r.rTensor V).comp
            ((Q.subtype.rTensor V).comp (g.rTensor V)) := by
              rw [LinearMap.rTensor_comp]
        _ = ((r.comp Q.subtype).rTensor V).comp (g.rTensor V) := by
              simp only [LinearMap.rTensor_comp, LinearMap.comp_assoc]
        _ = (LinearMap.id.rTensor V).comp (g.rTensor V) := by
              rw [hsplit]
        _ = g.rTensor V := by simp
    rw [← hcomp]
    simp [LinearMap.mem_ker.mp hx]
  · intro V _ _ x hx
    apply LinearMap.mem_ker.mpr
    rw [← hfactor, LinearMap.rTensor_comp_apply]
    simp [LinearMap.mem_ker.mp hx]

/-- A projective module is Mittag-Leffler. -/
theorem isMittagLefflerModule_of_projective
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (hM : Module.Projective R (M : Type v)) :
    IsMittagLefflerModule M := by
  obtain ⟨F, hFadd, hFmod, hfree, i, s, hs⟩ :=
    (Module.Projective.iff_split (R := R) (P := (M : Type v))).mp hM
  let _addCommGroup : AddCommGroup F :=
    @Module.addCommMonoidToAddCommGroup R F _ hFadd hFmod
  have hFML : IsMittagLefflerModule (ModuleCat.of R F) :=
    isMittagLefflerModule_of_free (ModuleCat.of R F) hfree
  have hcrit : IsMittagLefflerModule M ↔
      ∀ (A : Type v) (Q : A → ModuleCat.{max u v} R),
        Function.Injective (productTensorMap M Q) :=
    (mittagLeffler_tensor_iff M).out 0 1
  apply hcrit.mpr
  intro A Q
  have hFcrit : ∀ (A : Type v) (Q : A → ModuleCat.{max u v} R),
      Function.Injective (productTensorMap (ModuleCat.of R F) Q) := by
    exact ((mittagLeffler_tensor_iff (ModuleCat.of R F)).out 0 1).mp hFML
  let U : Type (max u v) := ∀ a, (Q a : Type (max u v))
  have hiU : Function.Injective (i.rTensor U) := by
    intro x y hxy
    have h := congrArg (fun z => (s.rTensor U) z) hxy
    simpa [← LinearMap.rTensor_comp_apply, hs] using h
  have hcomm : ∀ z : TensorProduct R (M : Type v) U,
      productTensorMap (ModuleCat.of R F) Q (i.rTensor U z) =
        fun a => (i.rTensor (Q a : Type (max u v)))
          (productTensorMap M Q z a) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        ext a
        simp [productTensorMap]
    | tmul m q =>
        ext a
        rw [LinearMap.rTensor_tmul, productTensorMap_tmul, productTensorMap_tmul]
        rfl
    | add x y hx hy =>
        ext a
        simp only [map_add, Pi.add_apply]
        rw [congrFun hx a, congrFun hy a]
  intro x y hxy
  have hprod : productTensorMap (ModuleCat.of R F) Q (i.rTensor U x) =
      productTensorMap (ModuleCat.of R F) Q (i.rTensor U y) := by
    rw [hcomm x, hcomm y]
    funext a
    rw [congrFun hxy a]
  exact hiU (hFcrit A Q hprod)

private theorem tensorProductContains_range_dual
    {R A B : Type u} [CommRing R]
    [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] [Module.Free R B] [Module.Finite R B]
    (f : A →ₗ[R] B) :
    tensorProductContains (LinearMap.range f.dualMap)
      ((dualTensorHomEquiv R A B).symm f) := by
  classical
  let b := Module.Free.chooseBasis R B
  let _fintype : Fintype (Module.Free.ChooseBasisIndex R B) := Fintype.ofFinite _
  let y : TensorProduct R (LinearMap.range f.dualMap) B :=
    ∑ i, (⟨(b.coord i).comp f, ⟨b.coord i, rfl⟩⟩ : LinearMap.range f.dualMap) ⊗ₜ[R] b i
  refine ⟨y, ?_⟩
  apply (dualTensorHomEquiv R A B).injective
  apply LinearMap.ext
  intro a
  have he : (dualTensorHomEquiv R A B).toLinearMap = dualTensorHom R A B := rfl
  rw [← LinearEquiv.coe_toLinearMap, he]
  have hs : dualTensorHom R A B ((dualTensorHomEquiv R A B).symm f) = f := by
    rw [← he]
    exact (dualTensorHomEquiv R A B).apply_symm_apply f
  rw [hs]
  rw [← b.sum_repr (f a)]
  simp [y, LinearMap.comp_apply, dualTensorHom_apply]

private theorem range_dual_le_of_tensorProductContains
    {R A B : Type u} [CommRing R]
    [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B]
    {f : A →ₗ[R] B} {G : Submodule R (Module.Dual R A)}
    (hG : ∃ y : TensorProduct R (G : Type u) B,
      G.subtype.rTensor B y = (dualTensorHomEquiv R A B).symm f) :
    LinearMap.range f.dualMap ≤ G := by
  rintro z ⟨φ, rfl⟩
  obtain ⟨y, hy⟩ := hG
  let q : G := TensorProduct.rid R (G : Type u) ((φ.lTensor G) y)
  have hnat0 : ∀ y : TensorProduct R (G : Type u) B,
      G.subtype (TensorProduct.rid R (G : Type u) ((φ.lTensor G) y)) =
        dualTensorHom R A R (φ.lTensor (Module.Dual R A)
          (G.subtype.rTensor B y)) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul g b =>
        apply LinearMap.ext
        intro a
        simp [dualTensorHom_apply, mul_comm]
    | add y z hy hz => simp only [map_add, hy, hz]
  have hnat : G.subtype q =
      dualTensorHom R A R (φ.lTensor (Module.Dual R A)
        (G.subtype.rTensor B y)) := hnat0 y
  have hright : dualTensorHom R A R (φ.lTensor (Module.Dual R A)
        ((dualTensorHomEquiv R A B).symm f)) = φ.comp f := by
    have hh := congrArg (fun q => q ((dualTensorHomEquiv R A B).symm f))
      (dualTensorHom_comp_lTensor (R := R) (M := A) (N := B) (P := R) φ)
    simpa [LinearMap.comp_apply] using hh
  have hq : G.subtype q = φ.comp f := by
    calc
    G.subtype q = dualTensorHom R A R (φ.lTensor (Module.Dual R A)
        (G.subtype.rTensor B y)) := hnat
    _ = dualTensorHom R A R (φ.lTensor (Module.Dual R A)
        ((dualTensorHomEquiv R A B).symm f)) := by rw [hy]
    _ = φ.comp f := hright
  change φ.comp f ∈ G
  rw [← hq]
  exact q.property

private theorem tensorProduct_factor_through_moduleDirectLimit
    {R I H : Type u} [CommRing R] [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [DecidableEq I] [AddCommMonoid H] [Module R H]
    {stage : I → Type u} [∀ i, AddCommGroup (stage i)] [∀ i, Module R (stage i)]
    (map : ∀ i j, i ≤ j → stage i →ₗ[R] stage j)
    [DirectedSystem stage (fun i j h => map i j h)]
    (y : TensorProduct R H (Module.DirectLimit stage map)) :
    ∃ i : I, ∃ x : TensorProduct R H (stage i),
      (Module.DirectLimit.of R I stage map i).lTensor H x = y := by
  let T := TensorProduct.directLimitRight map H
  have hT : ∀ {i : I} (x : TensorProduct R H (stage i)),
      T ((Module.DirectLimit.of R I stage map i).lTensor H x) =
        Module.DirectLimit.of R I (fun i => TensorProduct R H (stage i))
          (fun i j h => (map i j h).lTensor H) i x := by
    intro i x
    induction x using TensorProduct.induction_on with
    | zero => simp [T]
    | tmul h m => simp [T]
    | add x y hx hy => simp [T, hx, hy]
  obtain ⟨i, x, hx⟩ := Module.DirectLimit.exists_of (T y)
  refine ⟨i, x, ?_⟩
  apply T.injective
  rw [hT, hx]

private theorem tensorProduct_eq_of_moduleDirectLimit
    {R I H : Type u} [CommRing R] [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [DecidableEq I] [AddCommMonoid H] [Module R H]
    {stage : I → Type u} [∀ i, AddCommGroup (stage i)] [∀ i, Module R (stage i)]
    (map : ∀ i j, i ≤ j → stage i →ₗ[R] stage j)
    [DirectedSystem stage (fun i j h => map i j h)]
    {i j : I} (x : TensorProduct R H (stage i))
    (y : TensorProduct R H (stage j))
    (hxy : (Module.DirectLimit.of R I stage map i).lTensor H x =
      (Module.DirectLimit.of R I stage map j).lTensor H y) :
    ∃ k : I, ∃ hik : i ≤ k, ∃ hjk : j ≤ k,
      (map i k hik).lTensor H x = (map j k hjk).lTensor H y := by
  let T := TensorProduct.directLimitRight map H
  have hT : ∀ {i : I} (x : TensorProduct R H (stage i)),
      T ((Module.DirectLimit.of R I stage map i).lTensor H x) =
        Module.DirectLimit.of R I (fun i => TensorProduct R H (stage i))
          (fun i j h => (map i j h).lTensor H) i x := by
    intro i x
    induction x using TensorProduct.induction_on with
    | zero => simp [T]
    | tmul h m => simp [T]
    | add x y hx hy => simp [T, hx, hy]
  have hTxy := congrArg T hxy
  rw [hT x, hT y] at hTxy
  obtain ⟨c, hic, hjc⟩ := exists_ge_ge i j
  have hsame :
      Module.DirectLimit.of R I (fun j => TensorProduct R H (stage j))
          (fun j k h => (map j k h).lTensor H) c
          ((map i c hic).lTensor H x) =
        Module.DirectLimit.of R I (fun j => TensorProduct R H (stage j))
          (fun j k h => (map j k h).lTensor H) c
          ((map j c hjc).lTensor H y) := by
    calc
      _ = Module.DirectLimit.of R I (fun j => TensorProduct R H (stage j))
          (fun j k h => (map j k h).lTensor H) i x := by simp
      _ = Module.DirectLimit.of R I (fun j => TensorProduct R H (stage j))
          (fun j k h => (map j k h).lTensor H) j y := hTxy
      _ = _ := by simp
  obtain ⟨k, hck, heqk⟩ :=
    Module.DirectLimit.exists_eq_of_of_eq hsame
  refine ⟨k, hic.trans hck, hjc.trans hck, ?_⟩
  have hmap_i : (map c k hck).comp (map i c hic) =
      map i k (hic.trans hck) := by
    apply LinearMap.ext
    intro z
    exact DirectedSystem.map_map' (f := fun i j h => map i j h) hic hck z
  have hmap_j : (map c k hck).comp (map j c hjc) =
      map j k (hjc.trans hck) := by
    apply LinearMap.ext
    intro z
    exact DirectedSystem.map_map' (f := fun i j h => map i j h) hjc hck z
  calc
    (map i k (hic.trans hck)).lTensor H x =
        (map c k hck).lTensor H ((map i c hic).lTensor H x) := by
          rw [← LinearMap.lTensor_comp_apply, hmap_i]
    _ = (map j k (hjc.trans hck)).lTensor H y := by
          rw [heqk, ← LinearMap.lTensor_comp_apply, hmap_j]

/-! ## The flat Mittag-Leffler criterion -/

/-- For a flat module, Mittag-Lefflerness is equivalent to the existence of a
smallest submodule through which every tensor element from a finite free
module factors.  The predicate `tensorProductContains` is the canonical
tensor containment relation from Chapter 89. -/
theorem flat_isMittagLeffler_iff_minimal_tensor_submodule
    {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    (hflat : Module.Flat R M) :
    IsMittagLefflerModule (ModuleCat.of R M) ↔
      ∀ (F : Type u) [AddCommGroup F] [Module R F],
        Module.Free R F → Module.Finite R F →
          ∀ x : TensorProduct R F M, ∃ F' : Submodule R F,
            IsLeast {G : Submodule R F | tensorProductContains G x} F' := by
  constructor
  · intro hML F _ _ hfree hfinite x
    let _free := hfree
    let _finite := hfinite
    exact minimal_tensor_submodule hflat hML x |>.imp fun F' h => h.1
  · intro hmin
    obtain ⟨s⟩ := (lazard (R := R) (M := M)).mp hflat
    let _preorder : Preorder s.index := s.indexPreorder
    let _nonempty : Nonempty s.index := s.indexNonempty
    let _directed : IsDirectedOrder s.index := s.indexDirected
    let _stageGroup : ∀ i, AddCommGroup (s.stage i) := s.stageAddCommGroup
    let _stageModule : ∀ i, Module R (s.stage i) := s.stageModule
    let _stageDirected : DirectedSystem s.stage (fun i j h => s.map i j h) :=
      s.stageDirectedSystem
    let D : System s.index (ModuleCat.{u} R) := {
      obj := fun i => ModuleCat.of R (s.stage i)
      map := fun f => ModuleCat.ofHom (s.map _ _ f.le)
      map_id := by
        intro i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        simpa using DirectedSystem.map_self (f := fun i j h => s.map i j h) x
      map_comp := by
        intro i j k f g
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change s.map i k (f.le.trans g.le) x =
          s.map j k g.le (s.map i j f.le x)
        simpa using (DirectedSystem.map_map' (f := fun i j h => s.map i j h)
          f.le g.le x).symm
      }
    let e : DirectLimit s.stage s.map ≃ₗ[R] M := s.targetIso.some
    let ι : D ⟶ (Functor.const s.index).obj (ModuleCat.of R M) := {
      app := fun i => ModuleCat.ofHom
        (e.toLinearMap.comp (DirectLimit.Module.of R s.index s.stage s.map i))
      naturality := by
        intro i j f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have hf : f = homOfLE f.le := Subsingleton.elim _ _
        rw [hf]
        simp [D, e, LinearMap.comp_apply]
      }
    let c : Cocone D := Cocone.mk _ ι
    have hc : IsColimit c := by
      refine {
        desc := fun t => ?_
        fac := ?_
        uniq := ?_ }
      · let g : ∀ i, s.stage i →ₗ[R] (t.pt : Type u) :=
          fun i => (t.ι.app i).hom
        have hg : ∀ i j (hij : i ≤ j) (x : s.stage i),
            g j (s.map i j hij x) = g i x := by
          intro i j hij x
          have hn := congrArg ModuleCat.Hom.hom (t.ι.naturality (homOfLE hij))
          change (t.ι.app j).hom (s.map i j hij x) = (t.ι.app i).hom x
          simpa [D, ModuleCat.hom_comp, LinearMap.comp_apply] using
            congrArg (fun q => q x) hn
        exact ModuleCat.ofHom ((DirectLimit.Module.lift R s.index s.stage s.map g hg).comp
          e.symm.toLinearMap)
      · intro t i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        simp [c, ι, e, DirectLimit.Module.lift, LinearMap.comp_apply]
      · intro t f hf
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        obtain ⟨y, rfl⟩ := e.surjective x
        induction y using DirectLimit.induction with
        | _ i y =>
            have hi := congrArg ModuleCat.Hom.hom (hf i)
            simpa [c, ι, e, LinearMap.comp_apply] using congrArg (fun q => q y) hi
    let P : ColimitPresentation s.index (ModuleCat.of R M) := {
      diag := D
      ι := ι
      isColimit := hc }
    let hdual : (homInverseSystem P.diag (ModuleCat.of R R)).IsMittagLeffler := by
      classical
      apply (Functor.isMittagLeffler_iff_subset_range_comp _).mpr
      intro i
      let eold : Module.DirectLimit s.stage s.map ≃ₗ[R] M :=
        (Module.DirectLimit.linearEquiv s.stage s.map).trans e
      let i0 := i.unop
      let A := s.stage i0
      let _freeA : Module.Free R A := s.free i0
      let _finiteA : Module.Finite R A := s.finite i0
      let f0 : A →ₗ[R] M := (P.ι.app i.unop).hom
      let xi : TensorProduct R (Module.Dual R A) M :=
        (dualTensorHomEquiv R A M).symm f0
      obtain ⟨G, hG⟩ := hmin (Module.Dual R A) inferInstance inferInstance xi
      obtain ⟨y, hy⟩ := hG.1
      let yold : TensorProduct R (G : Type u)
          (Module.DirectLimit s.stage s.map) :=
        eold.symm.toLinearMap.lTensor (G : Type u) y
      obtain ⟨j, yj, hyj⟩ :=
        tensorProduct_factor_through_moduleDirectLimit s.map yold
      let x0 : TensorProduct R (Module.Dual R A) A :=
        (dualTensorHomEquiv R A A).symm LinearMap.id
      have hx0 :
          (Module.DirectLimit.of R s.index s.stage s.map i0).lTensor
              (Module.Dual R A) x0 =
            eold.symm.toLinearMap.lTensor (Module.Dual R A) xi := by
        let oldOf : A →ₗ[R] Module.DirectLimit s.stage s.map :=
          Module.DirectLimit.of R s.index s.stage s.map i0
        have he : (dualTensorHomEquiv R A
            (Module.DirectLimit s.stage s.map)).toLinearMap =
            dualTensorHom R A (Module.DirectLimit s.stage s.map) := rfl
        have he0 : (dualTensorHomEquiv R A A).toLinearMap =
            dualTensorHom R A A := rfl
        have hem : (dualTensorHomEquiv R A M).toLinearMap =
            dualTensorHom R A M := rfl
        have hx0fun : dualTensorHom R A A x0 = LinearMap.id := by
          rw [← he0]
          exact (dualTensorHomEquiv R A A).apply_symm_apply LinearMap.id
        have hxifun : dualTensorHom R A M xi = f0 := by
          rw [← hem]
          exact (dualTensorHomEquiv R A M).apply_symm_apply f0
        have hf0 : f0 = eold.comp oldOf := by
          let rootOf : A →ₗ[R] DirectLimit s.stage s.map :=
            DirectLimit.Module.of R s.index s.stage s.map i0
          have hlin : (Module.DirectLimit.linearEquiv s.stage s.map).toLinearMap.comp
                oldOf = rootOf := by
            apply LinearMap.ext
            intro z
            dsimp [oldOf, rootOf]
            exact Module.DirectLimit.linearEquiv_of (R := R) s.stage s.map
              (i := i0) (g := z)
          calc
            f0 = e.comp rootOf := by
              simp [f0, P, ι, D]
              change DirectLimit.Module.of R s.index s.stage s.map
                  (Opposite.unop i) =
                DirectLimit.Module.of R s.index s.stage s.map
                  (Opposite.unop i)
              rfl
            _ = e.comp ((Module.DirectLimit.linearEquiv s.stage s.map).toLinearMap.comp
                oldOf) := by rw [hlin]
            _ = eold.comp oldOf := by rfl
        apply (dualTensorHomEquiv R A (Module.DirectLimit s.stage s.map)).injective
        rw [← LinearEquiv.coe_toLinearMap, he]
        calc
          dualTensorHom R A (Module.DirectLimit s.stage s.map)
                (oldOf.lTensor (Module.Dual R A) x0) =
              oldOf.comp (dualTensorHom R A A x0) := by
                have hh := congrArg (fun q => q x0)
                  (dualTensorHom_comp_lTensor (R := R) (M := A)
                    (N := A) (P := Module.DirectLimit s.stage s.map) oldOf)
                simpa [LinearMap.comp_apply] using hh
          _ = oldOf := by rw [hx0fun, LinearMap.comp_id]
          _ = eold.symm.comp f0 := by rw [hf0]; simp
          _ = dualTensorHom R A (Module.DirectLimit s.stage s.map)
                (eold.symm.toLinearMap.lTensor (Module.Dual R A) xi) := by
                have hh := congrArg (fun q => q xi)
                  (dualTensorHom_comp_lTensor (R := R) (M := A)
                    (N := M) (P := Module.DirectLimit s.stage s.map)
                    eold.symm.toLinearMap)
                calc
                  eold.symm.comp f0 = eold.symm.comp
                      (dualTensorHom R A M xi) := by rw [hxifun]
                  _ = dualTensorHom R A (Module.DirectLimit s.stage s.map)
                      (eold.symm.toLinearMap.lTensor (Module.Dual R A) xi) := by
                      simpa [LinearMap.comp_apply, LinearMap.compRight_apply] using hh.symm
      have hf0 : f0 = eold.comp
          (Module.DirectLimit.of R s.index s.stage s.map i0) := by
        let rootOf : A →ₗ[R] DirectLimit s.stage s.map :=
          DirectLimit.Module.of R s.index s.stage s.map i0
        have hlin : (Module.DirectLimit.linearEquiv s.stage s.map).toLinearMap.comp
              (Module.DirectLimit.of R s.index s.stage s.map i0) = rootOf := by
          apply LinearMap.ext
          intro z
          dsimp [rootOf]
          exact Module.DirectLimit.linearEquiv_of (R := R) s.stage s.map
            (i := i0) (g := z)
        calc
          f0 = e.comp rootOf := by
            simp [f0, P, ι, D]
            change DirectLimit.Module.of R s.index s.stage s.map
                (Opposite.unop i) =
              DirectLimit.Module.of R s.index s.stage s.map
                (Opposite.unop i)
            rfl
          _ = e.comp ((Module.DirectLimit.linearEquiv s.stage s.map).toLinearMap.comp
              (Module.DirectLimit.of R s.index s.stage s.map i0)) := by rw [hlin]
          _ = eold.comp (Module.DirectLimit.of R s.index s.stage s.map i0) := by rfl
      have hG_le_range :
          ∀ (l : s.index) (hil : i0 ≤ l),
            G ≤ LinearMap.range (s.map i0 l hil).dualMap := by
        intro l hil
        let _freeStage : Module.Free R (s.stage l) := s.free l
        let _finiteStage : Module.Finite R (s.stage l) := s.finite l
        let f_il : s.stage i0 →ₗ[R] s.stage l := s.map i0 l hil
        let x_l : TensorProduct R (Module.Dual R A) (s.stage l) :=
          (dualTensorHomEquiv R A (s.stage l)).symm f_il
        let target_l : s.stage l →ₗ[R] M :=
          eold.comp (Module.DirectLimit.of R s.index s.stage s.map l)
        have hmap_l :
            (Module.DirectLimit.of R s.index s.stage s.map l).comp f_il =
              Module.DirectLimit.of R s.index s.stage s.map i0 := by
          apply LinearMap.ext
          intro z
          simp [f_il]
        have hf0l : f0 = target_l.comp f_il := by
          calc
            f0 = eold.comp (Module.DirectLimit.of R s.index s.stage s.map i0) := hf0
            _ = eold.comp
                ((Module.DirectLimit.of R s.index s.stage s.map l).comp f_il) := by
                  rw [hmap_l]
            _ = target_l.comp f_il := by rfl
        have he_l : (dualTensorHomEquiv R A (s.stage l)).toLinearMap =
            dualTensorHom R A (s.stage l) := rfl
        have hx_l : dualTensorHom R A (s.stage l) x_l = f_il := by
          rw [← he_l]
          exact (dualTensorHomEquiv R A (s.stage l)).apply_symm_apply f_il
        have he_M : (dualTensorHomEquiv R A M).toLinearMap =
            dualTensorHom R A M := rfl
        have hxi : dualTensorHom R A M xi = f0 := by
          rw [← he_M]
          exact (dualTensorHomEquiv R A M).apply_symm_apply f0
        have hxi_l : target_l.lTensor (Module.Dual R A) x_l = xi := by
          apply (dualTensorHomEquiv R A M).injective
          rw [← LinearEquiv.coe_toLinearMap, he_M]
          calc
            dualTensorHom R A M (target_l.lTensor (Module.Dual R A) x_l) =
                target_l.comp (dualTensorHom R A (s.stage l) x_l) := by
                  have hh := congrArg (fun q => q x_l)
                    (dualTensorHom_comp_lTensor (R := R) (M := A)
                      (N := s.stage l) (P := M) target_l)
                  simpa [LinearMap.comp_apply] using hh
            _ = f0 := by rw [hx_l, hf0l]
            _ = dualTensorHom R A M xi := hxi.symm
        obtain ⟨q, hq⟩ := tensorProductContains_range_dual f_il
        apply hG.2
        refine ⟨target_l.lTensor (LinearMap.range f_il.dualMap) q, ?_⟩
        calc
          (LinearMap.range f_il.dualMap).subtype.rTensor M
                (target_l.lTensor (LinearMap.range f_il.dualMap) q) =
              target_l.lTensor (Module.Dual R A)
                ((LinearMap.range f_il.dualMap).subtype.rTensor (s.stage l) q) := by
                  have hcomp :
                      ((LinearMap.range f_il.dualMap).subtype.rTensor M).comp
                          (target_l.lTensor (LinearMap.range f_il.dualMap)) =
                        (target_l.lTensor (Module.Dual R A)).comp
                          ((LinearMap.range f_il.dualMap).subtype.rTensor (s.stage l)) := by
                    rw [LinearMap.rTensor_comp_lTensor,
                      LinearMap.lTensor_comp_rTensor]
                  exact congrArg (fun q' => q' q) hcomp
            _ = target_l.lTensor (Module.Dual R A) x_l := by rw [hq]
            _ = xi := hxi_l
      have hcontent :
          (Module.DirectLimit.of R s.index s.stage s.map i0).lTensor
              (Module.Dual R A) x0 =
            (Module.DirectLimit.of R s.index s.stage s.map j).lTensor
              (Module.Dual R A)
                (G.subtype.rTensor (s.stage j) yj) := by
        calc
          (Module.DirectLimit.of R s.index s.stage s.map i0).lTensor
                (Module.Dual R A) x0 =
              eold.symm.toLinearMap.lTensor (Module.Dual R A) xi := hx0
          _ = eold.symm.toLinearMap.lTensor (Module.Dual R A)
                (G.subtype.rTensor M y) := by rw [hy]
          _ = G.subtype.rTensor (Module.DirectLimit s.stage s.map)
                (eold.symm.toLinearMap.lTensor (G : Type u) y) := by
                have hcomp :
                    (eold.symm.toLinearMap.lTensor (Module.Dual R A)).comp
                        (G.subtype.rTensor M) =
                      (G.subtype.rTensor (Module.DirectLimit s.stage s.map)).comp
                        (eold.symm.toLinearMap.lTensor (G : Type u)) := by
                  rw [LinearMap.lTensor_comp_rTensor,
                    LinearMap.rTensor_comp_lTensor]
                exact congrArg (fun q => q y) hcomp
          _ = G.subtype.rTensor (Module.DirectLimit s.stage s.map) yold := by
                rfl
          _ = G.subtype.rTensor (Module.DirectLimit s.stage s.map)
                ((Module.DirectLimit.of R s.index s.stage s.map j).lTensor
                  (G : Type u) yj) := by rw [hyj]
          _ = (Module.DirectLimit.of R s.index s.stage s.map j).lTensor
                (Module.Dual R A) (G.subtype.rTensor (s.stage j) yj) := by
                have hcomp :
                    (G.subtype.rTensor (Module.DirectLimit s.stage s.map)).comp
                        ((Module.DirectLimit.of R s.index s.stage s.map j).lTensor
                          (G : Type u)) =
                      ((Module.DirectLimit.of R s.index s.stage s.map j).lTensor
                          (Module.Dual R A)).comp
                        (G.subtype.rTensor (s.stage j)) := by
                  rw [LinearMap.rTensor_comp_lTensor,
                    LinearMap.lTensor_comp_rTensor]
                exact congrArg (fun q => q yj) hcomp
      obtain ⟨k, hik, hjk, hstage⟩ :=
        tensorProduct_eq_of_moduleDirectLimit s.map x0
          (G.subtype.rTensor (s.stage j) yj) hcontent
      let f_ik : s.stage i0 →ₗ[R] s.stage k := s.map i0 k hik
      let x_k : TensorProduct R (Module.Dual R A) (s.stage k) :=
        (dualTensorHomEquiv R A (s.stage k)).symm f_ik
      have hx0fun : dualTensorHom R A A x0 = LinearMap.id := by
        have he_A : (dualTensorHomEquiv R A A).toLinearMap =
            dualTensorHom R A A := rfl
        rw [← he_A]
        exact (dualTensorHomEquiv R A A).apply_symm_apply LinearMap.id
      have he_k : (dualTensorHomEquiv R A (s.stage k)).toLinearMap =
          dualTensorHom R A (s.stage k) := rfl
      have hx_k : dualTensorHom R A (s.stage k) x_k = f_ik := by
        rw [← he_k]
        exact (dualTensorHomEquiv R A (s.stage k)).apply_symm_apply f_ik
      have hx0_k : (s.map i0 k hik).lTensor (Module.Dual R A) x0 = x_k := by
        apply (dualTensorHomEquiv R A (s.stage k)).injective
        rw [← LinearEquiv.coe_toLinearMap, he_k]
        calc
          dualTensorHom R A (s.stage k)
                ((s.map i0 k hik).lTensor (Module.Dual R A) x0) =
              (s.map i0 k hik).comp (dualTensorHom R A A x0) := by
                have hh := congrArg (fun q => q x0)
                  (dualTensorHom_comp_lTensor (R := R) (M := A)
                    (N := A) (P := s.stage k) (s.map i0 k hik))
                simpa [LinearMap.comp_apply] using hh
          _ = f_ik := by rw [hx0fun]; simp [f_ik]
          _ = dualTensorHom R A (s.stage k) x_k := hx_k.symm
      let zG : TensorProduct R (G : Type u) (s.stage k) :=
        (s.map j k hjk).lTensor (G : Type u) yj
      have hfactor : G.subtype.rTensor (s.stage k) zG = x_k := by
        calc
          G.subtype.rTensor (s.stage k) zG =
              (s.map j k hjk).lTensor (Module.Dual R A)
                (G.subtype.rTensor (s.stage j) yj) := by
                have hcomp :
                    (G.subtype.rTensor (s.stage k)).comp
                        ((s.map j k hjk).lTensor (G : Type u)) =
                      ((s.map j k hjk).lTensor (Module.Dual R A)).comp
                        (G.subtype.rTensor (s.stage j)) := by
                  rw [LinearMap.rTensor_comp_lTensor,
                    LinearMap.lTensor_comp_rTensor]
                exact congrArg (fun q => q yj) hcomp
          _ = (s.map i0 k hik).lTensor (Module.Dual R A) x0 := hstage.symm
          _ = x_k := hx0_k
      have hrangeG :
          LinearMap.range f_ik.dualMap ≤ G := by
        apply range_dual_le_of_tensorProductContains
        refine ⟨zG, ?_⟩
        exact hfactor
      let f : (Opposite.op k : s.indexᵒᵖ) ⟶ i :=
        (CategoryTheory.homOfLE hik).op
      refine ⟨Opposite.op k, f, ?_⟩
      intro l g
      let l0 : s.index := l.unop
      have hkl : k ≤ l0 := g.unop.le
      have hil : i0 ≤ l0 := hik.trans hkl
      have hG_l := hG_le_range l0 hil
      intro z hz
      obtain ⟨φ, rfl⟩ := hz
      change φ.comp f_ik ∈ Set.range (fun ψ : Module.Dual R (s.stage l0) =>
        ψ.comp (s.map i0 l0 hil))
      apply hG_l
      apply hrangeG
      exact ⟨φ, rfl⟩
    exact isMittagLefflerModule_of_flat_of_dualSystem P hflat
      (fun i => s.free i) (fun i => s.finite i) hdual

/-! ## Products and power series -/

/-- A product of copies of a Noetherian ring is flat and Mittag-Leffler. -/
theorem modulePower_is_flat_and_mittagLeffler
    (R : Type u) [CommRing R] [IsNoetherianRing R] (A : Type v) :
    Module.Flat R (modulePower R A) ∧
      IsMittagLefflerModule (ModuleCat.of R (modulePower R A)) := by
  sorry

/-- Multivariate formal power series over a Noetherian ring are flat and
Mittag-Leffler as modules over the coefficient ring. -/
theorem mvPowerSeries_is_flat_and_mittagLeffler
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (n : ℕ) (hn : 0 < n) :
    Module.Flat R (MvPowerSeries (Fin n) R) ∧
      IsMittagLefflerModule
        (ModuleCat.of R (MvPowerSeries (Fin n) R)) := by
  sorry

/-! ## Non-examples -/

/- The first non-example reuses the rational module and the failed injectivity
   statement from Chapter 89. -/

/-- The rational numbers are not a Mittag-Leffler `ℤ`-module. -/
theorem rationalModule_not_mittagLeffler :
    ¬ IsMittagLefflerModule rationalModule := by
  sorry

/-- A flat, countably generated, non-projective module is not Mittag-Leffler.
This is the implication used in the second non-example. -/
theorem flat_countablyGenerated_nonprojective_not_mittagLeffler
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (hflat : Module.Flat R M)
    (hcountable : Module.IsCountablyGenerated R M)
    (hprojective : ¬ Module.Projective R M) :
    ¬ IsMittagLefflerModule (ModuleCat.of R M) := by
  sorry

/-! ### Quotients and annihilators -/

/-- The quotient of a module by `I M`, expressed using the canonical
submodule quotient. -/
abbrev moduleQuotientByIdeal
    {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) : Type u :=
  M ⧸ (I • (⊤ : Submodule R M))

/-- The canonical class of an element in a quotient by `I M`. -/
def moduleQuotientElement
    {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (m : M) :
  moduleQuotientByIdeal (R := R) (M := M) I :=
  (I • (⊤ : Submodule R M)).mkQ m

/-- The scalar annihilator of an element after quotienting a module by `I M`. -/
def elementAnnihilatorModuloIdeal
    {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (m : M) : Ideal R :=
  (Submodule.span R
    ({moduleQuotientElement (R := R) (M := M) I m} :
      Set (moduleQuotientByIdeal (R := R) (M := M) I))).annihilator

/-! ### The product of power-series quotients -/

/-- The principal ideal `(x)` in the one-variable power-series ring `k[[x]]`. -/
def powerSeriesXIdeal (k : Type u) [Field k] : Ideal (PowerSeries k) :=
  Ideal.span {(PowerSeries.X : PowerSeries k)}

/-- The family of quotients `k[[x]]/(x^n)`, indexed by positive integers. -/
abbrev powerSeriesQuotientFamily (k : Type u) [Field k] (n : ℕ+) :
    ModuleCat.{u} (PowerSeries k) :=
  ModuleCat.of (PowerSeries k)
    (PowerSeries k ⧸ (powerSeriesXIdeal k) ^ (n : ℕ))

/-- The product `∏ₙ k[[x]]/(x^n)` from the third non-example. -/
abbrev powerSeriesTorsionProduct (k : Type u) [Field k] : Type u :=
  ∀ n : ℕ+, (powerSeriesQuotientFamily k n : Type u)

/-- The positive natural number `2^m`. -/
def positivePowOfTwo (m : ℕ) : ℕ+ :=
  ⟨2 ^ m, Nat.pow_pos (by decide)⟩

/-- The displayed element `ξ`, with `ξ_(2^m) = x^(2^(m-1))` for positive
`m` and zero at the other coordinates. -/
noncomputable def powerSeriesXiCoordinate
    (k : Type u) [Field k] (n : ℕ+) :
    (powerSeriesQuotientFamily k n : Type u) := by
  classical
  exact if h : ∃ m : ℕ, 1 ≤ m ∧ (n : ℕ) = 2 ^ m then
    Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (n : ℕ))
      ((PowerSeries.X : PowerSeries k) ^
        (2 ^ (Classical.choose h - 1)))
  else 0

/-- The element used to witness failure of the Mittag-Leffler condition. -/
noncomputable def powerSeriesXi (k : Type u) [Field k] :
    powerSeriesTorsionProduct k :=
  fun n => powerSeriesXiCoordinate k n

/-- At the powers of two, `ξ` has the displayed coordinates. -/
theorem powerSeriesXi_at_powerOfTwo
    (k : Type u) [Field k] (m : ℕ) (hm : 1 ≤ m) :
    powerSeriesXi k (positivePowOfTwo m) =
      Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (2 ^ m))
        ((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1))) := by
  sorry

/-- The other coordinates of `ξ` vanish. -/
theorem powerSeriesXi_eq_zero_of_not_powerOfTwo
    (k : Type u) [Field k] (n : ℕ+)
    (h : ¬ ∃ m : ℕ, 1 ≤ m ∧ (n : ℕ) = 2 ^ m) :
    powerSeriesXi k n = 0 := by
  sorry

/-- The eventual annihilator calculation for the displayed element. -/
theorem powerSeriesXi_annihilator_eventually
    (k : Type u) [Field k] :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      elementAnnihilatorModuloIdeal
          ((powerSeriesXIdeal k) ^ (2 ^ m)) (powerSeriesXi k) =
        Ideal.span
          {((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)))} := by
  sorry

/-- The finite-module approximation supplied by the first characterization of
Mittag-Leffler modules. -/
theorem finite_annihilator_approximation_of_mittagLeffler
    (k : Type u) [Field k]
    (hML : IsMittagLefflerModule
      (ModuleCat.of (PowerSeries k) (powerSeriesTorsionProduct k))) :
    ∃ Q : ModuleCat.{u} (PowerSeries k),
      Module.Finite (PowerSeries k) (Q : Type u) ∧
        ∃ ξ' : (Q : Type u), ∀ l : ℕ, 1 ≤ l →
          elementAnnihilatorModuloIdeal
              ((powerSeriesXIdeal k) ^ l) (powerSeriesXi k) =
            elementAnnihilatorModuloIdeal
              ((powerSeriesXIdeal k) ^ l) ξ' := by
  sorry

/-- For a finite module over `k[[x]]`, the annihilator of an element in the
quotients by powers of `(x)` is eventually generated by `x^a` or by
`x^(l-a)`. -/
theorem finite_module_annihilator_eventually_principal
    (k : Type u) [Field k] (Q : ModuleCat.{u} (PowerSeries k))
    (ξ' : (Q : Type u)) (hQ : Module.Finite (PowerSeries k) (Q : Type u)) :
    ∃ a : ℕ,
      (∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l →
        elementAnnihilatorModuloIdeal
            ((powerSeriesXIdeal k) ^ l) ξ' =
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ a)}) ∨
      (∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l →
        elementAnnihilatorModuloIdeal
            ((powerSeriesXIdeal k) ^ l) ξ' =
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ (l - a))}) := by
  sorry

/-- The product `∏ₙ k[[x]]/(x^n)` is not Mittag-Leffler. -/
theorem powerSeriesTorsionProduct_not_mittagLeffler
    (k : Type u) [Field k] :
    ¬ IsMittagLefflerModule
      (ModuleCat.of (PowerSeries k) (powerSeriesTorsionProduct k)) := by
  sorry

/-! ### The adic completion of the direct sum -/

/-- The direct sum `⊕ₙ k[[x]]/(x^n)`. -/
abbrev powerSeriesTorsionDirectSum (k : Type u) [Field k] : Type u :=
  ⨁ n : ℕ+, (powerSeriesQuotientFamily k n : Type u)

/-- Its `(x)`-adic module completion. -/
abbrev powerSeriesTorsionDirectSumCompletion
    (k : Type u) [Field k] : Type u :=
  AdicCompletion (powerSeriesXIdeal k) (powerSeriesTorsionDirectSum k)

/-- The map from the completion of the direct sum to the completion of the
product induced by the canonical direct-sum inclusion. -/
def powerSeriesDirectSumCompletionToProductCompletion
    (k : Type u) [Field k] :
    powerSeriesTorsionDirectSumCompletion k →ₗ[
        AdicCompletion (powerSeriesXIdeal k) (PowerSeries k)]
      AdicCompletion (powerSeriesXIdeal k) (powerSeriesTorsionProduct k) :=
  AdicCompletion.map (powerSeriesXIdeal k)
    (DirectSum.coeFnLinearMap (PowerSeries k))

/-- The element `ξ` is represented by an element of the `(x)`-adic completion
of the direct sum. -/
theorem powerSeriesXi_lies_in_directSum_adicCompletion
    (k : Type u) [Field k] :
    ∃ η : powerSeriesTorsionDirectSumCompletion k,
      powerSeriesDirectSumCompletionToProductCompletion k η =
        AdicCompletion.of (powerSeriesXIdeal k)
          (powerSeriesTorsionProduct k) (powerSeriesXi k) := by
  sorry

/-- The `(x)`-adic completion of the direct sum is not Mittag-Leffler. -/
theorem powerSeriesTorsionDirectSumCompletion_not_mittagLeffler
    (k : Type u) [Field k] :
    ¬ IsMittagLefflerModule
      (ModuleCat.of (PowerSeries k) (powerSeriesTorsionDirectSumCompletion k)) := by
  sorry

/-! ### The Artinian-local example -/

/-- The polynomial ring in the two variables `a` and `b`. -/
abbrev artinianLocalExamplePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

/-- The ideal `(a^2, ab, b^2)`. -/
def artinianLocalExampleRelationIdeal (k : Type u) [Field k] :
    Ideal (artinianLocalExamplePolynomialRing k) :=
  Ideal.span
    {MvPolynomial.X (0 : Fin 2) ^ 2,
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2),
      MvPolynomial.X (1 : Fin 2) ^ 2}

/-- The Artinian local ring `k[a,b]/(a^2,ab,b^2)`. -/
abbrev artinianLocalExampleBaseRing (k : Type u) [Field k] :=
  artinianLocalExamplePolynomialRing k ⧸ artinianLocalExampleRelationIdeal k

/-- The residue classes of `a` and `b`. -/
def artinianLocalExampleA (k : Type u) [Field k] :
    artinianLocalExampleBaseRing k :=
  Ideal.Quotient.mk (artinianLocalExampleRelationIdeal k)
    (MvPolynomial.X (0 : Fin 2))

def artinianLocalExampleB (k : Type u) [Field k] :
    artinianLocalExampleBaseRing k :=
  Ideal.Quotient.mk (artinianLocalExampleRelationIdeal k)
    (MvPolynomial.X (1 : Fin 2))

/-- The polynomial relation `at-b`. -/
def artinianLocalExamplePolynomialRelation (k : Type u) [Field k] :
    Polynomial (artinianLocalExampleBaseRing k) :=
  Polynomial.C (artinianLocalExampleA k) * Polynomial.X -
    Polynomial.C (artinianLocalExampleB k)

/-- The relation ideal `(at-b)` in the polynomial ring over the base ring. -/
def artinianLocalExamplePolynomialRelationIdeal (k : Type u) [Field k] :
    Ideal (Polynomial (artinianLocalExampleBaseRing k)) :=
  Ideal.span {artinianLocalExamplePolynomialRelation k}

/-- The finitely presented algebra `S = R[t]/(at-b)`. -/
abbrev artinianLocalExampleAlgebra (k : Type u) [Field k] :=
  AdjoinRoot (artinianLocalExamplePolynomialRelation k)

/-- The algebra in the final non-example, viewed as an `R`-module. -/
abbrev artinianLocalExampleModule (k : Type u) [Field k] :
    ModuleCat.{u} (artinianLocalExampleBaseRing k) :=
  ModuleCat.of (artinianLocalExampleBaseRing k)
    (artinianLocalExampleAlgebra k)

/-- The displayed algebra is finitely presented over its base ring. -/
theorem artinianLocalExample_finitePresentation
    (k : Type u) [Field k] :
    Algebra.FinitePresentation (artinianLocalExampleBaseRing k)
      (artinianLocalExampleAlgebra k) := by
  sorry

/-- The displayed algebra is countably generated as a module. -/
theorem artinianLocalExample_countablyGenerated
    (k : Type u) [Field k] :
    Module.IsCountablyGenerated (artinianLocalExampleBaseRing k)
      (artinianLocalExampleAlgebra k) := by
  sorry

/-- The displayed module is indecomposable. -/
theorem artinianLocalExample_indecomposable
    (k : Type u) [Field k] :
    Indecomposable (artinianLocalExampleModule k) := by
  sorry

/-- The displayed module is not finitely generated.  This implicit fact is
needed to turn the direct-sum conclusion into the source's non-example. -/
theorem artinianLocalExample_not_finite
    (k : Type u) [Field k] :
    ¬ Module.Finite (artinianLocalExampleBaseRing k)
      (artinianLocalExampleAlgebra k) := by
  sorry

/-- The base ring is Artinian. -/
theorem artinianLocalExample_baseRing_isArtinian
    (k : Type u) [Field k] :
    IsArtinianRing (artinianLocalExampleBaseRing k) := by
  sorry

/-- The base ring is local. -/
theorem artinianLocalExample_baseRing_isLocal
    (k : Type u) [Field k] :
    IsLocalRing (artinianLocalExampleBaseRing k) := by
  sorry

/-- The base ring is complete at its maximal ideal. -/
theorem artinianLocalExample_baseRing_isComplete
    (k : Type u) [Field k] :
    letI : IsLocalRing (artinianLocalExampleBaseRing k) :=
      artinianLocalExample_baseRing_isLocal k
    IsAdicComplete
      (IsLocalRing.maximalIdeal (artinianLocalExampleBaseRing k))
      (artinianLocalExampleBaseRing k) := by
  sorry

/-- The base ring is henselian local. -/
theorem artinianLocalExample_baseRing_isHenselianLocal
    (k : Type u) [Field k] :
    HenselianLocalRing (artinianLocalExampleBaseRing k) := by
  sorry

/- The source's forward reference to `lemma-split-ML-henselian` is exposed as
   a small, named interface because the later source lemma is not an earlier
   chapter dependency. -/

/-- A countably generated Mittag-Leffler module over a henselian local ring is
a direct sum of finitely presented modules. -/
def IsDirectSumOfFinitelyPresentedModules
    (R : Type u) [CommRing R] (M : ModuleCat.{v} R) : Prop :=
  ∃ (ι : Type v) (N : ι → ModuleCat.{v} R),
    (∀ i, Module.FinitePresentation R (N i : Type v)) ∧
      Nonempty ((M : Type v) ≃ₗ[R] (⨁ i, (N i : Type v)))

theorem split_mittagLeffler_over_henselian_local
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    (M : ModuleCat.{v} R)
    (hcountable : Module.IsCountablyGenerated R (M : Type v))
    (hML : IsMittagLefflerModule M) :
    IsDirectSumOfFinitelyPresentedModules R M := by
  sorry

/-- In the final example, Mittag-Lefflerness would force the forbidden direct
sum decomposition. -/
theorem artinianLocalExample_mittagLeffler_implies_directSum
    (k : Type u) [Field k]
    (hML : IsMittagLefflerModule (artinianLocalExampleModule k)) :
    IsDirectSumOfFinitelyPresentedModules
      (artinianLocalExampleBaseRing k) (artinianLocalExampleModule k) := by
  sorry

/-- The finitely presented algebra in the final non-example is not
Mittag-Leffler as a module over the Artinian local base ring. -/
theorem artinianLocalExample_not_mittagLeffler
    (k : Type u) [Field k] :
    ¬ IsMittagLefflerModule (artinianLocalExampleModule k) := by
  sorry

end

end Formalization.Books.Algebra.Unit91
