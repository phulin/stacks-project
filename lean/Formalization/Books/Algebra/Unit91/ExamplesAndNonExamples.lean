import Formalization.Books.Algebra.Unit81.CharacterizingFlatness
import Formalization.Books.Algebra.Unit84.TransfiniteDevissage
import Formalization.Books.Algebra.Unit89.InterchangingDirectProductsWithTensor
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
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
    have hinj : ∀ (A : Type (max u v)) (Q : A → ModuleCat.{max u v} R),
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
      ∀ (A : Type (max u v)) (Q : A → ModuleCat.{max u v} R),
        Function.Injective (productTensorMap M Q) :=
    (mittagLeffler_tensor_iff M).out 0 1
  apply hcrit.mpr
  intro A Q
  have hFcrit : ∀ (A : Type (max u v)) (Q : A → ModuleCat.{max u v} R),
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

private theorem modulePower_is_flat_of_isNoetherianRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] (A : Type v) :
    Module.Flat R (modulePower R A) := by
  let A' : Type (max u v) := ULift.{u} A
  have hflat' : Module.Flat R (modulePower R A') := by
    rw [Module.Flat.iff_rTensor_injective]
    intro I hI
    let P : ModuleCat.{u} R := ModuleCat.of R (I : Type u)
    let : Module.Finite R (I : Type u) := Module.Finite.of_fg hI
    have hP : Module.FinitePresentation R (P : Type u) :=
      Module.finitePresentation_of_finite R (I : Type u)
    have hcrit :
        Module.FinitePresentation R (P : Type u) ↔
          ∀ B : Type (max u v), Function.Bijective
            (tensorModulePowerMap P (A := B)) :=
      (finite_presentation_tensor_iff.{u, v, u, u} P).out 0 3
        (a := Module.FinitePresentation R (P : Type u))
        (b := ∀ B : Type (max u v), Function.Bijective
          (tensorModulePowerMap P (A := B)))
    have hbij : Function.Bijective
        (tensorModulePowerMap P (A := A')) := hcrit.mp hP A'
    have hnat
        (z : TensorProduct R (I : Type u) (modulePower R A')) (a : A') :
        (TensorProduct.lid R (modulePower R A'))
            (I.subtype.rTensor (modulePower R A') z) a =
          I.subtype ((tensorModulePowerMap P (A := A') z) a) := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul i q => simp [tensorModulePowerMap, productTensorMap, mul_comm]
      | add x y hx hy => simp [map_add, hx, hy]
    intro x y hxy
    apply hbij.1
    funext a
    apply I.subtype_injective
    have hxy' :
        (TensorProduct.lid R (modulePower R A'))
            (I.subtype.rTensor (modulePower R A') x) =
          (TensorProduct.lid R (modulePower R A'))
            (I.subtype.rTensor (modulePower R A') y) :=
      congrArg (TensorProduct.lid R (modulePower R A')) hxy
    have hcoord := congrFun hxy' a
    rw [hnat x a, hnat y a] at hcoord
    exact hcoord
  let : Module.Flat R (modulePower R A') := hflat'
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.piCongrLeft (R := R) (φ := fun _ : A => R)
      (Equiv.ulift : A' ≃ A)).symm

private theorem isMittagLefflerModule_of_linearEquiv
    {R : Type u} [CommRing R] {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N)
    (hM : IsMittagLefflerModule (ModuleCat.of R M)) :
    IsMittagLefflerModule (ModuleCat.of R N) := by
  intro P hP f
  obtain ⟨Q, hQ, g, hmut⟩ := hM P hP (e.symm.toLinearMap.comp f)
  refine ⟨Q, hQ, g, ?_⟩
  constructor
  · intro X _ _ z hz
    apply hmut.1 X
    apply LinearMap.mem_ker.mpr
    rw [LinearMap.rTensor_comp_apply]
    simp [LinearMap.mem_ker.mp hz]
  · intro X _ _ z hz
    have hz' := hmut.2 X (LinearMap.mem_ker.mpr hz)
    apply LinearMap.mem_ker.mpr
    apply (LinearEquiv.rTensor X e.symm).injective
    have hz'' : (e.symm.toLinearMap.rTensor X) ((f.rTensor X) z) = 0 := by
      rw [← LinearMap.rTensor_comp_apply]
      exact LinearMap.mem_ker.mp hz'
    exact hz''

private theorem modulePower_is_mittagLeffler_sameUniverse
    (R : Type u) [CommRing R] [IsNoetherianRing R] (A : Type u) :
    IsMittagLefflerModule (ModuleCat.of R (modulePower R A)) := by
  have hflat : Module.Flat R (modulePower R A) :=
    modulePower_is_flat_of_isNoetherianRing R A
  apply (flat_isMittagLeffler_iff_minimal_tensor_submodule hflat).mpr
  intro F _ _ hfree hfinite x
  let : Module.Free R F := hfree
  let : Module.Finite R F := hfinite
  let : Module.Projective R F := Module.Projective.of_free
  have hFfp : Module.FinitePresentation R F :=
    Module.finitePresentation_of_projective R F
  have hcritF :
      Module.FinitePresentation R F ↔
        ∀ B : Type u, Function.Bijective
          (tensorModulePowerMap (ModuleCat.of R F) (A := B)) :=
    (finite_presentation_tensor_iff.{u, u, u, u} (ModuleCat.of R F)).out 0 3
      (a := Module.FinitePresentation R F)
      (b := ∀ B : Type u, Function.Bijective
        (tensorModulePowerMap (ModuleCat.of R F) (A := B)))
  have hbijF : Function.Bijective
      (tensorModulePowerMap (ModuleCat.of R F) (A := A)) := hcritF.mp hFfp A
  have hnat (G : Submodule R F)
      (y : TensorProduct R (G : Type u) (modulePower R A)) :
      tensorModulePowerMap (ModuleCat.of R F) (A := A)
          (G.subtype.rTensor (modulePower R A) y) =
        fun a => G.subtype
          (tensorModulePowerMap (ModuleCat.of R G) (A := A) y a) := by
    induction y using TensorProduct.induction_on with
    | zero => ext a; simp
    | tmul g q => ext a; simp [tensorModulePowerMap, productTensorMap]
    | add y z hy hz => ext a; simp [map_add, hy, hz]
  let coords : A → F := fun a =>
    tensorModulePowerMap (ModuleCat.of R F) (A := A) x a
  have hcontains (G : Submodule R F) :
      tensorProductContains G x ↔ ∀ a, coords a ∈ G := by
    constructor
    · rintro ⟨y, hy⟩ a
      have hya := congrFun (hnat G y) a
      rw [hy] at hya
      have hcoords : coords a = G.subtype
          (tensorModulePowerMap (ModuleCat.of R G) (A := A) y a) := by
        simpa [coords] using hya
      rw [hcoords]
      exact (tensorModulePowerMap (ModuleCat.of R G) (A := A) y a).property
    · intro hG
      have hGfinite : Module.Finite R (G : Type u) := by
        let : Module.Finite R F := hfinite
        have hFnoeth : IsNoetherian R F :=
          isNoetherian_of_isNoetherianRing_of_finite R F
        have hGnoeth : IsNoetherian R (G : Type u) :=
          isNoetherian_of_submodule_of_noetherian R F G hFnoeth
        exact ⟨hGnoeth.noetherian ⊤⟩
      let : Module.Finite R (G : Type u) := hGfinite
      have hGfp : Module.FinitePresentation R (G : Type u) :=
        Module.finitePresentation_of_finite R (G : Type u)
      have hcritG :
          Module.FinitePresentation R (G : Type u) ↔
            ∀ B : Type u, Function.Bijective
              (tensorModulePowerMap (ModuleCat.of R G) (A := B)) :=
        (finite_presentation_tensor_iff.{u, u, u, u} (ModuleCat.of R G)).out 0 3
          (a := Module.FinitePresentation R (G : Type u))
          (b := ∀ B : Type u, Function.Bijective
            (tensorModulePowerMap (ModuleCat.of R G) (A := B)))
      have hbijG : Function.Bijective
          (tensorModulePowerMap (ModuleCat.of R G) (A := A)) := hcritG.mp hGfp A
      let coordsG : A → G := fun a => ⟨coords a, hG a⟩
      obtain ⟨y, hy⟩ := hbijG.2 coordsG
      refine ⟨y, ?_⟩
      apply hbijF.1
      funext a
      calc
        tensorModulePowerMap (ModuleCat.of R F) (A := A)
              (G.subtype.rTensor (modulePower R A) y) a =
            G.subtype (tensorModulePowerMap (ModuleCat.of R G) (A := A) y a) :=
          congrFun (hnat G y) a
        _ = coords a := by rw [congrFun hy a]; rfl
  let F' : Submodule R F := Submodule.span R (Set.range coords)
  refine ⟨F', ?_⟩
  constructor
  · apply (hcontains F').mpr
    intro a
    exact Submodule.subset_span ⟨a, rfl⟩
  · intro G hG
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact (hcontains G).mp hG a

/-! ## Products and power series -/

/-- A product of copies of a Noetherian ring is flat and Mittag-Leffler. -/
theorem modulePower_is_flat_and_mittagLeffler
    (R : Type u) [CommRing R] [IsNoetherianRing R] (A : Type v) :
    Module.Flat R (modulePower R A) ∧
      IsMittagLefflerModule (ModuleCat.of R (modulePower R A)) := by
  have hflat : Module.Flat R (modulePower R A) :=
    modulePower_is_flat_of_isNoetherianRing R A
  let S : Type (max u v) := ULift.{v} R
  let A' : Type (max u v) := ULift.{u} A
  let f : R →+* S := (ULift.ringEquiv : S ≃+* R).symm.toRingHom
  let : Module R S := Module.compHom S f
  let : IsNoetherianRing S :=
    isNoetherianRing_of_ringEquiv R (ULift.ringEquiv : S ≃+* R).symm
  let eRS : R ≃ₗ[R] S :=
    (ULift.moduleEquiv (R := R) (M := R)).symm
  let : Module.Free R S :=
    Module.Free.of_equiv' (R := R) (P := R) (N := S)
      inferInstance eRS
  have hS : IsMittagLefflerModule (ModuleCat.of R S) := by
    exact isMittagLefflerModule_of_free (ModuleCat.of R S) inferInstance
  have hflatS : Module.Flat S (modulePower S A') :=
    modulePower_is_flat_of_isNoetherianRing S A'
  have hML' : IsMittagLefflerModule
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S (modulePower S A'))) :=
    flat_mittagLeffler_of_mittagLeffler_restrictScalars f
      (ModuleCat.of S (modulePower S A')) hS hflatS
      (modulePower_is_mittagLeffler_sameUniverse S A')
  let eIndex : (modulePower S A') ≃ₗ[R] (A → S) :=
    LinearEquiv.piCongrLeft (R := R) (φ := fun _ : A => S)
      (Equiv.ulift : A' ≃ A)
  let ePoint : (A → S) ≃ₗ[R] (A → R) :=
    LinearEquiv.piCongrRight (fun _ => (ULift.moduleEquiv (R := R) (M := R)))
  have hML : IsMittagLefflerModule (ModuleCat.of R (modulePower R A)) := by
    apply isMittagLefflerModule_of_linearEquiv (eIndex.trans ePoint)
    exact hML'
  exact ⟨hflat, hML⟩

/-- Multivariate formal power series over a Noetherian ring are flat and
Mittag-Leffler as modules over the coefficient ring. -/
theorem mvPowerSeries_is_flat_and_mittagLeffler
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (n : ℕ) (_hn : 0 < n) :
    Module.Flat R (MvPowerSeries (Fin n) R) ∧
      IsMittagLefflerModule
        (ModuleCat.of R (MvPowerSeries (Fin n) R)) := by
  change Module.Flat R ((Fin n →₀ ℕ) → R) ∧
    IsMittagLefflerModule (ModuleCat.of R ((Fin n →₀ ℕ) → R))
  exact modulePower_is_flat_and_mittagLeffler R (Fin n →₀ ℕ)

/-! ## Non-examples -/

/- The first non-example reuses the rational module and the failed injectivity
   statement from Chapter 89. -/

/-- The rational numbers are not a Mittag-Leffler `ℤ`-module. -/
theorem rationalModule_not_mittagLeffler :
    ¬ IsMittagLefflerModule rationalModule := by
  intro hML
  have hinj : ∀ (A : Type) (Q : A → ModuleCat ℤ),
      Function.Injective (productTensorMap rationalModule Q) :=
    (mittagLeffler_tensor_iff rationalModule).out 0 1 |>.mp hML
  exact rationalQuotientTensorMap_not_injective
    (hinj ℕ+ integerQuotientFamily)

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
  classical
  let n : ℕ+ := positivePowOfTwo m
  have hn : (n : ℕ) = 2 ^ m := rfl
  have h : ∃ j : ℕ, 1 ≤ j ∧ (n : ℕ) = 2 ^ j := ⟨m, hm, hn⟩
  change powerSeriesXiCoordinate k n = _
  simp only [powerSeriesXiCoordinate, dif_pos h]
  have hc : Classical.choose h = m := by
    apply (Nat.pow_right_injective (by decide : 2 ≤ 2))
    exact ((Classical.choose_spec h).2).symm.trans hn
  rw [hc]
  congr 1

/-- The other coordinates of `ξ` vanish. -/
theorem powerSeriesXi_eq_zero_of_not_powerOfTwo
    (k : Type u) [Field k] (n : ℕ+)
    (h : ¬ ∃ m : ℕ, 1 ≤ m ∧ (n : ℕ) = 2 ^ m) :
    powerSeriesXi k n = 0 := by
  classical
  unfold powerSeriesXi
  simp [powerSeriesXiCoordinate, h]

/-- The eventual annihilator calculation for the displayed element. -/
theorem powerSeriesXi_annihilator_eventually
    (k : Type u) [Field k] :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      elementAnnihilatorModuloIdeal
          ((powerSeriesXIdeal k) ^ (2 ^ m)) (powerSeriesXi k) =
        Ideal.span
          {((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)))} := by
  classical
  exact ⟨(1 : ℕ), by
    intro m hm
    ext r
    rw [elementAnnihilatorModuloIdeal,
      Submodule.mem_annihilator_span_singleton]
    unfold moduleQuotientElement
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp [powerSeriesXIdeal, Ideal.span_singleton_pow]
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    have hxi : powerSeriesXi k (positivePowOfTwo m) =
        Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (positivePowOfTwo m : ℕ))
          ((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1))) := by
      let n : ℕ+ := positivePowOfTwo m
      have hn : (n : ℕ) = 2 ^ m := rfl
      have h : ∃ j : ℕ, 1 ≤ j ∧ (n : ℕ) = 2 ^ j := ⟨m, hm, hn⟩
      change powerSeriesXiCoordinate k n = _
      simp only [powerSeriesXiCoordinate, dif_pos h]
      have hc : Classical.choose h = m := by
        apply (Nat.pow_right_injective (by decide : 2 ≤ 2))
        exact ((Classical.choose_spec h).2).symm.trans hn
      rw [hc]
    constructor
    · rintro ⟨q, hq⟩
      have hcoord := congrFun hq (positivePowOfTwo m)
      simp only [Pi.smul_apply, Pi.mul_apply] at hcoord
      change r • (powerSeriesXi k (positivePowOfTwo m)) = _ at hcoord
      rw [hxi] at hcoord
      change Ideal.Quotient.mk ((powerSeriesXIdeal k) ^
          (positivePowOfTwo m : ℕ))
        (r * (PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1))) = _ at hcoord
      have hmk : Ideal.Quotient.mk ((powerSeriesXIdeal k) ^
          (positivePowOfTwo m : ℕ))
          ((PowerSeries.X : PowerSeries k) ^ (2 ^ m)) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem]
        rw [show (powerSeriesXIdeal k) ^ (positivePowOfTwo m : ℕ) =
          Ideal.span {((PowerSeries.X : PowerSeries k) ^
            (positivePowOfTwo m : ℕ))} by
            simp [powerSeriesXIdeal, Ideal.span_singleton_pow]]
        apply Ideal.subset_span
        simp [positivePowOfTwo]
      simp [hmk] at hcoord
      change Ideal.Quotient.mk ((powerSeriesXIdeal k) ^
          (positivePowOfTwo m : ℕ))
        (r * (PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1))) = 0 at hcoord
      rw [Ideal.Quotient.eq_zero_iff_mem] at hcoord
      rw [show (powerSeriesXIdeal k) ^ (positivePowOfTwo m : ℕ) =
        Ideal.span {((PowerSeries.X : PowerSeries k) ^
          (positivePowOfTwo m : ℕ))} by
          simp [powerSeriesXIdeal, Ideal.span_singleton_pow]] at hcoord
      rw [Ideal.mem_span_singleton] at hcoord
      have hcoord' : (PowerSeries.X : PowerSeries k) ^ (2 ^ m) ∣
          r * (PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)) := by
        simpa [positivePowOfTwo] using hcoord
      rcases hcoord' with ⟨s, hs⟩
      refine ⟨s, ?_⟩
      have hpow : 2 ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
        rw [show m = (m - 1) + 1 by omega, pow_succ]
        simp [Nat.mul_two]
      apply (PowerSeries.X_pow_mul_cancel (k := 2 ^ (m - 1)))
      calc
        (PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)) * r =
            r * (PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)) := by
              rw [mul_comm]
        _ = (PowerSeries.X : PowerSeries k) ^ (2 ^ m) * s := hs
        _ = ((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)) *
            (PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1))) * s := by
              rw [← pow_add, hpow]
        _ = (PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)) *
            ((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)) * s) := by
              simp [mul_assoc]
    · intro hdiv
      rcases hdiv with ⟨s, hs⟩
      let q : powerSeriesTorsionProduct k := fun n =>
        if hn : ∃ j : ℕ, 1 ≤ j ∧ m ≤ j ∧ (n : ℕ) = 2 ^ j then
          Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (n : ℕ))
            ((PowerSeries.X : PowerSeries k) ^
              (2 ^ (Classical.choose hn - 1) - 2 ^ (m - 1)) * s)
        else 0
      refine ⟨q, ?_⟩
      funext n
      simp only [Pi.smul_apply, Pi.mul_apply]
      by_cases hpow : ∃ j : ℕ, 1 ≤ j ∧ (n : ℕ) = 2 ^ j
      · obtain ⟨j, hj, hjn⟩ := hpow
        have hpow0 : ∃ l : ℕ, 1 ≤ l ∧ (n : ℕ) = 2 ^ l :=
          ⟨j, hj, hjn⟩
        have hxi_n : powerSeriesXi k n =
            Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (n : ℕ))
              ((PowerSeries.X : PowerSeries k) ^ (2 ^ (j - 1))) := by
          unfold powerSeriesXi
          simp only [powerSeriesXiCoordinate, dif_pos hpow0]
          have hc : Classical.choose hpow0 = j := by
            apply (Nat.pow_right_injective (by decide : 2 ≤ 2))
            exact ((Classical.choose_spec hpow0).2).symm.trans hjn
          rw [hc]
        by_cases hmj : m ≤ j
        · have hq : ∃ l : ℕ, 1 ≤ l ∧ m ≤ l ∧ (n : ℕ) = 2 ^ l :=
            ⟨j, hj, hmj, hjn⟩
          have hcq : Classical.choose hq = j := by
            apply (Nat.pow_right_injective (by decide : 2 ≤ 2))
            exact ((Classical.choose_spec hq).2.2).symm.trans hjn
          rw [hxi_n, hs]
          change Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (n : ℕ))
              ((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)) * s *
                (PowerSeries.X : PowerSeries k) ^ (2 ^ (j - 1))) = _
          simp only [q, dif_pos hq, hcq]
          change Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (n : ℕ))
              ((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)) * s *
                (PowerSeries.X : PowerSeries k) ^ (2 ^ (j - 1))) =
            Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (n : ℕ))
              ((PowerSeries.X : PowerSeries k) ^ (2 ^ m) *
                ((PowerSeries.X : PowerSeries k) ^
                  (2 ^ (j - 1) - 2 ^ (m - 1)) * s))
          congr 1
          have hba : 2 ^ (m - 1) ≤ 2 ^ (j - 1) := by
            exact Nat.pow_le_pow_right (by decide : 0 < 2)
              (Nat.sub_le_sub_right hmj 1)
          have hsum : 2 ^ (j - 1) - 2 ^ (m - 1) + 2 ^ (m - 1) =
              2 ^ (j - 1) := Nat.sub_add_cancel hba
          have hpowm : 2 ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
            rw [show m = (m - 1) + 1 by omega, pow_succ]
            simp [Nat.mul_two]
          calc
            (PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)) * s *
                (PowerSeries.X : PowerSeries k) ^ (2 ^ (j - 1)) =
                (PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)) *
                  (PowerSeries.X : PowerSeries k) ^ (2 ^ (j - 1)) * s := by
                    simp [mul_assoc, mul_comm]
            _ = (PowerSeries.X : PowerSeries k) ^
                (2 ^ (m - 1) + 2 ^ (j - 1)) * s := by
                  rw [← pow_add]
            _ = (PowerSeries.X : PowerSeries k) ^
                (2 ^ (m - 1) +
                  (2 ^ (j - 1) - 2 ^ (m - 1) + 2 ^ (m - 1))) * s := by
                  rw [hsum]
            _ = (PowerSeries.X : PowerSeries k) ^
                (2 ^ (m - 1) + 2 ^ (m - 1)) *
                  ((PowerSeries.X : PowerSeries k) ^
                    (2 ^ (j - 1) - 2 ^ (m - 1)) * s) := by
                  calc
                    (PowerSeries.X : PowerSeries k) ^
                        (2 ^ (m - 1) +
                          (2 ^ (j - 1) - 2 ^ (m - 1) + 2 ^ (m - 1))) * s =
                        ((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)) *
                          (PowerSeries.X : PowerSeries k) ^
                            (2 ^ (j - 1) - 2 ^ (m - 1)) *
                        (PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1))) * s := by
                            rw [pow_add, pow_add]
                            ac_rfl
                    _ = (PowerSeries.X : PowerSeries k) ^
                          (2 ^ (m - 1) + 2 ^ (m - 1)) *
                        ((PowerSeries.X : PowerSeries k) ^
                          (2 ^ (j - 1) - 2 ^ (m - 1)) * s) := by
                            rw [pow_add]
                            simp [mul_assoc, mul_comm, mul_left_comm]
            _ = (PowerSeries.X : PowerSeries k) ^ (2 ^ m) *
                  ((PowerSeries.X : PowerSeries k) ^
                    (2 ^ (j - 1) - 2 ^ (m - 1)) * s) := by
                  rw [hpowm]
        · have hq : ¬ ∃ l : ℕ, 1 ≤ l ∧ m ≤ l ∧ (n : ℕ) = 2 ^ l := by
            rintro ⟨l, hl, hml, hln⟩
            have hlj : l = j := by
              apply (Nat.pow_right_injective (by decide : 2 ≤ 2))
              exact hln.symm.trans hjn
            exact hmj (by simpa [hlj] using hml)
          simp only [q, dif_neg hq]
          rw [hxi_n, hs]
          simp only [mul_zero]
          change Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (n : ℕ))
              ((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)) * s *
                (PowerSeries.X : PowerSeries k) ^ (2 ^ (j - 1))) = 0
          have hlt : j < m := Nat.lt_of_not_ge hmj
          have hna : 2 ^ j ≤ 2 ^ (m - 1) := by
            exact Nat.pow_le_pow_right (by decide : 0 < 2)
              (by omega)
          have hadd : 2 ^ j + (2 ^ (m - 1) - 2 ^ j) = 2 ^ (m - 1) := by
            omega
          have hxzero : Ideal.Quotient.mk ((powerSeriesXIdeal k) ^
              (n : ℕ)) ((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1))) = 0 := by
            rw [Ideal.Quotient.eq_zero_iff_mem]
            rw [show (powerSeriesXIdeal k) ^ (n : ℕ) =
              Ideal.span {((PowerSeries.X : PowerSeries k) ^ (n : ℕ))} by
                simp [powerSeriesXIdeal, Ideal.span_singleton_pow]]
            rw [Ideal.mem_span_singleton]
            refine ⟨(PowerSeries.X : PowerSeries k) ^
                (2 ^ (m - 1) - 2 ^ j), ?_⟩
            rw [← pow_add, hjn, hadd]
          calc
            Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (n : ℕ))
                ((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)) * s *
                  (PowerSeries.X : PowerSeries k) ^ (2 ^ (j - 1))) =
                Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (n : ℕ))
                  ((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1))) *
                  Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (n : ℕ))
                    (s * (PowerSeries.X : PowerSeries k) ^ (2 ^ (j - 1))) := by
                      rw [show (PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)) * s *
                          (PowerSeries.X : PowerSeries k) ^ (2 ^ (j - 1)) =
                          (PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)) *
                            (s * (PowerSeries.X : PowerSeries k) ^ (2 ^ (j - 1))) by
                            simp [mul_assoc], map_mul]
            _ = 0 := by rw [hxzero]; simp
      · have hq : ¬ ∃ j : ℕ, 1 ≤ j ∧ m ≤ j ∧ (n : ℕ) = 2 ^ j := by
          rintro ⟨j, hj, hjm, hjn⟩
          exact hpow ⟨j, hj, hjn⟩
        have hxi0 : powerSeriesXi k n = 0 := by
          unfold powerSeriesXi
          simp [powerSeriesXiCoordinate, hpow]
        rw [hxi0]
        simp [q, hq]
  ⟩

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
  classical
  let R := PowerSeries k
  let M := powerSeriesTorsionProduct k
  let f : R →ₗ[R] M :=
    LinearMap.toSpanSingleton R M (powerSeriesXi k)
  have hRfp : Module.FinitePresentation R R :=
    Module.finitePresentation_of_projective R R
  obtain ⟨Q, hQfp, g, hmut⟩ :=
    hML (ModuleCat.of R R) hRfp f
  let _ : Module.FinitePresentation R (Q : Type u) := hQfp
  refine ⟨Q, inferInstance, g 1, ?_⟩
  intro l hl
  ext r
  rw [elementAnnihilatorModuloIdeal,
    Submodule.mem_annihilator_span_singleton,
    elementAnnihilatorModuloIdeal,
    Submodule.mem_annihilator_span_singleton]
  let X := R ⧸ (powerSeriesXIdeal k) ^ l
  let z : R ⊗[R] X := 1 ⊗ₜ[R] (Ideal.Quotient.mk _ r)
  have heM :
      (TensorProduct.tensorQuotEquivQuotSMul (M : Type u)
        ((powerSeriesXIdeal k) ^ l)) ((f.rTensor X) z) =
        r • moduleQuotientElement ((powerSeriesXIdeal k) ^ l) (powerSeriesXi k) := by
    change _ = r • ((powerSeriesXIdeal k) ^ l •
      (⊤ : Submodule R M)).mkQ (powerSeriesXi k)
    rw [show z = (1 : R) ⊗ₜ[R] (Ideal.Quotient.mk _ r) by rfl]
    rw [LinearMap.rTensor_tmul]
    rw [show f 1 = powerSeriesXi k by simp [f]]
    rw [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]
    change ((powerSeriesXIdeal k) ^ l • (⊤ : Submodule R M)).mkQ
        (r • powerSeriesXi k) =
      r • ((powerSeriesXIdeal k) ^ l • (⊤ : Submodule R M)).mkQ
        (powerSeriesXi k)
    exact ((powerSeriesXIdeal k) ^ l • (⊤ : Submodule R M)).mkQ.map_smul r
      (powerSeriesXi k)
  have heQ :
      (TensorProduct.tensorQuotEquivQuotSMul (Q : Type u)
        ((powerSeriesXIdeal k) ^ l)) ((g.rTensor X) z) =
        r • moduleQuotientElement ((powerSeriesXIdeal k) ^ l) (g 1) := by
    change _ = r • ((powerSeriesXIdeal k) ^ l •
      (⊤ : Submodule R Q)).mkQ (g 1)
    rw [show z = (1 : R) ⊗ₜ[R] (Ideal.Quotient.mk _ r) by rfl]
    rw [LinearMap.rTensor_tmul]
    rw [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]
    change ((powerSeriesXIdeal k) ^ l • (⊤ : Submodule R Q)).mkQ
        (r • g 1) =
      r • ((powerSeriesXIdeal k) ^ l • (⊤ : Submodule R Q)).mkQ (g 1)
    exact ((powerSeriesXIdeal k) ^ l • (⊤ : Submodule R Q)).mkQ.map_smul r
      (g 1)
  have hker :
      LinearMap.ker (f.rTensor X) = LinearMap.ker (g.rTensor X) :=
    le_antisymm (hmut.1 X) (hmut.2 X)
  constructor
  · intro hr
    have hzf : (f.rTensor X) z = 0 := by
      apply (TensorProduct.tensorQuotEquivQuotSMul (M : Type u)
        ((powerSeriesXIdeal k) ^ l)).injective
      rw [heM]
      exact hr
    have hzg : (g.rTensor X) z = 0 :=
      LinearMap.mem_ker.mp (hker ▸ LinearMap.mem_ker.mpr hzf)
    have hzg' := congrArg
      (TensorProduct.tensorQuotEquivQuotSMul (Q : Type u)
        ((powerSeriesXIdeal k) ^ l)) hzg
    rw [heQ] at hzg'
    exact hzg'
  · intro hr
    have hzg : (g.rTensor X) z = 0 := by
      apply (TensorProduct.tensorQuotEquivQuotSMul (Q : Type u)
        ((powerSeriesXIdeal k) ^ l)).injective
      rw [heQ]
      exact hr
    have hzf : (f.rTensor X) z = 0 :=
      LinearMap.mem_ker.mp (hker.symm ▸ LinearMap.mem_ker.mpr hzg)
    have hzf' := congrArg
      (TensorProduct.tensorQuotEquivQuotSMul (M : Type u)
        ((powerSeriesXIdeal k) ^ l)) hzf
    rw [heM] at hzf'
    exact hzf'

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
  classical
  let : Module.Finite (PowerSeries k) (Q : Type u) := hQ
  let N : Submodule (PowerSeries k) (Q : Type u) :=
    Submodule.span (PowerSeries k) ({ξ'} : Set (Q : Type u))
  have hmem : ∀ (l : ℕ) (r : PowerSeries k),
      r ∈ elementAnnihilatorModuloIdeal ((powerSeriesXIdeal k) ^ l) ξ' ↔
        r • ξ' ∈ (powerSeriesXIdeal k) ^ l •
          (⊤ : Submodule (PowerSeries k) (Q : Type u)) := by
    intro l r
    rw [elementAnnihilatorModuloIdeal,
      Submodule.mem_annihilator_span_singleton]
    unfold moduleQuotientElement
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (powerSeriesXIdeal k) N
  have hpow (n : ℕ) : (powerSeriesXIdeal k) ^ n =
      Ideal.span {((PowerSeries.X : PowerSeries k) ^ n)} := by
    simp [powerSeriesXIdeal, Ideal.span_singleton_pow]
  have hsmul (m n : ℕ) :
      (powerSeriesXIdeal k) ^ m • Ideal.span
          {((PowerSeries.X : PowerSeries k) ^ n)} =
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ (m + n))} := by
    rw [hpow m, Submodule.ideal_span_singleton_smul, Submodule.smul_span]
    simp [smul_eq_mul, ← pow_add]
  let g : PowerSeries k →ₗ[PowerSeries k] (Q : Type u) :=
    LinearMap.toSpanSingleton (PowerSeries k) (Q : Type u) ξ'
  have hg : LinearMap.range g = N := by
    exact LinearMap.range_toSpanSingleton ξ'
  let K : Submodule (PowerSeries k) (Q : Type u) :=
    (powerSeriesXIdeal k) ^ c • (⊤ : Submodule (PowerSeries k) (Q : Type u)) ⊓ N
  let A : Ideal (PowerSeries k) := Submodule.comap g K
  have hK : Submodule.map g A = K := by
    apply Submodule.map_comap_eq_of_le
    rw [hg]
    exact inf_le_right
  have hformula (t : ℕ) :
      Submodule.comap g ((powerSeriesXIdeal k) ^ t • K) =
        (powerSeriesXIdeal k) ^ t • A ⊔ LinearMap.ker g := by
    rw [← hK, ← Submodule.map_smul'']
    exact Submodule.comap_map_eq g _
  have hE (l : ℕ) :
      elementAnnihilatorModuloIdeal ((powerSeriesXIdeal k) ^ l) ξ' =
        Submodule.comap g
          ((powerSeriesXIdeal k) ^ l • (⊤ : Submodule (PowerSeries k) (Q : Type u)) ⊓ N) := by
    ext r
    rw [hmem, Submodule.mem_comap]
    constructor
    · intro hr
      exact ⟨hr, by rw [← hg]; exact LinearMap.mem_range_self g r⟩
    · intro hr
      exact hr.1
  have hEl (l : ℕ) (hl : c ≤ l) :
      elementAnnihilatorModuloIdeal ((powerSeriesXIdeal k) ^ l) ξ' =
        (powerSeriesXIdeal k) ^ (l - c) • A ⊔ LinearMap.ker g := by
    rw [hE l, hc l hl]
    exact hformula (l - c)
  have hKA : LinearMap.ker g ≤ A := by
    intro r hr
    change g r ∈ K
    rw [LinearMap.mem_ker.mp hr]
    exact K.zero_mem
  have hIcA : (powerSeriesXIdeal k) ^ c ≤ A := by
    intro r hr
    change g r ∈ K
    refine ⟨?_, ?_⟩
    · change r • ξ' ∈ (powerSeriesXIdeal k) ^ c •
        (⊤ : Submodule (PowerSeries k) (Q : Type u))
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · rw [← hg]
      exact LinearMap.mem_range_self g r
  have hXpow_nezero (n : ℕ) :
      ((PowerSeries.X : PowerSeries k) ^ n) ≠ 0 := by
    intro hz
    have := congrArg (PowerSeries.coeff n) hz
    simp at this
  have hpow_le (m n : ℕ) (hmn : n ≤ m) :
      Ideal.span {((PowerSeries.X : PowerSeries k) ^ m)} ≤
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ n)} := by
    rw [Ideal.span_singleton_le_span_singleton]
    exact pow_dvd_pow _ hmn
  have hpow_exp_le (m n : ℕ) (h :
      Ideal.span {((PowerSeries.X : PowerSeries k) ^ m)} ≤
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ n)}) : n ≤ m := by
    have hdvd : (PowerSeries.X : PowerSeries k) ^ n ∣
        (PowerSeries.X : PowerSeries k) ^ m :=
      Ideal.span_singleton_le_span_singleton.mp h
    by_contra hnm
    have hlt : m < n := Nat.lt_of_not_ge hnm
    have hz := (PowerSeries.X_pow_dvd_iff.mp hdvd) m hlt
    simp at hz
  have hAnonbot : A ≠ (⊥ : Ideal (PowerSeries k)) := by
    intro hA
    have : (powerSeriesXIdeal k) ^ c = (⊥ : Ideal (PowerSeries k)) :=
      le_antisymm (hA ▸ hIcA) bot_le
    rw [hpow c] at this
    exact hXpow_nezero c (by
      rw [← Ideal.span_singleton_eq_bot]
      exact this)
  have hX : Irreducible (PowerSeries.X : PowerSeries k) :=
    PowerSeries.X_irreducible
  by_cases hker : LinearMap.ker g = (⊥ : Ideal (PowerSeries k))
  · obtain ⟨b, hb⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      hAnonbot hX
    have hbc : b ≤ c := by
      have hIcA' := hIcA
      rw [hpow c, hb] at hIcA'
      exact hpow_exp_le c b hIcA'
    refine ⟨c - b, Or.inr ⟨c, ?_⟩⟩
    intro l hl
    rw [hEl l hl, hker, sup_bot_eq, hb, hsmul]
    congr 1
    rw [show l - (c - b) = l - c + b by omega]
  · obtain ⟨d, hd⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (show LinearMap.ker g ≠ (⊥ : Ideal (PowerSeries k)) from hker) hX
    obtain ⟨b, hb⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      hAnonbot hX
    have hbd : b ≤ d := by
      apply hpow_exp_le d b
      have hKA' := hKA
      rw [hd, hb] at hKA'
      exact hKA'
    let l₀ := c + (d - b)
    refine ⟨d, Or.inl ⟨l₀, ?_⟩⟩
    intro l hl
    have hlc : c ≤ l := by dsimp [l₀] at hl; omega
    rw [hEl l hlc, hd, hb, hsmul]
    apply sup_eq_right.mpr
    apply hpow_le
    dsimp [l₀] at hl
    have hcb : c ≤ l := by omega
    omega

/-- The product `∏ₙ k[[x]]/(x^n)` is not Mittag-Leffler. -/
theorem powerSeriesTorsionProduct_not_mittagLeffler
    (k : Type u) [Field k] :
    ¬ IsMittagLefflerModule
      (ModuleCat.of (PowerSeries k) (powerSeriesTorsionProduct k)) := by
  intro hML
  obtain ⟨Q, hQ, ξ', hξ'⟩ :=
    finite_annihilator_approximation_of_mittagLeffler k hML
  obtain ⟨a, ha | ha⟩ :=
    finite_module_annihilator_eventually_principal k Q ξ' hQ
  · obtain ⟨l₀, hl₀⟩ := ha
    obtain ⟨m₀, hm₀⟩ := powerSeriesXi_annihilator_eventually k
    have hnatpow : ∀ t : ℕ, t ≤ 2 ^ t := by
      intro t
      induction t with
      | zero => simp
      | succ t iht =>
        calc
          t + 1 ≤ 2 ^ t + 1 := Nat.succ_le_succ iht
          _ ≤ 2 ^ t * 2 := by
            nlinarith [Nat.one_le_pow t 2 (by decide : 0 < 2)]
          _ = 2 ^ (t + 1) := by rw [pow_succ]
    let m := max (max m₀ l₀) (a + 1)
    have hm₀' : m₀ ≤ m := by
      dsimp [m]
      exact (le_max_left _ _).trans (le_max_left _ _)
    have hl₀' : l₀ ≤ m := by
      dsimp [m]
      exact (le_max_right _ _).trans (le_max_left _ _)
    have hm1 : 1 ≤ m := by
      have ha1 : a + 1 ≤ m := by
        dsimp [m]
        exact le_max_right _ _
      omega
    have hlpow : l₀ ≤ 2 ^ m :=
      hl₀'.trans (hnatpow m)
    have hpowann (j : ℕ) (hj : m ≤ j) :
        elementAnnihilatorModuloIdeal
            ((powerSeriesXIdeal k) ^ (2 ^ j)) (powerSeriesXi k) =
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ (j - 1)))} :=
      hm₀ j (hm₀'.trans hj)
    have h1pow : ∀ t : ℕ, 1 ≤ 2 ^ t := by
      intro t
      exact Nat.one_le_pow t 2 (by decide : 0 < 2)
    have hspan_pow_eq : ∀ {p q : ℕ},
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ p)} =
            Ideal.span {((PowerSeries.X : PowerSeries k) ^ q)} → p = q := by
      intro p q hpq
      have hp : (PowerSeries.X : PowerSeries k) ^ q ∣
          (PowerSeries.X : PowerSeries k) ^ p := by
        rcases Ideal.mem_span_singleton.mp
          (hpq ▸ Ideal.subset_span (Set.mem_singleton _)) with ⟨s, hs⟩
        exact ⟨s, hs⟩
      have hqp : q ≤ p := by
        by_contra hnot
        have hlt : p < q := by omega
        have hc := (PowerSeries.X_pow_dvd_iff.mp hp) p hlt
        simp at hc
      have hq : (PowerSeries.X : PowerSeries k) ^ p ∣
          (PowerSeries.X : PowerSeries k) ^ q := by
        rcases Ideal.mem_span_singleton.mp
          (hpq.symm ▸ Ideal.subset_span (Set.mem_singleton _)) with ⟨s, hs⟩
        exact ⟨s, hs⟩
      have hpq' : p ≤ q := by
        by_contra hnot
        have hlt : q < p := by omega
        have hc := (PowerSeries.X_pow_dvd_iff.mp hq) q hlt
        simp at hc
      omega
    have hEq1 :
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)))} =
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ a)} := by
      exact (hpowann m (le_rfl)).symm.trans
        ((hξ' (2 ^ m) (h1pow m)).trans (hl₀ (2 ^ m) hlpow))
    have hEq2 :
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ m))} =
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ a)} := by
      have hpa :
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ m))} =
            elementAnnihilatorModuloIdeal
              ((powerSeriesXIdeal k) ^ (2 ^ (m + 1))) (powerSeriesXi k) := by
        simpa [Nat.add_sub_cancel] using (hpowann (m + 1) (by omega)).symm
      exact hpa.trans
        ((hξ' (2 ^ (m + 1)) (h1pow (m + 1))).trans
          (hl₀ (2 ^ (m + 1)) (by
            exact hl₀'.trans (le_trans (Nat.le_succ m) (hnatpow (m + 1))))))
    have heq1 := hspan_pow_eq hEq1
    have heq2 := hspan_pow_eq hEq2
    have hpowlt : 2 ^ (m - 1) < 2 ^ m := by
      exact Nat.pow_lt_pow_right (by decide : 1 < 2)
        (Nat.sub_lt (Nat.zero_lt_of_lt hm1) (by omega))
    omega
  · obtain ⟨l₀, hl₀⟩ := ha
    obtain ⟨m₀, hm₀⟩ := powerSeriesXi_annihilator_eventually k
    have hnatpow : ∀ t : ℕ, t ≤ 2 ^ t := by
      intro t
      induction t with
      | zero => simp
      | succ t iht =>
        calc
          t + 1 ≤ 2 ^ t + 1 := Nat.succ_le_succ iht
          _ ≤ 2 ^ t * 2 := by
            nlinarith [Nat.one_le_pow t 2 (by decide : 0 < 2)]
          _ = 2 ^ (t + 1) := by rw [pow_succ]
    let m := max (max m₀ l₀) (a + 1)
    have hm₀' : m₀ ≤ m := by
      dsimp [m]
      exact (le_max_left _ _).trans (le_max_left _ _)
    have hl₀' : l₀ ≤ m := by
      dsimp [m]
      exact (le_max_right _ _).trans (le_max_left _ _)
    have hm1 : 1 ≤ m := by
      have ha1 : a + 1 ≤ m := by
        dsimp [m]
        exact le_max_right _ _
      omega
    have hpowann (j : ℕ) (hj : m ≤ j) :
        elementAnnihilatorModuloIdeal
            ((powerSeriesXIdeal k) ^ (2 ^ j)) (powerSeriesXi k) =
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ (j - 1)))} :=
      hm₀ j (hm₀'.trans hj)
    have h1pow : ∀ t : ℕ, 1 ≤ 2 ^ t := by
      intro t
      exact Nat.one_le_pow t 2 (by decide : 0 < 2)
    have hEq1 :
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)))} =
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ m - a))} := by
      exact (hpowann m (le_rfl)).symm.trans
        ((hξ' (2 ^ m) (h1pow m)).trans
          (hl₀ (2 ^ m) (hl₀'.trans (hnatpow m))))
    have hEq2 :
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ m))} =
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ (m + 1) - a))} := by
      have hpa :
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ m))} =
            elementAnnihilatorModuloIdeal
              ((powerSeriesXIdeal k) ^ (2 ^ (m + 1))) (powerSeriesXi k) := by
        simpa [Nat.add_sub_cancel] using (hpowann (m + 1) (by omega)).symm
      have hbig : l₀ ≤ 2 ^ (m + 1) :=
        hl₀'.trans (le_trans (Nat.le_succ m) (hnatpow (m + 1)))
      exact hpa.trans
        ((hξ' (2 ^ (m + 1)) (h1pow (m + 1))).trans
          (hl₀ (2 ^ (m + 1)) hbig))
    have hspan_pow_eq : ∀ {p q : ℕ},
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ p)} =
            Ideal.span {((PowerSeries.X : PowerSeries k) ^ q)} → p = q := by
      intro p q hpq
      have hp : (PowerSeries.X : PowerSeries k) ^ q ∣
          (PowerSeries.X : PowerSeries k) ^ p := by
        rcases Ideal.mem_span_singleton.mp
          (hpq ▸ Ideal.subset_span (Set.mem_singleton _)) with ⟨s, hs⟩
        exact ⟨s, hs⟩
      have hqp : q ≤ p := by
        by_contra hnot
        have hlt : p < q := by omega
        have hc := (PowerSeries.X_pow_dvd_iff.mp hp) p hlt
        simp at hc
      have hq : (PowerSeries.X : PowerSeries k) ^ p ∣
          (PowerSeries.X : PowerSeries k) ^ q := by
        rcases Ideal.mem_span_singleton.mp
          (hpq.symm ▸ Ideal.subset_span (Set.mem_singleton _)) with ⟨s, hs⟩
        exact ⟨s, hs⟩
      have hpq' : p ≤ q := by
        by_contra hnot
        have hlt : q < p := by omega
        have hc := (PowerSeries.X_pow_dvd_iff.mp hq) q hlt
        simp at hc
      omega
    have heq1 := hspan_pow_eq hEq1
    have heq2 := hspan_pow_eq hEq2
    have ham : a ≤ 2 ^ (m - 1) := by
      have : a ≤ m - 1 := by dsimp [m]; omega
      exact this.trans (hnatpow (m - 1))
    have ha1 : a = 2 ^ (m - 1) := by omega
    have ha2 : a = 2 ^ m := by
      have ham' : a ≤ m := by
        have ha1' : a + 1 ≤ m := by
          dsimp [m]
          exact le_max_right _ _
        omega
      have : a ≤ 2 ^ m := ham'.trans (hnatpow m)
      omega
    have hpowlt : 2 ^ (m - 1) < 2 ^ m := by
      exact Nat.pow_lt_pow_right (by decide : 1 < 2)
        (Nat.sub_lt (Nat.zero_lt_of_lt hm1) (by omega))
    omega

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
  classical
  let I := powerSeriesXIdeal k
  let D := powerSeriesTorsionDirectSum k
  have hprincipal : ∀ {M : Type u} [AddCommGroup M] [Module (PowerSeries k) M]
      (x : PowerSeries k) (y : M),
      y ∈ (Ideal.span {x} • (⊤ : Submodule (PowerSeries k) M)) ↔
        ∃ z : M, x • z = y := by
    intro M _ _ x y
    constructor
    · intro hy
      refine Submodule.smul_induction_on hy ?_ (fun a b ha hb ↦ ?_)
      · intro r hr z hz
        rcases Ideal.mem_span_singleton.mp hr with ⟨c, hc⟩
        refine ⟨c • z, ?_⟩
        rw [hc]
        exact (smul_assoc x c z).symm
      · rcases ha with ⟨a, rfl⟩
        rcases hb with ⟨b, rfl⟩
        exact ⟨a + b, by simp⟩
    · rintro ⟨z, rfl⟩
      exact Submodule.smul_mem_smul (Submodule.subset_span (Set.mem_singleton x))
        Submodule.mem_top
  let q : ℕ → D := fun n ↦
    Finset.sum (Finset.range n) (fun m ↦
      DirectSum.of _ (positivePowOfTwo (m + 1))
        (powerSeriesXi k (positivePowOfTwo (m + 1))))
  have hq : ∀ n : ℕ, q n ≡ q (n + 1) [SMOD (I ^ n • (⊤ : Submodule (PowerSeries k) D))] := by
    intro n
    rw [show q (n + 1) = q n + DirectSum.of _ (positivePowOfTwo (n + 1))
        (powerSeriesXi k (positivePowOfTwo (n + 1))) by
      simp [q, Finset.sum_range_succ]]
    have hle : n ≤ 2 ^ n := by
      induction n with
      | zero => simp
      | succ n ih =>
        calc
          n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
          _ ≤ 2 ^ n * 2 := by
            nlinarith [Nat.one_le_pow n 2 (by decide : 0 < 2)]
          _ = 2 ^ (n + 1) := by rw [pow_succ]
    let z : (powerSeriesQuotientFamily k (positivePowOfTwo (n + 1)) : Type u) :=
      Ideal.Quotient.mk (I ^ (2 ^ (n + 1)))
        ((PowerSeries.X : PowerSeries k) ^ (2 ^ n - n))
    have hterm :
        DirectSum.of (fun n : ℕ+ => (powerSeriesQuotientFamily k n : Type u))
            (positivePowOfTwo (n + 1))
            (powerSeriesXi k (positivePowOfTwo (n + 1))) ∈
          I ^ n • (⊤ : Submodule (PowerSeries k) D) := by
      have hpow : I ^ n = Ideal.span {((PowerSeries.X : PowerSeries k) ^ n)} := by
        simp [I, powerSeriesXIdeal, Ideal.span_singleton_pow]
      rw [hpow]
      have heq :
          DirectSum.of (fun n : ℕ+ => (powerSeriesQuotientFamily k n : Type u))
              (positivePowOfTwo (n + 1))
              (powerSeriesXi k (positivePowOfTwo (n + 1))) =
            ((PowerSeries.X : PowerSeries k) ^ n) •
              DirectSum.of (fun n : ℕ+ => (powerSeriesQuotientFamily k n : Type u))
                (positivePowOfTwo (n + 1)) z := by
        rw [← DirectSum.of_smul]
        congr 1
        rw [powerSeriesXi_at_powerOfTwo k (n + 1) (by omega)]
        change (I ^ (2 ^ (n + 1))).mkQ
              ((PowerSeries.X : PowerSeries k) ^ (2 ^ (n + 1 - 1))) =
            (I ^ (2 ^ (n + 1))).mkQ
              (((PowerSeries.X : PowerSeries k) ^ n) •
                ((PowerSeries.X : PowerSeries k) ^ (2 ^ n - n)))
        congr 1
        rw [smul_eq_mul, ← pow_add]
        congr 1
        rw [show n + 1 - 1 = n by omega, Nat.add_sub_of_le hle]
      rw [heq]
      exact Submodule.smul_mem_smul (Submodule.subset_span (Set.mem_singleton _))
        Submodule.mem_top
    have htermS : DirectSum.of (fun n : ℕ+ => (powerSeriesQuotientFamily k n : Type u))
        (positivePowOfTwo (n + 1))
        (powerSeriesXi k (positivePowOfTwo (n + 1))) ≡ 0 [SMOD
          (I ^ n • (⊤ : Submodule (PowerSeries k) D))] :=
      SModEq.zero.mpr hterm
    simpa only [add_zero] using
      (SModEq.add (SModEq.refl (q n)) htermS).symm
  have hprod : ∀ (x : PowerSeries k) (v : powerSeriesTorsionProduct k),
      v ∈ (Ideal.span {x} •
        (⊤ : Submodule (PowerSeries k) (powerSeriesTorsionProduct k))) ↔
        ∀ i, v i ∈ (Ideal.span {x} •
          (⊤ : Submodule (PowerSeries k)
            (powerSeriesQuotientFamily k i : Type u))) := by
    intro x v
    constructor
    · intro hv i
      rcases (hprincipal (M := powerSeriesTorsionProduct k) x v).mp hv with ⟨z, hz⟩
      have hzi : x • z i = v i := congrFun hz i
      rw [← hzi]
      change x • z i ∈ (Ideal.span {x} •
        (⊤ : Submodule (PowerSeries k) (powerSeriesQuotientFamily k i : Type u)))
      exact Submodule.smul_mem_smul (Submodule.subset_span (Set.mem_singleton x))
        Submodule.mem_top
    · intro hv
      let z : powerSeriesTorsionProduct k := fun i ↦
        Classical.choose ((hprincipal (M := (powerSeriesQuotientFamily k i : Type u))
          x (v i)).mp (hv i))
      have hz : ∀ i, x • z i = v i := fun i ↦
        Classical.choose_spec ((hprincipal (M := (powerSeriesQuotientFamily k i : Type u))
          x (v i)).mp (hv i))
      have hev : v = x • z := by
        funext i
        exact (hz i).symm
      rw [hev]
      exact Submodule.smul_mem_smul (Submodule.subset_span (Set.mem_singleton x))
        Submodule.mem_top
  let f : AdicCompletion.AdicCauchySequence I D :=
    AdicCompletion.AdicCauchySequence.mk I D q hq
  refine ⟨AdicCompletion.mk I D f, ?_⟩
  ext n
  change (AdicCompletion.map I (DirectSum.coeFnLinearMap (PowerSeries k))
      (AdicCompletion.mk I D f)).val n =
    (I ^ n • (⊤ : Submodule (PowerSeries k) (powerSeriesTorsionProduct k))).mkQ
      (powerSeriesXi k)
  rw [AdicCompletion.map_mk]
  simp only [AdicCompletion.mk_apply_coe,
    AdicCompletion.AdicCauchySequence.map_apply_coe]
  change (I ^ n • (⊤ : Submodule (PowerSeries k)
      (powerSeriesTorsionProduct k))).mkQ
      (DirectSum.coeFnLinearMap (PowerSeries k) (q n)) =
    (I ^ n • (⊤ : Submodule (PowerSeries k)
      (powerSeriesTorsionProduct k))).mkQ (powerSeriesXi k)
  change Submodule.Quotient.mk (DirectSum.coeFnLinearMap (PowerSeries k) (q n)) =
    Submodule.Quotient.mk (powerSeriesXi k)
  apply (Submodule.Quotient.eq _).mpr
  have hpow : I ^ n = Ideal.span {((PowerSeries.X : PowerSeries k) ^ n)} := by
    simp [I, powerSeriesXIdeal, Ideal.span_singleton_pow]
  rw [hpow, hprod]
  intro i
  change q n i - powerSeriesXi k i ∈
    (Ideal.span {((PowerSeries.X : PowerSeries k) ^ n)} •
      (⊤ : Submodule (PowerSeries k)
        (powerSeriesQuotientFamily k i : Type u)))
  by_cases hiPow : ∃ m : ℕ, 1 ≤ m ∧ (i : ℕ) = 2 ^ m
  · obtain ⟨m, hm, him⟩ := hiPow
    have hxi : powerSeriesXi k i =
        Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (i : ℕ))
          ((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1))) := by
      unfold powerSeriesXi
      simp only [powerSeriesXiCoordinate, dif_pos (show ∃ j : ℕ, 1 ≤ j ∧
        (i : ℕ) = 2 ^ j from ⟨m, hm, him⟩)]
      have hc : Classical.choose (show ∃ j : ℕ, 1 ≤ j ∧
          (i : ℕ) = 2 ^ j from ⟨m, hm, him⟩) = m := by
        apply (Nat.pow_right_injective (by decide : 2 ≤ 2))
        exact ((Classical.choose_spec (show ∃ j : ℕ, 1 ≤ j ∧
          (i : ℕ) = 2 ^ j from ⟨m, hm, him⟩)).2).symm.trans him
      rw [hc]
    by_cases hmn : m ≤ n
    · have hmem : m - 1 ∈ Finset.range n := by
        apply Finset.mem_range.mpr
        exact lt_of_lt_of_le
          (Nat.sub_lt (Nat.zero_lt_of_lt hm) (by omega)) hmn
      have hqeq : q n i = powerSeriesXi k i := by
        rw [hxi]
        change (DirectSum.coeFnLinearMap (PowerSeries k)
          (Finset.sum (Finset.range n) (fun j ↦
            DirectSum.of (fun n : ℕ+ => (powerSeriesQuotientFamily k n : Type u))
              (positivePowOfTwo (j + 1))
              (powerSeriesXi k (positivePowOfTwo (j + 1)))))) i = _
        rw [map_sum]
        rw [Finset.sum_apply]
        rw [Finset.sum_eq_single (m - 1) (by
          intro j hj hne
          have hji : positivePowOfTwo (j + 1) ≠ i := by
            intro heq
            have heq' : 2 ^ (j + 1) = 2 ^ m := by
              exact congrArg Subtype.val heq |>.trans him
            have : j + 1 = m :=
              Nat.pow_right_injective (by decide : 2 ≤ 2) heq'
            exact hne (by omega)
          rw [DirectSum.coeFnLinearMap_apply]
          rw [DirectSum.of_apply]
          simp [hji]
          ) (by
            intro hnot
            exact False.elim (hnot hmem))]
        have heq : positivePowOfTwo (m - 1 + 1) = i := by
          apply Subtype.ext
          change 2 ^ (m - 1 + 1) = (i : ℕ)
          rw [Nat.sub_add_cancel hm, him]
        rw [heq]
        rw [DirectSum.coeFnLinearMap_apply, DirectSum.of_eq_same]
        exact hxi
      rw [hqeq]
      simp
    · have hqzero : q n i = 0 := by
        change (DirectSum.coeFnLinearMap (PowerSeries k)
          (Finset.sum (Finset.range n) (fun j ↦
            DirectSum.of (fun n : ℕ+ => (powerSeriesQuotientFamily k n : Type u))
              (positivePowOfTwo (j + 1))
              (powerSeriesXi k (positivePowOfTwo (j + 1)))))) i = 0
        rw [map_sum, Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro j hj
        have hjlt : j < n := Finset.mem_range.mp hj
        have hji : positivePowOfTwo (j + 1) ≠ i := by
          intro heq
          have heq' : 2 ^ (j + 1) = 2 ^ m := by
            exact congrArg Subtype.val heq |>.trans him
          have hjm : j + 1 = m :=
            Nat.pow_right_injective (by decide : 2 ≤ 2) heq'
          apply hmn
          omega
        rw [DirectSum.coeFnLinearMap_apply, DirectSum.of_apply]
        simp [hji]
      rw [hqzero, zero_sub]
      apply (hprincipal (M := (powerSeriesQuotientFamily k i : Type u))
        ((PowerSeries.X : PowerSeries k) ^ n) (-(powerSeriesXi k i))).mpr
      have hnatpow : ∀ t : ℕ, t ≤ 2 ^ t := by
        intro t
        induction t with
        | zero => simp
        | succ t iht =>
          calc
            t + 1 ≤ 2 ^ t + 1 := Nat.succ_le_succ iht
            _ ≤ 2 ^ t * 2 := by
              nlinarith [Nat.one_le_pow t 2 (by decide : 0 < 2)]
            _ = 2 ^ (t + 1) := by rw [pow_succ]
      have hle : n ≤ 2 ^ (m - 1) := by
        exact (by omega : n ≤ m - 1).trans (hnatpow (m - 1))
      let z : (powerSeriesQuotientFamily k i : Type u) :=
        Ideal.Quotient.mk ((powerSeriesXIdeal k) ^ (i : ℕ))
          (-((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1) - n)))
      refine ⟨z, ?_⟩
      rw [hxi]
      change ((powerSeriesXIdeal k) ^ (i : ℕ)).mkQ
          (((PowerSeries.X : PowerSeries k) ^ n) •
            (-((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1) - n)))) =
        -((powerSeriesXIdeal k) ^ (i : ℕ)).mkQ
          ((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)))
      rw [← ((powerSeriesXIdeal k) ^ (i : ℕ)).mkQ.map_neg]
      congr 1
      rw [smul_eq_mul, mul_neg, ← pow_add, Nat.add_sub_of_le hle]
  · have hxi0 : powerSeriesXi k i = 0 :=
      powerSeriesXi_eq_zero_of_not_powerOfTwo k i hiPow
    have hqzero : q n i = 0 := by
      change (DirectSum.coeFnLinearMap (PowerSeries k)
        (Finset.sum (Finset.range n) (fun j ↦
          DirectSum.of (fun n : ℕ+ => (powerSeriesQuotientFamily k n : Type u))
            (positivePowOfTwo (j + 1))
            (powerSeriesXi k (positivePowOfTwo (j + 1)))))) i = 0
      rw [map_sum, Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro j hj
      have hji : positivePowOfTwo (j + 1) ≠ i := by
        intro heq
        apply hiPow
        refine ⟨j + 1, by omega, ?_⟩
        exact (congrArg Subtype.val heq).symm
      rw [DirectSum.coeFnLinearMap_apply, DirectSum.of_apply]
      simp [hji]
    rw [hqzero, hxi0]
    simp

/-- The `(x)`-adic completion of the direct sum is not Mittag-Leffler. -/
private theorem finite_annihilator_approximation_of_mittagLeffler_general
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (η : M)
    (hML : IsMittagLefflerModule (ModuleCat.of R M)) :
    ∃ Q : ModuleCat.{u} R,
      Module.Finite R (Q : Type u) ∧
        ∃ ξ' : (Q : Type u), ∀ l : ℕ, 1 ≤ l →
          elementAnnihilatorModuloIdeal (I ^ l) η =
            elementAnnihilatorModuloIdeal (I ^ l) ξ' := by
  classical
  let f : R →ₗ[R] M := LinearMap.toSpanSingleton R M η
  have hRfp : Module.FinitePresentation R R :=
    Module.finitePresentation_of_projective R R
  obtain ⟨Q, hQfp, g, hmut⟩ :=
    hML (ModuleCat.of R R) hRfp f
  let _ : Module.FinitePresentation R (Q : Type u) := hQfp
  refine ⟨Q, inferInstance, g 1, ?_⟩
  intro l hl
  ext r
  rw [elementAnnihilatorModuloIdeal,
    Submodule.mem_annihilator_span_singleton,
    elementAnnihilatorModuloIdeal,
    Submodule.mem_annihilator_span_singleton]
  let X := R ⧸ I ^ l
  let z : R ⊗[R] X := 1 ⊗ₜ[R] (Ideal.Quotient.mk _ r)
  have heM :
      (TensorProduct.tensorQuotEquivQuotSMul (M : Type u) (I ^ l))
          ((f.rTensor X) z) =
        r • moduleQuotientElement (I ^ l) η := by
    change _ = r • (I ^ l • (⊤ : Submodule R M)).mkQ η
    rw [show z = (1 : R) ⊗ₜ[R] (Ideal.Quotient.mk _ r) by rfl]
    rw [LinearMap.rTensor_tmul]
    rw [show f 1 = η by simp [f]]
    rw [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]
    change (I ^ l • (⊤ : Submodule R M)).mkQ (r • η) =
      r • (I ^ l • (⊤ : Submodule R M)).mkQ η
    exact (I ^ l • (⊤ : Submodule R M)).mkQ.map_smul r η
  have heQ :
      (TensorProduct.tensorQuotEquivQuotSMul (Q : Type u) (I ^ l))
          ((g.rTensor X) z) =
        r • moduleQuotientElement (I ^ l) (g 1) := by
    change _ = r • (I ^ l • (⊤ : Submodule R Q)).mkQ (g 1)
    rw [show z = (1 : R) ⊗ₜ[R] (Ideal.Quotient.mk _ r) by rfl]
    rw [LinearMap.rTensor_tmul]
    rw [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]
    change (I ^ l • (⊤ : Submodule R Q)).mkQ (r • g 1) =
      r • (I ^ l • (⊤ : Submodule R Q)).mkQ (g 1)
    exact (I ^ l • (⊤ : Submodule R Q)).mkQ.map_smul r (g 1)
  have hker : LinearMap.ker (f.rTensor X) = LinearMap.ker (g.rTensor X) :=
    le_antisymm (hmut.1 X) (hmut.2 X)
  constructor
  · intro hr
    have hzf : (f.rTensor X) z = 0 := by
      apply (TensorProduct.tensorQuotEquivQuotSMul (M : Type u) (I ^ l)).injective
      rw [heM]
      exact hr
    have hzg : (g.rTensor X) z = 0 :=
      LinearMap.mem_ker.mp (hker ▸ LinearMap.mem_ker.mpr hzf)
    have hzg' := congrArg
      (TensorProduct.tensorQuotEquivQuotSMul (Q : Type u) (I ^ l)) hzg
    rw [heQ] at hzg'
    exact hzg'
  · intro hr
    have hzg : (g.rTensor X) z = 0 := by
      apply (TensorProduct.tensorQuotEquivQuotSMul (Q : Type u) (I ^ l)).injective
      rw [heQ]
      exact hr
    have hzf : (f.rTensor X) z = 0 :=
      LinearMap.mem_ker.mp (hker.symm ▸ LinearMap.mem_ker.mpr hzg)
    have hzf' := congrArg
      (TensorProduct.tensorQuotEquivQuotSMul (M : Type u) (I ^ l)) hzf
    rw [heM] at hzf'
    exact hzf'

/-- The `(x)`-adic completion of the direct sum is not Mittag-Leffler. -/
theorem powerSeriesTorsionDirectSumCompletion_not_mittagLeffler
    (k : Type u) [Field k] :
    ¬ IsMittagLefflerModule
      (ModuleCat.of (PowerSeries k) (powerSeriesTorsionDirectSumCompletion k)) := by
  classical
  intro hML
  obtain ⟨η, hη⟩ := powerSeriesXi_lies_in_directSum_adicCompletion k
  obtain ⟨Q, hQ, ξ', hξ'⟩ :=
    finite_annihilator_approximation_of_mittagLeffler_general
      (powerSeriesXIdeal k) η hML
  let _ : ∀ n : ℕ+, AddCommGroup (powerSeriesQuotientFamily k n : Type u) := fun n => by
    change AddCommGroup
      (PowerSeries k ⧸ (powerSeriesXIdeal k) ^ (n : ℕ))
    infer_instance
  have hIFG : (powerSeriesXIdeal k).FG := by
    exact Submodule.fg_span_singleton (PowerSeries.X : PowerSeries k)
  have hprincipal : ∀ {M : Type u} [AddCommGroup M]
      [Module (PowerSeries k) M] (x : PowerSeries k) (y : M),
      y ∈ (Ideal.span {x} • (⊤ : Submodule (PowerSeries k) M)) ↔
        ∃ z : M, x • z = y := by
    intro M _ _ x y
    constructor
    · intro hy
      refine Submodule.smul_induction_on hy ?_ (fun a b ha hb ↦ ?_)
      · intro r hr z hz
        rcases Ideal.mem_span_singleton.mp hr with ⟨c, hc⟩
        refine ⟨c • z, ?_⟩
        rw [hc]
        exact (smul_assoc x c z).symm
      · rcases ha with ⟨a, rfl⟩
        rcases hb with ⟨b, rfl⟩
        exact ⟨a + b, by simp⟩
    · rintro ⟨z, rfl⟩
      exact Submodule.smul_mem_smul (Submodule.subset_span (Set.mem_singleton x))
        Submodule.mem_top
  have hquot (l : ℕ)
      (dbar : moduleQuotientByIdeal
        (R := PowerSeries k) (M := powerSeriesTorsionDirectSum k)
        (powerSeriesXIdeal k ^ l))
      (hd : (DirectSum.coeFnLinearMap (PowerSeries k)).reduceModIdeal
        (powerSeriesXIdeal k ^ l) dbar = 0) : dbar = 0 := by
    let N : Submodule (PowerSeries k) (powerSeriesTorsionDirectSum k) :=
      powerSeriesXIdeal k ^ l • (⊤ : Submodule (PowerSeries k) (powerSeriesTorsionDirectSum k))
    have hsurj := Submodule.Quotient.mk_surjective N
    obtain ⟨d, hdbar⟩ := hsurj dbar
    subst dbar
    change (powerSeriesXIdeal k ^ l •
      (⊤ : Submodule (PowerSeries k) (powerSeriesTorsionProduct k))).mkQ
        (DirectSum.coeFnLinearMap (PowerSeries k) d) = 0 at hd
    have hpow : powerSeriesXIdeal k ^ l =
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ l)} := by
      simp [powerSeriesXIdeal, Ideal.span_singleton_pow]
    rw [hpow] at hd
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hd
    obtain ⟨z, hz⟩ :=
      (hprincipal ((PowerSeries.X : PowerSeries k) ^ l)
        (DirectSum.coeFnLinearMap (PowerSeries k) d)).mp hd
    have hcomp : ∀ i,
        d i ∈ Ideal.span {((PowerSeries.X : PowerSeries k) ^ l)} •
          (⊤ : Submodule (PowerSeries k)
            (powerSeriesQuotientFamily k i : Type u)) := by
      intro i
      apply (hprincipal ((PowerSeries.X : PowerSeries k) ^ l) _).mpr
      refine ⟨z i, ?_⟩
      exact congrFun hz i
    change (powerSeriesXIdeal k ^ l •
      (⊤ : Submodule (PowerSeries k) (powerSeriesTorsionDirectSum k))).mkQ d = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [← DirectSum.sum_support_of d]
    apply Submodule.sum_mem
    intro i hi
    obtain ⟨w, hw⟩ := (hprincipal ((PowerSeries.X : PowerSeries k) ^ l) _).mp
      (hcomp i)
    rw [← hw, DirectSum.of_smul]
    have hX : (PowerSeries.X : PowerSeries k) ^ l ∈ powerSeriesXIdeal k ^ l := by
      rw [hpow]
      exact Ideal.subset_span (Set.mem_singleton _)
    exact Submodule.smul_mem_smul
      hX Submodule.mem_top
  have hmap (r : PowerSeries k) :
      powerSeriesDirectSumCompletionToProductCompletion k (r • η) =
        r • powerSeriesDirectSumCompletionToProductCompletion k η := by
    change AdicCompletion.map (powerSeriesXIdeal k)
        (DirectSum.coeFnLinearMap (PowerSeries k))
        ((algebraMap (PowerSeries k)
          (AdicCompletion (powerSeriesXIdeal k) (PowerSeries k)) r) • η) = _
    rw [map_smul]
    rfl
  have hann (l : ℕ) :
      elementAnnihilatorModuloIdeal
          ((powerSeriesXIdeal k) ^ l) η =
        elementAnnihilatorModuloIdeal
          ((powerSeriesXIdeal k) ^ l) (powerSeriesXi k) := by
    ext r
    constructor
    · intro hr
      rw [elementAnnihilatorModuloIdeal,
        Submodule.mem_annihilator_span_singleton] at hr ⊢
      unfold moduleQuotientElement at hr ⊢
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hr ⊢
      have hzero :
          (AdicCompletion.eval (powerSeriesXIdeal k)
            (powerSeriesTorsionDirectSum k) l) (r • η) = 0 := by
        apply LinearMap.mem_ker.mp
        apply (AdicCompletion.pow_smul_top_le_ker_eval
          (I := powerSeriesXIdeal k) (M := powerSeriesTorsionDirectSum k) l)
        exact hr
      have hzero_map :
          (AdicCompletion.eval (powerSeriesXIdeal k)
            (powerSeriesTorsionProduct k) l)
            (powerSeriesDirectSumCompletionToProductCompletion k (r • η)) = 0 := by
        change (AdicCompletion.map (powerSeriesXIdeal k)
          (DirectSum.coeFnLinearMap (PowerSeries k)) (r • η)).val l = 0
        rw [AdicCompletion.map_val_apply]
        rw [show (r • η).val l = 0 from hzero]
        simp
      rw [hmap] at hzero_map
      rw [hη] at hzero_map
      have hzero_of :
          (AdicCompletion.eval (powerSeriesXIdeal k)
            (powerSeriesTorsionProduct k) (l))
            (AdicCompletion.of (powerSeriesXIdeal k)
              (powerSeriesTorsionProduct k) (r • powerSeriesXi k)) = 0 := by
        rw [AdicCompletion.eval_of]
        have hzero_map' := hzero_map
        rw [map_smul, AdicCompletion.eval_of] at hzero_map'
        rw [(powerSeriesXIdeal k ^ l •
          (⊤ : Submodule (PowerSeries k) (powerSeriesTorsionProduct k))).mkQ.map_smul]
        exact hzero_map'
      rw [AdicCompletion.eval_of] at hzero_of
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzero_of
      exact hzero_of
    · intro hr
      rw [elementAnnihilatorModuloIdeal,
        Submodule.mem_annihilator_span_singleton] at hr ⊢
      unfold moduleQuotientElement at hr ⊢
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hr ⊢
      have hzero_target_mk :
          (powerSeriesXIdeal k ^ l •
            (⊤ : Submodule (PowerSeries k) (powerSeriesTorsionProduct k))).mkQ
              (r • powerSeriesXi k) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hr
      have hzero_target :
          (AdicCompletion.eval (powerSeriesXIdeal k)
            (powerSeriesTorsionProduct k) l)
            (r • AdicCompletion.of (powerSeriesXIdeal k)
              (powerSeriesTorsionProduct k) (powerSeriesXi k)) = 0 := by
        rw [map_smul, AdicCompletion.eval_of]
        rw [(powerSeriesXIdeal k ^ l •
          (⊤ : Submodule (PowerSeries k) (powerSeriesTorsionProduct k))).mkQ.map_smul]
          at hzero_target_mk
        exact hzero_target_mk
      have hzero_map :
          (AdicCompletion.eval (powerSeriesXIdeal k)
            (powerSeriesTorsionProduct k) l)
            (powerSeriesDirectSumCompletionToProductCompletion k (r • η)) = 0 := by
        rw [hmap, hη]
        exact hzero_target
      have hsource_coord :
          (AdicCompletion.eval (powerSeriesXIdeal k)
            (powerSeriesTorsionDirectSum k) l) (r • η) = 0 := by
        change (AdicCompletion.map (powerSeriesXIdeal k)
          (DirectSum.coeFnLinearMap (PowerSeries k)) (r • η)).val l = 0 at hzero_map
        rw [AdicCompletion.map_val_apply] at hzero_map
        exact hquot l ((r • η).val l) hzero_map
      rw [AdicCompletion.pow_smul_top_eq_ker_eval
        (I := powerSeriesXIdeal k) (M := powerSeriesTorsionDirectSum k) hIFG]
      exact LinearMap.mem_ker.mpr hsource_coord
  obtain ⟨a, ha | ha⟩ :=
    finite_module_annihilator_eventually_principal k Q ξ' hQ
  · obtain ⟨l₀, hl₀⟩ := ha
    obtain ⟨m₀, hm₀⟩ := powerSeriesXi_annihilator_eventually k
    let m := max (max m₀ l₀) (a + 1)
    have hm₀' : m₀ ≤ m := by
      dsimp [m]
      exact (le_max_left _ _).trans (le_max_left _ _)
    have hl₀' : l₀ ≤ m := by
      dsimp [m]
      exact (le_max_right _ _).trans (le_max_left _ _)
    have hm1 : 1 ≤ m := by
      have ha1 : a + 1 ≤ m := by
        dsimp [m]
        exact le_max_right _ _
      omega
    have hnatpow : ∀ t : ℕ, t ≤ 2 ^ t := by
      intro t
      induction t with
      | zero => simp
      | succ t iht =>
          calc
            t + 1 ≤ 2 ^ t + 1 := Nat.succ_le_succ iht
            _ ≤ 2 ^ t * 2 := by
              nlinarith [Nat.one_le_pow t 2 (by decide : 0 < 2)]
            _ = 2 ^ (t + 1) := by rw [pow_succ]
    have hlpow : l₀ ≤ 2 ^ m := hl₀'.trans (hnatpow m)
    have h1pow : ∀ t : ℕ, 1 ≤ 2 ^ t := by
      intro t
      exact Nat.one_le_pow t 2 (by decide : 0 < 2)
    have hEq1 :
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)))} =
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ a)} := by
      exact (hm₀ m (hm₀'.trans le_rfl)).symm.trans
        ((hann (2 ^ m)).symm.trans
          ((hξ' (2 ^ m) (h1pow m)).trans (hl₀ (2 ^ m) hlpow)))
    have hEq2 :
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ m))} =
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ a)} := by
      have hpa :
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ m))} =
            elementAnnihilatorModuloIdeal
              ((powerSeriesXIdeal k) ^ (2 ^ (m + 1))) (powerSeriesXi k) := by
        simpa [Nat.add_sub_cancel] using (hm₀ (m + 1) (by omega)).symm
      exact hpa.trans
        ((hann (2 ^ (m + 1))).symm.trans
          ((hξ' (2 ^ (m + 1)) (h1pow (m + 1))).trans
            (hl₀ (2 ^ (m + 1)) (hl₀'.trans
              (le_trans (Nat.le_succ m) (hnatpow (m + 1)))))))
    have hspan_pow_eq : ∀ {p q : ℕ},
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ p)} =
            Ideal.span {((PowerSeries.X : PowerSeries k) ^ q)} → p = q := by
      intro p q hpq
      have hp : (PowerSeries.X : PowerSeries k) ^ q ∣
          (PowerSeries.X : PowerSeries k) ^ p := by
        rcases Ideal.mem_span_singleton.mp
          (hpq ▸ Ideal.subset_span (Set.mem_singleton _)) with ⟨s, hs⟩
        exact ⟨s, hs⟩
      have hqp : q ≤ p := by
        by_contra hnot
        have hlt : p < q := by omega
        have hc := (PowerSeries.X_pow_dvd_iff.mp hp) p hlt
        simp at hc
      have hq : (PowerSeries.X : PowerSeries k) ^ p ∣
          (PowerSeries.X : PowerSeries k) ^ q := by
        rcases Ideal.mem_span_singleton.mp
          (hpq.symm ▸ Ideal.subset_span (Set.mem_singleton _)) with ⟨s, hs⟩
        exact ⟨s, hs⟩
      have hpq' : p ≤ q := by
        by_contra hnot
        have hlt : q < p := by omega
        have hc := (PowerSeries.X_pow_dvd_iff.mp hq) q hlt
        simp at hc
      omega
    have heq1 := hspan_pow_eq hEq1
    have heq2 := hspan_pow_eq hEq2
    have hpowlt : 2 ^ (m - 1) < 2 ^ m := by
      exact Nat.pow_lt_pow_right (by decide : 1 < 2)
        (Nat.sub_lt (Nat.zero_lt_of_lt hm1) (by omega))
    omega
  · obtain ⟨l₀, hl₀⟩ := ha
    obtain ⟨m₀, hm₀⟩ := powerSeriesXi_annihilator_eventually k
    let m := max (max m₀ l₀) (a + 1)
    have hm₀' : m₀ ≤ m := by
      dsimp [m]
      exact (le_max_left _ _).trans (le_max_left _ _)
    have hl₀' : l₀ ≤ m := by
      dsimp [m]
      exact (le_max_right _ _).trans (le_max_left _ _)
    have hm1 : 1 ≤ m := by
      have ha1 : a + 1 ≤ m := by
        dsimp [m]
        exact le_max_right _ _
      omega
    have hnatpow : ∀ t : ℕ, t ≤ 2 ^ t := by
      intro t
      induction t with
      | zero => simp
      | succ t iht =>
          calc
            t + 1 ≤ 2 ^ t + 1 := Nat.succ_le_succ iht
            _ ≤ 2 ^ t * 2 := by
              nlinarith [Nat.one_le_pow t 2 (by decide : 0 < 2)]
            _ = 2 ^ (t + 1) := by rw [pow_succ]
    have hm0pow : l₀ ≤ 2 ^ m := hl₀'.trans (hnatpow m)
    have h1pow : ∀ t : ℕ, 1 ≤ 2 ^ t := by
      intro t
      exact Nat.one_le_pow t 2 (by decide : 0 < 2)
    have hEq1 :
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ (m - 1)))} =
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ m - a))} := by
      exact (hm₀ m (hm₀'.trans le_rfl)).symm.trans
        ((hann (2 ^ m)).symm.trans
          ((hξ' (2 ^ m) (h1pow m)).trans
            (hl₀ (2 ^ m) hm0pow)))
    have hEq2 :
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ m))} =
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ (m + 1) - a))} := by
      have hpa :
          Ideal.span {((PowerSeries.X : PowerSeries k) ^ (2 ^ m))} =
            elementAnnihilatorModuloIdeal
              ((powerSeriesXIdeal k) ^ (2 ^ (m + 1))) (powerSeriesXi k) := by
        simpa [Nat.add_sub_cancel] using (hm₀ (m + 1) (by omega)).symm
      exact hpa.trans
        ((hann (2 ^ (m + 1))).symm.trans
          ((hξ' (2 ^ (m + 1)) (h1pow (m + 1))).trans
            (hl₀ (2 ^ (m + 1))
              (hl₀'.trans (le_trans (Nat.le_succ m) (hnatpow (m + 1)))))))
    have hspan_pow_eq : ∀ {p q : ℕ},
        Ideal.span {((PowerSeries.X : PowerSeries k) ^ p)} =
            Ideal.span {((PowerSeries.X : PowerSeries k) ^ q)} → p = q := by
      intro p q hpq
      have hp : (PowerSeries.X : PowerSeries k) ^ q ∣
          (PowerSeries.X : PowerSeries k) ^ p := by
        rcases Ideal.mem_span_singleton.mp
          (hpq ▸ Ideal.subset_span (Set.mem_singleton _)) with ⟨s, hs⟩
        exact ⟨s, hs⟩
      have hqp : q ≤ p := by
        by_contra hnot
        have hlt : p < q := by omega
        have hc := (PowerSeries.X_pow_dvd_iff.mp hp) p hlt
        simp at hc
      have hq : (PowerSeries.X : PowerSeries k) ^ p ∣
          (PowerSeries.X : PowerSeries k) ^ q := by
        rcases Ideal.mem_span_singleton.mp
          (hpq.symm ▸ Ideal.subset_span (Set.mem_singleton _)) with ⟨s, hs⟩
        exact ⟨s, hs⟩
      have hpq' : p ≤ q := by
        by_contra hnot
        have hlt : q < p := by omega
        have hc := (PowerSeries.X_pow_dvd_iff.mp hq) q hlt
        simp at hc
      omega
    have heq1 := hspan_pow_eq hEq1
    have heq2 := hspan_pow_eq hEq2
    have heq1' : 2 ^ (m - 1) = 2 ^ m - a := heq1
    have heq2' : 2 ^ m = 2 ^ (m + 1) - a := heq2
    have hpowlt : 2 ^ (m - 1) < 2 ^ m := by
      exact Nat.pow_lt_pow_right (by decide : 1 < 2)
        (Nat.sub_lt (Nat.zero_lt_of_lt hm1) (by omega))
    have hpow_succ : 2 ^ (m + 1) = 2 ^ m * 2 := by
      rw [pow_succ]
    generalize hp : 2 ^ (m - 1) = p at heq1 heq1' hpowlt
    generalize hq : 2 ^ m = q at heq1 heq1' heq2 heq2' hpowlt hpow_succ
    generalize hs : 2 ^ (m + 1) = s at heq2 heq2' hpow_succ
    have hp_pos : 1 ≤ p := by
      rw [← hp]
      exact h1pow (m - 1)
    omega

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
  infer_instance

/-- The displayed algebra is countably generated as a module. -/
theorem artinianLocalExample_countablyGenerated
    (k : Type u) [Field k] :
    Module.IsCountablyGenerated (artinianLocalExampleBaseRing k)
      (artinianLocalExampleAlgebra k) := by
  classical
  let f := artinianLocalExamplePolynomialRelation k
  let R := artinianLocalExampleBaseRing k
  let S := artinianLocalExampleAlgebra k
  let s : Set S := Set.range (fun n : ℕ => (AdjoinRoot.root f) ^ n)
  let Q : Submodule R S := Submodule.span R s
  refine ⟨s, Set.countable_range _, ?_⟩
  rw [eq_top_iff]
  intro x hx
  clear hx
  induction x using AdjoinRoot.induction_on with
  | ih p =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
          simpa [map_add] using Q.add_mem hp hq
      | monomial n a =>
          rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, AdjoinRoot.mk_C,
            map_pow, AdjoinRoot.mk_X]
          simpa [R, S, f, s, Q, Algebra.smul_def, AdjoinRoot.algebraMap_eq] using Q.smul_mem a
            (Submodule.subset_span (show (AdjoinRoot.root f) ^ n ∈ s by
              exact ⟨n, rfl⟩))

private lemma artinianLocalExample_idempotent
    (k : Type u) [Field k]
    (φ : artinianLocalExampleAlgebra k →+* Polynomial k)
    (σ : Polynomial k →+* artinianLocalExampleAlgebra k)
    (A : artinianLocalExampleBaseRing k)
    (hφσ : ∀ p : Polynomial k, φ (σ p) = p)
    (hA_formula :
      ∀ x : artinianLocalExampleAlgebra k,
        AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * x =
          AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ (φ x))
    (hmap_of :
      ∀ (e : artinianLocalExampleAlgebra k →ₗ[artinianLocalExampleBaseRing k]
          artinianLocalExampleAlgebra k)
        (r : artinianLocalExampleBaseRing k)
        (x : artinianLocalExampleAlgebra k),
        e (AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) r * x) =
          AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) r * e x)
    (htop_all :
      ∀ (e : artinianLocalExampleAlgebra k →ₗ[artinianLocalExampleBaseRing k]
          artinianLocalExampleAlgebra k)
        (x : artinianLocalExampleAlgebra k),
        φ (e x) = φ (e 1) * φ x)
    (hdecomp :
      ∀ (x : artinianLocalExampleAlgebra k),
        ∃ p : Polynomial k,
          x = σ (φ x) + AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ p)
    (e : artinianLocalExampleAlgebra k →ₗ[artinianLocalExampleBaseRing k]
      artinianLocalExampleAlgebra k)
    (he : e.comp e = e) :
    e = 0 ∨ e = LinearMap.id := by
  let R := artinianLocalExampleBaseRing k
  let S := artinianLocalExampleAlgebra k
  have hqmul : φ (e 1) * φ (e 1) = φ (e 1) := by
    have he1 : e (e 1) = e 1 := by
      simpa only [LinearMap.comp_apply] using LinearMap.congr_fun he 1
    rw [← htop_all e (e 1), he1]
  have hqfac : φ (e 1) * (φ (e 1) - 1) = 0 := by
    rw [mul_sub, hqmul]
    ring
  have hzero (e : S →ₗ[R] S) (he : e.comp e = e)
      (hq : φ (e 1) = 0) : e = 0 := by
    have htopzero (y : S) (hy : φ y = 0) : e y = 0 := by
      obtain ⟨p, hp⟩ := hdecomp y
      have hp' : y = AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ p := by
        rw [hp, hy]
        simp
      rw [hp', hmap_of, hA_formula, htop_all, hq]
      simp
    ext x
    obtain ⟨p, hp⟩ := hdecomp x
    have htop' : e (σ (φ x)) = 0 := by
      have htopimage : φ (e (σ (φ x))) = 0 := by
        rw [htop_all, hq]
        simp
      have hkill := htopzero (e (σ (φ x))) htopimage
      calc
        e (σ (φ x)) = e (e (σ (φ x))) :=
          (LinearMap.congr_fun he (σ (φ x))).symm
        _ = 0 := hkill
    have hbottom' : e (AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ p) = 0 := by
      rw [hmap_of, hA_formula, htop_all, hq]
      simp
    calc
      e x = e (σ (φ x) + AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ p) := congrArg e hp
      _ = e (σ (φ x)) + e (AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ p) := map_add _ _ _
      _ = 0 := by rw [htop', hbottom', add_zero]
  rcases mul_eq_zero.mp hqfac with hq | hq
  · exact Or.inl (hzero e he hq)
  · right
    have hqone : φ (e 1) = 1 := sub_eq_zero.mp hq
    have hsocle (q : Polynomial k) :
        e (AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ q) =
          AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ q := by
      rw [hmap_of, hA_formula, htop_all, hqone, hφσ]
      simp
    have htopfix (x : S) : e (σ (φ x)) = σ (φ x) := by
      obtain ⟨q, hqdecomp⟩ := hdecomp (e (σ (φ x)))
      have hφeq : φ (e (σ (φ x))) = φ x := by
        rw [htop_all, hqone, hφσ]
        simp
      have hqdecomp' : e (σ (φ x)) =
          σ (φ x) + AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ q := by
        calc
          e (σ (φ x)) = σ (φ (e (σ (φ x)))) +
              AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ q := hqdecomp
          _ = σ (φ x) + AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ q := by rw [hφeq]
      have heq : e (σ (φ x)) =
          e (σ (φ x)) + AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ q := by
        calc
          e (σ (φ x)) = e (e (σ (φ x))) :=
            (LinearMap.congr_fun he (σ (φ x))).symm
          _ = e (σ (φ x) + AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ q) := congrArg e hqdecomp'
          _ = e (σ (φ x)) + e (AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ q) := map_add _ _ _
          _ = e (σ (φ x)) + AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ q := by rw [hsocle]
      have hqzero : AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ q = 0 := by
        exact add_left_cancel (heq.symm.trans (add_zero _).symm)
      calc
        e (σ (φ x)) = σ (φ x) + AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ q := hqdecomp'
        _ = σ (φ x) := by rw [hqzero, add_zero]
    ext x
    change e x = x
    obtain ⟨p, hp⟩ := hdecomp x
    have hxe : e x = e (σ (φ x) + AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ p) :=
      congrArg (fun y : S => e y) hp
    have hsum : e (σ (φ x) + AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ p) =
        e (σ (φ x)) + e (AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ p) := by
      rw [map_add]
    have hfixed : e (σ (φ x)) + e (AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ p) =
        σ (φ x) + AdjoinRoot.of (artinianLocalExamplePolynomialRelation k) A * σ p := by
      simp only [htopfix x, hsocle p]
    exact hxe.trans (hsum.trans (hfixed.trans hp.symm))

private lemma moduleCat_isZero_of_biprod_projection_zero
    {R : Type u} [CommRing R] {M Y Z : ModuleCat R} (a : M ≅ Y ⊞ Z)
    (h : a.hom ≫ biprod.fst ≫ biprod.inl ≫ a.inv = 0) : IsZero Y := by
  rw [ModuleCat.isZero_iff_subsingleton]
  constructor
  intro y z
  have h' := congrArg
    (fun q : M ⟶ M =>
      (biprod.inl : Y ⟶ Y ⊞ Z) ≫ a.inv ≫ q ≫ a.hom ≫
        (biprod.fst : Y ⊞ Z ⟶ Y)) h
  have h'' : (biprod.inl : Y ⟶ Y ⊞ Z) ≫
      (biprod.fst : Y ⊞ Z ⟶ Y) = 0 := by
    simpa [Category.assoc] using h'
  have hid : (𝟙 Y : Y ⟶ Y) = 0 := by simpa using h''
  have hy : y = 0 := by
    simpa using congrArg (fun q : Y ⟶ Y => q y) hid
  have hz : z = 0 := by
    simpa using congrArg (fun q : Y ⟶ Y => q z) hid
  exact hy.trans hz.symm

private lemma moduleCat_isZero_of_biprod_projection_id
    {R : Type u} [CommRing R] {M Y Z : ModuleCat R} (a : M ≅ Y ⊞ Z)
    (h : a.hom ≫ biprod.fst ≫ biprod.inl ≫ a.inv = 𝟙 M) : IsZero Z := by
  rw [ModuleCat.isZero_iff_subsingleton]
  constructor
  intro y z
  have h' := congrArg
    (fun q : M ⟶ M =>
      (biprod.inr : Z ⟶ Y ⊞ Z) ≫ a.inv ≫ q ≫ a.hom ≫
        (biprod.snd : Y ⊞ Z ⟶ Z)) h
  have h'' : (biprod.inr : Z ⟶ Y ⊞ Z) ≫
      (biprod.snd : Y ⊞ Z ⟶ Z) = 0 := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_fst,
      Category.comp_id, Category.id_comp, zero_comp, biprod.inl_snd,
      comp_zero] using h'.symm
  have hid : (𝟙 Z : Z ⟶ Z) = 0 := by simpa using h''
  have hy : y = 0 := by
    simpa using congrArg (fun q : Z ⟶ Z => q y) hid
  have hz : z = 0 := by
    simpa using congrArg (fun q : Z ⟶ Z => q z) hid
  exact hy.trans hz.symm

/-- The displayed module is indecomposable. -/
theorem artinianLocalExample_indecomposable
    (k : Type u) [Field k] :
    Indecomposable (artinianLocalExampleModule k) := by
  classical
  let I := artinianLocalExampleRelationIdeal k
  let R := artinianLocalExampleBaseRing k
  let f := artinianLocalExamplePolynomialRelation k
  let S := artinianLocalExampleAlgebra k
  let A := artinianLocalExampleA k
  let B := artinianLocalExampleB k
  let ρ₀ : artinianLocalExamplePolynomialRing k →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)
  have hI : I ≤ RingHom.ker ρ₀ := by
    change artinianLocalExampleRelationIdeal k ≤ RingHom.ker ρ₀
    rw [artinianLocalExampleRelationIdeal, Ideal.span_le]
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> simp [ρ₀]
  let ρ : R →+* k :=
    Ideal.Quotient.lift I ρ₀ (fun x hx => RingHom.mem_ker.mp (hI hx))
  let ρP : R →+* Polynomial k := (Polynomial.C : k →+* Polynomial k).comp ρ
  have hρA : ρ A = 0 := by
    change ρ (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2))) = 0
    dsimp [ρ]
    rw [Ideal.Quotient.lift_mk]
    simp [ρ₀]
  have hρB : ρ B = 0 := by
    change ρ (Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2))) = 0
    dsimp [ρ]
    rw [Ideal.Quotient.lift_mk]
    simp [ρ₀]
  have hρC (c : k) :
      ρ (Ideal.Quotient.mk I (MvPolynomial.C c)) = c := by
    dsimp [ρ]
    rw [Ideal.Quotient.lift_mk]
    simp [ρ₀]
  have hA2 : A * A = 0 := by
    change Ideal.Quotient.mk I
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (0 : Fin 2)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp [pow_two])
  have hAB : A * B = 0 := by
    change Ideal.Quotient.mk I
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have hφhf : Polynomial.eval₂ ρP Polynomial.X f = 0 := by
    simp [f, artinianLocalExamplePolynomialRelation, ρP, A, B, hρA, hρB]
  let φ : S →+* Polynomial k := AdjoinRoot.lift ρP Polynomial.X hφhf
  have hφmk (p : Polynomial R) :
      φ (AdjoinRoot.mk f p) = p.map ρ := by
    rw [AdjoinRoot.lift_mk]
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simp [hp, hq]
    | monomial n a =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        simp [ρP]
  have hφof (r : R) : φ (AdjoinRoot.of f r) = Polynomial.C (ρ r) := by
    change φ (AdjoinRoot.mk f (Polynomial.C r)) = Polynomial.C (ρ r)
    rw [hφmk]
    simp
  have hA_mul (r : R) :
      A * algebraMap R S r = algebraMap k S (ρ r) * A := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    induction p using MvPolynomial.induction_on with
    | C c =>
        simp only [← AdjoinRoot.algebraMap_eq]
        change (algebraMap R S A) * algebraMap R S
            (Ideal.Quotient.mk I (MvPolynomial.C c)) =
          algebraMap k S (ρ (Ideal.Quotient.mk I (MvPolynomial.C c))) *
            algebraMap R S A
        have hmkC : Ideal.Quotient.mk I (MvPolynomial.C c) = algebraMap k R c := by
          change Ideal.Quotient.mk I
            (algebraMap k (artinianLocalExamplePolynomialRing k) c) = algebraMap k R c
          rw [Ideal.Quotient.mk_algebraMap]
        rw [hρC, hmkC]
        rw [IsScalarTower.algebraMap_apply k R S c, mul_comm]
    | add p q hp hq =>
        simp only [map_add, add_mul, mul_add, hp, hq]
    | mul_X p i hp =>
        fin_cases i
        · simp only [map_mul, A, artinianLocalExampleA,
            R, S]
          simp only [← AdjoinRoot.algebraMap_eq]
          have hA2S : (algebraMap R S A) * (algebraMap R S A) = 0 := by
            rw [← map_mul, hA2, map_zero]
          have hA2S' :
              (algebraMap R S (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2)))) *
                (algebraMap R S (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2)))) = 0 := by
            simpa [A, I, artinianLocalExampleA, R, S] using hA2S
          have hρX0 : ρ (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2))) = 0 := by
            simpa [A, I, artinianLocalExampleA] using hρA
          calc
            (algebraMap R S (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2)))) *
                ((algebraMap R S (Ideal.Quotient.mk I p)) *
                  (algebraMap R S (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2))))) =
              algebraMap R S (Ideal.Quotient.mk I p) *
                ((algebraMap R S (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2)))) *
                  (algebraMap R S (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2))))) := by ring
            _ = 0 := by rw [hA2S', mul_zero]
            _ = _ := by simp [hρX0, I, R, S]
        · simp only [map_mul, A, artinianLocalExampleA,
            R, S]
          simp only [← AdjoinRoot.algebraMap_eq]
          have hABS : (algebraMap R S A) * (algebraMap R S B) = 0 := by
            rw [← map_mul, hAB, map_zero]
          have hABS' :
              (algebraMap R S (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2)))) *
                (algebraMap R S (Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2)))) = 0 := by
            simpa [A, B, I, artinianLocalExampleA, artinianLocalExampleB, R, S] using hABS
          have hρX0 : ρ (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2))) = 0 := by
            simpa [A, I, artinianLocalExampleA] using hρA
          have hρX1 : ρ (Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2))) = 0 := by
            simpa [B, I, artinianLocalExampleB] using hρB
          calc
            (algebraMap R S (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2)))) *
                ((algebraMap R S (Ideal.Quotient.mk I p)) *
                  (algebraMap R S (Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2))))) =
              algebraMap R S (Ideal.Quotient.mk I p) *
                ((algebraMap R S (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2)))) *
                  (algebraMap R S (Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2))))) := by ring
            _ = 0 := by rw [hABS', mul_zero]
            _ = _ := by simp [hρX1, I, R, S]
  have hρalg (c : k) : ρ (algebraMap k R c) = c := by
    have hmkC : Ideal.Quotient.mk I (MvPolynomial.C c) = algebraMap k R c := by
      change Ideal.Quotient.mk I
        (algebraMap k (artinianLocalExamplePolynomialRing k) c) = algebraMap k R c
      rw [Ideal.Quotient.mk_algebraMap]
    rw [← hmkC]
    exact hρC c
  have hφalg (c : k) : φ (algebraMap k S c) = Polynomial.C c := by
    rw [IsScalarTower.algebraMap_apply k R S, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.lift_of]
    simp [ρP, hρalg]
  have hφroot : φ (AdjoinRoot.root f) = Polynomial.X := by
    change AdjoinRoot.lift ρP Polynomial.X hφhf (AdjoinRoot.root f) = Polynomial.X
    exact AdjoinRoot.lift_root hφhf
  let σ : Polynomial k →+* S :=
    Polynomial.eval₂RingHom (algebraMap k S) (AdjoinRoot.root f)
  have hφσ (p : Polynomial k) : φ (σ p) = p := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simp only [map_add, hp, hq, σ]
    | monomial n a =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        rw [map_mul, map_pow]
        rw [map_mul]
        rw [show σ (Polynomial.C a) = algebraMap k S a by simp [σ]]
        rw [show σ Polynomial.X = AdjoinRoot.root f by simp [σ]]
        rw [hφalg]
        rw [map_pow, hφroot]
  have hA_formula (x : S) :
      AdjoinRoot.of f A * x = AdjoinRoot.of f A * σ (φ x) := by
    induction x using AdjoinRoot.induction_on with
    | ih p =>
        induction p using Polynomial.induction_on' with
        | add p q hp hq =>
            simp only [map_add, hp, hq, mul_add]
        | monomial n r =>
            rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, AdjoinRoot.mk_C,
              map_pow, AdjoinRoot.mk_X]
            rw [← AdjoinRoot.algebraMap_eq]
            have hA_mul' :
                (algebraMap R (AdjoinRoot f) A) * algebraMap R (AdjoinRoot f) r =
                  algebraMap k (AdjoinRoot f) (ρ r) * algebraMap R (AdjoinRoot f) A := by
              simpa [S, f] using hA_mul r
            have hφalgR :
                φ (algebraMap R (AdjoinRoot f) r) = Polynomial.C (ρ r) := by
              rw [AdjoinRoot.algebraMap_eq]
              exact hφof r
            rw [← mul_assoc, hA_mul']
            rw [map_mul, map_pow, hφalgR, hφroot]
            rw [map_mul]
            rw [show σ (Polynomial.C (ρ r)) = algebraMap k S (ρ r) by simp [σ]]
            rw [map_pow]
            rw [show σ Polynomial.X = AdjoinRoot.root f by simp [σ]]
            ring
  let T₀ := TrivSqZeroExt (Polynomial k) (Polynomial k)
  let χ₀ : artinianLocalExamplePolynomialRing k →+* T₀ :=
    MvPolynomial.eval₂Hom
      ((TrivSqZeroExt.inlHom (Polynomial k) (Polynomial k)).comp Polynomial.C)
      (fun i => if i = 0 then TrivSqZeroExt.inr (1 : Polynomial k)
        else TrivSqZeroExt.inr Polynomial.X)
  have hχI : I ≤ RingHom.ker χ₀ := by
    change artinianLocalExampleRelationIdeal k ≤ RingHom.ker χ₀
    rw [artinianLocalExampleRelationIdeal, Ideal.span_le]
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    all_goals simp [χ₀, T₀, pow_two]
  let χ : R →+* T₀ :=
    Ideal.Quotient.lift I χ₀ (fun x hx => RingHom.mem_ker.mp (hχI hx))
  have hχA : χ A = TrivSqZeroExt.inr (1 : Polynomial k) := by
    change χ (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2))) = _
    dsimp [χ]
    rw [Ideal.Quotient.lift_mk]
    simp [χ₀, T₀]
  have hχB : χ B = TrivSqZeroExt.inr Polynomial.X := by
    change χ (Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2))) = _
    dsimp [χ]
    rw [Ideal.Quotient.lift_mk]
    simp [χ₀, T₀]
  have hχA' : χ (artinianLocalExampleA k) = TrivSqZeroExt.inr (1 : Polynomial k) := by
    simpa [A] using hχA
  have hχB' : χ (artinianLocalExampleB k) = TrivSqZeroExt.inr Polynomial.X := by
    simpa [B] using hχB
  have hτhf : Polynomial.eval₂ χ (TrivSqZeroExt.inl Polynomial.X) f = 0 := by
    have hmul :
        (TrivSqZeroExt.inr (1 : Polynomial k) : T₀) *
            (TrivSqZeroExt.inl Polynomial.X : T₀) =
          (TrivSqZeroExt.inr Polynomial.X : T₀) := by
      rw [TrivSqZeroExt.inr_mul_inl]
      simp
    simp [f, artinianLocalExamplePolynomialRelation, hχA', hχB', T₀]
    change (TrivSqZeroExt.inr (1 : Polynomial k) : T₀) *
        (TrivSqZeroExt.inl Polynomial.X : T₀) -
          Polynomial.X • (TrivSqZeroExt.inr (1 : Polynomial k) : T₀) = 0
    rw [← TrivSqZeroExt.inr_smul, hmul]
    simp [smul_eq_mul]
  let τ : S →+* T₀ :=
    AdjoinRoot.lift χ (TrivSqZeroExt.inl Polynomial.X) hτhf
  have hτA : τ (AdjoinRoot.of f A) = TrivSqZeroExt.inr (1 : Polynomial k) := by
    change AdjoinRoot.lift χ (TrivSqZeroExt.inl Polynomial.X) hτhf
      (AdjoinRoot.of f A) = _
    rw [AdjoinRoot.lift_of]
    exact hχA
  have hτB : τ (AdjoinRoot.of f B) = TrivSqZeroExt.inr Polynomial.X := by
    change AdjoinRoot.lift χ (TrivSqZeroExt.inl Polynomial.X) hτhf
      (AdjoinRoot.of f B) = _
    rw [AdjoinRoot.lift_of]
    exact hχB
  have hτroot : τ (AdjoinRoot.root f) = TrivSqZeroExt.inl Polynomial.X := by
    change AdjoinRoot.lift χ (TrivSqZeroExt.inl Polynomial.X) hτhf
      (AdjoinRoot.root f) = _
    exact AdjoinRoot.lift_root hτhf
  have hχalg (c : k) :
      χ (algebraMap k R c) = (TrivSqZeroExt.inl (Polynomial.C c) : T₀) := by
    have hmkC : Ideal.Quotient.mk I (MvPolynomial.C c) = algebraMap k R c := by
      change Ideal.Quotient.mk I
        (algebraMap k (artinianLocalExamplePolynomialRing k) c) = algebraMap k R c
      rw [Ideal.Quotient.mk_algebraMap]
    rw [← hmkC]
    dsimp [χ]
    rw [Ideal.Quotient.lift_mk]
    simp [χ₀, T₀]
  have hτalg (c : k) :
      τ (algebraMap k S c) = (TrivSqZeroExt.inl (Polynomial.C c) : T₀) := by
    rw [IsScalarTower.algebraMap_apply k R S, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.lift_of]
    exact hχalg c
  have hτσ (p : Polynomial k) :
      τ (σ p) = (TrivSqZeroExt.inl p : T₀) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simp only [map_add, hp, hq]
        rw [TrivSqZeroExt.inl_add]
    | monomial n c =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
        rw [show σ (Polynomial.C c) = algebraMap k S c by simp [σ]]
        rw [show σ Polynomial.X = AdjoinRoot.root f by simp [σ]]
        rw [map_mul, map_pow, hτalg, hτroot]
        simp [T₀]
  have hAσ_injective (p : Polynomial k)
      (hp : AdjoinRoot.of f A * σ p = 0) : p = 0 := by
    have h := congrArg TrivSqZeroExt.snd (congrArg τ hp)
    rw [map_mul, hτA, hτσ] at h
    simpa [T₀, TrivSqZeroExt.inr_mul_inl, smul_eq_mul] using h
  have hrootrel :
      AdjoinRoot.of f A * AdjoinRoot.root f = AdjoinRoot.of f B := by
    change AdjoinRoot.of (Polynomial.C A * Polynomial.X - Polynomial.C B) A *
        AdjoinRoot.root (Polynomial.C A * Polynomial.X - Polynomial.C B) =
      AdjoinRoot.of (Polynomial.C A * Polynomial.X - Polynomial.C B) B
    rw [← sub_eq_zero]
    convert AdjoinRoot.eval₂_root
      (Polynomial.C A * Polynomial.X - Polynomial.C B) using 1
    all_goals simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X]
    rfl
  have hmap_smul (e : S →ₗ[R] S) (r : R) (x : S) :
      e (algebraMap R S r * x) = algebraMap R S r * e x := by
    rw [← Algebra.smul_def, ← Algebra.smul_def]
    exact e.map_smul r x
  have hmap_of (e : S →ₗ[R] S) (r : R) (x : S) :
      e (AdjoinRoot.of f r * x) = AdjoinRoot.of f r * e x := by
    rw [← AdjoinRoot.algebraMap_eq]
    exact hmap_smul e r x
  have hB_formula (x : S) :
      AdjoinRoot.of f B * x =
        AdjoinRoot.of f A * σ (Polynomial.X * φ x) := by
    calc
      AdjoinRoot.of f B * x =
          (AdjoinRoot.of f A * AdjoinRoot.root f) * x := by rw [hrootrel]
      _ = AdjoinRoot.of f A * (AdjoinRoot.root f * x) := by ring
      _ = AdjoinRoot.of f A * σ (φ (AdjoinRoot.root f * x)) := hA_formula _
      _ = AdjoinRoot.of f A * σ (Polynomial.X * φ x) := by
        rw [map_mul, hφroot]
  have hφalgR (r : R) :
      φ (algebraMap R S r) = Polynomial.C (ρ r) := by
    rw [AdjoinRoot.algebraMap_eq]
    exact hφof r
  have htop (e : S →ₗ[R] S) (n : ℕ) :
      φ (e (AdjoinRoot.root f ^ n)) =
        φ (e 1) * Polynomial.X ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        have hpow :
            AdjoinRoot.of f A * AdjoinRoot.root f ^ (Nat.succ n) =
              AdjoinRoot.of f B * AdjoinRoot.root f ^ n := by
          rw [pow_succ]
          calc
            AdjoinRoot.of f A * (AdjoinRoot.root f ^ n * AdjoinRoot.root f) =
                (AdjoinRoot.of f A * AdjoinRoot.root f) *
                  AdjoinRoot.root f ^ n := by ring
            _ = AdjoinRoot.of f B * AdjoinRoot.root f ^ n := by rw [hrootrel]
        have heq :
            AdjoinRoot.of f A *
                σ (φ (e (AdjoinRoot.root f ^ Nat.succ n))) =
              AdjoinRoot.of f A *
                σ (Polynomial.X * φ (e (AdjoinRoot.root f ^ n))) := by
          calc
            AdjoinRoot.of f A *
                σ (φ (e (AdjoinRoot.root f ^ Nat.succ n))) =
                AdjoinRoot.of f A * e (AdjoinRoot.root f ^ Nat.succ n) :=
              (hA_formula _).symm
            _ = e (AdjoinRoot.of f A * AdjoinRoot.root f ^ Nat.succ n) :=
              (hmap_of e A _).symm
            _ = e (AdjoinRoot.of f B * AdjoinRoot.root f ^ n) := by rw [hpow]
            _ = AdjoinRoot.of f B * e (AdjoinRoot.root f ^ n) := hmap_of e B _
            _ = AdjoinRoot.of f A *
                σ (Polynomial.X * φ (e (AdjoinRoot.root f ^ n))) := hB_formula _
        have hdiff :
            φ (e (AdjoinRoot.root f ^ Nat.succ n)) -
                Polynomial.X * φ (e (AdjoinRoot.root f ^ n)) = 0 := by
          apply hAσ_injective
          rw [map_sub, mul_sub]
          exact sub_eq_zero.mpr heq
        calc
          φ (e (AdjoinRoot.root f ^ Nat.succ n)) =
              Polynomial.X * φ (e (AdjoinRoot.root f ^ n)) :=
            sub_eq_zero.mp hdiff
          _ = Polynomial.X * (φ (e 1) * Polynomial.X ^ n) := by rw [ih]
          _ = φ (e 1) * Polynomial.X ^ Nat.succ n := by
            rw [pow_succ]
            ring
  have htop_all (e : S →ₗ[R] S) (x : S) :
      φ (e x) = φ (e 1) * φ x := by
    induction x using AdjoinRoot.induction_on with
    | ih p =>
        induction p using Polynomial.induction_on' with
        | add p q hp hq =>
            simp only [map_add, hp, hq, e.map_add, φ.map_add]
            ring
        | monomial n r =>
            rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul,
              AdjoinRoot.mk_C, map_pow, AdjoinRoot.mk_X]
            calc
              φ (e (AdjoinRoot.of f r * AdjoinRoot.root f ^ n)) =
                  φ (AdjoinRoot.of f r * e (AdjoinRoot.root f ^ n)) := by
                    rw [hmap_of]
              _ = Polynomial.C (ρ r) * φ (e (AdjoinRoot.root f ^ n)) := by
                rw [map_mul, hφof]
              _ = Polynomial.C (ρ r) *
                  (φ (e 1) * Polynomial.X ^ n) := by rw [htop]
              _ = φ (e 1) *
                  (Polynomial.C (ρ r) * Polynomial.X ^ n) := by ring
              _ = φ (e 1) * φ (AdjoinRoot.of f r * AdjoinRoot.root f ^ n) := by
                rw [map_mul, hφof, map_pow, hφroot]
  have hB2 : B * B = 0 := by
    change Ideal.Quotient.mk I
      (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (1 : Fin 2)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp [pow_two])
  have hRA (r : R) : A * r = algebraMap k R (ρ r) * A := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    induction p using MvPolynomial.induction_on with
    | C c =>
        have hmkC : Ideal.Quotient.mk I (MvPolynomial.C c) = algebraMap k R c := by
          change Ideal.Quotient.mk I
            (algebraMap k (artinianLocalExamplePolynomialRing k) c) = algebraMap k R c
          rw [Ideal.Quotient.mk_algebraMap]
        rw [hmkC, hρalg]
        ring
    | add p q hp hq =>
        simp only [map_add, add_mul, mul_add]
        rw [hp, hq]
    | mul_X p i hp =>
        fin_cases i
        · have hρX0 : ρ (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2))) = 0 := by
            change ρ A = 0
            exact hρA
          simp only [map_mul]
          change A * ((Ideal.Quotient.mk I p) * A) =
            algebraMap k R (ρ (Ideal.Quotient.mk I p)) *
              algebraMap k R (ρ A) * A
          calc
            A * ((Ideal.Quotient.mk I p) * A) =
                (Ideal.Quotient.mk I p) * (A * A) := by ring
            _ = 0 := by rw [hA2, mul_zero]
            _ = algebraMap k R (ρ (Ideal.Quotient.mk I p)) *
                algebraMap k R (ρ A) * A := by simp [hρA]
        · have hρX1 : ρ (Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2))) = 0 := by
            change ρ B = 0
            exact hρB
          simp only [map_mul]
          change A * ((Ideal.Quotient.mk I p) * B) =
            algebraMap k R (ρ (Ideal.Quotient.mk I p)) *
              algebraMap k R (ρ B) * A
          calc
            A * ((Ideal.Quotient.mk I p) * B) =
                (Ideal.Quotient.mk I p) * (A * B) := by ring
            _ = 0 := by rw [hAB, mul_zero]
            _ = algebraMap k R (ρ (Ideal.Quotient.mk I p)) *
                algebraMap k R (ρ B) * A := by simp [hρB]
  have hRB (r : R) : B * r = algebraMap k R (ρ r) * B := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    induction p using MvPolynomial.induction_on with
    | C c =>
        have hmkC : Ideal.Quotient.mk I (MvPolynomial.C c) = algebraMap k R c := by
          change Ideal.Quotient.mk I
            (algebraMap k (artinianLocalExamplePolynomialRing k) c) = algebraMap k R c
          rw [Ideal.Quotient.mk_algebraMap]
        rw [hmkC, hρalg]
        ring
    | add p q hp hq =>
        simp only [map_add, add_mul, mul_add]
        rw [hp, hq]
    | mul_X p i hp =>
        fin_cases i
        · have hρX0 : ρ (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2))) = 0 := by
            change ρ A = 0
            exact hρA
          simp only [map_mul]
          change B * ((Ideal.Quotient.mk I p) * A) =
            algebraMap k R (ρ (Ideal.Quotient.mk I p)) *
              algebraMap k R (ρ A) * B
          calc
            B * ((Ideal.Quotient.mk I p) * A) =
                (Ideal.Quotient.mk I p) * (B * A) := by ring
            _ = 0 := by rw [show B * A = 0 by rw [mul_comm, hAB], mul_zero]
            _ = algebraMap k R (ρ (Ideal.Quotient.mk I p)) *
                algebraMap k R (ρ A) * B := by simp [hρA]
        · have hρX1 : ρ (Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2))) = 0 := by
            change ρ B = 0
            exact hρB
          simp only [map_mul]
          change B * ((Ideal.Quotient.mk I p) * B) =
            algebraMap k R (ρ (Ideal.Quotient.mk I p)) *
              algebraMap k R (ρ B) * B
          calc
            B * ((Ideal.Quotient.mk I p) * B) =
                (Ideal.Quotient.mk I p) * (B * B) := by ring
            _ = 0 := by rw [hB2, mul_zero]
            _ = algebraMap k R (ρ (Ideal.Quotient.mk I p)) *
                algebraMap k R (ρ B) * B := by simp [hρB]
  have himage (r u v : R)
      (hr : r = algebraMap k R (ρ r) + A * u + B * v) :
      AdjoinRoot.of f r =
        algebraMap k S (ρ r) + algebraMap k S (ρ u) * AdjoinRoot.of f A +
          algebraMap k S (ρ v) * AdjoinRoot.of f B := by
    have hr' : r = algebraMap k R (ρ r) +
        algebraMap k R (ρ u) * A + algebraMap k R (ρ v) * B := by
      calc
        r = algebraMap k R (ρ r) + A * u + B * v := hr
        _ = algebraMap k R (ρ r) + algebraMap k R (ρ u) * A +
            algebraMap k R (ρ v) * B := by rw [hRA u, hRB v]
    calc
      AdjoinRoot.of f r = AdjoinRoot.of f
          (algebraMap k R (ρ r) + algebraMap k R (ρ u) * A +
            algebraMap k R (ρ v) * B) := congrArg (AdjoinRoot.of f) hr'
      _ = algebraMap k S (ρ r) + algebraMap k S (ρ u) * AdjoinRoot.of f A +
          algebraMap k S (ρ v) * AdjoinRoot.of f B := by
        simp only [map_add, map_mul]
        rw [← AdjoinRoot.algebraMap_eq]
        simp only [IsScalarTower.algebraMap_apply k R S]
        ring
  have hcoeff (r : R) :
      ∃ u v : R, r = algebraMap k R (ρ r) + A * u + B * v := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    induction p using MvPolynomial.induction_on with
    | C c =>
        refine ⟨0, 0, ?_⟩
        have hmkC : Ideal.Quotient.mk I (MvPolynomial.C c) = algebraMap k R c := by
          change Ideal.Quotient.mk I
            (algebraMap k (artinianLocalExamplePolynomialRing k) c) = algebraMap k R c
          rw [Ideal.Quotient.mk_algebraMap]
        rw [hmkC, hρalg]
        simp
    | add p q hp hq =>
        rcases hp with ⟨u, v, hp⟩
        rcases hq with ⟨u', v', hq⟩
        refine ⟨u + u', v + v', ?_⟩
        calc
          Ideal.Quotient.mk I (p + q) =
              Ideal.Quotient.mk I p + Ideal.Quotient.mk I q := by rw [map_add]
          _ = (algebraMap k R (ρ (Ideal.Quotient.mk I p)) + A * u + B * v) +
              (algebraMap k R (ρ (Ideal.Quotient.mk I q)) + A * u' + B * v') := by
            exact congrArg₂ (· + ·) hp hq
          _ = algebraMap k R (ρ (Ideal.Quotient.mk I (p + q))) +
              A * (u + u') + B * (v + v') := by
            simp only [map_add, mul_add]
            ring
    | mul_X p i hp =>
        fin_cases i
        · refine ⟨algebraMap k R (ρ (Ideal.Quotient.mk I p)), 0, ?_⟩
          rw [map_mul]
          change (Ideal.Quotient.mk I p) * A =
            algebraMap k R (ρ ((Ideal.Quotient.mk I p) * A)) +
              A * algebraMap k R (ρ (Ideal.Quotient.mk I p)) + B * 0
          calc
            (Ideal.Quotient.mk I p) * A = A * (Ideal.Quotient.mk I p) := by ring
            _ = algebraMap k R (ρ (Ideal.Quotient.mk I p)) * A := hRA _
            _ = algebraMap k R (ρ ((Ideal.Quotient.mk I p) * A)) +
                A * algebraMap k R (ρ (Ideal.Quotient.mk I p)) + B * 0 := by
              simp [hρA]
              ring
        · refine ⟨0, algebraMap k R (ρ (Ideal.Quotient.mk I p)), ?_⟩
          rw [map_mul]
          change (Ideal.Quotient.mk I p) * B =
            algebraMap k R (ρ ((Ideal.Quotient.mk I p) * B)) +
              A * 0 + B * algebraMap k R (ρ (Ideal.Quotient.mk I p))
          calc
            (Ideal.Quotient.mk I p) * B = B * (Ideal.Quotient.mk I p) := by ring
            _ = algebraMap k R (ρ (Ideal.Quotient.mk I p)) * B := hRB _
            _ = algebraMap k R (ρ ((Ideal.Quotient.mk I p) * B)) +
                A * 0 + B * algebraMap k R (ρ (Ideal.Quotient.mk I p)) := by
              simp [hρB]
              ring
  have hdecomp (x : S) :
      ∃ p : Polynomial k, x = σ (φ x) + AdjoinRoot.of f A * σ p := by
    induction x using AdjoinRoot.induction_on with
    | ih p =>
        induction p using Polynomial.induction_on' with
        | add p q hp hq =>
            rcases hp with ⟨p', hp'⟩
            rcases hq with ⟨q', hq'⟩
            refine ⟨p' + q', ?_⟩
            calc
              AdjoinRoot.mk f (p + q) =
                  (σ (φ (AdjoinRoot.mk f p)) + AdjoinRoot.of f A * σ p') +
                    (σ (φ (AdjoinRoot.mk f q)) + AdjoinRoot.of f A * σ q') :=
                congrArg₂ (· + ·) hp' hq'
              _ = σ (φ (AdjoinRoot.mk f (p + q))) +
                  AdjoinRoot.of f A * σ (p' + q') := by
                simp only [map_add, mul_add]
                ring
        | monomial n r =>
            obtain ⟨u, v, hr⟩ := hcoeff r
            refine ⟨Polynomial.C (ρ u) * Polynomial.X ^ n +
              Polynomial.C (ρ v) * Polynomial.X ^ Nat.succ n, ?_⟩
            rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul,
              AdjoinRoot.mk_C, map_pow, AdjoinRoot.mk_X]
            have hmain :
                AdjoinRoot.of f r =
                  algebraMap k S (ρ r) +
                    algebraMap k S (ρ u) * AdjoinRoot.of f A +
                    algebraMap k S (ρ v) * AdjoinRoot.of f B := himage r u v hr
            rw [hmain, ← hrootrel]
            simp only [map_mul, map_add, map_pow]
            simp only [hφalg, hφof, hρA, map_zero]
            rw [show σ (Polynomial.C (ρ u)) = algebraMap k S (ρ u) by simp [σ],
              show σ (Polynomial.C (ρ v)) = algebraMap k S (ρ v) by simp [σ],
              show σ Polynomial.X = AdjoinRoot.root f by simp [σ]]
            rw [hφroot]
            simp only [show σ (Polynomial.C (ρ r)) = algebraMap k S (ρ r) by simp [σ],
              show σ Polynomial.X = AdjoinRoot.root f by simp [σ], f]
            rw [pow_succ]
            ring
  have hendo (e : S →ₗ[R] S) (he : e.comp e = e) :
      e = 0 ∨ e = LinearMap.id :=
    artinianLocalExample_idempotent k φ σ A hφσ hA_formula hmap_of htop_all hdecomp e he
  simp only [Indecomposable]
  constructor
  · rw [ModuleCat.isZero_iff_subsingleton]
    intro h
    have h10 : (1 : S) = 0 := @Subsingleton.elim S h 1 0
    have hφ10 : (1 : Polynomial k) = 0 := by
      have h := congrArg φ h10
      rw [map_one, map_zero] at h
      exact h
    exact (one_ne_zero : (1 : Polynomial k) ≠ 0) hφ10
  · intro Y Z a
    let e_cat : artinianLocalExampleModule k ⟶ artinianLocalExampleModule k :=
      a.hom ≫ biprod.fst ≫ biprod.inl ≫ a.inv
    let e : S →ₗ[R] S := e_cat.hom
    have he_cat : e_cat ≫ e_cat = e_cat := by
      simp [e_cat, Category.assoc]
    have he : e.comp e = e := by
      have h := congrArg (fun q => q.hom) he_cat
      simpa [e, ModuleCat.hom_comp] using h
    rcases hendo e he with he0 | he1
    · left
      have he_cat0 : e_cat = 0 := by
        apply ModuleCat.hom_ext
        simpa [e] using he0
      have hproj0 :
          a.hom ≫ biprod.fst ≫ biprod.inl ≫ a.inv = 0 := by
        change a.hom ≫ biprod.fst ≫ biprod.inl ≫ a.inv = 0 at he_cat0
        exact he_cat0
      exact moduleCat_isZero_of_biprod_projection_zero a hproj0
    · right
      have he_cat1 : e_cat = 𝟙 _ := by
        apply ModuleCat.hom_ext
        simpa [e] using he1
      have hproj1 :
          a.hom ≫ biprod.fst ≫ biprod.inl ≫ a.inv = 𝟙 _ := by
        change a.hom ≫ biprod.fst ≫ biprod.inl ≫ a.inv = 𝟙 _ at he_cat1
        exact he_cat1
      exact moduleCat_isZero_of_biprod_projection_id a hproj1

/-- The displayed module is not finitely generated.  This implicit fact is
needed to turn the direct-sum conclusion into the source's non-example. -/
theorem artinianLocalExample_not_finite
    (k : Type u) [Field k] :
    ¬ Module.Finite (artinianLocalExampleBaseRing k)
      (artinianLocalExampleAlgebra k) := by
  intro hfinite
  let I := artinianLocalExampleRelationIdeal k
  let R := artinianLocalExampleBaseRing k
  let f := artinianLocalExamplePolynomialRelation k
  let S := artinianLocalExampleAlgebra k
  let ρ₀ : artinianLocalExamplePolynomialRing k →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)
  have hI : I ≤ RingHom.ker ρ₀ := by
    change artinianLocalExampleRelationIdeal k ≤ RingHom.ker ρ₀
    rw [artinianLocalExampleRelationIdeal, Ideal.span_le]
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> simp [ρ₀]
  let ρ : R →+* k :=
    Ideal.Quotient.lift I ρ₀ (fun x hx => RingHom.mem_ker.mp (hI hx))
  let ρP : R →+* Polynomial k := (Polynomial.C : k →+* Polynomial k).comp ρ
  have hρA : ρ (artinianLocalExampleA k) = 0 := by
    change ρ (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2))) = 0
    dsimp [ρ]
    rw [Ideal.Quotient.lift_mk]
    simp [ρ₀]
  have hρB : ρ (artinianLocalExampleB k) = 0 := by
    change ρ (Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2))) = 0
    dsimp [ρ]
    rw [Ideal.Quotient.lift_mk]
    simp [ρ₀]
  have hf : Polynomial.eval₂ ρP Polynomial.X f = 0 := by
    simp [f, artinianLocalExamplePolynomialRelation, ρP,
      hρA, hρB]
  let φ : S →+* Polynomial k := AdjoinRoot.lift ρP Polynomial.X hf
  have hsurj : Function.Surjective φ := by
    intro p
    let q : Polynomial R := p.map (algebraMap k R)
    refine ⟨AdjoinRoot.mk f q, ?_⟩
    rw [AdjoinRoot.lift_mk, Polynomial.eval₂_map]
    have hcomp : ρP.comp (algebraMap k R) =
        (Polynomial.C : k →+* Polynomial k) := by
      apply RingHom.ext
      intro a
      simp only [ρP, RingHom.coe_comp, Function.comp_apply]
      rw [show algebraMap k R a = Ideal.Quotient.mk I (MvPolynomial.C a) by rfl,
        Ideal.Quotient.lift_mk]
      simp [ρ₀]
    rw [hcomp]
    simp
  let ψ : S →ₛₗ[ρ] Polynomial k :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := by
        intro r x
        simp only [Algebra.smul_def]
        rw [map_mul]
        congr 1
        rw [AdjoinRoot.algebraMap_eq]
        rw [AdjoinRoot.lift_of]
        rfl }
  have hfinite' : Module.Finite k (Polynomial k) :=
    Module.Finite.of_surjective ψ hsurj
  exact Polynomial.not_finite hfinite'

/-- The base ring is Artinian. -/
theorem artinianLocalExample_baseRing_isArtinian
    (k : Type u) [Field k] :
    IsArtinianRing (artinianLocalExampleBaseRing k) := by
  let I := artinianLocalExampleRelationIdeal k
  let R := artinianLocalExampleBaseRing k
  let A := artinianLocalExampleA k
  let B := artinianLocalExampleB k
  let Q : Submodule k R := Submodule.span k ({(1 : R), A, B} : Set R)
  have hA2 : A * A = 0 := by
    change Ideal.Quotient.mk I
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (0 : Fin 2)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp [pow_two])
  have hAB : A * B = 0 := by
    change Ideal.Quotient.mk I
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have hB2 : B * B = 0 := by
    change Ideal.Quotient.mk I
      (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (1 : Fin 2)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp [pow_two])
  have hmulA : ∀ z : R, z ∈ Q → z * A ∈ Q := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact Submodule.subset_span (by simp)
        · simp [hA2]
        · simp [mul_comm, hAB]
    | zero => simp
    | add x y _ _ hx hy =>
        rw [add_mul]
        exact Q.add_mem hx hy
    | smul c x hx hmul =>
        rw [smul_mul_assoc]
        exact Q.smul_mem c hmul
  have hmulB : ∀ z : R, z ∈ Q → z * B ∈ Q := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact Submodule.subset_span (by simp)
        · simp [hAB]
        · simp [hB2]
    | zero => simp
    | add x y _ _ hx hy =>
        rw [add_mul]
        exact Q.add_mem hx hy
    | smul c x hx hmul =>
        rw [smul_mul_assoc]
        exact Q.smul_mem c hmul
  have hspan : Q = ⊤ := by
    rw [eq_top_iff]
    intro x hx
    clear hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk I p ∈ Q
    induction p using MvPolynomial.induction_on with
    | C a =>
        change algebraMap k R a ∈ Q
        have hgen : (1 : R) ∈ ({(1 : R), A, B} : Set R) := by simp
        rw [Algebra.algebraMap_eq_smul_one]
        exact Q.smul_mem a (Submodule.subset_span hgen)
    | add p q hp hq =>
        simpa [map_add] using Q.add_mem hp hq
    | mul_X p i hp =>
        fin_cases i
        · simpa [A, artinianLocalExampleA, I, R] using hmulA
            (Ideal.Quotient.mk I p) hp
        · simpa [B, artinianLocalExampleB, I, R] using hmulB
            (Ideal.Quotient.mk I p) hp
  have hfinite : Module.Finite k R := by
    rw [Module.finite_def, Submodule.fg_def]
    exact ⟨{(1 : R), A, B}, by simp, hspan⟩
  exact IsArtinianRing.of_finite k R

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
