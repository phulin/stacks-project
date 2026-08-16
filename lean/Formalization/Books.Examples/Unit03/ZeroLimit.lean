import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Order.DirectedInverseSystem

/-!
# Examples, Chapter 3: A zero limit

This file formalizes the precise constructions and assertions in the section
“A zero limit”.  The inverse-limit notation is represented by Mathlib's
`Functor.sections`, after turning Mathlib's `InverseSystem` data into a
functor on the opposite preorder.
-/

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped DirectSum

namespace Formalization.«Books.Examples».Unit03

universe u v w z

/-! ## Inverse systems and their limits -/

/-- The type-valued functor associated to Mathlib's `InverseSystem` API. -/
def inverseSystemFunctor {I : Type u} [Preorder I] {X : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → X j → X i) [InverseSystem f] : Iᵒᵖ ⥤ Type v where
  obj i := X i.unop
  map {i j} p := ↾fun x => f p.unop.le x
  map_id := by
    intro i
    ext x
    simpa using (InverseSystem.map_self (f := f) x)
  map_comp := by
    intro i j k p q
    ext x
    simpa using (InverseSystem.map_map (f := f) q.unop.le p.unop.le x).symm

/-- The inverse limit of a type-valued inverse system, as a type of sections. -/
def inverseLimit {I : Type u} [Preorder I] {X : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → X j → X i) [InverseSystem f] : Type (max u v) :=
  (inverseSystemFunctor f).sections

/-! ## The set system and the direct-sum vector spaces -/

/-- The direct-sum vector space with one copy of `K` for every element of `S i`. -/
abbrev V (K : Type w) [Field K] {I : Type u} (S : I → Type v) (i : I) :=
  ⨁ _ : S i, K

/-- A basis vector in the direct sum, with the classical index equality made local. -/
noncomputable def basisVector {I : Type u} {S : I → Type v}
    (K : Type w) [Field K] (i : I) (s : S i) (x : K) : V K S i := by
  classical
  exact DirectSum.lof K (S i) (fun _ => K) s x

/-- The transition map on direct sums induced by a transition map on indices. -/
noncomputable def vMap {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    {i j : I} (h : i ≤ j) : V K S j →ₗ[K] V K S i := by
  classical
  exact DirectSum.toModule K (S j) (V K S i)
    (fun s => DirectSum.lof K (S i) (fun _ => K) (f h s))

@[simp]
theorem vMap_lof {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    {i j : I} (h : i ≤ j) (s : S j) (x : K) :
    vMap f K h (basisVector K j s x) = basisVector K i (f h s) x := by
  classical
  change
    DirectSum.toModule K (S j) (V K S i)
        (fun s => DirectSum.lof K (S i) (fun _ => K) (f h s))
        (DirectSum.lof K (S j) (fun _ => K) s x) =
      DirectSum.lof K (S i) (fun _ => K) (f h s) x
  exact DirectSum.toModule_lof (R := K) (ι := S j) (N := V K S i)
    (M := fun _ => K) (φ := fun s => DirectSum.lof K (S i) (fun _ => K) (f h s)) s x

/-- The direct-sum transitions form the inverse system appearing in the source. -/
instance vInverseSystem {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] :
    InverseSystem (fun {_i _j} h => vMap f K h) where
  map_self := by
    classical
    intro i x
    have hmap :
        vMap f K (i := i) (j := i) (le_refl i) = LinearMap.id := by
      apply DirectSum.linearMap_ext
      intro s
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, vMap, DirectSum.toModule_lof, LinearMap.id_apply]
      rw [InverseSystem.map_self (f := f)]
    exact congrArg (fun g : V K S i →ₗ[K] V K S i => g x) hmap
  map_map := by
    classical
    intro k j i hkj hji x
    have hmap :
        (vMap f K hkj).comp (vMap f K hji) = vMap f K (hkj.trans hji) := by
      apply DirectSum.linearMap_ext
      intro s
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, vMap, DirectSum.toModule_lof]
      rw [InverseSystem.map_map (f := f)]
    exact congrArg (fun g : V K S i →ₗ[K] V K S k => g x) hmap

/-- The transition maps on `V` are surjective whenever the maps on `S` are. -/
theorem vMap_surjective {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] {i j : I} (h : i ≤ j)
    (hf : Function.Surjective (f h)) :
    Function.Surjective (vMap f K h) := by
  sorry

/-- The type of compatible families in the direct-sum inverse system. -/
abbrev VLimit {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] := inverseLimit (fun {_i _j} h => vMap f K h)

/-- The component at `i` of a compatible family in `V`. -/
def vComponent {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] (x : VLimit f K) (i : I) : V K S i :=
  x.1 (Opposite.op i)

/-- The zero compatible family in the direct-sum inverse system. -/
def vZeroLimit {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] : VLimit f K := by
  refine ⟨(fun i : Iᵒᵖ => (0 : V K S i.unop)), ?_⟩
  intro i j p
  change vMap f K p.unop.le (0 : V K S i.unop) = (0 : V K S j.unop)
  simp

/-! ## Finite support subsystems -/

/-- A finite nonempty subsystem of a directed inverse system of sets. -/
structure FiniteSubsystem {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) [InverseSystem f] where
  carrier : ∀ i, Set (S i)
  nonempty : ∀ i, (carrier i).Nonempty
  finite : ∀ i, (carrier i).Finite
  stable : ∀ ⦃i j⦄ (h : i ≤ j), Set.MapsTo (f h) (carrier j) (carrier i)

/-- Restrict the transition maps to a finite subsystem. -/
def FiniteSubsystem.map {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) [InverseSystem f]
    (T : FiniteSubsystem f) {_i _j : I} (h : _i ≤ _j) :
    T.carrier _j → T.carrier _i :=
  fun x => ⟨f h x.1, T.stable h x.2⟩

/-- Restricted transition maps again satisfy the inverse-system equations. -/
instance FiniteSubsystem.inverseSystem {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) [InverseSystem f]
    (T : FiniteSubsystem f) :
    InverseSystem (fun {_i _j} h => T.map f h) where
  map_self := by
    intro i x
    apply Subtype.ext
    exact InverseSystem.map_self (f := f) x.1
  map_map := by
    intro k j i hkj hji x
    apply Subtype.ext
    exact InverseSystem.map_map (f := f) hkj hji x.1

/-- The inverse limit of a finite subsystem. -/
abbrev FiniteSubsystem.limit {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) [InverseSystem f]
    (T : FiniteSubsystem f) := inverseLimit (fun {_i _j} h => T.map f h)

/-- Forget the support restrictions in a compatible family. -/
def FiniteSubsystem.limitToParent {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) [InverseSystem f]
    (T : FiniteSubsystem f) :
    T.limit → inverseLimit f := by
  intro x
  refine ⟨fun i => (x.1 i).1, ?_⟩
  intro i j p
  have hx := congrArg Subtype.val (x.2 p)
  change f p.unop.le ((x.1 i).1) = (x.1 j).1 at hx
  exact hx

/-! A finite subsystem containing the supports of a compatible direct-sum family. -/
def supportSet {I : Type u} {S : I → Type v} (K : Type w) [Field K]
    (i : I) (x : V K S i) : Set (S i) := {s | x s ≠ 0}

/-- Every direct-sum vector has finite support. -/
theorem supportSet_finite {I : Type u} {S : I → Type v}
    (K : Type w) [Field K] (i : I) (x : V K S i) :
    (supportSet K i x).Finite := by
  exact DFinsupp.finite_support x

structure FiniteSupportSubsystem {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] (x : VLimit f K) extends FiniteSubsystem f where
  contains_support :
    ∀ i, supportSet K i (vComponent f K x i) ⊆ carrier i

theorem FiniteSupportSubsystem.support_finite {I : Type u} [Preorder I]
    {S : I → Type v} {f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i} [InverseSystem f]
    {K : Type w} [Field K] {x : VLimit f K} (T : FiniteSupportSubsystem f K x)
    (i : I) : (supportSet K i (vComponent f K x i)).Finite := by
  exact (T.toFiniteSubsystem.finite i).subset (T.contains_support i)

/-- The support argument in the proof of the zero-limit statement. -/
theorem exists_finite_support_subsystem {I : Type u} [Preorder I] [IsDirectedOrder I]
    {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] (hS : ∀ i, Nonempty (S i))
    (hf : ∀ ⦃i j⦄ (h : i ≤ j), Function.Surjective (f h))
    (x : VLimit f K)
    (hx : ∃ (i : I), vComponent f K x i ≠ 0) :
    ∃ T : FiniteSupportSubsystem f K x,
      Nonempty T.toFiniteSubsystem.limit := by
  sorry

/-- If the set-system limit is empty, the direct-sum limit is the zero type. -/
theorem v_limit_is_zero {I : Type u} [Preorder I] [IsDirectedOrder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] (hS : ∀ i, Nonempty (S i))
    (hf : ∀ ⦃i j⦄ (h : i ≤ j), Function.Surjective (f h))
    (hlim : IsEmpty (inverseLimit f)) :
    Nonempty (VLimit f K) ∧ Subsingleton (VLimit f K) := by
  refine ⟨⟨vZeroLimit f K⟩, ?_⟩
  sorry

/-! ## The coordinate-sum map and its kernel -/

/-- The unique linear map sending every direct-sum basis vector to `1`. -/
noncomputable def coordinateSum {I : Type u} {S : I → Type v}
    (K : Type w) [Field K] (i : I) : V K S i →ₗ[K] K := by
  classical
  exact DirectSum.toModule K (S i) K (fun _ => (LinearMap.id : K →ₗ[K] K))

@[simp]
theorem coordinateSum_lof {I : Type u} {S : I → Type v}
    (K : Type w) [Field K] (i : I) (s : S i) (x : K) :
    coordinateSum (S := S) K i (basisVector K i s x) = x := by
  classical
  simp [basisVector, coordinateSum]

/-- The coordinate-sum map is uniquely determined by its values on basis vectors. -/
theorem coordinateSum_unique {I : Type u} {S : I → Type v}
    (K : Type w) [Field K] (i : I) (φ : V K S i →ₗ[K] K)
    (hφ : ∀ s : S i, φ (basisVector K i s 1) = 1) :
    φ = coordinateSum (S := S) K i := by
  sorry

/-- The subspace `W_i` in the source. -/
noncomputable def W {I : Type u} {S : I → Type v} (K : Type w) [Field K] (i : I) :
    Submodule K (V K S i) := LinearMap.ker (coordinateSum (S := S) K i)

/-- The coordinate-sum maps commute with the direct-sum transitions. -/
theorem coordinateSum_comp_vMap {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] {i j : I} (h : i ≤ j) :
    (coordinateSum (S := S) K i).comp (vMap f K h) = coordinateSum (S := S) K j := by
  sorry

/-- The restricted transition map on the kernels `W_i`. -/
noncomputable def wMap {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] {i j : I} (h : i ≤ j) :
    W (S := S) K j →ₗ[K] W (S := S) K i :=
  ((vMap f K h).comp (W (S := S) K j).subtype).codRestrict (W (S := S) K i) (by
    intro x
    change coordinateSum (S := S) K i (vMap f K h x.1) = 0
    have hcoord :
        coordinateSum (S := S) K i (vMap f K h x.1) =
          coordinateSum (S := S) K j x.1 := by
      simpa using congrArg (fun g : V K S j →ₗ[K] K => g x.1)
        (coordinateSum_comp_vMap f K h)
    rw [hcoord]
    exact x.2)

/-- The kernel transition maps form the induced inverse system. -/
instance wInverseSystem {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] :
    InverseSystem (fun {_i _j} h => wMap f K h) where
  map_self := by
    classical
    intro i x
    have hmap : wMap f K (i := i) (j := i) (le_refl i) = LinearMap.id := by
      apply LinearMap.ext
      intro y
      apply Subtype.ext
      change vMap f K (le_refl i) y.1 = y.1
      exact InverseSystem.map_self (f := fun {i j} h => vMap f K h) y.1
    exact congrArg (fun g : W (S := S) K i →ₗ[K] W (S := S) K i => g x) hmap
  map_map := by
    classical
    intro k j i hkj hji x
    have hmap :
        (wMap f K hkj).comp (wMap f K hji) = wMap f K (hkj.trans hji) := by
      apply LinearMap.ext
      intro y
      apply Subtype.ext
      change vMap f K hkj (vMap f K hji y.1) = vMap f K (hkj.trans hji) y.1
      exact InverseSystem.map_map (f := fun {i j} h => vMap f K h) hkj hji y.1
    exact congrArg (fun g : W (S := S) K i →ₗ[K] W (S := S) K k => g x) hmap

/-- Surjectivity of the induced maps on the kernels. -/
theorem wMap_surjective {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] {i j : I} (h : i ≤ j)
    (hf : Function.Surjective (f h)) :
    Function.Surjective (wMap f K h) := by
  sorry

/-- The type of compatible families in the kernel inverse system. -/
abbrev WLimit {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] := inverseLimit (fun {_i _j} h => wMap f K h)

/-- The zero compatible family in the kernel inverse system. -/
noncomputable def wZeroLimit {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] : WLimit f K := by
  refine ⟨(fun i : Iᵒᵖ => (0 : W (S := S) K i.unop)), ?_⟩
  intro i j p
  change wMap f K p.unop.le (0 : W (S := S) K i.unop) =
    (0 : W (S := S) K j.unop)
  simp

/-! ## Inverse-system valued module diagrams -/

/-- The inverse system of modules associated with linear transition maps. -/
def inverseSystemModuleFunctor {I : Type u} [Preorder I] {W : I → Type z}
    (K : Type w) [Field K]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (g : ∀ ⦃i j : I⦄, i ≤ j → W j →ₗ[K] W i)
    [InverseSystem (fun {_i _j} h => g h)] :
    Iᵒᵖ ⥤ ModuleCat.{z} K where
  obj i := ModuleCat.of K (W i.unop)
  map {i j} p := ModuleCat.ofHom (g p.unop.le)
  map_id := by
    intro i
    apply ModuleCat.hom_ext
    ext x
    simpa using (InverseSystem.map_self (f := fun {_i _j} h => g h) x)
  map_comp := by
    intro i j k p q
    apply ModuleCat.hom_ext
    ext x
    simpa using
      (InverseSystem.map_map (f := fun {_i _j} h => g h) q.unop.le p.unop.le x).symm

/-- The constant inverse system of rank-one `K`-modules, lifted to a chosen universe. -/
def constantModuleFunctor {I : Type u} [Preorder I] (K : Type w) [Field K] :
    Iᵒᵖ ⥤ ModuleCat.{max z w} K :=
  (Functor.const Iᵒᵖ).obj (ModuleCat.of K (ULift.{z} K))

/-- The `V_i` module diagram in the source. -/
noncomputable def vModuleFunctor {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] : Iᵒᵖ ⥤ ModuleCat.{max v w} K :=
  inverseSystemModuleFunctor (W := fun i => V K S i) K
    (fun {_i _j} h => vMap f K h)

/-- The `W_i` module diagram in the source. -/
noncomputable def wModuleFunctor {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] : Iᵒᵖ ⥤ ModuleCat.{max v w} K :=
  inverseSystemModuleFunctor (W := fun i => W (S := S) K i) K
    (fun {_i _j} h => wMap f K h)

/-- The constant `K`-module diagram in the same universe as `V` and `W`. -/
def constantKModuleFunctor {I : Type u} [Preorder I] (K : Type w) [Field K] :
    Iᵒᵖ ⥤ ModuleCat.{max v w} K :=
  (Functor.const Iᵒᵖ).obj (ModuleCat.of K (ULift.{max v w} K))

/-- The inclusion of the kernel diagram into the direct-sum diagram. -/
noncomputable def wToVModuleNatTrans {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] : wModuleFunctor f K ⟶ vModuleFunctor f K where
  app i := ModuleCat.ofHom ((W (S := S) K i.unop).subtype)
  naturality i j p := by
    apply ModuleCat.hom_ext
    rfl

/-! The universe-lifted form of the coordinate map used by `wShortComplex`. -/
noncomputable def coordinateSumLift {I : Type u} {S : I → Type v}
    (K : Type w) [Field K] (i : I) :
    V K S i →ₗ[K] ULift.{max v w} K :=
  (ULift.moduleEquiv : ULift.{max v w} K ≃ₗ[K] K).symm.toLinearMap.comp
    (coordinateSum (S := S) K i)

/-- The coordinate-sum morphism from the direct-sum diagram to the constant diagram. -/
noncomputable def vToConstantKModuleNatTrans {I : Type u} [Preorder I]
    {S : I → Type v} (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] :
    vModuleFunctor f K ⟶ constantKModuleFunctor K where
  app i := ModuleCat.ofHom (coordinateSumLift (S := S) K i.unop)
  naturality i j p := by
    apply ModuleCat.hom_ext
    ext x
    apply ULift.ext
    change coordinateSum (S := S) K j.unop (vMap f K p.unop.le x) =
      coordinateSum (S := S) K i.unop x
    exact congrArg (fun g : V K S i.unop →ₗ[K] K => g x)
      (coordinateSum_comp_vMap f K p.unop.le)

/-- The levelwise short complex `0 → W_i → V_i → K → 0`. -/
noncomputable def wShortComplex {I : Type u} {S : I → Type v}
    (K : Type w) [Field K] (i : I) :
    ShortComplex (ModuleCat.{max v w} K) :=
  ShortComplex.mk
    (ModuleCat.ofHom (W (S := S) K i).subtype :
      ModuleCat.of K (W (S := S) K i) ⟶ ModuleCat.of K (V K S i))
    (ModuleCat.ofHom (coordinateSumLift (S := S) K i) :
      ModuleCat.of K (V K S i) ⟶ ModuleCat.of K (ULift.{max v w} K))
    (by
      apply ModuleCat.hom_ext
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero] using
        (LinearMap.ext (fun x : W (S := S) K i => by
          apply ULift.ext
          exact x.2) :
          (coordinateSumLift (S := S) K i).comp (W (S := S) K i).subtype = 0))

/-! The short complex of inverse-system valued modules in the source. -/
noncomputable def inverseSystemShortComplex {I : Type u} [Preorder I]
    {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] :
    ShortComplex (Iᵒᵖ ⥤ ModuleCat.{max v w} K) :=
  ShortComplex.mk (wToVModuleNatTrans f K) (vToConstantKModuleNatTrans f K) (by
    apply NatTrans.ext
    funext i
    apply ModuleCat.hom_ext
    ext x
    apply ULift.ext
    exact x.2)

/-- A split for the inverse-system short complex is a splitting in the functor category. -/
def IsSplitInverseSystemShortComplex {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] : Prop :=
  Nonempty (inverseSystemShortComplex f K).Splitting

/-- The source's nonsplit short exact sequence of inverse systems. -/
def IsNonsplitShortExactInverseSystem {I : Type u} [Preorder I]
    {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] : Prop :=
  (inverseSystemShortComplex f K).ShortExact ∧
    ¬ IsSplitInverseSystemShortComplex f K

/-- The kernel sequence is nonsplit and short exact as an inverse-system sequence. -/
theorem w_sequence_is_nonsplit_short_exact {I : Type u} [Preorder I] [IsDirectedOrder I]
    {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] (hS : ∀ i, Nonempty (S i))
    (hf : ∀ ⦃i j⦄ (h : i ≤ j), Function.Surjective (f h))
    (hlim : IsEmpty (inverseLimit f)) :
    IsNonsplitShortExactInverseSystem f K := by
  sorry

/-- The kernel system has zero inverse limit. -/
theorem w_limit_is_zero {I : Type u} [Preorder I] [IsDirectedOrder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] (hS : ∀ i, Nonempty (S i))
    (hf : ∀ ⦃i j⦄ (h : i ≤ j), Function.Surjective (f h))
    (hlim : IsEmpty (inverseLimit f)) :
    Nonempty (WLimit f K) ∧ Subsingleton (WLimit f K) := by
  refine ⟨⟨wZeroLimit f K⟩, ?_⟩
  sorry

/-! ## The first derived inverse limit -/

/-- The module diagram, lifted to the common universe needed for `Ext`. -/
noncomputable def liftedInverseSystemModuleFunctor
    {I : Type u} [Preorder I] {W : I → Type z}
    (K : Type w) [Field K]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (g : ∀ ⦃i j : I⦄, i ≤ j → W j →ₗ[K] W i)
    [InverseSystem (fun {_i _j} h => g h)] :
    Iᵒᵖ ⥤ ModuleCat.{max z w} K :=
  inverseSystemModuleFunctor K g ⋙ ModuleCat.uliftFunctor.{w} K

/-- `R¹ lim W_i`, modeled by the standard `Ext¹` description of derived limits.

The limit of a module diagram is the Hom functor from the constant rank-one
diagram, so its first right-derived functor is represented by this `Ext¹`. -/
noncomputable abbrev ROneLimit {I : Type u} [Preorder I] (K : Type w) [Field K]
    {W : I → Type z} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (g : ∀ ⦃i j : I⦄, i ≤ j → W j →ₗ[K] W i)
    [InverseSystem (fun {_i _j} h => g h)] :=
  let C := Iᵒᵖ ⥤ ModuleCat.{max z w} K
  letI := CategoryTheory.HasExt.standard C
  CategoryTheory.Abelian.Ext (constantModuleFunctor (I := I) K)
    (liftedInverseSystemModuleFunctor K g) 1

/-- The final nonvanishing assertion in the source section. -/
theorem w_first_derived_limit_nontrivial {I : Type u} [Preorder I] [IsDirectedOrder I]
    {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f]
    (hS : ∀ i, Nonempty (S i))
    (hf : ∀ ⦃i j⦄ (h : i ≤ j), Function.Surjective (f h))
    (hlim : IsEmpty (inverseLimit f)) :
    Nontrivial (ROneLimit (W := fun i => W (S := S) K i) K
      (fun {i j} h => wMap f K h)) := by
  sorry

end Formalization.«Books.Examples».Unit03
