import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Module.ULift
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

/-! The universe-lifted form of the coordinate map used by `wShortComplex`. -/
noncomputable def coordinateSumLift {I : Type u} {S : I → Type v}
    (K : Type w) [Field K] (i : I) :
    V K S i →ₗ[K] ULift.{max v w} K :=
  (ULift.moduleEquiv : ULift.{max v w} K ≃ₗ[K] K).symm.toLinearMap.comp
    (coordinateSum (S := S) K i)

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

/-- A compatible family of right inverses would split the short exact sequence. -/
def InverseSystemSplits {I : Type u} [Preorder I] {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] : Prop :=
  ∃ s : ∀ i, K →ₗ[K] V K S i,
    (∀ i, (coordinateSum (S := S) K i).comp (s i) = LinearMap.id) ∧
      (∀ ⦃i j⦄ (h : i ≤ j), (vMap f K h).comp (s j) = s i)

/-- The source's nonsplit short exact sequence of inverse systems. -/
def IsNonsplitShortExactInverseSystem {I : Type u} [Preorder I]
    {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f] : Prop :=
  (∀ i, (wShortComplex (S := S) K i).ShortExact) ∧
    (∀ ⦃i j⦄ (h : i ≤ j),
      (vMap f K h).comp (W (S := S) K j).subtype =
        (W (S := S) K i).subtype.comp (wMap f K h)) ∧
    (∀ ⦃i j⦄ (h : i ≤ j),
      (coordinateSum (S := S) K i).comp (vMap f K h) =
        coordinateSum (S := S) K j) ∧
    ¬ InverseSystemSplits f K

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

/-! ## The levelwise short complex and the first derived inverse limit -/

/--
Mathlib's current API has no canonical `R¹ lim` construction for arbitrary
inverse systems.  This small named interface records the carrier and its
module structure so the source's nonvanishing assertion remains a usable
statement without inventing a parallel derived-limit definition.
-/
class FirstDerivedLimit {I : Type u} [Preorder I] (K : Type w) [Field K]
    {W : I → Type z} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (g : ∀ ⦃i j : I⦄, i ≤ j → W j →ₗ[K] W i)
    [InverseSystem (fun {_i _j} h => g h)] where
  carrier : Type z
  [addCommGroup : AddCommGroup carrier]
  [module : Module K carrier]

/-- The carrier denoted by `R¹ lim W_i` once a derived-limit implementation is supplied. -/
abbrev ROneLimit {I : Type u} [Preorder I] (K : Type w) [Field K]
    {W : I → Type z} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (g : ∀ ⦃i j : I⦄, i ≤ j → W j →ₗ[K] W i)
    [InverseSystem (fun {_i _j} h => g h)] [FirstDerivedLimit (W := W) K g] : Type z :=
  FirstDerivedLimit.carrier (K := K) (g := g)

/-- The final nonvanishing assertion in the source section. -/
theorem w_first_derived_limit_nontrivial {I : Type u} [Preorder I] [IsDirectedOrder I]
    {S : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → S j → S i) (K : Type w) [Field K]
    [InverseSystem f]
    (hS : ∀ i, Nonempty (S i))
    (hf : ∀ ⦃i j⦄ (h : i ≤ j), Function.Surjective (f h))
    (hlim : IsEmpty (inverseLimit f))
    [FirstDerivedLimit (W := fun i => W (S := S) K i) K
      (fun {i j} h => wMap f K h)] :
    Nontrivial (ROneLimit (W := fun i => W (S := S) K i) K
      (fun {i j} h => wMap f K h)) := by
  sorry

end Formalization.«Books.Examples».Unit03
