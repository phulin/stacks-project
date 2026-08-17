import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.DirectedInverseSystem

/-!
# Examples, Chapter 2: An empty limit

The source uses the finite subsets of an uncountable set as a directed
indexing poset.  `Finset S` is Mathlib's canonical type of finite subsets;
its existing `IsDirectedOrder` instance supplies the directedness assertion.
The inverse limit is represented by the compatible sections of the associated
type-valued functor.
-/

open CategoryTheory
open Opposite

namespace Formalization.Books.Examples.Unit02

universe u v

/-! ## The inverse-system API -/

/-!
The Mathlib `InverseSystem` class records the identity and composition laws
for maps indexed by a preorder.  This small conversion exposes the same data
as the corresponding functor on the opposite preorder, so that
`Functor.sections` is the concrete type-valued inverse limit.
-/

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

def inverseLimit {I : Type u} [Preorder I] {X : I → Type v}
    (f : ∀ ⦃i j : I⦄, i ≤ j → X j → X i) [InverseSystem f] : Type (max u v) :=
  (inverseSystemFunctor f).sections

/-! ## Finite subsets and their injective maps -/

/-!
`Finset S` is definitionally a finite subset of `S`, with its order given by
inclusion.  In particular, the standard `Finset.isDirected_le` instance is
the directed partially ordered set used in the source.
-/

/-- The set of injective maps from a finite subset `T` to `ℕ`. -/
def M (S : Type u) (T : Finset S) : Set (T → ℕ) :=
  {f | Function.Injective f}

/-- The type of elements of the source's set `M_T`. -/
abbrev MType (S : Type u) (T : Finset S) := ↥(M S T)

/-- The inclusion of finite subsets as an injective map of their subtypes. -/
def finiteSubsetInclusion {S : Type u} {T T' : Finset S} (h : T ≤ T') : T → T' :=
  fun x => ⟨x.1, h x.2⟩

theorem finiteSubsetInclusion_injective {S : Type u} {T T' : Finset S} (h : T ≤ T') :
    Function.Injective (finiteSubsetInclusion h) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : T' => z.1) hxy

/-- Restriction of an injective map along an inclusion `T ⊆ T'`. -/
def restriction {S : Type u} {T T' : Finset S} (h : T ≤ T') : MType S T' → MType S T :=
  fun f => ⟨f.1 ∘ finiteSubsetInclusion h, f.2.comp (finiteSubsetInclusion_injective h)⟩

/-- Each `M_T` is nonempty, by enumerating the finite subtype `T`. -/
theorem m_nonempty (S : Type u) (T : Finset S) : Nonempty (MType S T) := by
  classical
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  refine ⟨⟨fun x => (e x : ℕ), ?_⟩⟩
  intro x y hxy
  apply e.injective
  exact Fin.ext hxy

/-- Restriction maps are surjective for inclusions of finite subsets. -/
theorem restriction_surjective {S : Type u} {T T' : Finset S} (h : T ≤ T') :
    Function.Surjective (restriction (S := S) h) := by
  sorry

/-! ## The inverse system and its limit -/

/-- The restriction maps satisfy the inverse-system identity law. -/
instance mInverseSystem (S : Type u) :
    InverseSystem (fun {_T _T' : Finset S} h => restriction (S := S) h) where
  map_self := by
    intro T f
    apply Subtype.ext
    funext x
    rfl
  map_map := by
    intro T T' T'' hTT' hT'T'' f
    apply Subtype.ext
    funext x
    rfl

/-- The inverse limit of the family `(M_T)_T`. -/
abbrev mLimit (S : Type u) :=
  inverseLimit (fun {_T _T' : Finset S} h => restriction (S := S) h)

/-- The component of a compatible family at a finite subset `T`. -/
def mLimitComponent {S : Type u} (x : mLimit S) (T : Finset S) : MType S T :=
  x.1 (Opposite.op T)

/-- The map `S → ℕ` obtained from a compatible family by evaluating singleton components. -/
def inducedMap {S : Type u} (x : mLimit S) : S → ℕ :=
  fun s => (mLimitComponent x ({s} : Finset S)).1 ⟨s, by simp⟩

/-- Compatibility of a family forces its singleton evaluations to be injective. -/
theorem inducedMap_injective {S : Type u} (x : mLimit S) :
    Function.Injective (inducedMap x) := by
  sorry

/-- The inverse limit is empty when the underlying set `S` is uncountable. -/
theorem mLimit_isEmpty (S : Type u) [Uncountable S] : IsEmpty (mLimit S) := by
  refine ⟨fun x => ?_⟩
  exact (not_injective_uncountable_countable (inducedMap x))
    (inducedMap_injective x)

end Formalization.Books.Examples.Unit02
