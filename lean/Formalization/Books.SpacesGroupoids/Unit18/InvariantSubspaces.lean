import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Sets.OpenCover

/-!
# Groupoids in Algebraic Spaces, Chapter 18: invariant subspaces

The algebraic-space development is not available in this project snapshot.  As
in the existing spaces formalizations, `TopCat` supplies the underlying
space, while `Over` supplies the structure morphism to a base space.  The
groupoid interface below retains the source's pointwise groupoid condition.
-/

namespace Formalization.«Books.SpacesGroupoids».Unit18

open CategoryTheory
open CategoryTheory.Limits
open Set
open TopologicalSpace

universe u v

/-! ## Ambient algebraic-space and groupoid interfaces -/

/-- The ambient category used for algebraic spaces in this project snapshot. -/
abbrev AlgebraicSpace := TopCat

/-- Morphisms of the ambient algebraic spaces. -/
abbrev AlgebraicSpaceMorphism (X Y : AlgebraicSpace) := X ⟶ Y

/-- Algebraic spaces over a fixed ambient base. -/
abbrev AlgebraicSpaceOver (B : AlgebraicSpace) := Over B

/-- Pairs of arrows which can be composed in the source-target convention. -/
abbrev Composable {Obj Arr : Type*} (source target : Arr → Obj) :=
  {p : Arr × Arr // source p.1 = target p.2}

/--
The pointwise axioms for the quintuple `(U, R, s, t, c)` in the source.

This is the set-level groupoid structure used for each test object.  The
composition convention is the one in the book: `(a, b)` is composable when
`s a = t b`, and its composite has source `s b` and target `t a`.
-/
structure IsPointwiseGroupoid {Obj Arr : Type*}
    (source target : Arr → Obj)
    (comp : Composable source target → Arr) where
  unit : Obj → Arr
  inv : Arr → Arr
  source_unit : ∀ x, source (unit x) = x
  target_unit : ∀ x, target (unit x) = x
  source_comp : ∀ p, source (comp p) = source p.1.2
  target_comp : ∀ p, target (comp p) = target p.1.1
  source_inv : ∀ a, source (inv a) = target a
  target_inv : ∀ a, target (inv a) = source a
  comp_right_unit : ∀ a,
    comp ⟨(a, unit (source a)), by
      rw [target_unit]⟩ = a
  comp_left_unit : ∀ a,
    comp ⟨(unit (target a), a), by
      rw [source_unit]⟩ = a
  comp_right_inv : ∀ a,
    comp ⟨(a, inv a), by
      rw [target_inv]⟩ = unit (target a)
  comp_left_inv : ∀ a,
    comp ⟨(inv a, a), by
      rw [source_inv]⟩ = unit (source a)
  assoc : ∀ (a b c : Arr) (hab : source a = target b)
    (hbc : source b = target c),
    comp ⟨(comp ⟨(a, b), hab⟩, c), by
      change source (comp ⟨(a, b), hab⟩) = target c
      rw [source_comp]
      exact hbc⟩ =
      comp ⟨(a, comp ⟨(b, c), hbc⟩), by
        change source a = target (comp ⟨(b, c), hbc⟩)
        rw [target_comp]
        exact hab⟩

/--
A groupoid in algebraic spaces over `B`, with the source's pointwise
characterization quantified over all algebraic-space test objects over `B`.
-/
structure GroupoidInAlgebraicSpaces (S B : AlgebraicSpace) where
  BToS : B ⟶ S
  U : AlgebraicSpaceOver B
  R : AlgebraicSpaceOver B
  s : R ⟶ U
  t : R ⟶ U
  c : pullback s t ⟶ R
  isGroupoid : ∀ T : AlgebraicSpaceOver B,
    IsPointwiseGroupoid
      (fun r : T ⟶ R => r ≫ s)
      (fun r : T ⟶ R => r ≫ t)
      (fun p => pullback.lift p.1.1 p.1.2 p.2 ≫ c)

/-- A quasi-compact map in the topological algebraic-space interface. -/
class QuasiCompactMap {X Y : AlgebraicSpace} (f : X ⟶ Y) : Prop where
  /-- The preimage of every quasi-compact open is quasi-compact. -/
  isCompact_preimage : ∀ V : Set Y, IsOpen V → IsCompact V → IsCompact (f ⁻¹' V)

/-- An open subset which is quasi-compact in the ambient topology. -/
def IsQuasiCompactOpen {X : AlgebraicSpace} (W : Opens X) : Prop :=
  IsCompact (W : Set X)

/-! ## Definition 18.1 -/

/--
The condition that an open subspace of the object space is invariant under
the groupoid.  The first conjunct records that `W` is an open subspace; the
second is the source's inclusion `t(s⁻¹(W)) ⊆ W`.
-/
def IsRInvariantOpen {S B : AlgebraicSpace}
    (G : GroupoidInAlgebraicSpaces S B) (W : Set G.U.left) : Prop :=
  IsOpen W ∧ G.t.left '' (G.s.left ⁻¹' W) ⊆ W

/-- The condition that a locally closed subspace is invariant under a groupoid. -/
def IsRInvariantLocallyClosed {S B : AlgebraicSpace}
    (G : GroupoidInAlgebraicSpaces S B) (Z : Set G.U.left) : Prop :=
  IsLocallyClosed Z ∧ G.t.left ⁻¹' Z = G.s.left ⁻¹' Z

/--
The condition that a monomorphism into the object space is invariant.  The
two pullback projections to `R` are compared as subobjects of `R`, which is
the categorical form of equality of the two fibre products over `R`.
-/
def IsRInvariantMonomorphism {S B : AlgebraicSpace}
    (G : GroupoidInAlgebraicSpaces S B) (T : AlgebraicSpaceOver B)
    (g : T ⟶ G.U) [Mono g] : Prop :=
  (Subobject.mk (pullback.snd g G.t) : Subobject G.R) =
    Subobject.mk (pullback.fst G.s g)

/-- The arrows of the restriction to an open subspace, on underlying points. -/
def restrictedArrowsToOpen {S B : AlgebraicSpace}
    (G : GroupoidInAlgebraicSpaces S B) (W : Set G.U.left) : Set G.R.left :=
  G.s.left ⁻¹' W

/-- The arrows of the restriction to a locally closed subspace, on underlying points. -/
def restrictedArrowsToLocallyClosed {S B : AlgebraicSpace}
    (G : GroupoidInAlgebraicSpaces S B) (Z : Set G.U.left) : Set G.R.left :=
  G.s.left ⁻¹' Z

/-! ## Immediate consequences of Definition 18.1 -/

/-- For an open subspace, invariance is equivalent to equality of source and target preimages. -/
theorem isRInvariantOpen_iff_preimage_eq
    {S B : AlgebraicSpace}
    (G : GroupoidInAlgebraicSpaces S B) {W : Set G.U.left} (hW : IsOpen W) :
    IsRInvariantOpen G W ↔ G.s.left ⁻¹' W = G.t.left ⁻¹' W := by
  sorry

/-- The restricted arrows of an invariant open are equally the source and target preimages. -/
theorem restrictedArrowsToOpen_eq_target_preimage
    {S B : AlgebraicSpace}
    (G : GroupoidInAlgebraicSpaces S B) {W : Set G.U.left}
    (hW : IsRInvariantOpen G W) :
    restrictedArrowsToOpen G W = G.t.left ⁻¹' W := by
  sorry

/-- The restricted arrows of an invariant locally closed subspace are equally the source and target preimages. -/
theorem restrictedArrowsToLocallyClosed_eq_target_preimage
    {S B : AlgebraicSpace}
    (G : GroupoidInAlgebraicSpaces S B) {Z : Set G.U.left}
    (hZ : IsRInvariantLocallyClosed G Z) :
    restrictedArrowsToLocallyClosed G Z = G.t.left ⁻¹' Z := by
  sorry

/-! ## Lemma 18.2 -/

/-- The open image `s(t⁻¹(W))` is invariant when source and target are open maps. -/
theorem isRInvariantOpen_source_image_target_preimage
    {S B : AlgebraicSpace}
    (G : GroupoidInAlgebraicSpaces S B) {W : Set G.U.left} (hW : IsOpen W)
    (hs : IsOpenMap G.s.left) (ht : IsOpenMap G.t.left) :
    IsRInvariantOpen G (G.s.left '' (G.t.left ⁻¹' W)) := by
  sorry

/-- Open, quasi-compact source and target maps admit an invariant quasi-compact open cover. -/
theorem exists_invariant_quasiCompactOpen_cover
    {S B : AlgebraicSpace}
    (G : GroupoidInAlgebraicSpaces S B)
    (hs : IsOpenMap G.s.left) (ht : IsOpenMap G.t.left)
    [QuasiCompactMap G.s.left] [QuasiCompactMap G.t.left] :
    ∃ (ι : Type v) (W : ι → Opens G.U.left),
      TopologicalSpace.IsOpenCover W ∧
        ∀ i, IsQuasiCompactOpen (W i) ∧
          IsRInvariantOpen G (W i : Set G.U.left) := by
  sorry

end Formalization.«Books.SpacesGroupoids».Unit18
