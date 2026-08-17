import Formalization.Books.Simplicial.Unit12.TruncatedSimplicialObjects
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.AlgebraicTopology.SimplicialObject.Split
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.AlgebraicTopology.SimplicialSet.Splitting
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Simplicial Methods, Chapter 18: Splitting simplicial objects

Mathlib already provides the categorical splitting interface for simplicial
objects.  The source-facing declarations below use
`SimplicialObject.Splitting` rather than introducing a parallel coproduct
decomposition.  In particular, its `IndexSet` is the finite type of
epimorphisms in the simplex category and its `cofan` is the source's displayed
coproduct map.
-/

namespace Formalization.Books.Simplicial.Unit18

open CategoryTheory CategoryTheory.Limits Opposite
open scoped _root_.Simplicial

universe v u

/-! ## The splitting definition -/

/-!
Mathlib's `Subobject` supplies the source's subobjects and their partial order.
The canonical splitting structure records the coproduct colimits, while the
predicate below records the additional requirement that its summand maps are
the chosen subobjects.
-/

/-- The summand maps of a Mathlib splitting are subobjects of the simplicial object. -/
def IsSubobjectSplitting
    {C : Type u} [Category.{v} C]
    {U : SimplicialObject C} (s : SimplicialObject.Splitting U) : Prop :=
  ∀ n, Mono (s.ι n)

/-- A simplicial object is split in the source's subobject sense. -/
abbrev IsSplit {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (U : SimplicialObject C) : Prop :=
  Nonempty {s : SimplicialObject.Splitting U // IsSubobjectSplitting s}

/-!
For a truncated object, every epimorphism out of `⦋m⦌` with `m ≤ r` lands in
a degree at most `r`.  The following helpers package the corresponding full
subcategory objects and morphisms so that the truncated definition has the
same colimit shape as the unrestricted one.
-/

def truncatedSplittingObject (r n : ℕ) (hn : n ≤ r) : SimplexCategory.Truncated r :=
  ⟨⦋n⦌, hn⟩

theorem truncatedSplittingIndexBound
    (r m : ℕ) (hm : m ≤ r)
    (A : SimplicialObject.Splitting.IndexSet (op ⦋m⦌)) : A.1.unop.len ≤ r :=
  (SimplexCategory.len_le_of_epi A.e).trans hm

def truncatedSplittingIndexObject
    (r m : ℕ) (hm : m ≤ r)
    (A : SimplicialObject.Splitting.IndexSet (op ⦋m⦌)) :
    SimplexCategory.Truncated r :=
  ⟨A.1.unop, truncatedSplittingIndexBound r m hm A⟩

def truncatedSplittingIndexMap
    (r m : ℕ) (hm : m ≤ r)
    (A : SimplicialObject.Splitting.IndexSet (op ⦋m⦌)) :
  truncatedSplittingObject r m hm ⟶ truncatedSplittingIndexObject r m hm A :=
  by
    exact ObjectProperty.homMk A.e

def truncatedSplittingCofan
    {C : Type u} [Category.{v} C] (r : ℕ)
    (U : SimplicialObject.Truncated C r)
    (N : (n : ℕ) → n ≤ r → C)
    (ι : ∀ (n : ℕ) (hn : n ≤ r),
      N n hn ⟶ U.obj (op (truncatedSplittingObject r n hn)))
    (m : ℕ) (hm : m ≤ r) :
    Cofan (fun A : SimplicialObject.Splitting.IndexSet (op ⦋m⦌) =>
      N A.1.unop.len (truncatedSplittingIndexBound r m hm A)) :=
  Cofan.mk (U.obj (op (truncatedSplittingObject r m hm))) (fun A =>
    ι A.1.unop.len (truncatedSplittingIndexBound r m hm A) ≫
      U.map (truncatedSplittingIndexMap r m hm A).op)

/-- The source's coproduct decomposition for an `r`-truncated simplicial object. -/
structure TruncatedSplitting
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] (r : ℕ)
    (U : SimplicialObject.Truncated C r) where
  /-- The nondegenerate summand in each degree at most `r`. -/
  N : (n : ℕ) → n ≤ r → C
  /-- Its map into the corresponding degree of the truncated object. -/
  ι : ∀ (n : ℕ) (hn : n ≤ r),
    N n hn ⟶ U.obj (op (truncatedSplittingObject r n hn))
  /-- Each summand map is a subobject inclusion. -/
  mono_ι : ∀ (n : ℕ) (hn : n ≤ r), Mono (ι n hn)
  /-- Each truncated degree is the coproduct of its epi-indexed summands. -/
  isColimit' : ∀ (m : ℕ) (hm : m ≤ r),
    IsColimit (truncatedSplittingCofan r U N ι m hm)

/-- An `r`-truncated simplicial object is split when it has a truncated splitting. -/
abbrev IsTruncatedSplit
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] (r : ℕ)
    (U : SimplicialObject.Truncated C r) : Prop :=
  Nonempty (TruncatedSplitting r U)

/-- The source's coproduct decomposition is the colimit cofan of a splitting. -/
def splitting_decomposition_is_colimit
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    {U : SimplicialObject C}
    (s : SimplicialObject.Splitting U) (n : ℕ) :
    IsColimit (s.cofan (op ⦋n⦌)) :=
  s.isColimit _

/-!
The source's statements `N(U_0) = U_0`,
`U_1 = U_0 \amalg N(U_1)`, and
`U_2 = U_0 \amalg N(U_1) \amalg N(U_1) \amalg N(U_2)` are the degree `0`, `1`,
and `2` specializations of `splitting_decomposition_is_colimit`.  Mathlib's
`IndexSet` records the corresponding identity and degeneracy epimorphisms,
so no separate, choice-dependent binary-coproduct notation is introduced.
-/

/-! ## Simplicial sets and uniqueness of nondegenerate decompositions -/

theorem simplicial_set_is_split (U : SSet.{u}) : IsSplit U :=
  ⟨⟨SSet.splitting U, by
    intro n
    dsimp [SSet.splitting]
    apply (ofHom_mono_iff_injective _).2
    exact Subtype.val_injective⟩⟩

theorem simplicial_set_canonical_summand (U : SSet.{u}) (n : ℕ) :
    (SSet.splitting U).N n = U.nonDegenerate n :=
  rfl

/-- Every splitting of a simplicial set has the canonical nondegenerate summands. -/
theorem simplicial_set_splitting_unique
    (U : SSet.{u}) (s : SimplicialObject.Splitting U) :
    ∀ n, ∃ e : s.N n ≅ (SSet.splitting U).N n,
      e.hom ≫ (SSet.splitting U).ι n = s.ι n := by
  sorry

theorem simplicial_set_nonDegenerate_decomposition
    (U : SSet.{u}) {n : ℕ} (x : U _⦋n⦌) :
    ∃ (m : ℕ) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f)
      (y : U.nonDegenerate m),
      x = U.map f.op y :=
  U.exists_nonDegenerate x

/-- The dimension in a nondegenerate decomposition is unique. -/
theorem simplicial_set_unique_nonDegenerate_dimension
    (U : SSet.{u}) {n m₁ m₂ : ℕ} (x : U _⦋n⦌)
    (f₁ : ⦋n⦌ ⟶ ⦋m₁⦌) [Epi f₁] (y₁ : U.nonDegenerate m₁)
    (h₁ : x = U.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m₂⦌) [Epi f₂] (y₂ : U.nonDegenerate m₂)
    (h₂ : x = U.map f₂.op y₂) :
    m₁ = m₂ :=
  U.unique_nonDegenerate_dim x f₁ y₁ h₁ f₂ y₂ h₂

/-- The nondegenerate simplex in a fixed-dimensional decomposition is unique. -/
theorem simplicial_set_unique_nonDegenerate_simplex
    (U : SSet.{u}) {n m : ℕ} (x : U _⦋n⦌)
    (f₁ f₂ : ⦋n⦌ ⟶ ⦋m⦌) [Epi f₁]
    (y₁ y₂ : U.nonDegenerate m)
    (h₁ : x = U.map f₁.op y₁) (h₂ : x = U.map f₂.op y₂) :
    y₁ = y₂ := by
  exact U.unique_nonDegenerate_simplex x f₁ y₁ h₁ f₂ y₂ h₂

/-- The epimorphism in a fixed-dimensional decomposition is unique. -/
theorem simplicial_set_unique_nonDegenerate_map
    (U : SSet.{u}) {n m : ℕ} (x : U _⦋n⦌)
    (f₁ f₂ : ⦋n⦌ ⟶ ⦋m⦌) [Epi f₁]
    (y₁ y₂ : U.nonDegenerate m)
    (h₁ : x = U.map f₁.op y₁) (h₂ : x = U.map f₂.op y₂) :
    f₁ = f₂ := by
  exact U.unique_nonDegenerate_map x f₁ y₁ h₁ f₂ y₂ h₂

/-! ## Maps preserving nondegenerate simplices -/

/-- Condition (a) in the source's map lemma. -/
def MapsNondegenerate
    {U V : SSet.{u}} (f : U ⟶ V) : Prop :=
  ∀ (n : ℕ) (x : U _⦋n⦌),
    x ∈ U.nonDegenerate n → f.app (op ⦋n⦌) x ∈ V.nonDegenerate n

/-- The map induced by a simplicial map on nondegenerate `n`-simplices. -/
def nondegenerateMap
    {U V : SSet.{u}} (f : U ⟶ V) (hf : MapsNondegenerate f) (n : ℕ) :
    U.nonDegenerate n → V.nonDegenerate n :=
  fun x => ⟨f.app (op ⦋n⦌) x.1, hf n x.1 x.2⟩

theorem simplicial_set_map_injective_of_nonDegenerate
    {U V : SSet.{u}} (f : U ⟶ V) (hf : MapsNondegenerate f)
    (hN : ∀ n, Function.Injective (nondegenerateMap f hf n)) :
    ∀ n, Function.Injective (f.app (op ⦋n⦌)) := by
  sorry

theorem simplicial_set_map_surjective_of_nonDegenerate
    {U V : SSet.{u}} (f : U ⟶ V) (hf : MapsNondegenerate f)
    (hN : ∀ n, Function.Surjective (nondegenerateMap f hf n)) :
    ∀ n, Function.Surjective (f.app (op ⦋n⦌)) := by
  sorry

theorem simplicial_set_map_bijective_of_nonDegenerate
    {U V : SSet.{u}} (f : U ⟶ V) (hf : MapsNondegenerate f)
    (hN : ∀ n, Function.Bijective (nondegenerateMap f hf n)) :
    ∀ n, Function.Bijective (f.app (op ⦋n⦌)) := by
  sorry

/-! ## The simplicial-set n-skeleton -/

/-- The source's sub-simplicial set `U'` is Mathlib's `U.skeleton (n + 1)`. -/
def simplicialSetNSkeleton (U : SSet.{u}) (n : ℕ) : U.Subcomplex :=
  U.skeleton (n + 1)

/-- The inclusion of the source's `n`-skeleton into the simplicial set. -/
def simplicialSetNSkeletonInclusion (U : SSet.{u}) (n : ℕ) :
    (simplicialSetNSkeleton U n : SSet) ⟶ U :=
  (simplicialSetNSkeleton U n).ι

theorem simplicial_set_n_skeleton_subobject (U : SSet.{u}) (n : ℕ) :
    Mono (simplicialSetNSkeletonInclusion U n) := by
  dsimp [simplicialSetNSkeletonInclusion]
  infer_instance

theorem simplicial_set_n_skeleton_agrees_below
    (U : SSet.{u}) (n i : ℕ) (hi : i ≤ n) :
    (simplicialSetNSkeleton U n).obj (op ⦋i⦌) = Set.univ := by
  simpa [simplicialSetNSkeleton] using
    U.skeleton_obj_eq_top (d := i) (n := n + 1) (Nat.lt_succ_of_le hi)

theorem simplicial_set_n_skeleton_high_simplices_degenerate
    (U : SSet.{u}) (n m : ℕ) (hm : n < m)
    {x : U _⦋m⦌} (hx : x ∈ (simplicialSetNSkeleton U n).obj (op ⦋m⦌)) :
    x ∈ U.degenerate m := by
  sorry

/-! ## Normalized subobjects in an abelian category -/

/--
The source's normalized subobject, using its convention that the first `m`
faces are killed.  This is intentionally stated directly rather than
identifying it with Mathlib's `NormalizedMooreComplex`, whose convention
kills the other set of `m` faces.
-/
noncomputable def normalizedSubobject
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    (n : ℕ) → Subobject (U _⦋n⦌)
  | 0 => ⊤
  | n + 1 =>
      Finset.univ.inf (fun i : Fin (n + 1) =>
        kernelSubobject (U.δ (Fin.castSucc i)))

noncomputable abbrev normalizedObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) : C :=
  normalizedSubobject U n

theorem normalizedSubobject_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    normalizedSubobject U 0 = ⊤ :=
  rfl

theorem normalizedSubobject_succ
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    normalizedSubobject U (n + 1) =
      Finset.univ.inf (fun i : Fin (n + 1) =>
        kernelSubobject (U.δ (Fin.castSucc i))) :=
  rfl

/-- A splitting whose summands and inclusions are the source's normalized ones. -/
def IsNormalizedSplitting
    {C : Type u} [Category.{v} C] [Abelian C]
    {U : SimplicialObject C} (s : SimplicialObject.Splitting U) : Prop :=
  (∀ n, ∃ e : s.N n ≅ normalizedObject U n,
    e.hom ≫ (normalizedSubobject U n).arrow = s.ι n) ∧
    ∀ n, Mono (s.ι n)

/-! ## Splitting of simplicial abelian groups -/

theorem simplicial_abelian_group_has_normalized_splitting
    (U : SimplicialObject (AddCommGrpCat.{u})) :
    ∃ s : SimplicialObject.Splitting U, IsNormalizedSplitting s := by
  sorry

/-- The normalized summands are functorial under maps of simplicial objects. -/
theorem normalizedSubobject_map_factors
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    (normalizedSubobject V n).Factors
      ((normalizedSubobject U n).arrow ≫ f.app (op ⦋n⦌)) := by
  sorry

noncomputable def normalizedSubobjectMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    normalizedObject U n ⟶ normalizedObject V n :=
  (normalizedSubobject V n).factorThru
    ((normalizedSubobject U n).arrow ≫ f.app (op ⦋n⦌))
    (normalizedSubobject_map_factors f n)

theorem normalizedSubobjectMap_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    normalizedSubobjectMap f n ≫ (normalizedSubobject V n).arrow =
      (normalizedSubobject U n).arrow ≫ f.app (op ⦋n⦌) :=
  Subobject.factorThru_arrow _ _ _

theorem normalizedSubobjectMap_id
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    normalizedSubobjectMap (𝟙 U) n = 𝟙 (normalizedObject U n) := by
  dsimp only [normalizedObject]
  apply (cancel_mono (normalizedSubobject U n).arrow).1
  rw [normalizedSubobjectMap_arrow]
  simp

theorem normalizedSubobjectMap_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V W : SimplicialObject C} (f : U ⟶ V) (g : V ⟶ W) (n : ℕ) :
    normalizedSubobjectMap (f ≫ g) n =
      normalizedSubobjectMap f n ≫ normalizedSubobjectMap g n := by
  sorry

/-! ## Splitting in an abelian category -/

theorem abelian_category_has_normalized_splitting
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    ∃ s : SimplicialObject.Splitting U, IsNormalizedSplitting s := by
  sorry

/-! ## Normalization reflects mono, epi, and isomorphism -/

theorem normalized_reflects_monomorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V)
    (hN : ∀ n, Mono (normalizedSubobjectMap f n)) :
    ∀ n, Mono (f.app (op ⦋n⦌)) := by
  sorry

theorem normalized_reflects_epimorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V)
    (hN : ∀ n, Epi (normalizedSubobjectMap f n)) :
    ∀ n, Epi (f.app (op ⦋n⦌)) := by
  sorry

theorem normalized_reflects_isomorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V)
    (hN : ∀ n, IsIso (normalizedSubobjectMap f n)) :
    ∀ n, IsIso (f.app (op ⦋n⦌)) := by
  sorry

/-! ## The last face on normalized subobjects -/

/-!
The source's last-face assertion is only meaningful in positive degree.  The
index `n + 1` below records its intended form
`d^(n+1)_(n+1)(N(U_(n+1))) ⊆ N(U_n)`.
-/

theorem normalized_last_face_factors
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (normalizedSubobject U n).Factors
      ((normalizedSubobject U (n + 1)).arrow ≫ U.δ (Fin.last (n + 1))) := by
  sorry

noncomputable def normalizedLastFace
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    normalizedObject U (n + 1) ⟶ normalizedObject U n :=
  (normalizedSubobject U n).factorThru
    ((normalizedSubobject U (n + 1)).arrow ≫ U.δ (Fin.last (n + 1)))
    (normalized_last_face_factors U n)

theorem normalizedLastFace_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    normalizedLastFace U n ≫ (normalizedSubobject U n).arrow =
      (normalizedSubobject U (n + 1)).arrow ≫ U.δ (Fin.last (n + 1)) :=
  Subobject.factorThru_arrow _ _ _

/-! ## The abelian n-skeleton -/

/-- Maps from degree `m` to a degree at most `n`, as used in the source's sum. -/
def boundedSimplexMapIndex (n m : ℕ) :=
  Σ i : Fin (n + 1), (⦋m⦌ ⟶ ⦋i.1⦌)

noncomputable instance boundedSimplexMapIndex_fintype (n m : ℕ) :
    Fintype (boundedSimplexMapIndex n m) := by
  letI : ∀ i : Fin (n + 1), Fintype (⦋m⦌ ⟶ ⦋i.1⦌) :=
    fun i => Fintype.ofFinite _
  exact Sigma.instFintype

/-- The source's sum of the images of all maps from degree `m` to degree at most `n`. -/
noncomputable def abelianNSkeletonSubobject
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n m : ℕ) :
    Subobject (U _⦋m⦌) :=
  Finset.univ.sup (fun a : boundedSimplexMapIndex n m =>
      imageSubobject (U.map a.2.op))

theorem abelian_n_skeleton_subobject
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    ∃ (U' : SimplicialObject C) (i : U' ⟶ U),
      Mono i ∧
      (∀ m, imageSubobject (i.app (op ⦋m⦌)) =
        abelianNSkeletonSubobject U n m) ∧
      (∀ m, m ≤ n → imageSubobject (i.app (op ⦋m⦌)) = ⊤) ∧
      (∀ m, n < m → normalizedSubobject U' m = ⊥) := by
  sorry

end Formalization.Books.Simplicial.Unit18
