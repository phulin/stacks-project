import Formalization.Books.Simplicial.Unit12.TruncatedSimplicialObjects
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.AlgebraicTopology.SimplicialObject.Split
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.AlgebraicTopology.SimplicialSet.Splitting
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Limits.MonoCoprod

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
abbrev IsSplit {C : Type u} [Category.{v} C]
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
    {C : Type u} [Category.{v} C] (r : ℕ)
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
    {C : Type u} [Category.{v} C] (r : ℕ)
    (U : SimplicialObject.Truncated C r) : Prop :=
  Nonempty (TruncatedSplitting r U)

/-- The source's coproduct decomposition is the colimit cofan of a splitting. -/
def splitting_decomposition_is_colimit
    {C : Type u} [Category.{v} C]
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
  have hrepr : ∀ {m} (y : U.nonDegenerate m), ∃ z : s.N m, s.ι m z = y := by
    intro m y
    obtain ⟨A, z, hz⟩ :=
      Cofan.inj_jointly_surjective_of_isColimit (s.isColimit (op ⦋m⦌))
        (y : U _⦋m⦌)
    dsimp [SimplicialObject.Splitting.cofan, Cofan.mk, Cofan.inj] at hz
    change (s.ι A.1.unop.len ≫ U.map A.e.op) z = y at hz
    have hlen : A.1.unop.len = m := by
      apply le_antisymm (SimplexCategory.len_le_of_epi A.e)
      by_contra h
      have hlt : A.1.unop.len < m := Nat.lt_of_not_ge h
      apply y.property
      rw [SSet.mem_degenerate_iff]
      refine ⟨A.1.unop.len, hlt, A.e, inferInstance, ?_⟩
      refine ⟨s.ι A.1.unop.len z, ?_⟩
      exact (comp_apply (s.ι A.1.unop.len) (U.map A.e.op) z).symm.trans hz
    have hA : A.EqId := A.eqId_iff_len_eq.mpr hlen
    change A = SimplicialObject.Splitting.IndexSet.id (op ⦋m⦌) at hA
    subst A
    change s.N m at z
    refine ⟨z, ?_⟩
    convert hz using 1
    simp [SimplicialObject.Splitting.IndexSet.id,
      SimplicialObject.Splitting.IndexSet.e, op_id]
    rfl
  have hND : ∀ (n : ℕ) (x : s.N n), s.ι n x ∈ U.nonDegenerate n := by
    intro n x
    obtain ⟨m, g, hg, y, hy⟩ := U.exists_nonDegenerate (s.ι n x)
    obtain ⟨z, hz⟩ := hrepr y
    have hindex : SimplicialObject.Splitting.IndexSet.id (op ⦋n⦌) =
        SimplicialObject.Splitting.IndexSet.mk g := by
      apply Cofan.eq_of_inj_apply_eq_of_isColimit (s.isColimit (op ⦋n⦌))
        (i₁ := SimplicialObject.Splitting.IndexSet.id (op ⦋n⦌))
        (i₂ := SimplicialObject.Splitting.IndexSet.mk g) x z
      dsimp [SimplicialObject.Splitting.cofan, Cofan.mk, Cofan.inj]
      change (s.ι n ≫ U.map (𝟙 (op ⦋n⦌))) x = (s.ι m ≫ U.map g.op) z
      rw [U.map_id, Category.comp_id]
      have hcomp := hy.trans (congrArg (U.map g.op) hz.symm)
      exact hcomp.trans (comp_apply (s.ι m) (U.map g.op) z).symm
    have hnm : n = m := by
      simpa [SimplicialObject.Splitting.IndexSet.id,
        SimplicialObject.Splitting.IndexSet.mk] using
        congrArg (fun A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌) =>
          A.1.unop.len) hindex
    subst m
    have hg' : g = 𝟙 _ := SimplexCategory.eq_id_of_epi g
    rw [hg'] at hy
    rw [hy]
    simp
  intro n
  let e : s.N n → U.nonDegenerate n := fun x => ⟨s.ι n x, hND n x⟩
  have he_inj : Function.Injective e := by
    intro x₁ x₂ h
    change s.N n at x₁ x₂
    have h' : s.ι n x₁ = s.ι n x₂ := by
      simpa [e] using congrArg Subtype.val h
    apply Cofan.inj_injective_of_isColimit (s.isColimit (op ⦋n⦌))
      (SimplicialObject.Splitting.IndexSet.id (op ⦋n⦌))
    dsimp [SimplicialObject.Splitting.cofan, Cofan.mk, Cofan.inj]
    change (s.ι n ≫ U.map (𝟙 (op ⦋n⦌))) x₁ =
      (s.ι n ≫ U.map (𝟙 (op ⦋n⦌))) x₂
    rw [U.map_id, Category.comp_id]
    exact h'
  have he_surj : Function.Surjective e := by
    intro y
    obtain ⟨z, hz⟩ := hrepr y
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hz
  refine ⟨(Equiv.ofBijective e ⟨he_inj, he_surj⟩).toIso, ?_⟩
  ext x
  rfl

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

/-!
The source notes that the canonical nondegenerate splitting is not functorial
for arbitrary simplicial-set maps: a map may send a nondegenerate simplex to a
degenerate one.  `MapsNondegenerate` records the additional hypothesis under
which the induced map on the canonical summands is defined; the three results
below give the corresponding injective, surjective, and bijective conclusions.
-/

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
  intro n x₁ x₂ h
  obtain ⟨m, g, hg, z, hz⟩ := U.exists_nonDegenerate x₁
  obtain ⟨p, k, hk, w, hw⟩ := U.exists_nonDegenerate x₂
  have hz' : f.app (op ⦋n⦌) x₁ = V.map g.op (f.app (op ⦋m⦌) z) := by
    rw [hz, NatTrans.naturality_apply]
  have hw' : f.app (op ⦋n⦌) x₂ = V.map k.op (f.app (op ⦋p⦌) w) := by
    rw [hw, NatTrans.naturality_apply]
  have hzm : f.app (op ⦋m⦌) z ∈ V.nonDegenerate m := hf m z z.property
  have hwp : f.app (op ⦋p⦌) w ∈ V.nonDegenerate p := hf p w w.property
  have hcomp : f.app (op ⦋n⦌) x₁ = V.map k.op (f.app (op ⦋p⦌) w) := h.trans hw'
  have hdim : m = p := by
    apply V.unique_nonDegenerate_dim (f.app (op ⦋n⦌) x₁)
      g ⟨f.app (op ⦋m⦌) z, hzm⟩ hz'
      k ⟨f.app (op ⦋p⦌) w, hwp⟩ hcomp
  subst p
  have hsimplex : (⟨f.app (op ⦋m⦌) z, hzm⟩ : V.nonDegenerate m) =
      ⟨f.app (op ⦋m⦌) w, hwp⟩ := by
    apply V.unique_nonDegenerate_simplex (f.app (op ⦋n⦌) x₁)
      g ⟨f.app (op ⦋m⦌) z, hzm⟩ hz' k ⟨f.app (op ⦋m⦌) w, hwp⟩
    exact hcomp
  have hzw : z = w := by
    apply hN m
    exact hsimplex
  have hgk : g = k := by
    apply V.unique_nonDegenerate_map (f.app (op ⦋n⦌) x₁)
      g ⟨f.app (op ⦋m⦌) z, hzm⟩ hz' k ⟨f.app (op ⦋m⦌) w, hwp⟩
    exact hcomp
  rw [hz, hw, hzw, hgk]

theorem simplicial_set_map_surjective_of_nonDegenerate
    {U V : SSet.{u}} (f : U ⟶ V) (hf : MapsNondegenerate f)
    (hN : ∀ n, Function.Surjective (nondegenerateMap f hf n)) :
    ∀ n, Function.Surjective (f.app (op ⦋n⦌)) := by
  intro n y
  obtain ⟨m, g, hg, z, hz⟩ := V.exists_nonDegenerate y
  obtain ⟨x, hx⟩ := hN m z
  refine ⟨U.map g.op x, ?_⟩
  rw [NatTrans.naturality_apply]
  have hfx : f.app (op ⦋m⦌) x = z := congrArg Subtype.val hx
  rw [hfx, ← hz]

theorem simplicial_set_map_bijective_of_nonDegenerate
    {U V : SSet.{u}} (f : U ⟶ V) (hf : MapsNondegenerate f)
    (hN : ∀ n, Function.Bijective (nondegenerateMap f hf n)) :
    ∀ n, Function.Bijective (f.app (op ⦋n⦌)) := by
  intro n
  refine ⟨?_, ?_⟩
  · apply simplicial_set_map_injective_of_nonDegenerate f hf
    intro m
    exact (hN m).1
  · apply simplicial_set_map_surjective_of_nonDegenerate f hf
    intro m
    exact (hN m).2

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
  rw [SSet.mem_degenerate_iff_notMem_nonDegenerate]
  intro hxn
  have hdim : m < n + 1 :=
    (U.mem_skeleton_obj_iff_of_nonDegenerate ⟨x, hxn⟩ (n + 1)).mp (by
      simpa [simplicialSetNSkeleton] using hx)
  omega

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

/-
Shepherd audit (2026-08-19): the failed-run dossier counted six placeholders,
but this source has seven active proof holes in the audited block: the two
splitting-existence theorems, the three reflection theorems, the last-face
factorization, and the n-skeleton theorem.  Their displayed interfaces agree
with the source mathematics and their existing downstream uses, so no target
type is weakened or changed below.  Each hole is intentionally retained for
the normal proof stage.
-/

/-
Proof roadmap for `simplicial_abelian_group_has_normalized_splitting`:

* Take `s.N n := normalizedObject U n` and `s.ι n :=
  (normalizedSubobject U n).arrow`; the second conjunct of
  `IsNormalizedSplitting` is then inferred and the first uses `Iso.refl`.
  Thus the only substantive field is `s.isColimit'`.
* For `Δ`, reduce `Δ.unop` with `SimplexCategory.rec`, and for the resulting
  degree `m` put

    `q_m := Sigma.desc (fun A : SimplicialObject.Splitting.IndexSet (op ⦋m⦌) =>
      (normalizedSubobject U A.1.unop.len).arrow ≫ U.map A.e.op)`.

  `Cofan.isColimitOfIsIsoSigmaDesc` from
  `Mathlib/CategoryTheory/Limits/Shapes/Products.lean` reduces the colimit
  field to `IsIso q_m`; use `ConcreteCategory.isIso_iff_bijective` from
  `Mathlib/CategoryTheory/ConcreteCategory/EpiMono.lean`.
* Prove bijectivity by induction on `m`, formalizing the normalization
  procedure in Stacks, Tag 017O: successively replace an `(m+1)`-simplex
  `x` by `x - U.σ i (U.δ i.castSucc x)`, for `i = 0, ..., m`.
  The identities needed to preserve the already killed faces and to split
  off the new degeneracy are exactly
  `SimplicialObject.δ_comp_σ_of_le`, `δ_comp_σ_self`, and
  `δ_comp_σ_succ` in
  `Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean`.
  The residual term lies in `normalizedObject U (m + 1)`; recursively expand
  every lower-degree term.  Package the resulting finite family with the
  biproduct projections and `Sigma.map`, rather than reasoning about an
  opaque element of the chosen coproduct.
* Identify the resulting strings of degeneracies with
  `SimplicialObject.Splitting.IndexSet (op ⦋m + 1⦌)`: the composite simplex
  map is epi by `SimplexCategory.epi_iff_surjective`, and equality of two
  indices follows from `Splitting.IndexSet.ext`; the index interface and its
  extensionality lemma are in
  `Mathlib/AlgebraicTopology/SimplicialObject/Split.lean`.  Applying the same
  face operators in reverse order recovers every coefficient, proving injectivity;
  summing the reconstructed coefficients proves surjectivity.  Concretely,
  package coefficient extraction as an additive inverse

    `r_m : U _⦋m⦌ ⟶ ∐ A : Splitting.IndexSet (op ⦋m⦌),
      normalizedObject U A.1.unop.len`.

  Prove `q_m ≫ r_m = 𝟙 _` by `Sigma.hom_ext` and the reverse face calculation,
  and prove `r_m ≫ q_m = 𝟙 _` by extensionality on the underlying abelian
  group and the reconstruction formula.  These equations can alternatively
  supply `IsIso q_m` directly, without converting through bijectivity.

Do not rewrite this target using Mathlib's `NormalizedMooreComplex.objX`:
that object kills the faces `i.succ`, whereas `normalizedSubobject` here
kills `i.castSucc`.  Any reuse of the Dold--Kan projectors would first need
an explicit reindexing through `SimplexCategory.rev` and is longer than the
degree induction above.
-/
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
  rcases n with _ | n
  · apply Subobject.top_factors
  · rw [normalizedSubobject, normalizedSubobject]
    apply (Subobject.finset_inf_factors _).mpr
    intro i _
    apply kernelSubobject_factors
    rw [SimplicialObject.δ_def, Category.assoc,
      ← f.naturality (SimplexCategory.δ i.castSucc).op]
    rw [← Category.assoc]
    rw [← Subobject.factorThru_arrow
      (kernelSubobject (U.δ i.castSucc))
      (Finset.univ.inf (fun j : Fin (n + 1) => kernelSubobject (U.δ j.castSucc))).arrow
      (Subobject.finset_inf_arrow_factors Finset.univ
        (fun j : Fin (n + 1) => kernelSubobject (U.δ j.castSucc)) i (by simp))]
    simp only [Category.assoc]
    rw [← SimplicialObject.δ_def]
    simp only [kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]

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
  apply (cancel_mono (normalizedSubobject W n).arrow).1
  rw [normalizedSubobjectMap_arrow]
  simp only [Category.assoc]
  rw [normalizedSubobjectMap_arrow]
  rw [← Category.assoc, normalizedSubobjectMap_arrow]
  simp [Category.assoc]

/-! ## Splitting in an abelian category -/

/-
Proof roadmap for `abelian_category_has_normalized_splitting`:

* Use the same candidate splitting as in the preceding AddCommGrp theorem.
  For a fixed `Δ`, use `Cofan.isColimitOfIsIsoSigmaDesc` and call its
  comparison morphism `q : (∐ A, normalizedObject U A.1.unop.len) ⟶ U.obj Δ`.
  Apply `isIso_of_yoneda_map_bijective q` from
  `Mathlib/CategoryTheory/Yoneda.lean`.
* For each test object `T : C`, set
  `F := preadditiveCoyoneda.obj (op T) : C ⥤ AddCommGrpCat.{v}` and
  `UT := U ⋙ F`.  The focused prerequisites are
  `Mathlib/CategoryTheory/Preadditive/Yoneda/Basic.lean` and
  `Mathlib/CategoryTheory/Preadditive/AdditiveFunctor.lean`.
  `F` is additive, hence preserves the finite biproduct indexed by
  `Splitting.IndexSet Δ`; use `PreservesCoproduct.iso F` and
  `sigmaComparison_map_desc` from
  `Mathlib/CategoryTheory/Limits/Preserves/Shapes/Products.lean`.
* Establish a local comparison iso, for every `n`,

    `F.obj (normalizedObject U n) ≅ normalizedObject UT n`,

  whose hom followed by the target normalized arrow is
  `F.map (normalizedSubobject U n).arrow`.  For `n = 0` use the two top
  subobjects.  For `n + 1`, use `finset_inf_factors`,
  `kernelSubobject_factors`, and preservation of composition by `F` to
  define the hom with `Subobject.factorThru`.  Define the inverse on a
  normalized hom `T ⟶ U _⦋n+1⦌` by factoring it through
  `normalizedSubobject U (n+1)`; additive preservation and cancellation by
  the two mono arrows prove the inverse laws.  This is the categorical form
  of `Hom(T, intersection of kernels) = intersection of kernels of Hom`;
  the subobject factorization lemmas are in
  `Mathlib/CategoryTheory/Subobject/Lattice.lean` and
  `Mathlib/CategoryTheory/Subobject/Limits.lean`.
* Apply `simplicial_abelian_group_has_normalized_splitting UT`.  Compose its
  summand isos with the comparison isos above.  After this change of
  summands, `F.map q` is the coproduct comparison morphism for the splitting
  of `UT`, hence is an iso by `sT.isColimit Δ`,
  `Cofan.nonempty_isColimit_iff_isIso_sigmaDesc`, `Sigma.map`, and
  `sigmaComparison_map_desc`.
* `ConcreteCategory.bijective_of_isIso (F.map q)` is definitionally the map
  `h : T ⟶ domain(q) ↦ h ≫ q`.  Feed this bijectivity to
  `isIso_of_yoneda_map_bijective`, then finish with
  `Cofan.isColimitOfIsIsoSigmaDesc` and the reflexive summand isos.

The universe of `UT` is `AddCommGrpCat.{v}` (not `{u}`), so instantiate the
preceding theorem at `u := v`.  This avoids an unnecessary `ULift` layer.
-/
theorem abelian_category_has_normalized_splitting
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    ∃ s : SimplicialObject.Splitting U, IsNormalizedSplitting s := by
  sorry

/-! ## Normalization reflects mono, epi, and isomorphism -/

/-
Proof roadmap for `normalized_reflects_monomorphism`:

* Choose normalized splittings `sU`, `sV` from
  `abelian_category_has_normalized_splitting`, and choose their comparison
  isos `eU n`, `eV n`.  Define

    `q n := (eU n).hom ≫ normalizedSubobjectMap f n ≫ (eV n).inv`.

  `normalizedSubobjectMap_arrow` and the two comparison equations give
  `sU.ι n ≫ f.app (op ⦋n⦌) = q n ≫ sV.ι n`; package this as a
  `SimplicialObject.Split.Hom`.
* Fix `n` and abbreviate `I := Splitting.IndexSet (op ⦋n⦌)`.  Enable the
  finite biproduct instance with
  `letI := CategoryTheory.Abelian.hasFiniteBiproducts (C := C)`.  Let `aU`
  and `aV` be the `IsColimit.coconePointUniqueUpToIso` isos from the
  canonical `Sigma` cofans to `sU.cofan (op ⦋n⦌)` and
  `sV.cofan (op ⦋n⦌)`.
* Use `SimplicialObject.Split.cofan_inj_naturality_symm`,
  `Sigma.ι_map`, and `IsColimit.comp_coconePointUniqueUpToIso_hom` to prove

    `f.app (op ⦋n⦌) = aU.inv ≫ Sigma.map (fun A : I => q A.1.unop.len) ≫ aV.hom`.

  The splitting naturality lemma is in
  `Mathlib/AlgebraicTopology/SimplicialObject/Split.lean`; the unique-up-to-iso
  declarations are in `Mathlib/CategoryTheory/Limits/IsLimit.lean`.

* Each component of the `Sigma.map` is mono: install `hN k` locally, then
  infer mono for its composites with the two isomorphisms.  The instance
  `Sigma.map_mono` is in
  `Mathlib/CategoryTheory/Limits/Shapes/Biproducts.lean`; the displayed
  factorization then supplies the required `Mono` instance.
-/
theorem normalized_reflects_monomorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V)
    (hN : ∀ n, Mono (normalizedSubobjectMap f n)) :
    ∀ n, Mono (f.app (op ⦋n⦌)) := by
  sorry

/-
Proof roadmap for `normalized_reflects_epimorphism`:

Repeat the construction of `sU`, `sV`, `eU`, `eV`, `q`, and the comparison
isos `aU`, `aV` from `normalized_reflects_monomorphism`.  The same summandwise
calculation gives

  `f.app (op ⦋n⦌) = aU.inv ≫ Sigma.map (fun A => q A.1.unop.len) ≫ aV.hom`.

Install `hN k` at each component; composition with `(eU k).hom` and
`(eV k).inv` makes every `q k` epi.  Use `Sigma.map_epi` from
`Mathlib/CategoryTheory/Limits/Shapes/Products.lean` (only coproducts are
needed for this direction), then infer epi for the composite with the two
isos.  Keeping the identical `q` and identical orientation of `aU`, `aV`
prevents the common dead end where `Sigma.map_epi` is applied to the inverse
family.
-/
theorem normalized_reflects_epimorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V)
    (hN : ∀ n, Epi (normalizedSubobjectMap f n)) :
    ∀ n, Epi (f.app (op ⦋n⦌)) := by
  sorry

/-
Proof roadmap for `normalized_reflects_isomorphism`:

For each `k`, install `hN k` as a local `IsIso` instance and infer both
`Mono (normalizedSubobjectMap f k)` and `Epi (normalizedSubobjectMap f k)`.
Apply `normalized_reflects_monomorphism` and
`normalized_reflects_epimorphism` to those two families.  At the requested
degree `n`, install the resulting mono and epi propositions as instances and
finish with `isIso_of_mono_of_epi (f.app (op ⦋n⦌))` from
`Mathlib/CategoryTheory/Balanced.lean`; abelian categories are balanced.
-/
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

/-
Proof roadmap for `normalized_last_face_factors`:

* Split on `n`.  Degree zero is `Subobject.top_factors`.
* In the successor case `n = r + 1`, unfold both normalized subobjects and
  apply `(Subobject.finset_inf_factors _).mpr`.  For
  `i : Fin (r + 1)`, it remains to factor through
  `kernelSubobject (U.δ i.castSucc)`; use `kernelSubobject_factors`.
* Reassociate the composite and rewrite the two consecutive faces with
  `SimplicialObject.δ_comp_δ'` from
  `Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean`, instantiated by

    `i := i.castSucc : Fin (r + 2)`,
    `j := Fin.last (r + 2) : Fin (r + 3)`.

  The side condition `Fin.castSucc i.castSucc < Fin.last (r + 2)` is `simp`.
  The right side starts with
  `U.δ (Fin.castSucc i.castSucc)`, one of the faces killed by
  `normalizedSubobject U (r + 2)`.
* Insert its factorization using `Subobject.finset_inf_arrow_factors`, then
  close with `kernelSubobject_arrow_comp`, `zero_comp`, and `comp_zero`.
  The first lemma is in `Mathlib/CategoryTheory/Subobject/Lattice.lean` and
  the kernel lemma is in `Mathlib/CategoryTheory/Subobject/Limits.lean`.
  Be careful that `δ_comp_δ'`, not the similarly named cosimplicial lemma,
  is selected; the required orientation is “last face, then face `i`”.
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

/-
Proof roadmap for `abelian_n_skeleton_subobject`:

* First make the construction uniform in an arbitrary
  `Δ : SimplexCategoryᵒᵖ`.  Use the finite index

    `Σ i : Fin (n + 1), (Δ.unop ⟶ ⦋i.1⦌)`

  and define `generator U n Δ` to be `Sigma.desc (fun a => U.map a.2.op)`.
  Let `S Δ := imageSubobject (generator U n Δ)`.  At `Δ = op ⦋m⦌`, prove
  `S Δ = abelianNSkeletonSubobject U n m`: one inequality uses
  `imageSubobject_le` after factoring every coproduct injection through the
  finite supremum, and the other uses `Finset.sup_le`,
  `imageSubobject_comp_le`, and `Sigma.ι_desc`.
* For `θ : Δ ⟶ Δ'`, send an index `a` to
  `⟨a.1, θ.unop ≫ a.2⟩`.  `Sigma.map'` gives the map between generator
  domains, and `U.map_comp` proves the square with right side `U.map θ`.
  Apply `imageSubobjectMap` and `imageSubobjectMap_arrow` from
  `Mathlib/CategoryTheory/Subobject/Limits.lean`.  These maps define a
  simplicial object `U'`; prove `map_id` and `map_comp` by cancelling the mono
  arrow of `S`, using only `imageSubobjectMap_arrow` and the functor laws of
  `U`.  Define `i : U' ⟶ U` by `i.app Δ := (S Δ).arrow`; its naturality is
  the same equation, and `NatTrans.mono_of_mono_app` from
  `Mathlib/CategoryTheory/Functor/Category.lean` gives `Mono i`.
* The required image equality follows from `imageSubobject_mono`,
  `Subobject.mk_arrow`, and the specialization `S (op ⦋m⦌) = ...` above.
  If `m ≤ n`, the generator indexed by
  `⟨⟨m, Nat.lt_succ_of_le hm⟩, 𝟙 ⦋m⦌⟩` has image `⊤`; use
  `Finset.le_sup (Finset.mem_univ _)`, `imageSubobject_mono`, and
  `Subobject.top_eq_id` to prove the “agrees below” clause.  Consequently
  `i.app (op ⦋m⦌)` is an iso in these degrees by
  `Subobject.isIso_iff_mk_eq_top`.
* For `m > n`, choose a normalized splitting `s'` of `U'`.  It suffices to
  show `s'.N m` is zero and transport this through the iso in
  `IsNormalizedSplitting`.  Define the projection onto the identity summand
  by

    `p := s'.desc (op ⦋m⦌) (fun A => if h : A.EqId then
      eqToHom (by rw [(Splitting.IndexSet.eqId_iff_len_eq A).mp h]) else 0)`.

  `s'.ι_desc` gives `s'.ι m ≫ p = 𝟙 _` and says every nonidentity summand
  maps to zero.
* Show `p = 0` after precomposition with the epi
  `factorThruImageSubobject (generator U n (op ⦋m⦌))`.  On a generator
  `a : [m] ⟶ [i]`, first establish the exact lift equation

    `Sigma.ι (fun a => U.obj (op ⦋a.1.1⦌)) a ≫
        factorThruImageSubobject (generator U n (op ⦋m⦌)) =
      inv (i.app (op ⦋a.1.1⦌)) ≫ U'.map a.2.op`.

  Here the component of `i` in degree `a.1.1 ≤ n` is an iso by the preceding
  “agrees below” clause.  Prove the equation by cancelling the mono
  `i.app (op ⦋m⦌)` and using `imageSubobject_arrow_comp`, naturality of `i`,
  `Sigma.ι_desc`, and the inverse law.  Now factor `a.2` as
  `factorThruImage a.2 ≫ image.ι a.2`.  Its epi part has target length at
  most `i ≤ n < m`, so the corresponding index in the splitting of `U'` is
  not `EqId` by `Splitting.IndexSet.eqId_iff_len_eq`.  Use
  `s'.cofan_inj_epi_naturality`, `s'.hom_ext'`, and `s'.ι_desc` to show the
  generator followed by `p` is zero; cancel the generator-image epi to get
  `p = 0`.  Then `s'.ι m ≫ p = 𝟙` makes `s'.N m` a zero object, and
  `Subobject.mk_eq_bot_iff_zero` (after transporting across the normalized
  summand iso) yields `normalizedSubobject U' m = ⊥`.  The splitting lemmas
  used in this step are all in
  `Mathlib/AlgebraicTopology/SimplicialObject/Split.lean`, and
  `Subobject.mk_eq_bot_iff_zero` is in
  `Mathlib/CategoryTheory/Subobject/Lattice.lean`.

Do not build `U'` only on the standard objects `op ⦋m⦌`; doing so creates
avoidable `eqToHom` transports in both functor laws.  The arbitrary-`Δ`
generator above makes composition strictly compatible with index
precomposition.  Also do not import the later Unit21 skeleton functor: this
lemma is its chronological input.
-/
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
