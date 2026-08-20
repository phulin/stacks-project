import Formalization.Books.MoreAlgebra.Unit55.InjectiveModules
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Monomorphisms
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.SmallObject.Construction
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Injectives, Chapter 2: Baer's argument for modules

This file formalizes the definitions and theorem interfaces in the chapter.
The comparison map uses the covariant representable functor `Hom(A, -)`, and
the large pushout is implemented by Mathlib's canonical small-object
construction for the family of ideal inclusions.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace Formalization.Books.Injectives.Unit02

/-! ## The comparison map and its set-theoretic examples -/

/-- The comparison map from the colimit of the hom-sets to the hom-set of the
colimit.  This is equation (compare) in the source. -/
noncomputable def comparisonMap
    {C : Type u} [Category.{v} C]
    {J : Type w} [Category.{w} J]
    (A : C) (F : J ⥤ C) [HasColimit F]
    [HasColimit (F ⋙ coyoneda.obj (Opposite.op A))] :
    colimit (F ⋙ coyoneda.obj (Opposite.op A)) →
      (A ⟶ colimit F) :=
  colimit.desc (F ⋙ coyoneda.obj (Opposite.op A))
    { pt := A ⟶ colimit F
      ι :=
        { app := fun j =>
            (coyoneda.obj (Opposite.op A)).map (colimit.ι F j)
          naturality := by
            intro j k f
            ext g
            change (g ≫ F.map f) ≫ colimit.ι F k = g ≫ colimit.ι F j
            rw [Category.assoc, colimit.w] } }

/-- The ordinal-indexed form of the comparison map. -/
abbrev ordinalComparisonMap
    {C : Type u} [Category.{v} C]
    (A : C) (α : Ordinal.{w}) (F : Set.Iio α ⥤ C)
    [HasColimit F]
    [HasColimit (F ⋙ coyoneda.obj (Opposite.op A))] :=
  comparisonMap A F

/-- The finite-source assertion is a bijectivity statement for the comparison
map, with the existence of the two colimits made explicit. -/
def comparisonMapBijective
    {C : Type u} [Category.{v} C]
    {J : Type w} [Category.{w} J]
    (A : C) (F : J ⥤ C) (hF : HasColimit F)
    (hHom : HasColimit (F ⋙ coyoneda.obj (Opposite.op A))) : Prop :=
  letI := hF
  letI := hHom
  Function.Bijective (comparisonMap A F)

/-- A finite set is small for every nonempty ordinal-indexed system of sets. -/
theorem comparisonMap_bijective_of_finite
    (α : Ordinal.{w}) (hα : 0 < α) (A : Type u) [Finite A]
    (F : Set.Iio α ⥤ Type u) [HasColimit F]
    [HasColimit (F ⋙ coyoneda.obj (Opposite.op A))] :
    Function.Bijective (comparisonMap A F) := by
  sorry

/-- The increasing finite-set diagram used in the first counterexample.  We
use `Fin (n + 1)` as the zero-based version of `{1, ..., n}`. -/
def finiteSetChain : ℕ ⥤ Type where
  obj n := Fin (n + 1)
  map {n m} h :=
    ↾(fun x : Fin (n + 1) =>
      ⟨x.1, Nat.lt_of_lt_of_le x.2
        (Nat.succ_le_succ (leOfHom h))⟩)
  map_id := by
    intro n
    ext x
    rfl
  map_comp := by
    intro n m k h₁ h₂
    ext x
    rfl

/-- The map from `ℕ` to the colimit of the finite-set chain which sends `n` to
the image of the largest element of the `n`th stage. -/
noncomputable def finiteSetChainColimitMap :
    ℕ → colimit finiteSetChain :=
  fun n => colimit.ι finiteSetChain n ⟨n, Nat.lt_succ_self n⟩

/-- The map in the first example does not factor through any finite stage. -/
theorem finiteSetChain_no_finite_factor :
    ∀ n : ℕ, ¬ ∃ g : ℕ → finiteSetChain.obj n,
      ∀ k : ℕ,
        colimit.ι finiteSetChain n (g k) =
          finiteSetChainColimitMap k := by
  intro n
  rintro ⟨g, hg⟩
  have hiff := Types.FilteredColimit.colimit_eq_iff (F := finiteSetChain)
    (i := n) (j := n + 1)
    (xi := g (n + 1))
    (xj := ⟨n + 1, Nat.lt_succ_self (n + 1)⟩)
  have heq :
      (colimit.ι finiteSetChain n) (g (n + 1)) =
        (colimit.ι finiteSetChain (n + 1))
          ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ := by
    simpa [finiteSetChainColimitMap] using hg (n + 1)
  obtain ⟨k, f, g', hfg⟩ := hiff.mp heq
  have hv := congrArg Fin.val hfg
  change (g (n + 1)).val = n + 1 at hv
  exact (Nat.ne_of_lt (g (n + 1)).isLt) hv

/-- Consequently the comparison map in the first example is not surjective. -/
theorem finiteSetChain_comparison_not_surjective :
    ¬ Function.Surjective
      (comparisonMap (A := ℕ) finiteSetChain) := by
  intro hs
  let target : ℕ ⟶ colimit finiteSetChain :=
    TypeCat.ofHom finiteSetChainColimitMap
  obtain ⟨x, hx⟩ := hs target
  obtain ⟨n, g, hι⟩ :=
    Types.jointly_surjective
      (finiteSetChain ⋙ coyoneda.obj (Opposite.op ℕ))
      (colimit.isColimit (finiteSetChain ⋙ coyoneda.obj (Opposite.op ℕ))) x
  let gfun : ℕ → finiteSetChain.obj n := TypeCat.homEquiv g
  rw [← hι] at hx
  have hf : ∀ k : ℕ,
      colimit.ι finiteSetChain n (gfun k) = finiteSetChainColimitMap k := by
    intro k
    have hk := congrArg (fun q : ℕ ⟶ colimit finiteSetChain => q k) hx
    simp [comparisonMap, target] at hk
    exact hk
  exact finiteSetChain_no_finite_factor n ⟨gfun, hf⟩

/-- The setoid which collapses the initial segment `{0, ..., n - 1}` of `ℕ`
to one point. -/
def collapsedSetoid (n : ℕ) : Setoid ℕ where
  r a b := a = b ∨ (a < n ∧ b < n)
  iseqv :=
    { refl := by
        intro a
        exact Or.inl rfl
      symm := by
        intro a b h
        rcases h with h | h
        · exact Or.inl h.symm
        · exact Or.inr ⟨h.2, h.1⟩
      trans := by
        intro a b c hab hbc
        rcases hab with hab | hab
        · subst hab
          exact hbc
        · rcases hbc with hbc | hbc
          · subst hbc
            exact Or.inr hab
          · exact Or.inr ⟨hab.1, hbc.2⟩ }

abbrev collapsedQuotient (n : ℕ) := Quotient (collapsedSetoid n)

/-- The transition map between the collapsed quotients. -/
def collapsedMap {n m : ℕ} (h : n ≤ m) :
    collapsedQuotient n → collapsedQuotient m :=
  Quotient.map id (by
    intro a b hab
    rcases hab with hab | hab
    · exact Or.inl hab
    · exact Or.inr ⟨Nat.lt_of_lt_of_le hab.1 h, Nat.lt_of_lt_of_le hab.2 h⟩)

/-- The increasing system of quotients used in the second counterexample. -/
def collapsedNatChain : ℕ ⥤ Type where
  obj n := collapsedQuotient n
  map {n m} h := ↾(collapsedMap (leOfHom h))
  map_id := by
    intro n
    ext x
    refine Quotient.inductionOn x ?_
    intro a
    rfl
  map_comp := by
    intro n m k h₁ h₂
    ext x
    refine Quotient.inductionOn x ?_
    intro a
    rfl

/-- The natural projection `ℕ → Bₙ` in the second example. -/
def collapsedProjection (n : ℕ) : ℕ → collapsedQuotient n :=
  @Quotient.mk' ℕ (collapsedSetoid n)

/-- The constant map to the class of `0` in `Bₙ`. -/
def collapsedConstant (n : ℕ) : ℕ → collapsedQuotient n :=
  fun _ => @Quotient.mk' ℕ (collapsedSetoid n) 0

/-- The colimit of the collapsed-quotient chain is a one-point set. -/
theorem collapsedNatChain_colimit_subsingleton :
    Subsingleton (colimit collapsedNatChain) := by
  constructor
  intro x y
  have hstage :
      ∀ (n m : ℕ) (a : collapsedQuotient n) (b : collapsedQuotient m),
        ∃ (k : ℕ) (f : n ⟶ k) (g : m ⟶ k),
          collapsedNatChain.map f a = collapsedNatChain.map g b := by
    intro n m a b
    refine Quotient.inductionOn a ?_
    intro a
    refine Quotient.inductionOn b ?_
    intro b
    let k := max (max n m) (max a b) + 1
    let f : n ⟶ k := homOfLE (by
      dsimp [k]
      omega)
    let g : m ⟶ k := homOfLE (by
      dsimp [k]
      omega)
    refine ⟨k, f, g, ?_⟩
    apply Quotient.sound
    dsimp [k]
    exact Or.inr ⟨by omega, by omega⟩
  obtain ⟨n, a, hx⟩ :=
    Types.jointly_surjective collapsedNatChain (colimit.isColimit collapsedNatChain) x
  obtain ⟨m, b, hy⟩ :=
    Types.jointly_surjective collapsedNatChain (colimit.isColimit collapsedNatChain) y
  obtain ⟨k, f, g, hfg⟩ := hstage n m a b
  rw [← hx, ← hy]
  exact Types.colimit_sound' (F := collapsedNatChain)
    (j := n) (j' := m) (x := a) (x' := b) (j'' := k) f g hfg

/-- The two displayed families of maps in the second example are distinct at
each finite stage. -/
theorem collapsedProjection_ne_collapsedConstant (n : ℕ) :
    collapsedProjection n ≠ collapsedConstant n := by
  intro h
  have h' := congrArg (fun f : ℕ → collapsedQuotient n => f (n + 1)) h
  have h'' := Quotient.exact h'
  change n + 1 = 0 ∨ (n + 1 < n ∧ 0 < n) at h''
  omega

/-- The comparison map in the second example is not injective. -/
theorem collapsedNatChain_comparison_not_injective :
    ¬ Function.Injective
      (comparisonMap (A := ℕ) collapsedNatChain) := by
  intro hinj
  let H := collapsedNatChain ⋙ coyoneda.obj (Opposite.op ℕ)
  let x : colimit H := colimit.ι H 0 (TypeCat.ofHom (collapsedProjection 0))
  let y : colimit H := colimit.ι H 0 (TypeCat.ofHom (collapsedConstant 0))
  have hxy : x = y := by
    apply hinj
    ext z
    exact collapsedNatChain_colimit_subsingleton.elim _ _
  have hiff := Types.FilteredColimit.colimit_eq_iff (F := H) (i := 0) (j := 0)
    (xi := TypeCat.ofHom (collapsedProjection 0))
    (xj := TypeCat.ofHom (collapsedConstant 0))
  obtain ⟨k, f, g, hfg⟩ := hiff.mp hxy
  have hfg' : f = g := Subsingleton.elim _ _
  subst g
  dsimp [H] at hfg
  have hz := congrArg (fun q : ℕ ⟶ collapsedQuotient k =>
    (ConcreteCategory.hom q) (k + 1)) hfg
  change (ConcreteCategory.hom (collapsedNatChain.map f))
      (collapsedProjection 0 (k + 1)) =
    (ConcreteCategory.hom (collapsedNatChain.map f))
      (collapsedConstant 0 (k + 1)) at hz
  have hz' := Quotient.exact hz
  change k + 1 = 0 ∨ (k + 1 < k ∧ 0 < k) at hz'
  omega

/-! ## Small objects and module colimits -/

/-- An object is `α`-small with respect to a morphism property when every
ordinal-indexed diagram whose transition maps satisfy that property has a
bijective comparison map. -/
def IsAlphaSmall
    {C : Type u} [Category.{v} C] (A : C) (α : Ordinal.{w})
    (P : MorphismProperty C) : Prop :=
  ∀ (F : Set.Iio α ⥤ C),
    (∀ {i j : Set.Iio α} (f : i ⟶ j), P (F.map f)) →
    ∀ (hF : HasColimit F)
      (hHom : HasColimit (F ⋙ coyoneda.obj (Opposite.op A))),
      comparisonMapBijective A F hF hHom

/-- For an ordinal chain of modules with monomorphic transition maps, every
stage maps monomorphically into the colimit. -/
theorem ordinal_module_colimit_ι_mono
    {R : Type u} [Ring R] {α : Ordinal.{u}}
    (F : Set.Iio α ⥤ ModuleCat.{u} R)
    (hF : ∀ {i j : Set.Iio α} (f : i ⟶ j), Mono (F.map f)) :
    ∀ i : Set.Iio α, Mono (colimit.ι F i) := by
  intro i
  let : Nonempty (Set.Iio α) := ⟨i⟩
  let : IsFiltered (Set.Iio α) := by infer_instance
  let : Nonempty α.ToType :=
    ⟨Ordinal.ToType.mk (o := α) i⟩
  let : IsFiltered α.ToType := by infer_instance
  let : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u} R)) :=
    ModuleCat.FilteredColimits.forget_preservesFilteredColimits
  let : PreservesColimitsOfShape α.ToType (forget (ModuleCat.{u} R)) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits.{u, u} _
  let : PreservesColimitsOfShape (Set.Iio α) (forget (ModuleCat.{u} R)) :=
    preservesColimitsOfShape_of_equiv
      (Ordinal.ToType.mk (o := α)).equivalence.symm _
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  obtain ⟨k, f, g, hfg⟩ :=
    (Concrete.colimit_rep_eq_iff_exists F x y).mp hxy
  have hfg' : f = g := Subsingleton.elim _ _
  subst g
  exact (ModuleCat.mono_iff_injective (F.map f)).mp (hF f) hfg

/-- With monomorphic transition maps, the comparison map out of any module
 is injective. -/
theorem module_comparisonMap_injective
    {R : Type u} [Ring R] {α : Ordinal.{u}}
    (A : ModuleCat.{u} R) (F : Set.Iio α ⥤ ModuleCat.{u} R)
    (hF : ∀ {i j : Set.Iio α} (f : i ⟶ j), Mono (F.map f)) :
    Function.Injective (comparisonMap A F) := by
  classical
  let H := F ⋙ coyoneda.obj (Opposite.op A)
  intro x y hxy
  obtain ⟨i, f, hf⟩ := Types.jointly_surjective H (colimit.isColimit H) x
  obtain ⟨j, g, hg⟩ := Types.jointly_surjective H (colimit.isColimit H) y
  by_cases hα : 0 < α
  · let : Nonempty (Set.Iio α) := ⟨⟨0, hα⟩⟩
    let : IsFiltered (Set.Iio α) := by infer_instance
    let : Nonempty α.ToType :=
      ⟨Ordinal.ToType.mk (o := α) ⟨0, hα⟩⟩
    let : IsFiltered α.ToType := by infer_instance
    let : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u} R)) :=
      inferInstance
    let : PreservesColimitsOfShape α.ToType (forget (ModuleCat.{u} R)) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits.{u, u} _
    let : PreservesColimitsOfShape (Set.Iio α) (forget (ModuleCat.{u} R)) :=
      preservesColimitsOfShape_of_equiv
        (Ordinal.ToType.mk (o := α)).equivalence.symm _
    let k : Set.Iio α := ⟨max i j, by
      show max (i : Ordinal) (j : Ordinal) < α
      exact max_lt i.2 j.2⟩
    let fi : i ⟶ k := homOfLE (le_max_left _ _)
    let gj : j ⟶ k := homOfLE (le_max_right _ _)
    let : Mono (colimit.ι F k) := ordinal_module_colimit_ι_mono F hF k
    rw [← hf, ← hg] at hxy
    have hstage : f ≫ colimit.ι F i = g ≫ colimit.ι F j := by
      simpa [comparisonMap, H] using hxy
    have hcommon : f ≫ F.map fi = g ≫ F.map gj := by
      apply (cancel_mono (colimit.ι F k)).mp
      simp only [Category.assoc]
      rw [colimit.w F fi, colimit.w F gj]
      exact hstage
    rw [← hf, ← hg]
    apply (Types.FilteredColimit.colimit_eq_iff (F := H)
      (i := i) (j := j) (xi := f) (xj := g)).2
    exact ⟨k, fi, gj, by
      simpa [H] using hcommon⟩
  · exact (hα (lt_of_le_of_lt bot_le i.2)).elim

/-- In the concrete module interpretation of the ordinal colimit, the
underlying module is the union of the images of its stages. -/
theorem ordinal_module_colimit_union
    {R : Type u} [Ring R] {α : Ordinal.{u}}
    (F : Set.Iio α ⥤ ModuleCat.{u} R)
    (hα : 0 < α)
    (hF : ∀ {i j : Set.Iio α} (f : i ⟶ j), Mono (F.map f)) :
    (Set.univ : Set (↑(colimit F : ModuleCat.{u} R))) =
      ⋃ i : Set.Iio α, Set.range (fun x => (colimit.ι F i) x) := by
  classical
  let : Nonempty (Set.Iio α) := ⟨⟨0, hα⟩⟩
  let : IsFiltered (Set.Iio α) := by infer_instance
  let : Nonempty α.ToType :=
    ⟨Ordinal.ToType.mk (o := α) ⟨0, hα⟩⟩
  let : IsFiltered α.ToType := by infer_instance
  let : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u} R)) :=
    inferInstance
  let : PreservesColimitsOfShape α.ToType (forget (ModuleCat.{u} R)) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits.{u, u} _
  let : PreservesColimitsOfShape (Set.Iio α) (forget (ModuleCat.{u} R)) :=
    preservesColimitsOfShape_of_equiv
      (Ordinal.ToType.mk (o := α)).equivalence.symm _
  let _ : Mono (colimit.ι F ⟨0, hα⟩) :=
    ordinal_module_colimit_ι_mono F hF ⟨0, hα⟩
  let hc : IsColimit ((forget (ModuleCat.{u} R)).mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves (forget (ModuleCat.{u} R)) (colimit.isColimit F)
  ext x
  constructor
  · intro hx
    obtain ⟨i, y, hy⟩ :=
      Types.jointly_surjective (F ⋙ forget (ModuleCat.{u} R)) hc x
    exact Set.mem_iUnion.2 ⟨i, Set.mem_range.2 ⟨y, hy⟩⟩
  · intro hx
    exact Set.mem_univ x

/-- The cardinality used in the module smallness proposition. -/
def moduleSubmoduleCardinal (R : Type u) [Ring R]
    (M : ModuleCat.{u} R) : Cardinal.{u} :=
  Cardinal.mk (Submodule R (M : Type u))

/-- For modules, a cofinality larger than the cardinality of the submodule set
forces the comparison map to be bijective. -/
theorem module_is_alpha_small
    {R : Type u} [Ring R] (M : ModuleCat.{u} R) (α : Ordinal.{u})
    (hα : moduleSubmoduleCardinal R M < Ordinal.cof α) :
    IsAlphaSmall M α (MorphismProperty.monomorphisms (ModuleCat.{u} R)) := by
  open scoped Ordinal in
  classical
  have hαpos : 0 < α := by
    by_contra h
    have hzero : α = 0 := le_antisymm (not_lt.mp h) bot_le
    subst α
    simp at hα
  intro F hF hFcol hHom
  let _ : HasColimit F := hFcol
  let _ : HasColimit (F ⋙ coyoneda.obj (Opposite.op M)) := hHom
  have hFmono : ∀ {i j : Set.Iio α} (q : i ⟶ j), Mono (F.map q) :=
    fun q => hF q
  have hinj : Function.Injective (comparisonMap M F) :=
    module_comparisonMap_injective M F hFmono
  refine ⟨hinj, ?_⟩
  intro f
  let P : ∀ i : Set.Iio α, Submodule R (↑(colimit F : ModuleCat.{u} R)) :=
    fun i => LinearMap.range (colimit.ι F i).hom
  let L : ∀ i : Set.Iio α, Submodule R (M : Type u) :=
    fun i => (P i).comap f.hom
  have hP_mono : ∀ {i j : Set.Iio α} (q : i ⟶ j), P i ≤ P j := by
    intro i j q z hz
    rcases hz with ⟨y, rfl⟩
    refine ⟨(F.map q).hom y, ?_⟩
    change (F.map q ≫ colimit.ι F j).hom y =
      (colimit.ι F i).hom y
    rw [colimit.w F q]
  have hL_mono : ∀ {i j : Set.Iio α} (q : i ⟶ j), L i ≤ L j := by
    intro i j q
    exact Submodule.comap_mono (hP_mono q)
  have hL_nonempty : ∀ m : (M : Type u), ∃ i : Set.Iio α, m ∈ L i := by
    intro m
    have hm : f.hom m ∈ ⋃ i : Set.Iio α, Set.range (fun x => (colimit.ι F i) x) := by
      rw [← ordinal_module_colimit_union F hαpos hFmono]
      exact Set.mem_univ _
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.1 hm
    refine ⟨i, ?_⟩
    change f.hom m ∈ LinearMap.range (colimit.ι F i).hom
    exact ⟨y, hy⟩
  let s : Submodule R (M : Type u) → Ordinal := fun K =>
    if hK : ∃ i : Set.Iio α, L i = K then
      (Classical.choose hK : Set.Iio α).1
    else 0
  have hslt (K : Submodule R (M : Type u)) : s K < α := by
    dsimp [s]
    split_ifs with hK
    · exact (Classical.choose hK).2
    · exact hαpos
  have hstage (i : Set.Iio α) :
      ∃ j : Set.Iio α, L j = L i ∧ (j : Ordinal) = s (L i) := by
    have hi : ∃ j : Set.Iio α, L j = L i := ⟨i, rfl⟩
    let j : Set.Iio α := Classical.choose hi
    have hj : L j = L i := Classical.choose_spec hi
    refine ⟨j, hj, ?_⟩
    change (j : Ordinal) =
      if hK : ∃ k : Set.Iio α, L k = L i then
        (Classical.choose hK : Set.Iio α).1 else 0
    rw [dif_pos hi]
  have hsup : (⨆ K : Submodule R (M : Type u), s K) < α :=
    Ordinal.iSup_lt_of_lt_cof
      (by simpa [moduleSubmoduleCardinal] using hα) hslt
  let β : Set.Iio α :=
    ⟨⨆ K : Submodule R (M : Type u), s K, hsup⟩
  have hLtop : L β = ⊤ := by
    apply top_unique
    intro m hm
    obtain ⟨i, hi⟩ := hL_nonempty m
    obtain ⟨j, hji, hsj⟩ := hstage i
    have hjβ : (j : Ordinal) ≤ β := by
      change (j : Ordinal) ≤ ⨆ K : Submodule R (M : Type u), s K
      rw [hsj]
      exact Ordinal.le_iSup s (L i)
    have hle : L j ≤ L β :=
      hL_mono (homOfLE hjβ)
    apply hle
    rw [hji]
    exact hi
  let : Mono (colimit.ι F β) := ordinal_module_colimit_ι_mono F hFmono β
  let eβ : (F.obj β : Type u) ≃ₗ[R] P β :=
    LinearEquiv.ofInjective (colimit.ι F β).hom
      ((ModuleCat.mono_iff_injective (colimit.ι F β)).mp inferInstance)
  have hf_range : ∀ m : (M : Type u), f.hom m ∈ P β := by
    intro m
    have hm : m ∈ L β := by
      rw [hLtop]
      exact Submodule.mem_top
    exact hm
  let fβ : M ⟶ F.obj β :=
    ModuleCat.ofHom
      (eβ.symm.toLinearMap.comp (f.hom.codRestrict (P β) hf_range))
  have hfactor : fβ ≫ colimit.ι F β = f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (colimit.ι F β).hom
        (eβ.symm ⟨f.hom m, hf_range m⟩) = f.hom m
    exact congrArg Subtype.val (eβ.apply_symm_apply ⟨f.hom m, hf_range m⟩)
  refine ⟨colimit.ι (F ⋙ coyoneda.obj (Opposite.op M)) β fβ, ?_⟩
  simpa [comparisonMap] using hfactor

/-! ## Baer's criterion and the first pushout -/

/-- Baer's ideal-extension criterion, using the established module-category
interface `HasIdealExtension`. -/
theorem baer_criterion {R : Type u} [Ring R] (Q : ModuleCat.{u} R) :
    Injective Q ↔ Formalization.Books.MoreAlgebra.Unit55.HasIdealExtension Q := by
  exact (Formalization.Books.MoreAlgebra.Unit55.injective_iff_baer_criterion Q).out 0 2

/-- The module pushout attached to an ideal map `φ : I → M`. -/
noncomputable def idealPushout
    {R : Type u} [Ring R] (I : Ideal R) (M : ModuleCat.{u} R)
    (φ : ModuleCat.of R I ⟶ M) : ModuleCat.{u} R :=
  pushout (ModuleCat.ofHom I.subtype) φ

/-- The map from `M` into the ideal pushout. -/
noncomputable def idealPushout_inclusion
    {R : Type u} [Ring R] (I : Ideal R) (M : ModuleCat.{u} R)
    (φ : ModuleCat.of R I ⟶ M) : M ⟶ idealPushout I M φ :=
  pushout.inr (ModuleCat.ofHom I.subtype) φ

/-- The pushout supplies the extension map from `R`. -/
theorem idealPushout_extension
    {R : Type u} [Ring R] (I : Ideal R) (M : ModuleCat.{u} R)
    (φ : ModuleCat.of R I ⟶ M) :
    ∃ ψ : ModuleCat.of R R ⟶ idealPushout I M φ,
      ModuleCat.ofHom I.subtype ≫ ψ =
        φ ≫ idealPushout_inclusion I M φ := by
  refine ⟨pushout.inl (ModuleCat.ofHom I.subtype) φ, ?_⟩
  exact pushout.condition

/-- Pushout along the ideal inclusion preserves the monomorphism of the
vertical map in the displayed square. -/
theorem idealPushout_inclusion_mono
    {R : Type u} [Ring R] (I : Ideal R) (M : ModuleCat.{u} R)
    (φ : ModuleCat.of R I ⟶ M) :
    Mono (idealPushout_inclusion I M φ) := by
  change Mono (pushout.inr (ModuleCat.ofHom I.subtype) φ)
  have hmono : Mono (ModuleCat.ofHom I.subtype) := by
    rw [ModuleCat.mono_iff_injective]
    exact Subtype.val_injective
  exact @CategoryTheory.Abelian.mono_pushout_of_mono_f _ _ _ _ _ _ _ _ _ hmono

/-! ## The huge pushout and its functorial iteration -/

/-- The family of all ideal inclusions `I → R`. -/
def idealInclusionFamily {R : Type u} [Ring R] :
    ∀ I : Ideal R, ModuleCat.of R I ⟶ ModuleCat.of R R :=
  fun I => ModuleCat.ofHom I.subtype

/-- The arrow `M → 0`, used to apply Mathlib's small-object pushout to all
ideal maps into `M`. -/
def moduleZero (R : Type u) [Ring R] : ModuleCat.{u} R := ModuleCat.of R PUnit

def toZeroArrowFunctor (R : Type u) [Ring R] :
    ModuleCat.{u} R ⥤ Arrow (ModuleCat.{u} R) where
  obj M := Arrow.mk (0 : M ⟶ moduleZero R)
  map f := Arrow.homMk f (𝟙 (moduleZero R)) (by simp)
  map_id := by
    intro M
    ext <;> simp
  map_comp := by
    intro M N P f g
    ext <;> simp

/-- The functorial huge pushout `M ↦ 𝕄(M)`, implemented by the canonical
small-object construction for the family of ideal inclusions. -/
noncomputable def baerStepArrowFunctor (R : Type u) [Ring R] :
    Arrow (ModuleCat.{u} R) ⥤ Arrow (ModuleCat.{u} R) :=
  SmallObject.functor (idealInclusionFamily (R := R))

noncomputable def baerStepFunctor (R : Type u) [Ring R] :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  toZeroArrowFunctor R ⋙ baerStepArrowFunctor R ⋙ Arrow.leftFunc

/-- The object `𝕄(M)` in the source's huge pushout diagram. -/
noncomputable def baerStep (R : Type u) [Ring R] (M : ModuleCat.{u} R) :
    ModuleCat.{u} R :=
  (baerStepFunctor R).obj M

/-- The natural map `M → 𝕄(M)` supplied by the pushout construction. -/
noncomputable def baerStepEmbedding (R : Type u) [Ring R] :
    𝟭 (ModuleCat.{u} R) ⟶ baerStepFunctor R where
  app M :=
    SmallObject.ιFunctorObj (idealInclusionFamily (R := R))
      ((toZeroArrowFunctor R).obj M).hom
  naturality M N f := by
    exact (SmallObject.ιFunctorObj_naturality
      (idealInclusionFamily (R := R))
      (τ := (toZeroArrowFunctor R).map f)).symm

/-- The huge pushout extends every map from an ideal. -/
theorem baerStep_ideal_extension
    {R : Type u} [Ring R] (M : ModuleCat.{u} R) (I : Ideal R)
    (φ : ModuleCat.of R I ⟶ M) :
    ∃ ψ : ModuleCat.of R R ⟶ baerStep R M,
      ModuleCat.ofHom I.subtype ≫ ψ =
        φ ≫ (baerStepEmbedding R).app M := by
  have hs : φ ≫ ((toZeroArrowFunctor R).obj M).hom = 0 := by
    change φ ≫ 0 = 0
    simp
  obtain ⟨ψ, hψ, _⟩ :=
    SmallObject.ιFunctorObj_extension
      (idealInclusionFamily (R := R))
      (πX := ((toZeroArrowFunctor R).obj M).hom)
      φ 0 ⟨hs.trans (by simp)⟩
  exact ⟨ψ, hψ⟩

/-- The map into the huge pushout is monomorphic. -/
theorem baerStepEmbedding_mono
    {R : Type u} [Ring R] (M : ModuleCat.{u} R) :
    Mono ((baerStepEmbedding R).app M) := by
  change Mono (pushout.inl _ _)
  have hleft : Mono (SmallObject.functorObjLeft idealInclusionFamily
      ((toZeroArrowFunctor R).obj M).hom) := by
    have hmono : ∀ x, Mono (SmallObject.functorObjLeftFamily idealInclusionFamily
        ((toZeroArrowFunctor R).obj M).hom x) := by
      intro x
      rw [ModuleCat.mono_iff_injective]
      exact Subtype.val_injective
    let φ : Discrete.functor (SmallObject.functorObjSrcFamily idealInclusionFamily
        ((toZeroArrowFunctor R).obj M).hom) ⟶
        Discrete.functor (SmallObject.functorObjTgtFamily idealInclusionFamily
          ((toZeroArrowFunctor R).obj M).hom) :=
      Discrete.natTrans (fun x => SmallObject.functorObjLeftFamily
        idealInclusionFamily ((toZeroArrowFunctor R).obj M).hom x.as)
    have hφ : Mono φ :=
      @NatTrans.mono_of_mono_app _ _ _ _ _ _ φ (fun x => by
        change Mono (SmallObject.functorObjLeftFamily idealInclusionFamily
          ((toZeroArrowFunctor R).obj M).hom x.as)
        exact hmono x.as)
    exact @CategoryTheory.Limits.colim.map_mono' _ _ _ _ _ _ _ _ φ hφ
      _ (colimit.isColimit _)
      _ (colimit.isColimit _) _ (by
        intro x
        change Sigma.ι (SmallObject.functorObjSrcFamily idealInclusionFamily
          ((toZeroArrowFunctor R).obj M).hom) x.as ≫
            CategoryTheory.Limits.Sigma.map (SmallObject.functorObjLeftFamily idealInclusionFamily
              ((toZeroArrowFunctor R).obj M).hom) =
          SmallObject.functorObjLeftFamily idealInclusionFamily
              ((toZeroArrowFunctor R).obj M).hom x.as ≫
            Sigma.ι (SmallObject.functorObjTgtFamily idealInclusionFamily
              ((toZeroArrowFunctor R).obj M).hom) x.as
        exact Sigma.ι_map _ x.as)
  exact @CategoryTheory.Abelian.mono_pushout_of_mono_g _ _ _ _ _ _ _ _ _ hleft

/-- The successor structure used by the transfinite construction. -/
noncomputable def baerSuccStruct (R : Type u) [Ring R] :
    CategoryTheory.SmallObject.SuccStruct
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  CategoryTheory.SmallObject.SuccStruct.ofNatTrans (baerStepEmbedding R)

/-- The endofunctor at every stage of the ordinal-indexed iteration. -/
noncomputable def baerIterationFunctor (R : Type u) [Ring R]
    (α : Ordinal.{u})
    [HasIterationOfShape (Set.Iic α)
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)] :
    Set.Iic α ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  (baerSuccStruct R).iterationFunctor (Set.Iic α)

/-- The functor `𝕄_α` at the top stage of the iteration over `α`. -/
noncomputable def baerIteration (R : Type u) [Ring R] (α : Ordinal.{u})
    [HasIterationOfShape (Set.Iic α)
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)] :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (baerIterationFunctor R α).obj ⟨α, by simp⟩

/-- The functorial embedding `N → 𝕄_α(N)`. -/
noncomputable def baerIterationEmbedding (R : Type u) [Ring R]
    (α : Ordinal.{u})
    [HasIterationOfShape (Set.Iic α)
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)] :
    𝟭 (ModuleCat.{u} R) ⟶ baerIteration R α :=
  ((baerSuccStruct R).ιIterationFunctor (Set.Iic α)).app ⟨α, by simp⟩

/-- The coherent diagram of stages below a limit ordinal. -/
noncomputable def baerIterationDiagram (R : Type u) [Ring R]
    (α : Ordinal.{u})
    [HasIterationOfShape (Set.Iic α)
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)] :
    Set.Iio α ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  (Set.principalSegIioIicOfLE (le_rfl : α ≤ α)).monotone.functor ⋙
    baerIterationFunctor R α

/-- The zero stage is the identity functor. -/
theorem baerIteration_zero {R : Type u} [Ring R]
    [HasIterationOfShape (Set.Iic (0 : Ordinal.{u}))
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)] :
    Nonempty (baerIteration R 0 ≅
      𝟭 (ModuleCat.{u} R)) := by
  exact ⟨(baerSuccStruct R).iterationFunctorObjBotIso
    (Set.Iic (0 : Ordinal.{u}))⟩

/-- The first stage is the huge-pushout functor. -/
theorem baerIteration_one {R : Type u} [Ring R]
    [HasIterationOfShape (Set.Iic (1 : Ordinal.{u}))
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)] :
    Nonempty (baerIteration R 1 ≅ baerStepFunctor R) := by
  let j : Set.Iic (1 : Ordinal.{u}) := ⊥
  have hj : ¬ IsMax j := by
    apply not_isMax_iff.mpr
    refine ⟨(⊤ : Set.Iic (1 : Ordinal.{u})), ?_⟩
    change (0 : Ordinal.{u}) < 1
    exact zero_lt_one
  have hsucc : Order.succ j =
      (⟨1, by simp⟩ : Set.Iic (1 : Ordinal.{u})) := by
    apply Subtype.ext
    rw [Set.Iic.coe_succ_of_not_isMax hj]
    exact zero_add 1
  exact ⟨by
    simpa only [baerIteration, baerIterationFunctor] using
      (eqToIso (congrArg
          ((baerSuccStruct R).iterationFunctor (Set.Iic (1 : Ordinal.{u}))).obj
          hsucc).symm ≪≫
        (baerSuccStruct R).iterationFunctorObjSuccIso j hj ≪≫
        Functor.isoWhiskerRight
          ((baerSuccStruct R).iterationFunctorObjBotIso
            (Set.Iic (1 : Ordinal.{u}))) (baerStepFunctor R) ≪≫
        Functor.leftUnitor (baerStepFunctor R))⟩

/-- Successor stages are obtained by applying the huge-pushout functor.

The lower stage is taken from the same ambient iteration over `Set.Iic (α + 1)`;
using `baerIteration R α` here would introduce an independently chosen
`SuccStruct` iteration and would require an unavailable initial-segment
invariance interface. -/
theorem baerIteration_succ {R : Type u} [Ring R] (α : Ordinal.{u})
    [HasIterationOfShape (Set.Iic (α + 1))
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)] :
    Nonempty (baerIteration R (α + 1) ≅
      (baerIterationFunctor R (α + 1)).obj
          ⟨α, by simp⟩ ⋙ baerStepFunctor R) := by
  let j : Set.Iic (α + 1) := ⟨α, by simp⟩
  have hj : ¬ IsMax j := by
    apply not_isMax_iff.mpr
    refine ⟨(⊤ : Set.Iic (α + 1)), ?_⟩
    change α < α + 1
    simp
  have hsucc : Order.succ j =
      (⟨α + 1, by simp⟩ : Set.Iic (α + 1)) := by
    apply Subtype.ext
    rw [Set.Iic.coe_succ_of_not_isMax hj]
    simp [j]
  have hsucc_obj :
      (baerSuccStruct R).succ
          (((baerSuccStruct R).iterationFunctor (Set.Iic (α + 1))).obj j) =
        ((baerSuccStruct R).iterationFunctor (Set.Iic (α + 1))).obj j ⋙
          baerStepFunctor R := by
    rfl
  exact ⟨by
    simpa only [baerIteration, baerIterationFunctor] using
      (eqToIso (congrArg
          ((baerSuccStruct R).iterationFunctor (Set.Iic (α + 1))).obj
          hsucc).symm ≪≫
        (baerSuccStruct R).iterationFunctorObjSuccIso j hj ≪≫
        eqToIso hsucc_obj)⟩

/-- At a limit stage, the iteration is the colimit of its earlier stages. -/
theorem baerIteration_limit {R : Type u} [Ring R] (α : Ordinal.{u})
    [HasIterationOfShape (Set.Iic α)
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)]
    (hα : Order.IsSuccLimit α) :
    Nonempty (baerIteration R α ≅ colimit (baerIterationDiagram R α)) := by
  let f := Set.principalSegIioIicOfLE (le_rfl : α ≤ α)
  have htop : Order.IsSuccLimit f.top := by
    rw [Order.isSuccLimit_iff_of_orderBot]
    constructor
    · intro h
      exact (ne_of_gt hα.bot_lt) (congrArg Subtype.val h)
    · intro b hb
      apply hα.isSuccPrelimit b.1
      refine ⟨?_, ?_⟩
      · exact hb.lt
      · intro c hbc hca
        let c' : Set.Iic α := ⟨c, hca.le⟩
        exact hb.2 (show b < c' from hbc) (show c' < f.top from hca)
  have hc := CategoryTheory.Functor.isColimitOfIsWellOrderContinuous'
    ((baerSuccStruct R).iterationFunctor (Set.Iic α)) f htop
  exact ⟨IsColimit.coconePointUniqueUpToIso hc
    (colimit.isColimit (baerIterationDiagram R α))⟩

/-- The cardinality of the set of ideals of `R`. -/
def idealCardinal (R : Type u) [Ring R] : Cardinal.{u} := Cardinal.mk (Ideal R)

/-- Baer's transfinite construction reaches an injective module at any stage
whose cofinality is larger than the cardinality of the ideal set, and the
canonical map from the starting module is a functorial monomorphic embedding.
-/
theorem baer_grothendieck
    {R : Type u} [Ring R] (N : ModuleCat.{u} R) (α : Ordinal.{u})
    [HasIterationOfShape (Set.Iic α)
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)]
    (hα : idealCardinal R < Ordinal.cof α) :
    Injective ((baerIteration R α).obj N) ∧
      Mono ((baerIterationEmbedding R α).app N) := by
  let ev := (evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj N
  have hle :
      (baerSuccStruct R).prop ≤
        (MorphismProperty.monomorphisms (ModuleCat.{u} R)).inverseImage ev := by
    intro X Y f hf
    change Mono (ev.map f)
    have hto : Mono ((baerSuccStruct R).toSucc X) := by
      letI : ∀ M, Mono (((baerSuccStruct R).toSucc X).app M) := by
        intro M
        change Mono ((baerStepEmbedding R).app (X.obj M))
        exact baerStepEmbedding_mono _
      exact NatTrans.mono_of_mono_app _
    rw [hf.fac]
    rw [Functor.map_comp]
    infer_instance
  let t :=
    (baerSuccStruct R).transfiniteCompositionOfShapeιIteration (Set.Iic α)
  have htop (i : Set.Iic α) : Mono (ev.map (t.incl.app i)) := by
    letI : HasColimitsOfShape (Set.Ici i) (ModuleCat.{u} R) := by
      infer_instance
    letI : HasIterationOfShape (Set.Ici i) (ModuleCat.{u} R) := by
      constructor <;> infer_instance
    letI : IsGrothendieckAbelian.{u} (ModuleCat.{u} R) := by
      infer_instance
    letI : MorphismProperty.IsStableUnderFilteredColimits.{u, u}
        (MorphismProperty.monomorphisms (ModuleCat.{u} R)) := by
      infer_instance
    let hfiltered : MorphismProperty.IsStableUnderFilteredColimits.{u, u}
        (MorphismProperty.monomorphisms (ModuleCat.{u} R)) := by
      infer_instance
    letI := hfiltered
    letI : (MorphismProperty.monomorphisms (ModuleCat.{u} R)).IsStableUnderTransfiniteCompositionOfShape
        (Shrink.{u} (Set.Ici i)) := by
      exact
        MorphismProperty.IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape
          (fun J _ _ _ _ ↦ hfiltered.isStableUnderColimitsOfShape J)
    have hmap :=
      MorphismProperty.TransfiniteCompositionOfShape.map
        (F := ev) ((t.ici i).ofLE hle)
    let e : Shrink.{u} (Set.Ici i) ≃o Set.Ici i :=
      (orderIsoShrink.{u} (Set.Ici i)).symm
    exact (MorphismProperty.transfiniteCompositionsOfShape_le
      (MorphismProperty.monomorphisms (ModuleCat.{u} R))
      (Shrink.{u} (Set.Ici i))) _ (hmap.ofOrderIso e).mem
  let F : Set.Iio α ⥤ ModuleCat.{u} R :=
    baerIterationDiagram R α ⋙ ev
  have hF : ∀ {i j : Set.Iio α} (q : i ⟶ j), Mono (F.map q) := by
    intro i j q
    change Mono (ev.map ((baerIterationDiagram R α).map q))
    have hiα : (i : Ordinal) ≤ α := le_of_lt i.2
    have hjα : (j : Ordinal) ≤ α := le_of_lt j.2
    let i' : Set.Iic α := ⟨(i : Ordinal), hiα⟩
    let j' : Set.Iic α := ⟨(j : Ordinal), hjα⟩
    have hnat := t.incl.naturality (show i' ⟶ j' from q)
    have hcomp :
        ev.map ((baerIterationDiagram R α).map q) ≫ ev.map (t.incl.app j') =
          ev.map (t.incl.app i') := by
      have hnat' := congrArg ev.map hnat
      rw [Functor.map_comp] at hnat'
      change
        ev.map (t.F.map (show i' ⟶ j' from q)) ≫
            ev.map (t.incl.app j') =
          ev.map (t.incl.app i') ≫
            ev.map (((Functor.const _).obj
              ((baerSuccStruct R).iteration (Set.Iic α))).map
              (show i' ⟶ j' from q)) at hnat'
      change
        ev.map (t.F.map (show i' ⟶ j' from q)) ≫
            ev.map (t.incl.app j') =
          ev.map (t.incl.app i')
      simpa using hnat'
    have hmono : Mono (ev.map ((baerIterationDiagram R α).map q) ≫
        ev.map (t.incl.app j')) := by
      rw [hcomp]
      exact htop i'
    constructor
    intro Z g h e
    apply (cancel_mono (ev.map ((baerIterationDiagram R α).map q) ≫
      ev.map (t.incl.app j'))).mp
    rw [← Category.assoc, e, Category.assoc]
  have hcard : (1 : Cardinal.{u}) ≤ idealCardinal R := by
    rw [Cardinal.one_le_iff_ne_zero]
    simp [idealCardinal]
  have hαlim : Order.IsSuccLimit α :=
    (Ordinal.one_lt_cof_iff).mp (hcard.trans_lt hα)
  have hsucc_lt (i : Set.Iio α) : Order.succ (i : Ordinal) < α := by
    exact hαlim.succ_lt i.2
  let eα : baerIteration R α ≅ colimit (baerIterationDiagram R α) :=
    (baerIteration_limit α hαlim).some
  have hcolim : IsColimit (ev.mapCocone
      (colimit.cocone (baerIterationDiagram R α))) :=
    isColimitOfPreserves ev (colimit.isColimit (baerIterationDiagram R α))
  let eN := eα.app N
  let eF : ev.obj (colimit (baerIterationDiagram R α)) ≅ colimit F :=
    IsColimit.coconePointUniqueUpToIso hcolim (colimit.isColimit F)
  constructor
  · rw [baer_criterion]
    intro I φ
    let idealMap : Submodule R (I : Type u) → Ideal R :=
      fun K => K.map I.subtype
    have idealMap_inj : Function.Injective idealMap := by
      intro K L h
      apply le_antisymm
      · apply (Submodule.map_le_map_iff_of_injective (f := I.subtype)
          Subtype.val_injective K L).mp
        exact le_of_eq h
      · apply (Submodule.map_le_map_iff_of_injective (f := I.subtype)
          Subtype.val_injective L K).mp
        exact le_of_eq h.symm
    have hcardI : moduleSubmoduleCardinal R (ModuleCat.of R I) ≤
        idealCardinal R := by
      change Cardinal.mk (Submodule R (I : Type u)) ≤ Cardinal.mk (Ideal R)
      exact Cardinal.mk_le_of_injective idealMap_inj
    have hsmall := module_is_alpha_small (ModuleCat.of R I) α
      (hcardI.trans_lt hα)
    have hbij := hsmall F hF (by infer_instance) (by infer_instance)
    let φ' : ModuleCat.of R I ⟶ colimit F :=
      φ ≫ eN.hom ≫ eF.hom
    obtain ⟨x, hx⟩ := hbij.2 φ'
    obtain ⟨i, f, hf⟩ := Types.jointly_surjective
      (F ⋙ coyoneda.obj (Opposite.op (ModuleCat.of R I)))
      (colimit.isColimit (F ⋙ coyoneda.obj
        (Opposite.op (ModuleCat.of R I)))) x
    have hfactor : f ≫ colimit.ι F i = φ' := by
      rw [← hf] at hx
      simpa [comparisonMap] using hx
    have hiα : (i : Ordinal) ≤ α := le_of_lt i.2
    let j : Set.Iic α := ⟨(i : Ordinal), hiα⟩
    have hj : ¬ IsMax j := by
      apply not_isMax_iff.mpr
      refine ⟨(⟨α, by simp⟩ : Set.Iic α), ?_⟩
      exact i.2
    have hsuccj : Order.succ j =
        (⟨Order.succ (i : Ordinal), (hsucc_lt i).le⟩ : Set.Iic α) := by
      apply Subtype.ext
      exact Set.Iic.coe_succ_of_not_isMax hj
    let k : Set.Iio α := ⟨Order.succ (i : Ordinal), hsucc_lt i⟩
    let q : i ⟶ k := homOfLE (Order.le_succ (i : Ordinal))
    have hpi :
        ((Set.principalSegIioIicOfLE (le_rfl : α ≤ α)).monotone.functor).obj i =
          (⟨(i : Ordinal), hiα⟩ : Set.Iic α) := by
      rfl
    have hpk :
        ((Set.principalSegIioIicOfLE (le_rfl : α ≤ α)).monotone.functor).obj k =
          (⟨Order.succ (i : Ordinal), (hsucc_lt i).le⟩ : Set.Iic α) := by
      rfl
    obtain ⟨ψ, hψ⟩ := baerStep_ideal_extension (F.obj i) I f
    have hobj_i : F.obj i =
        (((baerSuccStruct R).iterationFunctor (Set.Iic α)).obj j).obj N := by
      rfl
    have hobj_k : F.obj k =
        (((baerSuccStruct R).iterationFunctor (Set.Iic α)).obj
          (Order.succ j)).obj N := by
      simp [F, baerIterationDiagram, baerIterationFunctor, ev, j, k, hsuccj]
    have hjs : j ≤ Order.succ j := by
      exact Order.le_succ j
    have hpk_succ :
          ((Set.principalSegIioIicOfLE (le_rfl : α ≤ α)).monotone.functor).obj k =
          Order.succ j := by
      calc
        _ = (⟨Order.succ (i : Ordinal), (hsucc_lt i).le⟩ : Set.Iic α) := hpk
        _ = Order.succ j := hsuccj.symm
    let q' :
        ((Set.principalSegIioIicOfLE (le_rfl : α ≤ α)).monotone.functor).obj i ⟶
          ((Set.principalSegIioIicOfLE (le_rfl : α ≤ α)).monotone.functor).obj k :=
      eqToHom hpi ≫ homOfLE hjs ≫ eqToHom hpk_succ.symm
    have hq_q :
        ((Set.principalSegIioIicOfLE (le_rfl : α ≤ α)).monotone.functor).map q = q' := by
      apply Subsingleton.elim
    have hsource : baerStep R (F.obj i) =
        ((baerSuccStruct R).succ
          (((baerSuccStruct R).iterationFunctor (Set.Iic α)).obj j)).obj N := by
      rfl
    let heSuccN : baerStep R (F.obj i) ≅ F.obj k :=
      eqToIso hsource ≪≫
        (((baerSuccStruct R).iterationFunctorObjSuccIso j hj).app N |>.symm) ≪≫
        eqToIso hobj_k.symm
    have hcomp :
        (baerStepEmbedding R).app (F.obj i) ≫ heSuccN.hom ≍
          ((((baerSuccStruct R).iterationFunctor (Set.Iic α)).obj j).whiskerLeft
              (baerStepEmbedding R)).app N ≫
            ((baerSuccStruct R).iterationFunctorObjSuccIso j hj).inv.app N := by
      apply CategoryTheory.heq_comp (eq1 := hobj_i) (eq2 := hsource)
        (eq3 := hobj_k)
      · have hobj_i' :
            ((baerIterationDiagram R α).obj i).obj N =
              (((baerSuccStruct R).iterationFunctor (Set.Iic α)).obj j).obj N := by
          simpa [F, baerIterationDiagram, ev, j] using hobj_i
        simp only [baerStepEmbedding]
        cases hobj_i'
        rfl
      · have hsymm :
            (((baerSuccStruct R).iterationFunctorObjSuccIso j hj).app N).symm.hom =
              ((baerSuccStruct R).iterationFunctorObjSuccIso j hj).inv.app N := by
          rfl
        simpa only [heSuccN, Iso.trans_hom, eqToIso.hom, Category.assoc,
          hsymm, eqToHom_comp_heq_iff, heq_comp_eqToHom_iff] using
          (CategoryTheory.comp_eqToHom_heq
            (((baerSuccStruct R).iterationFunctorObjSuccIso j hj).inv.app N)
            hobj_k.symm)
    have hmap : F.map q =
        (baerStepEmbedding R).app (F.obj i) ≫ heSuccN.hom := by
      have hiter := (baerSuccStruct R).iterationFunctor_map_succ j hj
      have hiterN := congrArg (fun m => m.app N) hiter
      convert hiterN using 1
      · rw [hobj_i, hobj_k]
      · have hq_map := congrArg (fun m => m.app N)
            (congrArg ((baerSuccStruct R).iterationFunctor (Set.Iic α)).map hq_q)
        have hq'_map_heq :
            (((baerSuccStruct R).iterationFunctor (Set.Iic α)).map q').app N ≍
              (((baerSuccStruct R).iterationFunctor (Set.Iic α)).map
                (homOfLE hjs)).app N := by
          simp only [q', Functor.map_comp]
          rw [CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_map]
          simp only [NatTrans.comp_app, Category.assoc,
            CategoryTheory.eqToHom_app,
            CategoryTheory.eqToHom_comp_heq_iff,
            CategoryTheory.heq_comp_eqToHom_iff]
          symm
          rw [CategoryTheory.heq_comp_eqToHom_iff]
        simpa [F, baerIterationDiagram, baerIterationFunctor, ev, q] using
          (HEq.trans (heq_of_eq hq_map) hq'_map_heq)
      · simpa [baerSuccStruct, CategoryTheory.SmallObject.SuccStruct.ofNatTrans,
          baerStep, baerStepFunctor, baerStepEmbedding, F,
          baerIterationDiagram, baerIterationFunctor, ev, j, k, hsuccj,
          hsource, heSuccN]
          using hcomp
    let g0 : ModuleCat.of R R ⟶ colimit F :=
      ψ ≫ heSuccN.hom ≫ colimit.ι F k
    have hstage :
        ModuleCat.ofHom I.subtype ≫
            (ψ ≫ heSuccN.hom ≫ colimit.ι F k) =
          f ≫ colimit.ι F i := by
      rw [← Category.assoc, ← Category.assoc, hψ]
      have hmap_f := congrArg
        (fun m => f ≫ m ≫ colimit.ι F k) hmap.symm
      calc
        ((f ≫ (baerStepEmbedding R).app (F.obj i)) ≫ heSuccN.hom) ≫
              colimit.ι F k =
            f ≫ ((baerStepEmbedding R).app (F.obj i) ≫ heSuccN.hom) ≫
              colimit.ι F k := by simp only [Category.assoc, baerStep]
        _ = f ≫ F.map q ≫ colimit.ι F k := hmap_f
        _ = f ≫ colimit.ι F i := by rw [colimit.w F q]
    refine ⟨g0 ≫ eF.inv ≫ eN.inv, ?_⟩
    have hfinal := congrArg (fun m => m ≫ eF.inv ≫ eN.inv) hstage
    simpa [g0, Category.assoc, hfactor, φ'] using hfinal
  · have hmono : Mono (ev.map (t.isoBot.inv ≫ t.incl.app ⊥)) := by
      rw [Functor.map_comp]
      letI : Mono (ev.map (t.incl.app ⊥)) := htop ⊥
      infer_instance
    have hι :
        ((baerSuccStruct R).ιIterationFunctor (Set.Iic α)).app
            (⟨α, by simp⟩ : Set.Iic α) =
          t.isoBot.inv ≫ t.F.map (homOfLE bot_le) := by
      rfl
    have hnat := t.incl.naturality (homOfLE bot_le :
      (⊥ : Set.Iic α) ⟶ (⟨α, by simp⟩ : Set.Iic α))
    have hnat' :
        t.isoBot.inv ≫ t.F.map (homOfLE bot_le) ≫
            t.incl.app (⟨α, by simp⟩ : Set.Iic α) =
          t.isoBot.inv ≫ t.incl.app ⊥ := by
      simpa [Category.assoc] using
        congrArg (fun m => t.isoBot.inv ≫ m) hnat
    have hcomp :
        ev.map (((baerSuccStruct R).ιIterationFunctor (Set.Iic α)).app
          (⟨α, by simp⟩ : Set.Iic α)) ≫
            ev.map (t.incl.app (⟨α, by simp⟩ : Set.Iic α)) =
          ev.map (t.isoBot.inv ≫ t.incl.app ⊥) := by
      change
        (((baerSuccStruct R).ιIterationFunctor (Set.Iic α)).app
          (⟨α, by simp⟩ : Set.Iic α)).app N ≫
          (t.incl.app (⟨α, by simp⟩ : Set.Iic α)).app N =
            (t.isoBot.inv ≫ t.incl.app ⊥).app N
      have hιN := congrArg (fun m => m.app N) hι
      have hnatN' := congrArg (fun m => m.app N) hnat'
      rw [hιN]
      change
        (t.isoBot.inv.app N ≫
            (t.F.map (homOfLE bot_le)).app N) ≫
          (t.incl.app (⟨α, by simp⟩ : Set.Iic α)).app N =
            t.isoBot.inv.app N ≫ (t.incl.app ⊥).app N at hnatN'
      exact hnatN'
    let m : ev.obj (t.F.obj (⟨α, by simp⟩ : Set.Iic α)) ⟶
        ev.obj ((baerSuccStruct R).iteration (Set.Iic α)) := by
      exact ev.map (t.incl.app (⟨α, by simp⟩ : Set.Iic α))
    have hcomp' :
        ev.map (((baerSuccStruct R).ιIterationFunctor (Set.Iic α)).app
          (⟨α, by simp⟩ : Set.Iic α)) ≫ m =
          ev.map (t.isoBot.inv ≫ t.incl.app ⊥) := by
      change ev.map (((baerSuccStruct R).ιIterationFunctor (Set.Iic α)).app
          (⟨α, by simp⟩ : Set.Iic α)) ≫
            ev.map (t.incl.app (⟨α, by simp⟩ : Set.Iic α)) =
          ev.map (t.isoBot.inv ≫ t.incl.app ⊥)
      exact hcomp
    change Mono (ev.map (((baerSuccStruct R).ιIterationFunctor
      (Set.Iic α)).app (⟨α, by simp⟩ : Set.Iic α)))
    rw [hι] at hcomp'
    have hm0 : Mono (ev.map (t.isoBot.inv ≫
        t.F.map (homOfLE (bot_le :
          (⊥ : Set.Iic α) ≤ (⟨α, by simp⟩ : Set.Iic α))))) := by
      letI : Mono (ev.map (t.isoBot.inv ≫ t.incl.app ⊥)) := hmono
      constructor
      intro Z g h e
      apply (cancel_mono (ev.map (t.isoBot.inv ≫ t.incl.app ⊥))).mp
      rw [← hcomp']
      simp only [Functor.const_obj_obj]
      change
        (g ≫ ev.map (t.isoBot.inv ≫
          t.F.map (homOfLE (bot_le :
            (⊥ : Set.Iic α) ≤ (⟨α, by simp⟩ : Set.Iic α))))) ≫ m =
          (h ≫ ev.map (t.isoBot.inv ≫
            t.F.map (homOfLE (bot_le :
              (⊥ : Set.Iic α) ≤ (⟨α, by simp⟩ : Set.Iic α))))) ≫ m
      rw [e]
    rw [hι]
    exact hm0

end Formalization.Books.Injectives.Unit02
