import Formalization.Books.Algebra.Unit84.TransfiniteDevissage
import Formalization.Books.Algebra.Unit88.MittagLefflerModules
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.CategoryTheory.Limits.Presentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Commutative Algebra, Chapter 92: Countably generated Mittag-Leffler modules

The source's directed systems are represented by `ColimitPresentation`s.  The
countable subdiagram is expressed using the canonical colimit map from a
subtype-indexed restriction, and factorization through a finitely presented
module is recorded as a property of a module-category morphism.
-/

namespace Formalization.Books.Algebra.Unit92

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit84
open Formalization.Books.Algebra.Unit88
open Formalization.Books.Categories.Unit21

universe u v w

noncomputable section

/-! ## Countable directed colimits -/

/-- The inclusion of a subtype-indexed subset into its preorder. -/
def subtypeInclusion
    {I : Type u} [Preorder I] (S : Set I) : (S : Type u) ⥤ I where
  obj i := i.1
  map f := homOfLE (leOfHom f)
  map_id := by simp
  map_comp f g := by simp

/-- The canonical map from a colimit presentation of a restricted subdiagram
to the target of the original colimit presentation. -/
def restrictedColimitMap
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    {M : ModuleCat.{w} R} (P : ColimitPresentation I M)
    {S : Set I} {Q : ModuleCat.{w} R}
    (P' : ColimitPresentation S Q)
    (hdiag : P'.diag = subtypeInclusion S ⋙ P.diag) : Q ⟶ M := by
  exact P'.isColimit.desc
      (Cocone.mk _ (hdiag.symm ▸ ((subtypeInclusion S).whiskerLeft P.ι)))

private structure GeneralFilteredColimit92
    {R : Type u} [CommRing R] (N : ModuleCat.{max u w} R) where
  index : Type (max u w)
  [indexPreorder : Preorder index]
  [indexFiltered : IsFiltered index]
  presentation : ColimitPresentation index N
  underlyingIsColimit :
    IsColimit ((forget (ModuleCat.{max u w} R)).mapCocone presentation.cocone)
  finitelyPresented : ∀ i, Module.FinitePresentation R (presentation.diag.obj i)

private local instance generalFilteredColimit92IndexPreorder
    {R : Type u} [CommRing R] {N : ModuleCat.{max u w} R}
    (C : GeneralFilteredColimit92 N) : Preorder C.index :=
  C.indexPreorder

private local instance generalFilteredColimit92IndexFiltered
    {R : Type u} [CommRing R] {N : ModuleCat.{max u w} R}
    (C : GeneralFilteredColimit92 N) : IsFiltered C.index :=
  C.indexFiltered

private theorem exists_generalFilteredColimit92
    {R : Type u} [CommRing R] (N : ModuleCat.{max u w} R) :
    Nonempty (GeneralFilteredColimit92 N) := by
  /-
  Proof roadmap.

  * Use the construction in
    `Formalization/Books/Algebra/Unit88/MittagLefflerModules.lean`, theorem
    `exists_finitelyPresentedFilteredColimit`, as the template, but do not try
    to extract a `Preorder` from that theorem's result: the public
    `FinitelyPresentedFilteredColimit` interface remembers only a `Category`
    instance. This declaration needs the actual thin preorder in order to
    feed `exists_countable_directed_subcolimit`.
  * Repeat that construction with `M := (N : Type (max u w))` and
    `Index : Type (max u w)`. Every stage, the diagram, and the forgetful
    functor must likewise use `ModuleCat.{max u w} R`; the `Type w` and
    `ModuleCat.{w} R` annotations in the retained sketch below are invalid
    when `u` is larger than `w`.
  * Order pairs `(S, E)` by extension of the finite set of generators and of
    the finite set of relations. Prove filteredness by finite unions, exactly
    as in `exists_finitelyPresentedFilteredColimit`. Define each stage as
    `(S →₀ R) ⧸ Submodule.span R E`; use `Submodule.mapQ` for transition maps
    and `Submodule.liftQ` for the maps to `N`.
  * Prove the underlying type cocone colimiting with
    `Types.FilteredColimit.isColimitOf'` from
    `Mathlib/CategoryTheory/Limits/Types/Filtered.lean`: singleton generators
    give joint surjectivity, while adjoining `x' - y'` to `E` gives eventual
    equality.
  * Bundle the same `diag`, `ι`, underlying colimit witness, and finite
    presentation proof first as
    `FinitelyPresentedFilteredColimit.{u, max u w, w} N`. Then obtain the
    module-category witness with `finitelyPresentedFilteredColimit_isColimit`
    from Unit 88 and use it to form `ColimitPresentation Index N`. Finally
    package that presentation, the local `Preorder`/`IsFiltered` instances,
    the underlying witness, and `Module.finitePresentation_of_surjective` into
    `GeneralFilteredColimit92 N`.
  -/
  /- prior attempt retained during diagnostic repair:
  classical
  let M := (N : Type w)
  let embedding (S T : Finset M) (hST : S ≤ T) : S ↪ T :=
    { toFun := fun s => ⟨s.1, hST s.2⟩
      inj' := by
        intro s t h
        apply Subtype.ext
        exact congrArg (fun z : T => (z : M)) h }
  let extend (S T : Finset M) (hST : S ≤ T) :
      (S →₀ R) →ₗ[R] (T →₀ R) :=
    Finsupp.lmapDomain R R (embedding S T hST)
  have extend_id (S : Finset M) (x : S →₀ R) :
      extend S S le_rfl x = x := by
    change Finsupp.mapDomain (embedding S S le_rfl) x = x
    have he : (embedding S S le_rfl : S → S) = id := by
      funext s
      exact Subtype.ext rfl
    rw [he, Finsupp.mapDomain_id]
  have extend_comp (S T U : Finset M) (hST : S ≤ T) (hTU : T ≤ U)
      (x : S →₀ R) :
      extend T U hTU (extend S T hST x) = extend S U (hST.trans hTU) x := by
    change Finsupp.mapDomain (embedding T U hTU)
        (Finsupp.mapDomain (embedding S T hST) x) =
      Finsupp.mapDomain (embedding S U (hST.trans hTU)) x
    rw [← Finsupp.mapDomain_comp]
    congr 1
  let Index : Type (max u w) :=
    Σ S : Finset M, {E : Finset (S →₀ R) //
      ∀ e ∈ E, Finsupp.linearCombination R (fun s : S => (s : M)) e = 0}
  let indexLE : Index → Index → Prop := fun a b =>
    ∃ hST : a.1 ≤ b.1, ∀ e ∈ a.2.1,
      extend a.1 b.1 hST e ∈ b.2.1
  let _ : LE Index := ⟨indexLE⟩
  let _ : Preorder Index := {
    le_refl := by
      intro a
      refine ⟨le_rfl, ?_⟩
      intro e he
      simpa [extend_id] using he
    le_trans := by
      intro a b c hab hbc
      rcases hab with ⟨habS, habE⟩
      rcases hbc with ⟨hbcS, hbcE⟩
      refine ⟨habS.trans hbcS, ?_⟩
      intro e he
      have he' := hbcE (extend a.1 b.1 habS e) (habE e he)
      rw [extend_comp] at he'
      exact he' }
  have index_filtered : IsFiltered Index := by
    let emptyIndex : Index := ⟨∅, ⟨∅, by simp⟩⟩
    refine
      { cocone_objs := ?_
        cocone_maps := ?_
        nonempty := ⟨emptyIndex⟩ }
    · intro a b
      let S : Finset M := a.1 ∪ b.1
      have haS : a.1 ≤ S := by simp [S]
      have hbS : b.1 ≤ S := by simp [S]
      let Ea : Finset (S →₀ R) := a.2.1.image (extend a.1 S haS)
      let Eb : Finset (S →₀ R) := b.2.1.image (extend b.1 S hbS)
      let E : Finset (S →₀ R) := Ea ∪ Eb
      have hrel : ∀ e ∈ E,
          Finsupp.linearCombination R (fun s : S => (s : M)) e = 0 := by
        intro e he
        rcases Finset.mem_union.mp he with he | he
        · rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
          change Finsupp.linearCombination R (fun s : S => (s : M))
              (Finsupp.mapDomain (embedding a.1 S haS) e') = 0
          rw [Finsupp.linearCombination_mapDomain]
          change Finsupp.linearCombination R (fun s : a.1 => (s : M)) e' = 0
          exact a.2.2 e' he'
        · rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
          change Finsupp.linearCombination R (fun s : S => (s : M))
              (Finsupp.mapDomain (embedding b.1 S hbS) e') = 0
          rw [Finsupp.linearCombination_mapDomain]
          change Finsupp.linearCombination R (fun s : b.1 => (s : M)) e' = 0
          exact b.2.2 e' he'
      let c : Index := ⟨S, ⟨E, hrel⟩⟩
      have hac : a ≤ c := by
        refine ⟨haS, ?_⟩
        intro e he
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      have hbc : b ≤ c := by
        refine ⟨hbS, ?_⟩
        intro e he
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      exact ⟨c, homOfLE hac, homOfLE hbc, trivial⟩
    · intro X Y f g
      exact ⟨Y, 𝟙 _, by subsingleton⟩
  let stage (a : Index) : ModuleCat.{w} R :=
    ModuleCat.of R ((a.1 →₀ R) ⧸ Submodule.span R (a.2.1 : Set (a.1 →₀ R)))
  have span_extend {a b : Index} (h : a ≤ b) :
      Submodule.span R (a.2.1 : Set (a.1 →₀ R)) ≤
        Submodule.comap (extend a.1 b.1 h.choose)
          (Submodule.span R (b.2.1 : Set (b.1 →₀ R))) := by
    rcases h with ⟨hST, hE⟩
    rw [Submodule.span_le]
    intro e he
    change extend a.1 b.1 hST e ∈
      Submodule.span R (b.2.1 : Set (b.1 →₀ R))
    exact Submodule.subset_span (hE e he)
  let stageMap {a b : Index} (h : a ≤ b) : stage a ⟶ stage b :=
    ModuleCat.ofHom <|
      Submodule.mapQ (Submodule.span R (a.2.1 : Set (a.1 →₀ R)))
        (Submodule.span R (b.2.1 : Set (b.1 →₀ R)))
        (extend a.1 b.1 h.choose) (span_extend h)
  let D : Index ⥤ ModuleCat.{w} R := {
    obj := stage
    map := fun {a b} f => stageMap (leOfHom f)
    map_id := by
      intro a
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      let hS : a.1 ≤ a.1 := le_rfl
      change Submodule.Quotient.mk (extend a.1 a.1 hS x) =
        Submodule.Quotient.mk x
      rw [extend_id]
    map_comp := by
      intro a b c f g
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      let hf : a ≤ b := leOfHom f
      let hg : b ≤ c := leOfHom g
      let hfg : a ≤ c := leOfHom (f ≫ g)
      change Submodule.Quotient.mk (extend a.1 c.1 hfg.choose x) =
        Submodule.Quotient.mk
          (extend b.1 c.1 hg.choose (extend a.1 b.1 hf.choose x))
      rw [extend_comp] }
  let stageToN (a : Index) : stage a ⟶ N :=
    ModuleCat.ofHom <|
      Submodule.liftQ _
        (Finsupp.linearCombination R (fun s : a.1 => (s : M)))
        (by
          apply Submodule.span_le.2
          intro e he
          exact a.2.2 e he)
  let c : Cocone D := {
    pt := N
    ι :=
      { app := stageToN
        naturality := by
          intro a b f
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
          let hf : a ≤ b := leOfHom f
          change Finsupp.linearCombination R (fun s : b.1 => (s : M))
              (Finsupp.mapDomain (embedding a.1 b.1 hf.choose) x) =
            Finsupp.linearCombination R (fun s : a.1 => (s : M)) x
          rw [Finsupp.linearCombination_mapDomain]
          rfl } }
  have hc : IsColimit ((forget (ModuleCat.{w} R)).mapCocone c) := by
    apply Types.FilteredColimit.isColimitOf'
    · intro x
      let S : Finset M := {x}
      let a : Index := ⟨S, ⟨∅, by simp⟩⟩
      let q : S →₀ R := Finsupp.single ⟨x, by simp [S]⟩ 1
      refine ⟨a, Submodule.Quotient.mk q, ?_⟩
      change x = Finsupp.linearCombination R (fun s : S => (s : M)) q
      simp [q, S]
    · intro a x y hxy
      obtain ⟨x', hx'⟩ := Submodule.mkQ_surjective
        (Submodule.span R (a.2.1 : Set (a.1 →₀ R))) x
      obtain ⟨y', hy'⟩ := Submodule.mkQ_surjective
        (Submodule.span R (a.2.1 : Set (a.1 →₀ R))) y
      have hxy' :
          stageToN a (Submodule.Quotient.mk x') =
            stageToN a (Submodule.Quotient.mk y') := by
        rw [← hx', ← hy'] at hxy
        simpa [c] using hxy
      have hrel :
          Finsupp.linearCombination R (fun s : a.1 => (s : M)) (x' - y') = 0 := by
        have hxy'' :
            Finsupp.linearCombination R (fun s : a.1 => (s : M)) x' =
              Finsupp.linearCombination R (fun s : a.1 => (s : M)) y' := by
          change Finsupp.linearCombination R (fun s : a.1 => (s : M)) x' =
            Finsupp.linearCombination R (fun s : a.1 => (s : M)) y' at hxy'
          exact hxy'
        rw [map_sub]
        exact sub_eq_zero.mpr hxy''
      let E : Finset (a.1 →₀ R) := insert (x' - y') a.2.1
      have hE : ∀ e ∈ E,
          Finsupp.linearCombination R (fun s : a.1 => (s : M)) e = 0 := by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact hrel
        · exact a.2.2 e he
      let b : Index := ⟨a.1, ⟨E, hE⟩⟩
      have hab : a ≤ b := by
        refine ⟨le_rfl, ?_⟩
        intro e he
        rw [extend_id]
        exact Finset.mem_insert_of_mem he
      refine ⟨b, homOfLE hab, ?_⟩
      rw [← hx', ← hy']
      change Submodule.Quotient.mk (extend a.1 b.1 hab.choose x') =
        Submodule.Quotient.mk (extend a.1 b.1 hab.choose y')
      rw [extend_id]
      rw [extend_id]
      rw [← sub_eq_zero]
      change (Submodule.mkQ _ x') - (Submodule.mkQ _ y') = 0
      rw [← map_sub]
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact Submodule.subset_span (Finset.mem_insert_self _ _)
  let P : ColimitPresentation Index N :=
    { diag := D
      ι := c.ι
      isColimit := isColimitOfReflects (forget (ModuleCat.{w} R)) hc }
  exact ⟨{
    index := Index
    indexPreorder := inferInstance
    indexFiltered := index_filtered
    presentation := P
    underlyingIsColimit := hc
    finitelyPresented := by
      intro a
      change Module.FinitePresentation R
        ((a.1 →₀ R) ⧸ Submodule.span R (a.2.1 : Set (a.1 →₀ R)))
      apply Module.finitePresentation_of_surjective (Submodule.mkQ _)
      · exact Submodule.mkQ_surjective _
      · rw [Submodule.ker_mkQ]
      exact Submodule.fg_span a.2.1.finite_toSet }⟩
  -/
  sorry

/-- A countably generated Mittag-Leffler module has a countable directed
subdiagram of any finitely presented colimit presentation with the same
colimit. -/
theorem exists_countable_directed_subcolimit
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    [Nonempty I] [IsDirectedOrder I] {M : ModuleCat.{max u w} R}
    (P : ColimitPresentation I M)
    (hstage : ∀ i, Module.FinitePresentation R (P.diag.obj i))
    (hML : IsMittagLefflerModule M)
    (hcountable : Module.IsCountablyGenerated R (M : Type (max u w))) :
    ∃ (S : Set I) (Q : ModuleCat.{max u w} R)
      (P' : ColimitPresentation S Q)
      (hdiag : P'.diag = subtypeInclusion S ⋙ P.diag),
      S.Countable ∧ IsDirectedSet S ∧
        IsIso (restrictedColimitMap P P' hdiag) := by
  /-
  Proof roadmap.

  * Work throughout in the carrier universe `Type (max u w)`; the index stays
    in `Type v`. This separation is the reason for the signature repair above.
    Obtain a countable spanning set `X` from `hcountable`, insert zero,
    enumerate it, and represent each enumerated generator at a stage using
    `Types.jointly_surjective_of_isColimit` from
    `Mathlib/CategoryTheory/Limits/Types/Colimits.lean` applied to
    `isColimitOfPreserves (forget (ModuleCat.{max u w} R)) P.isColimit`.
  * Instantiate
    `mittagLeffler_characterization.{u, v, max u w, max u w} P hstage`
    (Unit 88) and take conditions 1 and 3. For each `i`, choose `stable i`
    with `i ≤ stable i` and maps back from every later stage which factor the
    transition `i ⟶ stable i`.
  * Choose binary upper bounds and recursively define `a : ℕ → I` so that
    `a n ≤ a (n + 1)`, the `n`th generator stage lies below `a n`, and
    `stable (a n) ≤ a (n + 1)`. Put `S := Set.range a`; prove countability by
    `Set.countable_range` and directedness with the stage `a (max m n)`.
  * Let `D := subtypeInclusion S ⋙ P.diag` in
    `ModuleCat.{max u w} R`, take `Q := colimit D`, and use `colimit.cocone`
    and `colimit.isColimit` for `P' : ColimitPresentation S Q`. Set
    `uS := restrictedColimitMap P P' rfl`.
  * Prove `uS.hom` surjective by checking that its linear range contains the
    spanning set: move each chosen representative from its generator stage to
    `a n` and use `P'.isColimit.fac` plus `P.ι.naturality`.
  * For injectivity, use
    `Types.FilteredColimit.isColimit_eq_iff`/`isColimit_eq_iff'` from
    `Mathlib/CategoryTheory/Limits/Types/Filtered.lean`. If `x` at `i : S`
    maps to zero, write `i.1 = a n`, make `x` zero at some full-diagram stage
    `k`, and apply the Mittag-Leffler factorization to make it zero at
    `stable i.1`. Then map once more along
    `stable (a n) ≤ a (n + 1)` and use the restricted stage `a (n + 1)`.
    Crucially, do not use `stable i.1` itself as an object of `S`: the data only
    proves it lies below a member of `S`, not that it is in `Set.range a`.
  * Convert injectivity and surjectivity to `Mono uS` and `Epi uS` with
    `ModuleCat.mono_iff_injective` and `ModuleCat.epi_iff_surjective`
    (`Mathlib/Algebra/Category/ModuleCat/EpiMono.lean`), apply
    `isIso_of_mono_of_epi`, and return `⟨S, Q, P', rfl, ...⟩`.
  -/
  /- prior attempt retained during diagnostic repair:
  classical
  obtain ⟨X, hX, hspan⟩ := hcountable
  let X' : Set (M : Type w) := insert 0 X
  have hX' : X'.Countable := hX.insert 0
  have hX'nonempty : X'.Nonempty := ⟨0, Set.mem_insert _ _⟩
  obtain ⟨enum, henum⟩ := hX'.exists_eq_range hX'nonempty
  let enum' : ℕ → X' := fun n => ⟨enum n, by
    rw [henum]
    exact ⟨n, rfl⟩⟩
  have hrep (x : (M : Type w)) :
      ∃ (i : I) (y : (P.diag.obj i : Type w)), (P.ι.app i).hom y = x := by
    simpa using
      (Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget (ModuleCat.{max u w} R)) P.isColimit) x)
  let stageOf : X' → I := fun x => (hrep x).choose
  have stageOf_spec (x : X') :
      ∃ y : (P.diag.obj (stageOf x) : Type w),
        (P.ι.app (stageOf x)).hom y = (x : (M : Type w)) := by
    exact (hrep x).choose_spec
  let b : ℕ → I := fun n => stageOf (enum' n)
  have hML' := (mittagLeffler_characterization P hstage).out 0 2
  have hstable := hML'.mp hML
  let stable : I → I := fun i => (hstable i).choose
  have hstable_le (i : I) : i ≤ stable i :=
    (hstable i).choose_spec.choose
  have hstable_factor (i k : I) (hik : i ≤ k) :
      ∃ h : (P.diag.obj k : Type w) →ₗ[R] (P.diag.obj (stable i) : Type w),
        directedMap P.diag (hstable_le i) =
          h.comp (directedMap P.diag hik) := by
    simpa [stable, hstable_le] using
      (hstable i).choose_spec.choose_spec k hik
  let upper : I → I → I := fun x y =>
    (directed_of (· ≤ ·) x y).choose
  have upper_left (x y : I) : x ≤ upper x y := by
    exact (directed_of (· ≤ ·) x y).choose_spec.1
  have upper_right (x y : I) : y ≤ upper x y := by
    exact (directed_of (· ≤ ·) x y).choose_spec.2
  let upper3 : I → I → I → I := fun x y z => upper (upper x y) z
  have upper3_left (x y z : I) : x ≤ upper3 x y z := by
    exact (upper_left x y).trans (upper_left (upper x y) z)
  have upper3_mid (x y z : I) : y ≤ upper3 x y z := by
    exact (upper_right x y).trans (upper_left (upper x y) z)
  have upper3_right (x y z : I) : z ≤ upper3 x y z := by
    exact upper_right (upper x y) z
  let a : ℕ → I := Nat.rec (b 0)
    (fun n x => upper3 x (b (n + 1)) (stable x))
  have ha_succ (n : ℕ) : a n ≤ a (n + 1) := by
    simpa [a] using upper3_left (a n) (b (n + 1)) (stable (a n))
  have hb (n : ℕ) : b n ≤ a n := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
        simpa [a] using upper3_mid (a n) (b (n + 1)) (stable (a n))
  have hstable_a (n : ℕ) : stable (a n) ≤ a (n + 1) := by
    simpa [a] using upper3_right (a n) (b (n + 1)) (stable (a n))
  have ha_mono : Monotone a := monotone_nat_of_le_succ ha_succ
  let S : Set I := Set.range a
  have hS_countable : S.Countable := by
    exact Set.countable_range a
  have hS_directed : IsDirectedSet (↑S) := by
    refine ⟨⟨⟨a 0, ⟨0, rfl⟩⟩⟩, ?_⟩
    refine ⟨?_⟩
    intro x y
    rcases x.property with ⟨m, hm⟩
    rcases y.property with ⟨n, hn⟩
    have hx : x = ⟨a m, ⟨m, rfl⟩⟩ := by
      apply Subtype.ext
      exact hm.symm
    have hy : y = ⟨a n, ⟨n, rfl⟩⟩ := by
      apply Subtype.ext
      exact hn.symm
    rw [hx, hy]
    refine ⟨⟨a (max m n), ⟨max m n, rfl⟩⟩, ?_, ?_⟩
    · exact ha_mono (Nat.le_max_left _ _)
    · exact ha_mono (Nat.le_max_right _ _)
  letI : IsFiltered (↑S) := by
    refine { cocone_objs := ?_, cocone_maps := ?_, nonempty := hS_directed.1 }
    · intro x y
      obtain ⟨z, hxz, hyz⟩ := hS_directed.2.directed x y
      exact ⟨z, homOfLE hxz, homOfLE hyz, trivial⟩
    · intro X Y f g
      exact ⟨Y, 𝟙 _, by subsingleton⟩
  let D : (↑S) ⥤ ModuleCat.{w} R := subtypeInclusion S ⋙ P.diag
  let Q : ModuleCat.{w} R := colimit D
  let P' : ColimitPresentation (↑S) Q :=
    { diag := D
      ι := (colimit.cocone D).ι
      isColimit := colimit.isColimit D }
  let u : Q ⟶ M := restrictedColimitMap P P' rfl
  have hu_surjective : Function.Surjective u.hom := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.2
    intro x hx
    obtain ⟨n, hn⟩ := henum ▸ hx
    obtain ⟨y, hy⟩ := stageOf_spec (enum' n)
    let y' := P.diag.map (homOfLE (hb n)) y
    refine ⟨P'.ι.app ⟨a n, ⟨n, rfl⟩⟩ y', ?_⟩
    have hfac := P'.isColimit.fac (Cocone.mk _
      (rfl ▸ ((subtypeInclusion S).whiskerLeft P.ι)))
      ⟨a n, ⟨n, rfl⟩⟩
    change (P'.ι.app ⟨a n, ⟨n, rfl⟩⟩ ≫ u).hom y' = x
    rw [hfac]
    change (P.ι.app (a n)).hom y' = x
    rw [← hy]
    simpa [y', colimitComponentMap, directedMap] using
      congrArg (fun q => q y) (P.ι.naturality (homOfLE (hb n)))
  have hu_injective : Function.Injective u.hom := by
    intro z hz
    obtain ⟨i, x, rfl⟩ :=
      Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget (ModuleCat.{w} R)) P'.isColimit) z
    obtain ⟨k, hik, hk0⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff _
        (isColimitOfPreserves (forget (ModuleCat.{w} R)) P.isColimit)).mp hz
    obtain ⟨h, hfactor⟩ := hstable_factor i.1 k hik
    have hzero : (P.diag.map (homOfLE (hstable_le i.1))).hom x = 0 := by
      rw [hfactor]
      simp [hk0]
    apply (Types.FilteredColimit.isColimit_eq_iff _
      (isColimitOfPreserves (forget (ModuleCat.{w} R)) P'.isColimit)).2
    refine ⟨⟨stable i.1, ?_⟩, ?_, le_rfl, ?_⟩
    · exact ⟨i, hstable_le i.1⟩
    · exact hstable_le i.1
    · simpa [D, subtypeInclusion, directedMap] using hzero
  have hu_iso : IsIso u := by
    apply isIso_of_mono_of_epi u
    · exact (ModuleCat.mono_iff_injective u).2 hu_injective
    · exact (ModuleCat.epi_iff_surjective u).2 hu_surjective
  refine ⟨S, Q, P', rfl, hS_countable, hS_directed, hu_iso⟩
  -/
  sorry

/-- A countable directed set admits a cofinal monotone sequence indexed by
`ℕ`; repetitions are allowed, which also covers finite directed sets. -/
theorem exists_cofinal_monotone_sequence
    {I : Type u} [Preorder I] [Countable I]
    (hI : IsDirectedSet I) :
    ∃ a : ℕ → I, (∀ n, a n ≤ a (n + 1)) ∧
      ∀ i, ∃ n, i ≤ a n := by
  classical
  let _ : Nonempty I := hI.1
  obtain ⟨s, hs⟩ := countable_iff_exists_surjective.mp
    (inferInstance : Countable I)
  let a : ℕ → I := Nat.rec (s 0)
    (fun n x => (hI.2.directed (s (n + 1)) x).choose)
  have ha (n : ℕ) : s (n + 1) ≤ a (n + 1) := by
    exact (hI.2.directed (s (n + 1)) (a n)).choose_spec.1
  have hamono (n : ℕ) : a n ≤ a (n + 1) := by
    exact (hI.2.directed (s (n + 1)) (a n)).choose_spec.2
  refine ⟨a, ?_, ?_⟩
  · intro n
    exact hamono n
  · intro i
    obtain ⟨n, hn⟩ := hs i
    subst i
    cases n with
    | zero => exact ⟨0, le_rfl⟩
    | succ n => exact ⟨n + 1, ha n⟩

/-- A countably generated Mittag-Leffler module is a sequential filtered
colimit of finitely presented modules. -/
theorem exists_nat_colimitPresentation_of_mittagLeffler_countablyGenerated
    {R : Type u} [CommRing R] {M : ModuleCat.{max u w} R}
    (hML : IsMittagLefflerModule M)
    (hcountable : Module.IsCountablyGenerated R (M : Type (max u w))) :
    ∃ P : ColimitPresentation ℕ M,
      ∀ n, Module.FinitePresentation R (P.diag.obj n) := by
  /-
  Proof roadmap.

  * Choose `C : GeneralFilteredColimit92 M`; install its `Preorder` and
    `IsFiltered` fields and derive `Nonempty C.index` and
    `IsDirectedOrder C.index` from `C.indexFiltered.cocone_objs`.
  * Apply `exists_countable_directed_subcolimit` to `C.presentation` at index
    universe `max u w` and module universe `max u w`. This yields a countable
    directed `S`, a presentation `P' : ColimitPresentation S Q`, and an
    isomorphism `uS : Q ⟶ M`. Install `Countable S` using
    `hScountable.to_subtype` and the filtered-category instance coming from
    `hSdirected`.
  * Apply `exists_cofinal_monotone_sequence hSdirected` to obtain
    `a : ℕ → S`. Define `D : ℕ ⥤ ModuleCat.{max u w} R` by
    `D.obj n := P'.diag.obj (a n)` and map the unique order morphisms using
    monotonicity of `a`.
  * Put `L := colimit D` and define `vLQ : L ⟶ Q` by the cocone with legs
    `P'.ι.app (a n)`. Prove surjectivity of `vLQ.hom` using
    `Types.jointly_surjective_of_isColimit` for `P'` followed by cofinality of
    `a`. Prove injectivity by representing two elements in stages `n,m`, using
    `Types.FilteredColimit.isColimit_eq_iff` in `P'`, choosing a cofinal stage,
    and moving both representatives to `max (max n m) k₀`.
  * Obtain `IsIso vLQ` with the ModuleCat mono/epi criteria. Compose it with
    `uS` to get an isomorphism `wLM : L ⟶ M`. Transport
    `colimit.isColimit D` across `wLM`: the cocone legs are
    `colimit.ι D n ≫ wLM`, its `desc` is
    `inv wLM ≫ (colimit.isColimit D).desc`, and uniqueness follows by
    cancelling the epi `wLM`.
  * Bundle this transported cocone as `P : ColimitPresentation ℕ M`.
    Rewrite `P'.diag` with `hdiag` and discharge finite presentation of
    `D.obj n` using `C.finitelyPresented (a n).1`.

  The retained sketch has the correct assembly but all occurrences of
  `Type w`/`ModuleCat.{w}` in it must be replaced by
  `Type (max u w)`/`ModuleCat.{max u w}`.
  -/
  /- prior attempt retained during diagnostic repair:
  classical
  obtain ⟨C⟩ := exists_generalFilteredColimit92 M
  letI : Preorder C.index := C.indexPreorder
  letI : Category.{max u w} C.index := inferInstance
  letI : IsFiltered C.index := C.indexFiltered
  letI : Nonempty C.index := C.indexFiltered.nonempty
  letI : IsDirectedOrder C.index := by
    refine ⟨?_⟩
    intro i j
    obtain ⟨k, f, g, _⟩ := C.indexFiltered.cocone_objs i j
    exact ⟨k, leOfHom f, leOfHom g⟩
  obtain ⟨S, Q, P', hdiag, hScountable, hSdirected, hu⟩ :=
    exists_countable_directed_subcolimit C.presentation C.finitelyPresented hML hcountable
  letI : Countable (↑S) := hScountable.to_subtype
  letI : IsFiltered (↑S) := by
    refine { cocone_objs := ?_, cocone_maps := ?_, nonempty := hSdirected.1 }
    · intro x y
      obtain ⟨z, hxz, hyz⟩ := hSdirected.2.directed x y
      exact ⟨z, homOfLE hxz, homOfLE hyz, trivial⟩
    · intro X Y f g
      exact ⟨Y, 𝟙 _, by subsingleton⟩
  obtain ⟨a, ha_succ, hcofinal⟩ := exists_cofinal_monotone_sequence hSdirected
  have ha_mono : Monotone a := monotone_nat_of_le_succ ha_succ
  let D : ℕ ⥤ ModuleCat.{w} R := {
    obj := fun n => P'.diag.obj (a n)
    map := fun {n m} f =>
      P'.diag.map (homOfLE (ha_mono (leOfHom f)))
    map_id := by
      intro n
      rw [show homOfLE (ha_mono (leOfHom (𝟙 n))) = 𝟙 _ by subsingleton,
        P'.diag.map_id]
    map_comp := by
      intro n m k f g
      change
        P'.diag.map (homOfLE (ha_mono (leOfHom (f ≫ g)))) =
          P'.diag.map (homOfLE (ha_mono (leOfHom f))) ≫
            P'.diag.map (homOfLE (ha_mono (leOfHom g)))
      rw [← P'.diag.map_comp]
      congr 1 <;> subsingleton }
  let L : ModuleCat.{w} R := colimit D
  let cQ : Cocone D := {
    pt := Q
    ι := {
      app := fun n => P'.ι.app (a n)
      naturality := by
        intro n m f
        simpa [D] using P'.ι.naturality (homOfLE (ha_mono (leOfHom f))) } }
  let v : L ⟶ Q := (colimit.isColimit D).desc cQ
  have hv_fac (n : ℕ) (x : (D.obj n : Type w)) :
      v.hom ((colimit.ι D n).hom x) = (P'.ι.app (a n)).hom x := by
    have h := congrArg (fun q => q.hom x)
      ((colimit.isColimit D).fac cQ n)
    simpa [v, cQ, D] using h
  have hv_surjective : Function.Surjective v.hom := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    intro y _
    obtain ⟨i, x, hx⟩ :=
      Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget (ModuleCat.{w} R)) P'.isColimit) y
    obtain ⟨n, hin⟩ := hcofinal i
    let x' := P'.diag.map (homOfLE hin) x
    refine ⟨(colimit.ι D n).hom x', ?_⟩
    rw [hv_fac]
    rw [← hx]
    simpa [x', D] using
      congrArg (fun q => q x) (P'.ι.naturality (homOfLE hin))
  have hv_injective : Function.Injective v.hom := by
    intro z₁ z₂ hz
    obtain ⟨n, x, hx⟩ :=
      Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget (ModuleCat.{w} R)) (colimit.isColimit D)) z₁
    obtain ⟨m, y, hy⟩ :=
      Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget (ModuleCat.{w} R)) (colimit.isColimit D)) z₂
    have hz' : (P'.ι.app (a n)).hom x = (P'.ι.app (a m)).hom y := by
      rw [← hx, ← hy] at hz
      change v.hom ((colimit.ι D n).hom x) =
        v.hom ((colimit.ι D m).hom y) at hz
      exact (hv_fac n x).symm.trans (hz.trans (hv_fac m y))
    obtain ⟨i, hni, hmi, hxy⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff _
        (isColimitOfPreserves (forget (ModuleCat.{w} R)) P'.isColimit)).mp hz'
    obtain ⟨k₀, hik₀⟩ := hcofinal i
    let k := max (max n m) k₀
    have hnk : n ≤ k :=
      (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
    have hmk : m ≤ k :=
      (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
    have hik : i ≤ a k := hik₀.trans (ha_mono (Nat.le_max_right _ _))
    have hxy' := congrArg
      (fun q => (P'.diag.map (homOfLE hik)).hom q) hxy
    have hxy'' :
        (D.map (homOfLE hnk)).hom x =
          (D.map (homOfLE hmk)).hom y := by
      change (P'.diag.map (homOfLE (ha_mono hnk))).hom x =
        (P'.diag.map (homOfLE (ha_mono hmk))).hom y
      rw [show homOfLE (ha_mono hnk) = hni ≫ homOfLE hik by subsingleton,
        show homOfLE (ha_mono hmk) = hmi ≫ homOfLE hik by subsingleton,
        P'.diag.map_comp, P'.diag.map_comp]
      exact hxy'
    apply (Types.FilteredColimit.isColimit_eq_iff _
      (isColimitOfPreserves (forget (ModuleCat.{w} R)) (colimit.isColimit D))).2
    rw [← hx, ← hy]
    exact ⟨k, homOfLE hnk, homOfLE hmk, hxy''⟩
  have hv : IsIso v := by
    apply isIso_of_mono_of_epi v
    · exact (ModuleCat.mono_iff_injective v).2 hv_injective
    · exact (ModuleCat.epi_iff_surjective v).2 hv_surjective
  let u : Q ⟶ M := restrictedColimitMap C.presentation P' hdiag
  letI : IsIso u := hu
  letI : IsIso v := hv
  let w : L ⟶ M := v ≫ u
  let cM : Cocone D := {
    pt := M
    ι := {
      app := fun n => (colimit.ι D n) ≫ w
      naturality := by
        intro n m f
        rw [← Category.assoc, ← Category.assoc]
        rw [show D.map f ≫ colimit.ι D m = colimit.ι D n by
          simpa using (colimit.cocone D).ι.naturality f]
      }
    }
  have hcM : IsColimit cM := by
    refine
      { desc := fun s => inv w ≫ (colimit.isColimit D).desc s
        fac := by
          intro s n
          dsimp [cM]
          simp only [Category.assoc, IsIso.hom_inv_id_assoc]
          exact (colimit.isColimit D).fac s n
        uniq := by
          intro s m hm
          apply (cancel_epi w).1
          apply (colimit.isColimit D).hom_ext
          intro n
          have hn := hm n
          simpa [cM, Category.assoc] using hn }
  have hstage' (i : (↑S)) :
      Module.FinitePresentation R (P'.diag.obj i) := by
    rw [hdiag]
    exact C.finitelyPresented i.1
  let P : ColimitPresentation ℕ M :=
    { diag := D
      ι := cM.ι
      isColimit := hcM }
  refine ⟨P, ?_⟩
  intro n
  exact hstage' (a n)
  -/
  sorry

/-! ## Finite-presentation factorization -/

/-- A module-category morphism factors through a finitely presented module. -/
def FactorsThroughFinitelyPresented
    {R : Type u} [CommRing R] {M N : ModuleCat.{w} R}
    (f : M ⟶ N) : Prop :=
  ∃ Q : ModuleCat.{w} R, Module.FinitePresentation R (Q : Type w) ∧
    ∃ g : M ⟶ Q, ∃ h : Q ⟶ N, g ≫ h = f

private theorem exists_section_with_value_zero
    (E : ℕᵒᵖ ⥤ Type v)
    (hE : ∀ ⦃i j : ℕᵒᵖ⦄ (f : i ⟶ j), Function.Surjective (E.map f))
    (y : E.obj (Opposite.op 0)) :
    ∃ s : E.sections, s.val (Opposite.op 0) = y := by
  /-
  Proof roadmap.

  * Specialize `hE` to the successor arrows and apply
    `Types.surjective_π_app_zero_of_surjective_map` from
    `Mathlib/CategoryTheory/Limits/Types/Images.lean` to
    `Types.limitConeIsLimit E`. Concretely, the second argument is
    `(fun n => hE ((homOfLE (Nat.le_succ n)).op))`.
  * In this universe (`ℕᵒᵖ : Type` and `E : ℕᵒᵖ ⥤ Type v`),
    `Types.limitCone E` is definitionally the cone whose point is
    `E.sections` and whose zero projection is
    `s ↦ s.val (Opposite.op 0)`
    (`Mathlib/CategoryTheory/Limits/Types/Limits.lean`). Apply the resulting
    surjectivity statement to `y` and return its preimage directly.

  Do not pass through `IsFiltered.sequentialFunctor`, initial-functor limit
  isomorphisms, or `Types.limitEquivSections`; that retained route adds an
  unnecessary reindexing and obscures the definitional section model. The
  direct four-line proof has been checked at this hole.
  -/
  /- prior attempt retained during diagnostic repair:
  let hI : IsDirectedSet ℕ := ⟨inferInstance, inferInstance⟩
  let Q₀ : ℕ ⥤ ℕ := IsFiltered.sequentialFunctor ℕ
  let Q : ℕᵒᵖ ⥤ ℕᵒᵖ := Q₀.op
  letI : Q.Initial := by
    dsimp [Q]
    infer_instance
  let H : ℕᵒᵖ ⥤ Type v := Q ⋙ E
  have hH : ∀ n : ℕ, Function.Surjective
      (H.map (homOfLE (Nat.le_succ n)).op) := by
    intro n
    change Function.Surjective (E.map (Q.map (homOfLE (Nat.le_succ n)).op))
    exact hE _
  have hπ : Function.Surjective ((Types.limitCone H).π.app ⟨0⟩) :=
    Types.surjective_π_app_zero_of_surjective_map
      (Types.limitConeIsLimit H) hH
  let y' : H.obj ⟨0⟩ := by
    change E.obj (Opposite.op ((IsFiltered.sequentialFunctor ℕ).obj 0))
    simpa only [IsFiltered.sequentialFunctor_obj] using y
  obtain ⟨x, hx⟩ := hπ y'
  let eH : (Types.limitCone H).pt ≅ limit H :=
    (Types.limitConeIsLimit H).conePointUniqueUpToIso (limit.isLimit H)
  let eF : limit H ≅ limit E := Functor.Initial.limitIso Q E
  let s : E.sections := Types.limitEquivSections E (eF.hom (eH.hom x))
  refine ⟨s, ?_⟩
  simpa [s, eF, eH, Types.limitEquivSections, y'] using hx
  -/
  sorry

/-- For a finitely generated source, every map into a countably generated
Mittag-Leffler module is fixed by an endomorphism factoring through a finitely
presented module. -/
theorem exists_endomorphism_factorsThroughFinitelyPresented
    {R : Type u} [CommRing R] {M P : ModuleCat.{max u w} R}
    (hML : IsMittagLefflerModule M)
    (hcountable : Module.IsCountablyGenerated R (M : Type (max u w)))
    (hP : Module.Finite R (P : Type (max u w))) (f : P ⟶ M) :
    ∃ α : M ⟶ M,
      FactorsThroughFinitelyPresented α ∧ f ≫ α = f := by
  /- prior attempt retained during diagnostic repair:
  classical
  letI : Module.Finite R (P : Type w) := hP
  obtain ⟨n, gen, hgen⟩ := Module.Finite.exists_fin' R (P : Type w)
  obtain ⟨P₀, hP₀⟩ := exists_nat_colimitPresentation_of_mittagLeffler_countablyGenerated
    hML hcountable
  by_cases hn : n = 0
  · have hf0 : f = 0 := by
      subst n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨k, rfl⟩ := hgen x
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      rw [map_zero, map_zero]
    refine ⟨0, ?_, ?_⟩
    · refine ⟨ModuleCat.of R (ULift.{w} PUnit), inferInstance, 0, 0, by simp⟩
    · simpa [hf0]
  · letI : IsFiltered ℕ := by
      refine { cocone_objs := ?_, cocone_maps := ?_, nonempty := inferInstance }
      · intro i j
        exact ⟨max i j, homOfLE (Nat.le_max_left _ _),
          homOfLE (Nat.le_max_right _ _), trivial⟩
      · intro i j g h
        exact ⟨j, 𝟙 _, by subsingleton⟩
    choose idx x hx using fun k : Fin n =>
      Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget (ModuleCat.{w} R)) P₀.isColimit)
          (f.hom (gen k))
    let J : Finset ℕ := Finset.univ.image idx
    have hJ : J.Nonempty := by
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      refine ⟨idx ⟨0, hnpos⟩, ?_⟩
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    let j : ℕ := J.max' hJ
    have hj (k : Fin n) : idx k ≤ j := by
      exact Finset.le_max' J (idx k)
        (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    let D₀ : ℕ ⥤ ModuleCat.{w} R := {
      obj := fun m => P₀.diag.obj (j + m)
      map := fun {m l} g =>
        P₀.diag.map (homOfLE (Nat.add_le_add_left (leOfHom g) j))
      map_id := by
        intro m
        change P₀.diag.map (homOfLE _) = 𝟙 _
        rw [show homOfLE _ = 𝟙 _ by subsingleton, P₀.diag.map_id]
      map_comp := by
        intro m l r g h
        dsimp [D₀]
        rw [← P₀.diag.map_comp]
        congr 1 <;> subsingleton }
    let c₀ : Cocone D₀ := {
      pt := M
      ι := {
        app := fun m => P₀.ι.app (j + m)
        naturality := by
          intro m l g
          simpa [D₀] using
            P₀.ι.naturality (homOfLE (Nat.add_le_add_left (leOfHom g) j)) } }
    have hc₀ : IsColimit ((forget (ModuleCat.{w} R)).mapCocone c₀) := by
      apply Types.FilteredColimit.isColimitOf'
      · intro y
        obtain ⟨m, z, hz⟩ :=
          Types.jointly_surjective_of_isColimit
            (isColimitOfPreserves (forget (ModuleCat.{w} R)) P₀.isColimit) y
        have hm : m ≤ j + m := by omega
        let z' := P₀.diag.map (homOfLE hm) z
        refine ⟨m, z', ?_⟩
        have hnat := congrArg (fun q => q.hom z)
          (P₀.ι.naturality (homOfLE hm))
        simpa [c₀, z', D₀] using hnat.trans hz
      · intro m z z' hzz'
        obtain ⟨l, hml, hm'l, hzz⟩ :=
          (Types.FilteredColimit.isColimit_eq_iff _
            (isColimitOfPreserves (forget (ModuleCat.{w} R)) P₀.isColimit)).mp hzz'
        have hml' : m ≤ l := by
          exact (Nat.le_add_left m j).trans (leOfHom hml)
        have hm'l' : m ≤ l := by
          exact (Nat.le_add_left m j).trans (leOfHom hm'l)
        have hl : l ≤ j + l := by omega
        have hzz' := congrArg
          (fun q => (P₀.diag.map (homOfLE hl)).hom q) hzz
        refine ⟨l, homOfLE hml', homOfLE hm'l', ?_⟩
        · simpa [D₀, Functor.map_comp] using hzz'
    let P₁ : ColimitPresentation ℕ M :=
      { diag := D₀
        ι := c₀.ι
        isColimit := isColimitOfReflects (forget (ModuleCat.{w} R)) hc₀ }
    have hP₁ (m : ℕ) : Module.FinitePresentation R (P₁.diag.obj m) := by
      exact hP₀ (j + m)
    let N : ModuleCat.{w} R :=
      ModuleCat.of R (∀ s : ℕ, (P₁.diag.obj s : Type w))
    let G := homInverseSystem P₁.diag N
    have hG : G.IsMittagLeffler := by
      have hML' := ((mittagLeffler_characterization P₁ hP₁).out 0 3).mp hML
      exact hML' N
    obtain ⟨kop, fop, hfop⟩ :=
      (Formalization.Books.Algebra.Unit86.isMittagLeffler_iff_eventualRange G).mp
        hG (Opposite.op 0)
    let k : ℕ := kop.unop
    have h0k : 0 ≤ k := le_of_op_hom fop
    let x₀ : (P₁.diag.obj k : Type w) →ₗ[R] (N : Type w) :=
      { toFun := fun z s => if h : s = k then h ▸ z else 0
        map_add' := by
          intro z z'
          funext s
          by_cases h : s = k
          · subst s
            simp
          · simp [h]
        map_smul' := by
          intro r z
          funext s
          by_cases h : s = k
          · subst s
            simp
          · simp [h] }
    let y := G.map fop x₀
    have hy : y ∈ G.eventualRange (Opposite.op 0) := by
      rw [hfop]
      exact ⟨x₀, rfl⟩
    let E := G.toEventualRanges
    have hE : ∀ ⦃i l : ℕᵒᵖ⦄ (g : i ⟶ l), Function.Surjective (E.map g) := by
      intro i l g
      exact Formalization.Books.Algebra.Unit86.eventualRange_map_surjective G hG g
    obtain ⟨sE, hsE⟩ := exists_section_with_value_zero E hE ⟨y, hy⟩
    let sG : G.sections := G.toEventualRangesSectionsEquiv ⟨sE, sE.property⟩
    have hsG : sG.val (Opposite.op 0) = y := by
      have hs := congrArg Subtype.val hsE
      simpa [sG, Functor.toEventualRangesSectionsEquiv] using hs
    let cN : Cocone P₁.diag := {
      pt := N
      ι := {
        app := fun m => ModuleCat.ofHom (sG.val (Opposite.op m))
        naturality := by
          intro m l g
          apply ModuleCat.hom_ext
          change (sG.val (Opposite.op l)).comp (P₁.diag.map g).hom =
            sG.val (Opposite.op m)
          have hs := sG.property g.op
          change (sG.val (Opposite.op l)).comp (P₁.diag.map g).hom =
            sG.val (Opposite.op m) at hs
          exact hs } }
    let zHom : M ⟶ N := P₁.isColimit.desc cN
    let proj (m : ℕ) : (N : Type w) →ₗ[R] (P₁.diag.obj m : Type w) :=
      { toFun := fun z => z m
        map_add' := by
          intro z z'
          change (z + z') m = z m + z' m
          rfl
        map_smul' := by
          intro r z
          change (r • z) m = r • z m
          rfl }
    let zₖ : M ⟶ P₁.diag.obj k := ModuleCat.ofHom ((proj k).comp zHom.hom)
    let α : M ⟶ M := zₖ ≫ P₁.ι.app k
    have hgen_fix (r : Fin n) : α.hom (f.hom (gen r)) = f.hom (gen r) := by
      obtain ⟨z, y₀, hz⟩ :=
        (Types.jointly_surjective_of_isColimit
          (isColimitOfPreserves (forget (ModuleCat.{w} R)) P₀.isColimit)
          (f.hom (gen r)))
      have hzj : (P₁.ι.app 0).hom
          ((P₀.diag.map (homOfLE (hj r))).hom z) = f.hom (gen r) := by
        simpa [P₁, D₀] using
          congrArg (fun q => q.hom z)
            (P₀.ι.naturality (homOfLE (hj r))) |>.symm.trans hz
      have hfac := P₁.isColimit.fac cN 0
      have hyk (q : (P₁.diag.obj 0 : Type w)) :
          (proj k) (y q) =
            (P₁.diag.map (homOfLE h0k)).hom q := by
        apply LinearMap.ext
        intro q
        simp [y, G, homInverseSystem, x₀, proj, k, h0k]
      have hfac' : zHom.hom.comp (P₁.ι.app 0).hom =
          (cN.ι.app 0).hom := by
        simpa [zHom, cN] using congrArg ModuleCat.Hom.hom hfac
      have hzα := congrArg
        (fun q => (proj k)
          (q ((P₁.ι.app 0).hom
            ((P₀.diag.map (homOfLE (hj r))).hom z))))
        hfac'
      rw [hzj] at hzα
      rw [hsG, hyk] at hzα
      simpa [α, zₖ, P₁, cN, proj] using hzα
    have hfix : f ≫ α = f := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro p
      obtain ⟨r, hr⟩ := hgen p
      rw [← hr]
      change α.hom (f.hom (gen r)) = f.hom (gen r)
      exact hgen_fix r
    refine ⟨α, ?_, hfix⟩
    unfold FactorsThroughFinitelyPresented
    refine ⟨P₁.diag.obj k, hP₁ k, zₖ, P₁.ι.app k, rfl⟩
  -/
  sorry

/-! ## The polynomial quotient example -/

/-- The polynomial ring in countably many variables over `k`. -/
abbrev countablePolynomialRing (k : Type u) [CommRing k] :=
  MvPolynomial ℕ k

/-- The ideal generated by all polynomial variables. -/
def countablePolynomialVariableIdeal (k : Type u) [CommRing k] :
    Ideal (countablePolynomialRing k) :=
  Ideal.span (Set.range
    (MvPolynomial.X (R := k) : ℕ → countablePolynomialRing k))

/-- The quotient module `k[x₁, x₂, …]/(x₁, x₂, …)`, viewed over the
polynomial ring. -/
abbrev countablePolynomialQuotientModule
    (k : Type u) [CommRing k] :
    ModuleCat.{u} (countablePolynomialRing k) :=
  ModuleCat.of (countablePolynomialRing k)
    (countablePolynomialRing k ⧸ countablePolynomialVariableIdeal k)

/-- The ideal generated by the first `n` variables.  The index `0` represents
`x₁`, so the displayed family starts at `n = 0` in Lean. -/
def finitePolynomialVariableIdeal (k : Type u) [CommRing k] (n : ℕ) :
    Ideal (countablePolynomialRing k) :=
  Ideal.span (Set.range (fun i : Fin n =>
    (MvPolynomial.X (R := k) (i : ℕ) : countablePolynomialRing k)))

/-- The finite stage `k[x₁, …, xₙ]/(x₁, …, xₙ)`. -/
abbrev finitePolynomialStage (k : Type u) [CommRing k] (n : ℕ) :
    ModuleCat.{u} (countablePolynomialRing k) :=
  ModuleCat.of (countablePolynomialRing k)
    (countablePolynomialRing k ⧸ finitePolynomialVariableIdeal k n)

/-- The finite-variable ideals increase with the stage. -/
theorem finitePolynomialVariableIdeal_mono
    (k : Type u) [CommRing k] {m n : ℕ} (h : m ≤ n) :
    finitePolynomialVariableIdeal k m ≤ finitePolynomialVariableIdeal k n := by
  apply Ideal.span_mono
  rintro x ⟨i, rfl⟩
  refine ⟨⟨i.1, lt_of_lt_of_le i.2 h⟩, ?_⟩
  rfl

/-- The canonical quotient transition map between finite polynomial stages. -/
def finitePolynomialStageMap
    (k : Type u) [CommRing k] {m n : ℕ} (h : m ≤ n) :
    finitePolynomialStage k m ⟶ finitePolynomialStage k n :=
  ModuleCat.ofHom
    (Ideal.Quotient.factorₐ (countablePolynomialRing k)
      (finitePolynomialVariableIdeal_mono k h)).toLinearMap

/-- The sequential system of finite polynomial stages and quotient maps. -/
def finitePolynomialStageSystem
    (k : Type u) [CommRing k] : ℕ ⥤ ModuleCat.{u} (countablePolynomialRing k) where
  obj n := finitePolynomialStage k n
  map f := finitePolynomialStageMap k (leOfHom f)
  map_id := by
    intro X
    simp [finitePolynomialStageMap]
  map_comp := by
    intros
    apply ModuleCat.hom_ext
    ext
    simp [finitePolynomialStageMap, Ideal.Quotient.factorₐ]

/- The quotient by all variables is finitely generated but not finitely
presented, hence it is not Mittag-Leffler. -/
theorem countablePolynomialQuotient_finite_not_finitePresentation
    (k : Type u) [CommRing k] [Nontrivial k] :
    Module.Finite (countablePolynomialRing k)
        (countablePolynomialQuotientModule k : Type u) ∧
      ¬ Module.FinitePresentation (countablePolynomialRing k)
        (countablePolynomialQuotientModule k : Type u) := by
  sorry

theorem countablePolynomialQuotient_not_mittagLeffler
    (k : Type u) [CommRing k] [Nontrivial k] :
    ¬ IsMittagLefflerModule (countablePolynomialQuotientModule k) := by
  sorry

/-- The quotient by all variables is the colimit of the finite-stage system. -/
theorem countablePolynomialQuotient_is_finiteStage_colimit
    (k : Type u) [CommRing k] :
    ∃ P : ColimitPresentation ℕ (countablePolynomialQuotientModule k),
      P.diag = finitePolynomialStageSystem k ∧
        ∀ n, Module.FinitePresentation (countablePolynomialRing k)
          (P.diag.obj n : Type u) := by
  sorry

/-- Writing a module as a sequential colimit of finitely presented modules does
not imply that it is Mittag-Leffler. -/
theorem exists_finiteStage_colimit_not_mittagLeffler
    (k : Type u) [CommRing k] [Nontrivial k] :
    ∃ (M : ModuleCat.{u} (countablePolynomialRing k))
      (P : ColimitPresentation ℕ M),
      (∀ n, Module.FinitePresentation (countablePolynomialRing k)
        (P.diag.obj n : Type u)) ∧
      ¬ IsMittagLefflerModule M := by
  sorry

end

end Formalization.Books.Algebra.Unit92
