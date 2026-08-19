import Formalization.Books.Algebra.Unit82.UniversallyInjective
import Formalization.Books.Algebra.Unit87.InverseSystems
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Homology.CommSq
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Commutative Algebra, Chapter 88: Mittag-Leffler modules

The source's directed systems are represented by functors from a directed
preorder to `ModuleCat`.  For a fixed target module, the inverse system of
duals is written explicitly using precomposition with the transition maps;
the Mittag-Leffler predicate itself is Mathlib's `Functor.IsMittagLeffler`.
-/

namespace Formalization.Books.Algebra.Unit88

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit82
open Formalization.Books.Categories.Unit21
open scoped TensorProduct

universe u v w z

noncomputable section

/-! ## Directed systems and their dual inverse systems -/

/-- The inverse system of `R`-linear duals of a directed module diagram. -/
def homInverseSystem
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    (D : System I (ModuleCat.{w} R)) (N : ModuleCat.{z} R) :
    InverseSystem I (Type (max w z)) where
  obj i := (D.obj i.unop : Type w) →ₗ[R] (N : Type z)
  map f := ↾(fun φ => φ.comp (D.map f.unop).hom)
  map_id i := by
    ext φ x
    simp
  map_comp f g := by
    ext φ x
    simp [LinearMap.comp_apply]

/-- A directed module system is Mittag-Leffler when its stages are finitely
presented and every inverse system of duals is Mittag-Leffler. -/
def IsMittagLefflerDirectedSystem
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    [Nonempty I] [IsDirectedOrder I]
    (D : System I (ModuleCat.{w} R)) : Prop :=
  (∀ i, Module.FinitePresentation R (D.obj i)) ∧
    ∀ N : ModuleCat.{z} R, (homInverseSystem D N).IsMittagLeffler

/-- The transition map of a module diagram, in the source's linear-map form. -/
def directedMap
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    (D : System I (ModuleCat.{w} R)) {i j : I} (h : i ≤ j) :
    (D.obj i : Type w) →ₗ[R] (D.obj j : Type w) :=
  (D.map (homOfLE h)).hom

/-- The canonical map from a stage of a colimit presentation to its target. -/
def colimitComponentMap
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    {M : ModuleCat.{w} R} (P : ColimitPresentation I M) (i : I) :
    (P.diag.obj i : Type w) →ₗ[R] (M : Type w) :=
  (P.ι.app i).hom

/-! ## Domination -/

/-- A map `g` dominates a map `f` when every tensor-kernel of `f` is contained
in the corresponding tensor-kernel of `g`. -/
def dominates
    {R : Type u} [CommRing R] {M N N' : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (g : M →ₗ[R] N') (f : M →ₗ[R] N) : Prop :=
  ∀ (Q : Type (max u w)) [AddCommGroup Q] [Module R Q],
    LinearMap.ker (f.rTensor Q) ≤ LinearMap.ker (g.rTensor Q)

/-- Two maps dominate each other. -/
def mutuallyDominates
    {R : Type u} [CommRing R] {M N N' : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (g : M →ₗ[R] N') (f : M →ₗ[R] N) : Prop :=
  dominates g f ∧ dominates f g

/-- A filtered presentation of a module by finitely presented modules, with
the colimit also witnessed after forgetting to types. -/
structure FinitelyPresentedFilteredColimit
    {R : Type u} [CommRing R] (N : ModuleCat.{max u w} R) where
  index : Type v
  [indexCategory : Category.{v} index]
  [indexFiltered : IsFiltered index]
  diag : index ⥤ ModuleCat.{max u w} R
  ι : diag ⟶ (Functor.const index).obj N
  underlyingIsColimit :
    IsColimit ((forget (ModuleCat.{max u w} R)).mapCocone
      { pt := N, ι := ι })
  finitelyPresented : ∀ i, Module.FinitePresentation R (diag.obj i)

instance finitelyPresentedFilteredColimitIndexCategory
    {R : Type u} [CommRing R] {N : ModuleCat.{max u w} R}
    (C : FinitelyPresentedFilteredColimit N) : Category.{v} C.index :=
  C.indexCategory

instance finitelyPresentedFilteredColimitIndexFiltered
    {R : Type u} [CommRing R] {N : ModuleCat.{max u w} R}
    (C : FinitelyPresentedFilteredColimit N) : IsFiltered C.index :=
  C.indexFiltered

/-- Every module is a filtered colimit of finitely presented modules in a
universe containing both the ring and the module. -/
theorem exists_finitelyPresentedFilteredColimit
    {R : Type u} [CommRing R] (N : ModuleCat.{max u w} R) :
    Nonempty (FinitelyPresentedFilteredColimit.{u, max u w, w} N) := by
  classical
  let M := (N : Type (max u w))
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
  let stage (a : Index) : ModuleCat.{max u w} R :=
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
  let D : Index ⥤ ModuleCat.{max u w} R := {
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
          rw [Submodule.span_le]
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
  have hc : IsColimit ((forget (ModuleCat.{max u w} R)).mapCocone c) := by
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
  exact ⟨{
    index := Index
    indexCategory := inferInstance
    indexFiltered := index_filtered
    diag := D
    ι := c.ι
    underlyingIsColimit := hc
    finitelyPresented := by
      intro a
      change Module.FinitePresentation R
        ((a.1 →₀ R) ⧸ Submodule.span R (a.2.1 : Set (a.1 →₀ R)))
      apply Module.finitePresentation_of_surjective (Submodule.mkQ _)
      · exact Submodule.mkQ_surjective _
      · rw [Submodule.ker_mkQ]
        exact Submodule.fg_span a.2.1.finite_toSet }⟩
/-- Every tensor with the colimit module is represented at one stage of a
finitely presented filtered-colimit presentation. -/
lemma finitelyPresentedFilteredColimit_tensor_rep
    {R : Type u} [CommRing R] {P : Type z} [AddCommGroup P] [Module R P]
    {Q : ModuleCat.{max u w} R} (C : FinitelyPresentedFilteredColimit Q) :
    ∀ x : TensorProduct R P (Q : Type (max u w)),
        ∃ (i : C.index) (y : TensorProduct R P
          (C.diag.obj i : Type (max u w))),
        (C.ι.app i).hom.lTensor P y = x := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero =>
      let i : C.index := IsFiltered.nonempty.some
      exact ⟨i, 0, by simp⟩
  | tmul p q =>
      obtain ⟨i, qi, hqi⟩ :=
        Types.jointly_surjective_of_isColimit C.underlyingIsColimit q
      refine ⟨i, p ⊗ₜ[R] qi, ?_⟩
      have hqi' : (C.ι.app i).hom qi = q := by
        change (ConcreteCategory.hom
          (((forget (ModuleCat.{max u w} R)).mapCocone
            { pt := Q, ι := C.ι }).ι.app i)) qi = q
        exact hqi
      simp [hqi']
  | add x y hx hy =>
      obtain ⟨i, xi, hxi⟩ := hx
      obtain ⟨j, yj, hyj⟩ := hy
      obtain ⟨k, a, b, _⟩ := IsFilteredOrEmpty.cocone_objs i j
      let yk := (C.diag.map a).hom.lTensor P xi +
        (C.diag.map b).hom.lTensor P yj
      refine ⟨k, yk, ?_⟩
      dsimp [yk]
      rw [map_add, ← hxi, ← hyj]
      have ha0 : (C.ι.app k).hom.comp
          (C.diag.map a).hom = (C.ι.app i).hom := by
        apply LinearMap.ext
        intro v
        have hnat := congrArg ModuleCat.Hom.hom (C.ι.naturality a)
        dsimp at hnat
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
          congrArg (fun h : (C.diag.obj i : Type (max u w)) →ₗ[R]
            (Q : Type (max u w)) => h v) hnat
      have hb0 : (C.ι.app k).hom.comp
          (C.diag.map b).hom = (C.ι.app j).hom := by
        apply LinearMap.ext
        intro v
        have hnat := congrArg ModuleCat.Hom.hom (C.ι.naturality b)
        dsimp at hnat
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
          congrArg (fun h : (C.diag.obj j : Type (max u w)) →ₗ[R]
            (Q : Type (max u w)) => h v) hnat
      have ha := congrArg (fun t => t.lTensor P) ha0
      have hb := congrArg (fun t => t.lTensor P) hb0
      rw [LinearMap.lTensor_comp] at ha hb
      rw [← ha, ← hb]
      simp only [LinearMap.comp_apply]

/-- An element represented at a stage and vanishing in the filtered colimit
already vanishes after a transition to some later stage. -/
lemma finitelyPresentedFilteredColimit_eventually_zero
    {R : Type u} [CommRing R] {Q : ModuleCat.{max u w} R}
    (C : FinitelyPresentedFilteredColimit Q) {i : C.index} (x : C.diag.obj i) :
    (C.ι.app i).hom x = 0 →
      ∃ (j : C.index) (h : i ⟶ j),
        (C.diag.map h).hom x = 0 := by
  intro hx
  obtain ⟨j, h, hh⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' C.underlyingIsColimit x 0).1
      (hx.trans (by simp))
  exact ⟨j, h, by simpa using hh⟩

/-- A map from a finite module which is zero in the colimit becomes zero at a
later stage. -/
lemma finitelyPresentedFilteredColimit_eventually_zero_map
    {R : Type u} [CommRing R]
    {P : Type z} [AddCommGroup P] [Module R P]
    {Q : ModuleCat.{max u w} R}
    (C : FinitelyPresentedFilteredColimit Q) {i : C.index}
    (hP : Module.Finite R P)
    (f : P →ₗ[R] (C.diag.obj i : Type (max u w)))
    (hf : (C.ι.app i).hom.comp f = 0) :
    ∃ (j : C.index) (h : i ⟶ j),
      (C.diag.map h).hom.comp f = 0 := by
  classical
  let _ : Module.Finite R P := hP
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R P
  choose l z hz using fun b : Fin n =>
    finitelyPresentedFilteredColimit_eventually_zero C
      (f (p (Pi.single b 1))) (by
        have h := congrArg (fun t => t (p (Pi.single b 1))) hf
        simpa [LinearMap.comp_apply] using h)
  let O : Finset C.index := insert i (Finset.univ.image l)
  let H : Finset (Σ' (X Y : C.index) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
    Finset.univ.image (fun b : Fin n =>
      (⟨i, l b, Finset.mem_insert_self i _,
        Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨b, Finset.mem_univ _, rfl⟩), z b⟩ :
        Σ' (X Y : C.index) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y))
  obtain ⟨j, t, ht⟩ := IsFiltered.sup_exists O H
  refine ⟨j, t (Finset.mem_insert_self i _), ?_⟩
  have hzero (b : Fin n) :
      (C.diag.map (t (Finset.mem_insert_self i _))).hom
        (f (p (Pi.single b 1))) = 0 := by
    have hcomm := ht
      (Finset.mem_insert_self i _)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨b, Finset.mem_univ _, rfl⟩))
      (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
    have hmap := congrArg ModuleCat.Hom.hom
      (congrArg C.diag.map hcomm)
    have hz' := congrArg (fun s => s (f (p (Pi.single b 1)))) hmap
    rw [← hz']
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
      hz b, map_zero]
  apply LinearMap.ext
  intro x
  obtain ⟨y, hy⟩ := hp x
  rw [← hy]
  have hy' : y = ∑ b, y b • Pi.single b 1 := by
    ext b
    simp [Pi.single_apply]
  rw [hy']
  simp only [map_sum, map_smul, LinearMap.comp_apply]
  have hrhs : (∑ b, y b •
      (0 : P →ₗ[R] (C.diag.obj j : Type (max u w)))
        (p (Pi.single b 1))) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    rw [LinearMap.zero_apply, smul_zero]
  have hleft : (∑ b, y b •
      (C.diag.map (t (Finset.mem_insert_self i _))).hom
        (f (p (Pi.single b 1)))) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    rw [hzero b, smul_zero]
  exact hleft.trans hrhs.symm

/-! The following three lemmas are the public interface used when a finite
presentation is tested against this filtered colimit. -/

/-- Every element of the presented module comes from one stage. -/
lemma finitelyPresentedFilteredColimit_element_rep
    {R : Type u} [CommRing R] {Q : ModuleCat.{max u w} R}
    (C : FinitelyPresentedFilteredColimit Q) (x : (Q : Type (max u w))) :
    ∃ (i : C.index) (y : (C.diag.obj i : Type (max u w))),
      (C.ι.app i).hom y = x := by
  exact Types.jointly_surjective_of_isColimit C.underlyingIsColimit x

/-- A map from a finitely presented module into the colimit factors through
one stage.  The source and the stages are allowed to live in different
universes. -/
lemma finitelyPresentedFilteredColimit_map_factor
    {R : Type u} [CommRing R]
    {P : Type z} [AddCommGroup P] [Module R P]
    {Q : ModuleCat.{max u w} R}
    (C : FinitelyPresentedFilteredColimit Q)
    (hP : Module.FinitePresentation R P)
    (f : P →ₗ[R] (Q : Type (max u w))) :
    ∃ (i : C.index) (g : P →ₗ[R] (C.diag.obj i : Type (max u w))),
      (C.ι.app i).hom.comp g = f := by
  classical
  let _ : Module.FinitePresentation R P := hP
  obtain ⟨n, m, p, q, hp, hpq⟩ :=
    Module.FinitePresentation.exists_fin' R P
  choose i yi hyi using fun a : Fin n =>
    finitelyPresentedFilteredColimit_element_rep C (f (p (Pi.single a 1)))
  let S : Finset C.index := Finset.univ.image i
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists S
  let y : Fin n → (C.diag.obj k : Type (max u w)) := fun a =>
    (C.diag.map (hk (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)).some).hom
      (yi a)
  let g₀ : (Fin n → R) →ₗ[R] (C.diag.obj k : Type (max u w)) :=
    Fintype.linearCombination R y
  have hy (a : Fin n) : (C.ι.app k).hom (y a) = f (p (Pi.single a 1)) := by
    have hn := congrArg ModuleCat.Hom.hom
      (C.ι.naturality (hk (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)).some)
    have hn' := congrArg (fun h => h (yi a)) hn
    simpa [y, ModuleCat.hom_comp, LinearMap.comp_apply] using hn'.trans (hyi a)
  have hgp : (C.ι.app k).hom.comp g₀ = f.comp p := by
    apply LinearMap.ext
    intro x
    have hx : x = ∑ a, x a • Pi.single a 1 := by
      ext a
      simp [Pi.single_apply]
    rw [hx]
    simp only [map_sum, map_smul, LinearMap.comp_apply]
    apply Finset.sum_congr rfl
    intro a ha
    simpa [g₀] using congrArg (fun t => x a • t) (hy a)
  have hgqzero : (C.ι.app k).hom.comp (g₀.comp q) = 0 := by
    calc
      (C.ι.app k).hom.comp (g₀.comp q) = (f.comp p).comp q := by
        rw [← LinearMap.comp_assoc, hgp]
      _ = f.comp (p.comp q) := by rw [LinearMap.comp_assoc]
      _ = 0 := by
        have hpq0 : p.comp q = 0 := by
          apply LinearMap.ext
          intro x
          have h := congrArg (fun h => h x) hpq.comp_eq_zero
          simpa [LinearMap.comp_apply] using h
        have hzero := congrArg
          (fun h : (Fin m → R) →ₗ[R] P => f.comp h) hpq0
        simpa using hzero
  choose l z hz using fun b : Fin m =>
    finitelyPresentedFilteredColimit_eventually_zero C
      (g₀ (q (Pi.single b 1))) (by
        have h := congrArg (fun t => t (Pi.single b 1)) hgqzero
        simpa [LinearMap.comp_apply] using h)
  let O : Finset C.index := insert k (Finset.univ.image l)
  let H : Finset (Σ' (X Y : C.index) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
    Finset.univ.image (fun b : Fin m =>
      (⟨k, l b, Finset.mem_insert_self k _,
        Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨b, Finset.mem_univ _, rfl⟩), z b⟩ :
        Σ' (X Y : C.index) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y))
  obtain ⟨r, t, ht⟩ := IsFiltered.sup_exists O H
  let g₁ : (Fin n → R) →ₗ[R] (C.diag.obj r : Type (max u w)) :=
    (C.diag.map (t (Finset.mem_insert_self k _))).hom.comp g₀
  have hg₁q (b : Fin m) : g₁ (q (Pi.single b 1)) = 0 := by
    have hcomm := ht
      (Finset.mem_insert_self k _)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨b, Finset.mem_univ _, rfl⟩))
      (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
    have hmap := congrArg ModuleCat.Hom.hom
      (congrArg C.diag.map hcomm)
    have hz' := congrArg (fun s => s (g₀ (q (Pi.single b 1)))) hmap
    dsimp [g₁]
    rw [← hz']
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
      hz b, map_zero]
  have hg₁qzero : g₁.comp q = 0 := by
    apply LinearMap.ext
    intro x
    have hx : x = ∑ b, x b • Pi.single b 1 := by
      ext b
      simp [Pi.single_apply]
    rw [hx]
    simp only [map_sum, map_smul, LinearMap.comp_apply]
    simp_rw [hg₁q]
    simp
  have hker : LinearMap.ker p ≤ LinearMap.ker g₁ := by
    rw [LinearMap.exact_iff.mp hpq]
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    apply LinearMap.mem_ker.mpr
    simpa using congrArg (fun h => h y) hg₁qzero
  let e := p.quotKerEquivOfSurjective hp
  let g : P →ₗ[R] (C.diag.obj r : Type (max u w)) :=
    (LinearMap.ker p).liftQ g₁ hker |>.comp e.symm.toLinearMap
  refine ⟨r, g, ?_⟩
  have hgp' : g.comp p = g₁ := by
    apply LinearMap.ext
    intro x
    simp [g, e]
  have hιg₁ : (C.ι.app r).hom.comp g₁ = f.comp p := by
    apply LinearMap.ext
    intro x
    have hmap := congrArg ModuleCat.Hom.hom
      (C.ι.naturality (t (Finset.mem_insert_self k _)))
    have hmap' := congrArg (fun h => h (g₀ x)) hmap
    have hgp' := congrArg (fun h => h x) hgp
    calc
      (C.ι.app r).hom (g₁ x) = (C.ι.app k).hom (g₀ x) := by
        exact hmap'
      _ = (f.comp p) x := by simpa using hgp'
  apply LinearMap.ext
  intro x
  obtain ⟨y, hy⟩ := hp x
  rw [← hy]
  have hgp'y := congrArg (fun h => h y) hgp'
  have hιg₁y := congrArg (fun h => h y) hιg₁
  simpa [LinearMap.comp_apply] using
    (congrArg (C.ι.app r).hom hgp'y).trans hιg₁y

theorem dominates_iff_finitelyPresented
    {R : Type u} [CommRing R] {M N N' : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (g : M →ₗ[R] N') (f : M →ₗ[R] N) :
    dominates g f ↔
      ∀ (Q : Type (max u w)) [AddCommGroup Q] [Module R Q],
        Module.FinitePresentation R Q →
          LinearMap.ker (f.rTensor Q) ≤ LinearMap.ker (g.rTensor Q) := by
  sorry

/-- Domination is equivalent to universal injectivity of the map from the
second leg into the pushout. -/
theorem dominates_iff_pushout_inr_universallyInjective
    {R : Type u} [CommRing R] {M N N' : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] N) (g : M →ₗ[R] N') :
    dominates g f ↔
      universallyInjective
        ((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom) := by
  constructor
  · intro hd Q _ _ x y hxy
    apply sub_eq_zero.mp
    let p := pushout (ModuleCat.ofHom f) (ModuleCat.ofHom g)
    let d : M →ₗ[R]
        (ModuleCat.of R N ⊞ ModuleCat.of R N').carrier :=
      (biprod.lift (ModuleCat.ofHom f) (-(ModuleCat.ofHom g))).hom
    let π : (ModuleCat.of R N ⊞ ModuleCat.of R N').carrier →ₗ[R] (p : Type w) :=
      (biprod.desc (pushout.inl (ModuleCat.ofHom f) (ModuleCat.ofHom g))
        (pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g))).hom
    let S := ShortComplex.moduleCatMk d π (by
      change (biprod.lift (ModuleCat.ofHom f) (-(ModuleCat.ofHom g)) ≫
        biprod.desc (pushout.inl (ModuleCat.ofHom f) (ModuleCat.ofHom g))
          (pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g))).hom = 0
      rw [biprod.lift_desc]
      rw [CategoryTheory.Preadditive.neg_comp]
      rw [← pushout.condition (f := ModuleCat.ofHom f) (g := ModuleCat.ofHom g)]
      simp)
    have hp := IsPushout.of_isColimit
      (pushoutIsPushout (ModuleCat.ofHom f) (ModuleCat.ofHom g))
    have hS : S.Exact := by
      apply ShortComplex.exact_of_g_is_cokernel
      exact hp.isColimitCokernelCofork
    have hπ : Function.Surjective π := by
      apply (ModuleCat.epi_iff_surjective _).mp
      exact epi_of_isColimit_cofork hp.isColimitCokernelCofork
    have hExact : Function.Exact d π :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS
    have hπQ := rTensor_exact Q hExact hπ
    have hfd :
        (biprod.fst : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
          ModuleCat.of R N).hom ∘ₗ d = f := by
      dsimp [d]
      ext z
      change
        ((biprod.lift (ModuleCat.ofHom f) (-ModuleCat.ofHom g) ≫
          (biprod.fst : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
            ModuleCat.of R N)).hom) z = f z
      rw [biprod.lift_fst]
      rfl
    have hfi :
        (biprod.fst : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
          ModuleCat.of R N).hom ∘ₗ
            (biprod.inr : ModuleCat.of R N' ⟶
              (ModuleCat.of R N ⊞ ModuleCat.of R N')).hom = 0 := by
      ext z
      change ((biprod.inr : ModuleCat.of R N' ⟶
          (ModuleCat.of R N ⊞ ModuleCat.of R N')) ≫
        (biprod.fst : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
          ModuleCat.of R N)).hom z = 0
      rw [biprod.inr_fst]
      rfl
    have hsd :
        (biprod.snd : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
          ModuleCat.of R N').hom ∘ₗ d = -g := by
      dsimp [d]
      ext z
      change (biprod.lift (ModuleCat.ofHom f) (-ModuleCat.ofHom g) ≫
        biprod.snd).hom z = (-g) z
      rw [biprod.lift_snd]
      rfl
    have hsi :
        (biprod.snd : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
          ModuleCat.of R N').hom ∘ₗ
            (biprod.inr : ModuleCat.of R N' ⟶
              (ModuleCat.of R N ⊞ ModuleCat.of R N')).hom =
          LinearMap.id := by
      ext z
      change ((biprod.inr : ModuleCat.of R N' ⟶
          (ModuleCat.of R N ⊞ ModuleCat.of R N')) ≫
        (biprod.snd : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
          ModuleCat.of R N')).hom z = LinearMap.id z
      rw [biprod.inr_snd]
      rfl
    have hfdQ :
        (biprod.fst : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
          ModuleCat.of R N).hom.rTensor Q ∘ₗ d.rTensor Q = f.rTensor Q := by
      rw [← LinearMap.rTensor_comp Q, hfd]
    have hfiQ :
        (biprod.fst : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
          ModuleCat.of R N).hom.rTensor Q ∘ₗ
            (biprod.inr : ModuleCat.of R N' ⟶
              (ModuleCat.of R N ⊞ ModuleCat.of R N')).hom.rTensor Q = 0 := by
      rw [← LinearMap.rTensor_comp Q, hfi]
      simp
    have hsdQ :
        (biprod.snd : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
          ModuleCat.of R N').hom.rTensor Q ∘ₗ d.rTensor Q = -(g.rTensor Q) := by
      rw [← LinearMap.rTensor_comp Q, hsd]
      simp
    have hsiQ :
        (biprod.snd : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
          ModuleCat.of R N').hom.rTensor Q ∘ₗ
            (biprod.inr : ModuleCat.of R N' ⟶
              (ModuleCat.of R N ⊞ ModuleCat.of R N')).hom.rTensor Q =
          LinearMap.id := by
      rw [← LinearMap.rTensor_comp Q, hsi]
      simp
    have hfd_apply (z : M ⊗[R] Q) :
        (biprod.fst : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
          ModuleCat.of R N).hom.rTensor Q ((d.rTensor Q) z) =
          (f.rTensor Q) z := by
      rw [← LinearMap.comp_apply, hfdQ]
    have hfi_apply (z : (ModuleCat.of R N' : Type w) ⊗[R] Q) :
        (biprod.fst : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
          ModuleCat.of R N).hom.rTensor Q
            ((biprod.inr : ModuleCat.of R N' ⟶
              (ModuleCat.of R N ⊞ ModuleCat.of R N')).hom.rTensor Q z) = 0 := by
      rw [← LinearMap.comp_apply, hfiQ]
      rfl
    have hsd_apply (z : M ⊗[R] Q) :
        (biprod.snd : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
          ModuleCat.of R N').hom.rTensor Q ((d.rTensor Q) z) =
            -(g.rTensor Q) z := by
      rw [← LinearMap.comp_apply, hsdQ]
      simp
    have hsi_apply (z : (ModuleCat.of R N' : Type w) ⊗[R] Q) :
        (biprod.snd : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
          ModuleCat.of R N').hom.rTensor Q
            ((biprod.inr : ModuleCat.of R N' ⟶
              (ModuleCat.of R N ⊞ ModuleCat.of R N')).hom.rTensor Q z) = z := by
      rw [← LinearMap.comp_apply, hsiQ]
      rfl
    have hx0 : ((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom.rTensor Q)
        (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hxπ : (π.rTensor Q)
        ((biprod.inr : ModuleCat.of R N' ⟶
          (ModuleCat.of R N ⊞ ModuleCat.of R N')).hom.rTensor Q (x - y)) = 0 := by
      have heq :
          (π.rTensor Q).comp ((biprod.inr : ModuleCat.of R N' ⟶
            (ModuleCat.of R N ⊞ ModuleCat.of R N')).hom.rTensor Q) =
            ((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom.rTensor Q) := by
        rw [← LinearMap.rTensor_comp]
        congr 1
        change (biprod.inr ≫
          biprod.desc (pushout.inl (ModuleCat.ofHom f) (ModuleCat.ofHom g))
            (pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g))).hom =
          (pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom
        simp
      rw [← LinearMap.comp_apply, heq, hx0]
    obtain ⟨a, ha⟩ := (hπQ _).mp hxπ
    have hfa : (f.rTensor Q) a = 0 := by
      have hfst := congrArg (fun z =>
        ((biprod.fst : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
          ModuleCat.of R N).hom.rTensor Q) z) ha
      rw [hfd_apply, hfi_apply] at hfst
      simpa using hfst
    have hga : (g.rTensor Q) a = 0 := hd Q (LinearMap.mem_ker.mpr hfa)
    have hsnd := congrArg (fun z =>
      ((biprod.snd : (ModuleCat.of R N ⊞ ModuleCat.of R N') ⟶
        ModuleCat.of R N').hom.rTensor Q) z) ha
    rw [hsd_apply, hsi_apply] at hsnd
    have hxy0 : x - y = 0 := by
      rw [hga, neg_zero] at hsnd
      exact hsnd.symm
    exact hxy0
  · intro hu Q _ _ x hx
    change (g.rTensor Q) x = 0
    change (f.rTensor Q) x = 0 at hx
    have hpush := pushout.condition
      (f := ModuleCat.ofHom f) (g := ModuleCat.ofHom g)
    have hpush' := congrArg ModuleCat.Hom.hom hpush
    have hpushQ :
        ((pushout.inl (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom.rTensor Q).comp
            (f.rTensor Q) =
          ((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom.rTensor Q).comp
            (g.rTensor Q) := by
      rw [← LinearMap.rTensor_comp Q, ← LinearMap.rTensor_comp Q]
      simpa using congrArg (fun t => t.rTensor Q) hpush'
    have hz :
        ((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom.rTensor Q)
          ((g.rTensor Q) x) = 0 := by
      have heq := congrArg (fun t => t x) hpushQ
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hx] at heq
      simpa using heq.symm
    apply (hu Q)
    simpa using hz
/-
  constructor
  · intro hd Q _ _
    intro x y hxy
    apply sub_eq_zero.mp
    let p := pushout (ModuleCat.ofHom f) (ModuleCat.ofHom g)
    let d : M →ₗ[R] (N × N') := LinearMap.prod f (-g)
    let π : (N × N') →ₗ[R] (p : Type w) :=
      (biprod.desc (pushout.inl (ModuleCat.ofHom f) (ModuleCat.ofHom g))
        (pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g))).hom
    let S := ShortComplex.moduleCatMk d π (by
      ext z <;> simp [d, π, LinearMap.prod_apply])
    have hS : S.Exact := by
      apply S.exact_of_g_is_cokernel
      exact (pushoutIsPushout (ModuleCat.ofHom f) (ModuleCat.ofHom g)).
        isColimitCokernelCofork
    have hπ : Function.Surjective π := by
      apply ModuleCat.epi_iff_surjective.mp
      exact epi_of_isColimit_cofork
        (pushoutIsPushout (ModuleCat.ofHom f) (ModuleCat.ofHom g)).
          isColimitCokernelCofork
    have hExact : Function.Exact d π :=
      (S.moduleCat_exact_iff_function_exact).mp hS
    have hπQ := TensorProduct.rTensor_exact Q hExact hπ
    have hx0 : ((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom.rTensor Q)
        (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hxπ : (π.rTensor Q)
        ((LinearMap.inr R N N').rTensor Q (x - y)) = 0 := by
      have heq :
          (π.rTensor Q).comp ((LinearMap.inr R N N').rTensor Q) =
            ((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom.rTensor Q) := by
        rw [← LinearMap.rTensor_comp]
        rfl
      rw [← LinearMap.comp_apply, heq, hx0]
    obtain ⟨a, ha⟩ := hπQ hxπ
    have hfa : (f.rTensor Q) a = 0 := by
      have hfst := congrArg (fun z => (LinearMap.fst R N N').rTensor Q z) ha
      simpa [d, LinearMap.prod_apply] using hfst
    have hga : (g.rTensor Q) a = 0 := hd Q (LinearMap.mem_ker.mpr hfa)
    have hsnd := congrArg (fun z => (LinearMap.snd R N N').rTensor Q z) ha
    have hxy0 : x - y = 0 := by
      simpa [d, LinearMap.prod_apply] using congrArg Neg.neg hsnd
    exact hxy0
  · intro hu Q _ _ x hx
    have hpush := pushout.condition (ModuleCat.ofHom f) (ModuleCat.ofHom g)
    have hpush' := congrArg ModuleCat.Hom.hom hpush
    have hpushQ := congrArg (fun t => t.rTensor Q) hpush'
    have hz :
        ((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom.rTensor Q)
          ((g.rTensor Q) x) = 0 := by
      have heq := congrArg (fun t => t x) hpushQ
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hx] at heq
      simpa using heq
    exact (hu Q).eq_of_sub_eq_zero (by simpa using hz)
-/

/-- If the cokernel of `f` is finitely presented, domination is the usual
factorization relation. -/
private lemma injective_of_universallyInjective
    {R : Type u} [CommRing R] {M N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {f : M →ₗ[R] N}
  (hu : universallyInjective f) : Function.Injective f := by
  intro x y hxy
  have ht : (f.rTensor (ULift.{w} R))
        (TensorProduct.tmul R x (ULift.up 1)) =
      (f.rTensor (ULift.{w} R))
        (TensorProduct.tmul R y (ULift.up 1)) := by
    simp [hxy]
  have ht' := (hu (ULift.{w} R)) ht
  have ht'' := congrArg
    (TensorProduct.congr (LinearEquiv.refl R M)
      (ULift.moduleEquiv : ULift.{w} R ≃ₗ[R] R)) ht'
  simpa using congrArg (TensorProduct.rid R M) ht''
/-
  intro x y hxy
  apply (TensorProduct.rid R N).injective
  apply hu R
  simp [hxy]
-/

private lemma pushout_inr_cokernel
    {R : Type u} [CommRing R] {M N N' : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] N) (g : M →ₗ[R] N') :
    let ff := ModuleCat.ofHom f
    let gg := ModuleCat.ofHom g
    let p := pushout ff gg
    let q : N →ₗ[R] (N ⧸ LinearMap.range f) := Submodule.mkQ _
    let π : (p : Type w) →ₗ[R] (N ⧸ LinearMap.range f) :=
      (pushout.desc (ModuleCat.ofHom q) 0 (by
        ext x
        change Submodule.Quotient.mk (f x) = 0
        apply (Submodule.Quotient.mk_eq_zero _).2
        exact LinearMap.mem_range_self f x)).hom
    Function.Exact (ModuleCat.Hom.hom (pushout.inr ff gg)) π ∧
      Function.Surjective π := by
  dsimp
  let ff := ModuleCat.ofHom f
  let gg := ModuleCat.ofHom g
  let p := pushout ff gg
  let q : N →ₗ[R] (N ⧸ LinearMap.range f) := Submodule.mkQ _
  let π : (p : Type w) →ₗ[R] (N ⧸ LinearMap.range f) :=
    (pushout.desc (ModuleCat.ofHom q) 0 (by
      ext x
      change Submodule.Quotient.mk (f x) = 0
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact LinearMap.mem_range_self f x)).hom
  have hπinl : pushout.inl ff gg ≫ ModuleCat.ofHom π = ModuleCat.ofHom q := by
    dsimp [π]
    rw [pushout.inl_desc]
  have hπinr : pushout.inr ff gg ≫ ModuleCat.ofHom π = 0 := by
    dsimp [π]
    rw [pushout.inr_desc]
  have hqcol := ModuleCat.cokernelIsColimit ff
  dsimp [ModuleCat.cokernelCocone] at hqcol
  have hπsurj : Function.Surjective π := by
    intro z
    obtain ⟨n, hn⟩ := Submodule.mkQ_surjective
      (LinearMap.range f) z
    refine ⟨(pushout.inl ff gg).hom n, ?_⟩
    change (pushout.inl ff gg ≫
      pushout.desc (ModuleCat.ofHom q) 0 _).hom n = z
    rw [pushout.inl_desc]
    simpa [q] using hn
  let _ : Epi (ModuleCat.ofHom π) :=
    (ModuleCat.epi_iff_surjective _).2 hπsurj
  let cπ : CokernelCofork (pushout.inr ff gg) :=
    CokernelCofork.ofπ (ModuleCat.ofHom π) (by
      change pushout.inr ff gg ≫ pushout.desc (ModuleCat.ofHom q) 0 _ = 0
      rw [pushout.inr_desc])
  have hcπ : IsColimit cπ := by
    apply CokernelCofork.IsColimit.ofπ'
    intro A k hk
    let k' : ModuleCat.of R N ⟶ A := pushout.inl ff gg ≫ k
    have hk' : ff ≫ k' = 0 := by
      dsimp [k']
      rw [pushout.condition_assoc]
      simp [hk]
    refine ⟨hqcol.desc (CokernelCofork.ofπ k' hk'), ?_⟩
    apply pushout.hom_ext
    · change (pushout.inl ff gg ≫ ModuleCat.ofHom π ≫
        hqcol.desc (CokernelCofork.ofπ k' hk')) =
          pushout.inl ff gg ≫ k
      calc
        _ = (pushout.inl ff gg ≫ ModuleCat.ofHom π) ≫
            hqcol.desc (CokernelCofork.ofπ k' hk') := by
          rw [Category.assoc]
        _ = ModuleCat.ofHom q ≫
            hqcol.desc (CokernelCofork.ofπ k' hk') := by rw [hπinl]
        _ = k' := Cofork.IsColimit.π_desc hqcol
        _ = pushout.inl ff gg ≫ k := rfl
    · dsimp [π]
      change (pushout.inr ff gg ≫ ModuleCat.ofHom π) ≫
        hqcol.desc (CokernelCofork.ofπ k' hk') =
          pushout.inr ff gg ≫ k
      rw [hπinr]
      rw [hk]
      simp only [zero_comp]
  let S' := ShortComplex.moduleCatMk
    (ModuleCat.Hom.hom (pushout.inr ff gg)) π (by
      ext x
      change (pushout.inr ff gg ≫
        pushout.desc (ModuleCat.ofHom q) 0 _).hom x = 0
      rw [pushout.inr_desc]
      simp
      )
  have hS' : S'.Exact := S'.exact_of_g_is_cokernel hcπ
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S').mp hS',
    (ModuleCat.epi_iff_surjective _).mp (epi_of_isColimit_cofork hcπ)⟩

private lemma universallyExact_factor_finiteFree_of_universes
    {R : Type u} {M₁ M₂ : Type w} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    {f₁ : M₁ →ₗ[R] M₂}
    (h : universallyInjective f₁)
    {n m : ℕ}
    (a : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R))
    (u : (Fin n →₀ R) →ₗ[R] M₁)
    (v : (Fin m →₀ R) →ₗ[R] M₂)
    (ha : v.comp a = f₁.comp u) :
    ∃ w : (Fin m →₀ R) →ₗ[R] M₁, w.comp a = u := by
  let A : (Fin m →₀ R) →ₗ[R] (Fin n →₀ R) :=
    Finsupp.linearCombination R (fun j =>
      ∑ i, (a (Finsupp.single i 1)) j • Finsupp.single i 1)
  let Q₀ : Type u := (Fin n →₀ R) ⧸ LinearMap.range A
  let Q : Type (max u w) := ULift.{w} Q₀
  let q₀ : (Fin n →₀ R) →ₗ[R] Q₀ := Submodule.mkQ _
  let eQ : Q₀ ≃ₗ[R] Q := ULift.moduleEquiv.symm
  let q : (Fin n →₀ R) →ₗ[R] Q := eQ.toLinearMap.comp q₀
  let tx : M₁ ⊗[R] Q :=
    ∑ i, u (Finsupp.single i 1) ⊗ₜ[R] q (Finsupp.single i 1)
  have htx : (f₁.rTensor Q) tx = 0 := by
    dsimp [tx]
    simp only [map_sum, LinearMap.rTensor_tmul]
    have ha' (i : Fin n) :
        f₁ (u (Finsupp.single i 1)) = v (a (Finsupp.single i 1)) := by
      simpa [LinearMap.comp_apply] using
        (LinearMap.congr_fun ha (Finsupp.single i 1)).symm
    simp_rw [ha']
    classical
    have ha_basis (i : Fin n) :
        a (Finsupp.single i 1) =
          ∑ j, (a (Finsupp.single i 1)) j • Finsupp.single j 1 := by
      ext j
      simp
    calc
      _ = ∑ i, v (∑ j, (a (Finsupp.single i 1)) j •
          Finsupp.single j 1) ⊗ₜ[R] q (Finsupp.single i 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrArg (fun z => v z ⊗ₜ[R] q (Finsupp.single i 1)) (ha_basis i)
      _ = ∑ i, ∑ j, (a (Finsupp.single i 1)) j •
          (v (Finsupp.single j 1) ⊗ₜ[R] q (Finsupp.single i 1)) := by
        simp_rw [map_sum, TensorProduct.sum_tmul, map_smul, TensorProduct.smul_tmul,
          TensorProduct.tmul_smul]
      _ = ∑ j, ∑ i, (a (Finsupp.single i 1)) j •
          (v (Finsupp.single j 1) ⊗ₜ[R] q (Finsupp.single i 1)) := by
        exact Finset.sum_comm
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        change ∑ i, (a (Finsupp.single i 1)) j •
            (v (Finsupp.single j 1) ⊗ₜ[R] q (Finsupp.single i 1)) = 0
        simp_rw [← TensorProduct.tmul_smul]
        rw [← TensorProduct.tmul_sum]
        simp_rw [← map_smul]
        rw [← map_sum]
        rw [show (∑ i, (a (Finsupp.single i 1)) j • Finsupp.single i 1) =
            A (Finsupp.single j 1) by
              simp [A, Finsupp.linearCombination_single]]
        have hq₀ : q₀ (A (Finsupp.single j 1)) = 0 := by
          apply (Submodule.Quotient.mk_eq_zero (LinearMap.range A)).2
          exact ⟨Finsupp.single j 1, rfl⟩
        have hq : q (A (Finsupp.single j 1)) = 0 := by
          simp [q, hq₀]
        simpa [q, Submodule.mkQ_apply] using
          congrArg (fun z => v (Finsupp.single j 1) ⊗ₜ[R] z) hq
  have hQ : Function.Injective (f₁.rTensor Q) := h Q
  have htx0 : tx = 0 := hQ (by simpa using htx)
  let t0 : M₁ ⊗[R] (Fin n →₀ R) :=
    ∑ i, u (Finsupp.single i 1) ⊗ₜ[R] Finsupp.single i 1
  have ht0 : (LinearMap.lTensor M₁ q) t0 = tx := by
    dsimp [t0, tx]
    simp only [map_sum, LinearMap.lTensor_tmul]
  have ht0zero : (LinearMap.lTensor M₁ q) t0 = 0 := ht0.trans htx0
  have hqsurj : Function.Surjective q := by
    intro y
    obtain ⟨y₀, hy₀⟩ := eQ.surjective y
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective _ y₀
    refine ⟨x, ?_⟩
    calc
      q x = eQ (q₀ x) := rfl
      _ = eQ y₀ := congrArg eQ hx
      _ = y := hy₀
  have hqker : LinearMap.ker q = LinearMap.ker q₀ := by
    apply le_antisymm
    · intro x hx
      apply LinearMap.mem_ker.mpr
      apply eQ.injective
      simpa [q] using LinearMap.mem_ker.mp hx
    · intro x hx
      apply LinearMap.mem_ker.mpr
      simp [q, LinearMap.mem_ker.mp hx]
  have hqexact : Function.Exact A q := by
    apply LinearMap.exact_iff.mpr
    rw [hqker]
    exact (LinearMap.exact_iff.mp A.exact_map_mkQ_range)
  have hex : Function.Exact (LinearMap.lTensor M₁ A) (LinearMap.lTensor M₁ q) :=
    _root_.lTensor_exact M₁ hqexact hqsurj
  have hrange : t0 ∈ LinearMap.range (LinearMap.lTensor M₁ A) := by
    rw [← hex.linearMap_ker_eq]
    exact ht0zero
  obtain ⟨t, ht⟩ := hrange
  have hcontract (z : M₁ ⊗[R] (Fin m →₀ R))
    (b : (Fin m →₀ R) →ₗ[R] R) :
      TensorProduct.rid R M₁ (LinearMap.lTensor M₁ b z) =
        ∑ j, b (Finsupp.single j 1) •
            TensorProduct.rid R M₁
            (LinearMap.lTensor M₁
              (Finsupp.lapply j : (Fin m →₀ R) →ₗ[R] R) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        simp only [TensorProduct.rid_tmul, LinearMap.lTensor_tmul]
        have hy : y = ∑ j, y j • Finsupp.single j 1 := by
          ext j
          simp
        rw [hy]
        have hb : b (∑ j, y j • Finsupp.single j 1) =
            ∑ j, y j • b (Finsupp.single j 1) := by
          simp only [map_sum, map_smul]
        have hl (j : Fin m) :
            (Finsupp.lapply j : (Fin m →₀ R) →ₗ[R] R)
              (∑ k, y k • Finsupp.single k 1) = y j := by
          change (∑ k, y k • Finsupp.single k 1) j = y j
          simp
        rw [hb]
        simp_rw [hl]
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro j hj
        simp [smul_smul, mul_comm]
    | add x y hx hy =>
        simp only [map_add, hx, hy,
          Finset.sum_add_distrib, smul_add]
  let w : (Fin m →₀ R) →ₗ[R] M₁ :=
    Finsupp.linearCombination R (fun j =>
      TensorProduct.rid R M₁
        (LinearMap.lTensor M₁
          (Finsupp.lapply j : (Fin m →₀ R) →ₗ[R] R) t))
  have hcoord (i : Fin n) : w (a (Finsupp.single i 1)) =
      u (Finsupp.single i 1) := by
    have hc := hcontract t
      ((Finsupp.lapply i : (Fin n →₀ R) →ₗ[R] R).comp A)
    have hleft : TensorProduct.rid R M₁
        (LinearMap.lTensor M₁
          ((Finsupp.lapply i : (Fin n →₀ R) →ₗ[R] R).comp A) t) =
        u (Finsupp.single i 1) := by
      rw [LinearMap.lTensor_comp_apply, ht]
      dsimp [t0]
      simp [Finsupp.single_apply]
    have hcoeff (j : Fin m) :
        ((Finsupp.lapply i : (Fin n →₀ R) →ₗ[R] R).comp A)
            (Finsupp.single j 1) = (a (Finsupp.single i 1)) j := by
      simp [LinearMap.comp_apply, A, Finsupp.linearCombination_single,
        Finsupp.single_apply]
    have ha_exp : a (Finsupp.single i 1) =
        ∑ j, (a (Finsupp.single i 1)) j • Finsupp.single j 1 := by
      ext j
      simp
    calc
      w (a (Finsupp.single i 1)) =
          ∑ j, (a (Finsupp.single i 1)) j •
            TensorProduct.rid R M₁
              (LinearMap.lTensor M₁
                (Finsupp.lapply j : (Fin m →₀ R) →ₗ[R] R) t) := by
        rw [ha_exp]
        simp only [map_sum, map_smul]
        simp [w, Finsupp.linearCombination_single]
      _ = ∑ j, ((Finsupp.lapply i : (Fin n →₀ R) →ₗ[R] R).comp A)
          (Finsupp.single j 1) •
          TensorProduct.rid R M₁
            (LinearMap.lTensor M₁
              (Finsupp.lapply j : (Fin m →₀ R) →ₗ[R] R) t) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcoeff]
      _ = TensorProduct.rid R M₁
          (LinearMap.lTensor M₁
            ((Finsupp.lapply i : (Fin n →₀ R) →ₗ[R] R).comp A) t) := hc.symm
      _ = u (Finsupp.single i 1) := hleft
  refine ⟨w, ?_⟩
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext
  intro c
  change w (a (Finsupp.single i c)) = u (Finsupp.single i c)
  rw [← Finsupp.smul_single_one]
  simp only [map_smul]
  rw [hcoord]

private lemma section_of_universallyExact_of_finitePresentation
    {R : Type u} {M₁ M₂ M₃ : Type w} [CommRing R]
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    [Module.FinitePresentation R M₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃)
    (hshort : Function.Injective f₁ ∧ Function.Exact f₁ f₂ ∧
      Function.Surjective f₂)
    (hue : universallyExact f₁ f₂) :
    ∃ s : M₃ →ₗ[R] M₂, f₂.comp s = LinearMap.id := by
  obtain ⟨n, m, p₀, q₀, hp₀, hpq₀⟩ :=
    Module.FinitePresentation.exists_fin' R M₃
  classical
  let eₙ : (Fin n →₀ R) ≃ₗ[R] (Fin n → R) :=
    Finsupp.linearEquivFunOnFinite R R (Fin n)
  let eₘ : (Fin m →₀ R) ≃ₗ[R] (Fin m → R) :=
    Finsupp.linearEquivFunOnFinite R R (Fin m)
  let p : (Fin n →₀ R) →ₗ[R] M₃ := p₀.comp eₙ.toLinearMap
  let q : (Fin m →₀ R) →ₗ[R] (Fin n →₀ R) :=
    eₙ.symm.toLinearMap.comp (q₀.comp eₘ.toLinearMap)
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨y, hy⟩ := hp₀ x
    refine ⟨eₙ.symm y, ?_⟩
    simpa [p] using hy
  have hpq : Function.Exact q p := by
    intro x
    constructor
    · intro hx
      have hx' : p₀ (eₙ x) = 0 := by
        simpa [p] using hx
      obtain ⟨y, hy⟩ := (hpq₀ (eₙ x)).mp hx'
      refine ⟨eₘ.symm y, ?_⟩
      apply eₙ.injective
      simp [q, hy]
    · rintro ⟨y, rfl⟩
      have hz := congrArg (fun z => z (eₘ y)) hpq₀.comp_eq_zero
      simpa [p, q] using hz
  let choose (i : Fin n) : M₂ :=
    (hshort.2.2 (p (Finsupp.single i 1))).choose
  have choose_spec (i : Fin n) :
      f₂ (choose i) = p (Finsupp.single i 1) :=
    (hshort.2.2 (p (Finsupp.single i 1))).choose_spec
  let v : (Fin n →₀ R) →ₗ[R] M₂ :=
    Finsupp.linearCombination R choose
  have hv : f₂.comp v = p := by
    apply Finsupp.lhom_ext'
    intro i
    apply LinearMap.ext
    intro c
    change f₂ (v (Finsupp.single i c)) = p (Finsupp.single i c)
    rw [← Finsupp.smul_single_one]
    simp only [map_smul]
    simp only [v, Finsupp.linearCombination_single, one_smul]
    rw [choose_spec]
  have hvqzero (i : Fin m) :
      f₂ (v (q (Finsupp.single i 1))) = 0 := by
    rw [← LinearMap.comp_apply, hv]
    have hzero := congrArg (fun z => z (Finsupp.single i 1)) hpq.comp_eq_zero
    simpa [LinearMap.comp_apply] using hzero
  have humem (i : Fin m) : v (q (Finsupp.single i 1)) ∈ LinearMap.range f₁ :=
    (hshort.2.1 _).mp (hvqzero i)
  let choose' (i : Fin m) : M₁ := (humem i).choose
  have choose'_spec (i : Fin m) :
      f₁ (choose' i) = v (q (Finsupp.single i 1)) :=
    (humem i).choose_spec
  let u : (Fin m →₀ R) →ₗ[R] M₁ :=
    Finsupp.linearCombination R choose'
  have hu : f₁.comp u = v.comp q := by
    apply Finsupp.lhom_ext'
    intro i
    apply LinearMap.ext
    intro c
    change f₁ (u (Finsupp.single i c)) = v (q (Finsupp.single i c))
    rw [← Finsupp.smul_single_one]
    simp only [map_smul]
    simp only [u, Finsupp.linearCombination_single, one_smul]
    rw [choose'_spec]
  obtain ⟨w, hw⟩ :=
    universallyExact_factor_finiteFree_of_universes hue.2.2.2 q u v hu.symm
  let s₀ : (Fin n →₀ R) →ₗ[R] M₂ := v - f₁.comp w
  have hs₀ : f₂.comp s₀ = p := by
    apply LinearMap.ext
    intro x
    have hcomp := congrArg (fun z => z (w x)) hshort.2.1.comp_eq_zero
    have hvx := congrArg (fun z => z x) hv
    have hcomp' : f₂ (f₁ (w x)) = 0 := by
      simpa [Function.comp_apply] using hcomp
    change f₂ (v x - f₁ (w x)) = p x
    rw [map_sub, hcomp', sub_zero]
    exact hvx
  have hs₀q : s₀.comp q = 0 := by
    apply LinearMap.ext
    intro x
    have hux := congrArg (fun z => z x) hu
    have hwx := congrArg (fun z => z x) hw
    change v (q x) - f₁ (w (q x)) = 0
    have hux' : f₁ (u x) = v (q x) := by
      change f₁ (u x) = v (q x) at hux
      exact hux
    have hwx' : w (q x) = u x := by
      change w (q x) = u x at hwx
      exact hwx
    rw [hwx', ← hux']
    simp
  have hker : LinearMap.ker p ≤ LinearMap.ker s₀ := by
    rw [LinearMap.exact_iff.mp hpq]
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    apply LinearMap.mem_ker.mpr
    have hs₀qx := congrArg (fun z => z y) hs₀q
    simpa [LinearMap.comp_apply] using hs₀qx
  let e := p.quotKerEquivOfSurjective hp
  let s : M₃ →ₗ[R] M₂ :=
    (LinearMap.ker p).liftQ s₀ hker |>.comp e.symm.toLinearMap
  have hsp : s.comp p = s₀ := by
    apply LinearMap.ext
    intro x
    simp [s, e]
  refine ⟨s, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y, hy⟩ := hp x
  rw [← hy]
  have hspx := congrArg (fun z => z y) hsp
  have hs₀x := congrArg (fun z => z y) hs₀
  calc
    f₂ (s (p y)) = f₂ (s₀ y) := by
      simpa [LinearMap.comp_apply] using congrArg f₂ hspx
    _ = p y := by
      simpa [LinearMap.comp_apply] using hs₀x

theorem dominates_iff_factors_of_finitelyPresented_cokernel
    {R : Type u} [CommRing R] {M N N' : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] N) (g : M →ₗ[R] N')
    (h : Module.FinitePresentation R
      (N ⧸ LinearMap.range f)) :
    dominates g f ↔ ∃ h' : N →ₗ[R] N', g = h'.comp f := by
  symm
  constructor
  · rintro ⟨h', rfl⟩
    intro Q _ _ x hx
    apply LinearMap.mem_ker.mpr
    have hx0 := LinearMap.mem_ker.mp hx
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply, hx0]
    simp
  · intro hd
    have : Module.FinitePresentation R
        (N ⧸ LinearMap.range f) := h
    let ff := ModuleCat.ofHom f
    let gg := ModuleCat.ofHom g
    let p := pushout ff gg
    let inl : N →ₗ[R] (p : Type w) := (pushout.inl ff gg).hom
    let inr : N' →ₗ[R] (p : Type w) := (pushout.inr ff gg).hom
    let q : N →ₗ[R] (N ⧸ LinearMap.range f) := Submodule.mkQ _
    let π : (p : Type w) →ₗ[R] (N ⧸ LinearMap.range f) :=
      (pushout.desc (ModuleCat.ofHom q) 0 (by
        ext x
        change Submodule.Quotient.mk (f x) = 0
        apply (Submodule.Quotient.mk_eq_zero _).2
        exact LinearMap.mem_range_self f x)).hom
    have hc : Function.Exact inr π ∧ Function.Surjective π := by
      simpa [ff, gg, p, inr, q, π] using pushout_inr_cokernel f g
    have hu : universallyInjective inr := by
      simpa [ff, gg, p, inr] using
        (dominates_iff_pushout_inr_universallyInjective f g).1 hd
    have hinj : Function.Injective inr :=
      injective_of_universallyInjective hu
    have huniv : universallyExact inr π :=
      ⟨hinj, hc.1, hc.2, hu⟩
    obtain ⟨s, hs⟩ :=
      section_of_universallyExact_of_finitePresentation inr π
        ⟨hinj, hc.1, hc.2⟩ huniv
    have hker : LinearMap.ker π = LinearMap.range inr :=
      LinearMap.exact_iff.mp hc.1
    let t : (p : Type w) →ₗ[R] (p : Type w) := LinearMap.id - s.comp π
    have ht (x : (p : Type w)) : t x ∈ LinearMap.range inr := by
      rw [← hker]
      apply LinearMap.mem_ker.mpr
      dsimp [t]
      rw [map_sub]
      have hsx := congrArg (fun z => z (π x)) hs
      have hsx' : π (s (π x)) = π x := by
        simpa [LinearMap.comp_apply] using hsx
      rw [hsx', sub_self]
    let tr : (p : Type w) →ₗ[R] LinearMap.range inr :=
      t.codRestrict _ ht
    let e : N' ≃ₗ[R] LinearMap.range inr :=
      LinearEquiv.ofBijective inr.rangeRestrict
        ⟨by
          intro x y hxy
          apply hinj
          exact congrArg Subtype.val hxy,
          LinearMap.surjective_rangeRestrict _⟩
    let r : (p : Type w) →ₗ[R] N' := e.symm.toLinearMap.comp tr
    have hr : r.comp inr = LinearMap.id := by
      ext x
      change e.symm (tr (inr x)) = x
      apply e.injective
      rw [e.apply_symm_apply]
      apply Subtype.ext
      change t (inr x) = inr x
      have hπinr : π (inr x) = 0 := by
        change (pushout.inr ff gg ≫
          pushout.desc (ModuleCat.ofHom q) 0 _).hom x = 0
        rw [pushout.inr_desc]
        simp
      simp [t, hπinr]
    refine ⟨r.comp inl, ?_⟩
    apply LinearMap.ext
    intro x
    change g x = r (inl (f x))
    have hcond := congrArg ModuleCat.Hom.hom
      (pushout.condition (f := ff) (g := gg))
    have hcond' : inl (f x) = inr (g x) := by
      have hx := congrArg (fun z => z x) hcond
      change inl (f x) = inr (g x) at hx
      exact hx
    rw [hcond']
    have hr' := congrArg (fun z => z (g x)) hr
    simpa [LinearMap.comp_apply] using hr'.symm
/-
  constructor
  · rintro ⟨h', rfl⟩
    intro Q _ _
    intro x hx
    apply LinearMap.mem_ker.mpr
    simpa [LinearMap.rTensor_comp, hx]
  · intro hd
    have : Module.FinitePresentation R
        (N ⧸ LinearMap.range f) := h
    let ff := ModuleCat.ofHom f
    let gg := ModuleCat.ofHom g
    let p := pushout ff gg
    let inl : N →ₗ[R] (p : Type w) := (pushout.inl ff gg).hom
    let inr : N' →ₗ[R] (p : Type w) := (pushout.inr ff gg).hom
    let q : N →ₗ[R] (N ⧸ LinearMap.range f) := Submodule.mkQ _
    let π : (p : Type w) →ₗ[R] (N ⧸ LinearMap.range f) :=
      (pushout.desc (ModuleCat.ofHom q) 0 (by
        ext x
        simp [q])).hom
    have hc : Function.Exact inr π ∧ Function.Surjective π := by
      simpa [ff, gg, p, inr, q, π] using pushout_inr_cokernel f g
    have hu : universallyInjective inr := by
      simpa [ff, gg, p, inr] using
        (dominates_iff_pushout_inr_universallyInjective f g).1 hd
    have hinj : Function.Injective inr :=
      injective_of_universallyInjective hu
    have huniv : universallyExact inr π :=
      ⟨hinj, hc.1, hc.2, hu⟩
    obtain ⟨s, hs⟩ :=
      (universallyExact_iff_split_of_finitePresentation inr π
        ⟨hinj, hc.1, hc.2⟩).1 huniv
    have hker : LinearMap.ker π = LinearMap.range inr :=
      (LinearMap.exact_iff.mp hc.1).symm
    let t : (p : Type w) →ₗ[R] (p : Type w) := LinearMap.id - s.comp π
    have ht (x : (p : Type w)) : t x ∈ LinearMap.range inr := by
      rw [← hker]
      apply LinearMap.mem_ker.mpr
      simp [t, hs]
    let tr : (p : Type w) →ₗ[R] LinearMap.range inr :=
      t.codRestrict _ ht
    let e : N' ≃ₗ[R] LinearMap.range inr :=
      LinearEquiv.ofBijective inr.rangeRestrict
        ⟨hinj, LinearMap.surjective_rangeRestrict _⟩
    let r : (p : Type w) →ₗ[R] N' := e.symm.toLinearMap.comp tr
    have hr : r.comp inr = LinearMap.id := by
      ext x
      simp [r, tr, t, e]
    refine ⟨r.comp inl, ?_⟩
    apply LinearMap.ext
    intro x
    change r (inl (f x)) = g x
    have hcond := congrArg ModuleCat.Hom.hom (pushout.condition ff gg)
    have hcond' := congrArg (fun z => z x) hcond
    rw [hcond']
    have hr' := congrArg (fun z => z (g x)) hr
    simpa [LinearMap.comp_apply] using hr'

-/
/-! ## The five equivalent characterizations -/

/-- The first condition in the source's characterization of a Mittag-Leffler
module. -/
def MLModuleCondition
    {R : Type u} [CommRing R] (M : ModuleCat.{w} R) : Prop :=
  ∀ (P : ModuleCat.{w} R), Module.FinitePresentation R P →
    ∀ (f : (P : Type w) →ₗ[R] (M : Type w)),
      ∃ Q : ModuleCat.{w} R, Module.FinitePresentation R Q ∧
        ∃ g : (P : Type w) →ₗ[R] (Q : Type w), mutuallyDominates g f

/-- The five conditions in the source are equivalent for any filtered
colimit presentation by finitely presented modules. -/
theorem mittagLeffler_characterization
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    [Nonempty I] [IsDirectedOrder I] {M : ModuleCat.{w} R}
    (P : ColimitPresentation I M)
    (hP : ∀ i, Module.FinitePresentation R (P.diag.obj i)) :
    List.TFAE [
      MLModuleCondition M,
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        dominates (directedMap P.diag hij) (colimitComponentMap P i),
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        ∀ (k : I) (hik : i ≤ k),
          ∃ h : (P.diag.obj k : Type w) →ₗ[R] (P.diag.obj j : Type w),
            directedMap P.diag hij = h.comp (directedMap P.diag hik),
      ∀ N : ModuleCat.{z} R, (homInverseSystem P.diag N).IsMittagLeffler,
      (homInverseSystem P.diag
        (ModuleCat.of R (∀ s : I, (P.diag.obj s : Type w)))).IsMittagLeffler
    ] := by
  sorry

/-- A module is Mittag-Leffler when it satisfies the equivalent conditions of
the preceding characterization. -/
def IsMittagLefflerModule
    {R : Type u} [CommRing R] (M : ModuleCat.{w} R) : Prop :=
  MLModuleCondition M

/-- Every finitely presented module is Mittag-Leffler. -/
theorem isMittagLefflerModule_of_finitePresentation
    {R : Type u} [CommRing R] (M : ModuleCat.{w} R)
    (hM : Module.FinitePresentation R M) :
    IsMittagLefflerModule M := by
  intro P hP f
  exact ⟨M, hM, f, ⟨by intro Q _ _; exact le_rfl, by intro Q _ _; exact le_rfl⟩⟩

/-! ## Flat modules, tensor products, and finite-free tests -/

/-- For a flat module presented as a directed colimit of finite free modules,
Mittag-Lefflerness is enough to check on the duals with target `R`. -/
theorem isMittagLefflerModule_of_flat_of_dualSystem
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    [Nonempty I] [IsDirectedOrder I] {M : ModuleCat.{w} R}
    (P : ColimitPresentation I M) (_hflat : Module.Flat R M)
    (hfree : ∀ i, Module.Free R (P.diag.obj i))
    (hfinite : ∀ i, Module.Finite R (P.diag.obj i))
    (hdual : (homInverseSystem P.diag (ModuleCat.of R R)).IsMittagLeffler) :
    IsMittagLefflerModule M := by
  have hcond3 :
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
      ∀ (k : I) (hik : i ≤ k),
          ∃ h : (P.diag.obj k : Type w) →ₗ[R] (P.diag.obj j : Type w),
            directedMap P.diag hij = h.comp (directedMap P.diag hik) := by
    intro i
    obtain ⟨jop, f, hf⟩ :=
      (Functor.isMittagLeffler_iff_subset_range_comp
        (homInverseSystem P.diag (ModuleCat.of R R))).mp hdual (Opposite.op i)
    let hij : i ≤ jop.unop := le_of_op_hom f
    refine ⟨jop.unop, hij, ?_⟩
    intro k hik
    obtain ⟨l, hjl, hkl⟩ := directed_of (· ≤ ·) jop.unop k
    let gl := (homOfLE hjl).op
    let u : (P.diag.obj i : Type w) →ₗ[R] (P.diag.obj jop.unop : Type w) :=
      directedMap P.diag hij
    let vl : (P.diag.obj i : Type w) →ₗ[R] (P.diag.obj l : Type w) :=
      directedMap P.diag (hik.trans hkl)
    have hfactor (lam : (P.diag.obj jop.unop : Type w) →ₗ[R] R) :
        ∃ μ : (P.diag.obj l : Type w) →ₗ[R] R, μ.comp vl = lam.comp u := by
      have hmem : lam.comp u ∈ Set.range
          (fun φ : (P.diag.obj jop.unop : Type w) →ₗ[R] R =>
            φ.comp (P.diag.map f.unop).hom) := by
        refine ⟨lam, ?_⟩
        change lam.comp (P.diag.map f.unop).hom = lam.comp u
        congr 1
      have hmem' : lam.comp u ∈ Set.range
          ⇑(ConcreteCategory.hom
            ((homInverseSystem P.diag (ModuleCat.of R R)).map f)) := by
        change ∃ y : (P.diag.obj jop.unop : Type w) →ₗ[R] R,
          y.comp (P.diag.map f.unop).hom = lam.comp u
        exact hmem
      obtain ⟨μ, hμ⟩ := hf gl hmem'
      have hμ' : μ.comp (P.diag.map (gl ≫ f).unop).hom = lam.comp u := by
        change (ConcreteCategory.hom
          ((homInverseSystem P.diag (ModuleCat.of R R)).map (gl ≫ f))) μ = lam.comp u
        exact hμ
      have hproof : (gl ≫ f).unop = homOfLE (hik.trans hkl) :=
        Subsingleton.elim _ _
      have hmap' := congrArg P.diag.map hproof
      refine ⟨μ, ?_⟩
      rw [hmap'] at hμ'
      simpa [vl, u, directedMap] using hμ'
    let : Module.Free R (P.diag.obj jop.unop : Type w) := hfree jop.unop
    let : Module.Finite R (P.diag.obj jop.unop : Type w) := hfinite jop.unop
    let ι := Module.Free.ChooseBasisIndex R (P.diag.obj jop.unop : Type w)
    let b : Module.Basis ι R (P.diag.obj jop.unop : Type w) :=
      Module.Free.chooseBasis R (P.diag.obj jop.unop : Type w)
    let μ : ι → (P.diag.obj l : Type w) →ₗ[R] R :=
      fun a => (hfactor (b.coord a)).choose
    let c : (P.diag.obj l : Type w) →ₗ[R] (ι → R) :=
      LinearMap.pi μ
    let h : (P.diag.obj l : Type w) →ₗ[R] (P.diag.obj jop.unop : Type w) :=
      b.repr.symm.toLinearMap.comp
        ((Finsupp.linearEquivFunOnFinite R R ι).symm.toLinearMap.comp c)
    have hcomp : u = h.comp vl := by
      apply LinearMap.ext
      intro x
      apply b.repr.injective
      ext a
      have ha := (hfactor (b.coord a)).choose_spec
      have ha' := congrArg (fun z => z x) ha
      simpa [h, c, μ] using ha'.symm
    let h' : (P.diag.obj k : Type w) →ₗ[R] (P.diag.obj jop.unop : Type w) :=
      h.comp (directedMap P.diag hkl)
    refine ⟨h', ?_⟩
    apply LinearMap.ext
    intro x
    have hmap : P.diag.map (homOfLE (hik.trans hkl)) =
        P.diag.map (homOfLE hik) ≫ P.diag.map (homOfLE hkl) := by
      rw [← P.diag.map_comp]
      congr 1
    have hmap' := congrArg ModuleCat.Hom.hom hmap
    have hvl := congrArg (fun z => z x) hmap'
    have hvl' : vl x = (directedMap P.diag hkl) ((directedMap P.diag hik) x) := by
      simpa [vl, directedMap, ModuleCat.hom_comp, LinearMap.comp_apply] using hvl
    have hc : u x = h (vl x) := by
      simpa [LinearMap.comp_apply] using congrArg (fun z => z x) hcomp
    rw [hvl'] at hc
    simpa [h', u, vl, LinearMap.comp_apply] using hc
  have hfp : ∀ i, Module.FinitePresentation R (P.diag.obj i) := by
    intro i
    let : Module.Free R (P.diag.obj i : Type w) := hfree i
    let : Module.Finite R (P.diag.obj i : Type w) := hfinite i
    let : Module.Projective R (P.diag.obj i : Type w) := Module.Projective.of_free
    exact Module.finitePresentation_of_projective R (P.diag.obj i : Type w)
  have h13 := (mittagLeffler_characterization.{u, v, w, u} P hfp).out 0 2
  change MLModuleCondition M
  exact h13.mpr hcond3
/-
  have hcond3 :
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        ∀ (k : I) (hik : i ≤ k),
          ∃ h : (P.diag.obj k : Type w) →ₗ[R] (P.diag.obj j : Type w),
            directedMap P.diag hij = h.comp (directedMap P.diag hik) := by
    intro i
    obtain ⟨jop, f, hf⟩ := hdual (Opposite.op i)
    let hij : i ≤ jop.unop := le_of_op_hom f
    refine ⟨jop.unop, hij, ?_⟩
    intro k hik
    let g := (homOfLE hik).op
    let u : (P.diag.obj i : Type w) →ₗ[R] (P.diag.obj jop.unop : Type w) :=
      directedMap P.diag hij
    let v : (P.diag.obj i : Type w) →ₗ[R] (P.diag.obj k : Type w) :=
      directedMap P.diag hik
    have hfactor (λ : (P.diag.obj jop.unop : Type w) →ₗ[R] R) :
        ∃ μ : (P.diag.obj k : Type w) →ₗ[R] R, μ.comp v = λ.comp u := by
      have hmem : λ.comp u ∈ Set.range
          (homInverseSystem P.diag (ModuleCat.of R R)).map f := by
        refine ⟨λ, ?_⟩
        change λ.comp (P.diag.map f.unop).hom = λ.comp u
        congr 1
        apply Subsingleton.elim
      obtain ⟨μ, hμ⟩ := hf g hmem
      refine ⟨μ, ?_⟩
      change μ.comp (P.diag.map g.unop).hom = λ.comp u at hμ
      simpa [g, v, u] using hμ
    letI : Module.Free R (P.diag.obj jop.unop : Type w) := hfree jop.unop
    letI : Module.Finite R (P.diag.obj jop.unop : Type w) := hfinite jop.unop
    let ι := Module.Free.ChooseBasisIndex R (P.diag.obj jop.unop : Type w)
    let b : Basis ι R (P.diag.obj jop.unop : Type w) :=
      Module.Free.chooseBasis R (P.diag.obj jop.unop : Type w)
    let μ : ι → (P.diag.obj k : Type w) →ₗ[R] R :=
      fun a => (hfactor (b.coord a)).choose
    let c : (P.diag.obj k : Type w) →ₗ[R] (ι → R) :=
      LinearMap.pi μ
    let h : (P.diag.obj k : Type w) →ₗ[R] (P.diag.obj jop.unop : Type w) :=
      b.repr.symm.toLinearMap.comp
        ((Finsupp.linearEquivFunOnFinite R R ι).symm.toLinearMap.comp c)
    have hcomp : u = h.comp v := by
      apply LinearMap.ext
      intro x
      apply b.repr.injective
      ext a
      have ha := (hfactor (b.coord a)).choose_spec
      simp [h, c, μ, ha]
    refine ⟨h, ?_⟩
    simpa [u, v] using hcomp
  have h13 := (mittagLeffler_characterization P hfinite).out 0 2
  exact h13.mpr hcond3
-/

/-- Tensor products of Mittag-Leffler modules are Mittag-Leffler. -/
theorem tensorProduct_isMittagLefflerModule
    {R : Type u} [CommRing R] (M N : ModuleCat.{w} R)
    (hM : IsMittagLefflerModule M) (hN : IsMittagLefflerModule N) :
    IsMittagLefflerModule
      (ModuleCat.of R ((M : Type w) ⊗[R] (N : Type w))) := by
  sorry

/-- The finite-free test for the Mittag-Leffler condition. -/
theorem isMittagLefflerModule_iff_finiteFreeTest
    {R : Type u} [CommRing R] (M : ModuleCat.{w} R) :
    IsMittagLefflerModule M ↔
      ∀ (F : ModuleCat.{w} R), Module.Free R F → Module.Finite R F →
      ∀ f : (F : Type w) →ₗ[R] (M : Type w),
            ∃ Q : ModuleCat.{w} R, Module.FinitePresentation R Q ∧
            ∃ g : (F : Type w) →ₗ[R] (Q : Type w), mutuallyDominates g f := by
  sorry
/-
  constructor
  · intro h F hFfree hFfinite f
    exact h F hFfree hFfinite f
  · intro h P hP f
    obtain ⟨n, m, p, q, hp, hpq⟩ :=
      Module.FinitePresentation.exists_fin' R (P : Type w) (fp := hP)
    let F : ModuleCat.{w} R := ModuleCat.of R (Fin n → R)
    let p' : (F : Type w) →ₗ[R] (P : Type w) := p
    obtain ⟨Q, hQ, g, hmut⟩ := h F (by infer_instance) (by infer_instance)
      (f.comp p')
    have hker : LinearMap.ker p' ≤ LinearMap.ker g := by
      intro x hx
      apply LinearMap.mem_ker.mpr
      have hpx : p' x = 0 := LinearMap.mem_ker.mp hx
      have hx' : (f.comp p').rTensor R
          ((TensorProduct.rid R (F : Type w)).symm x) = 0 := by
        rw [TensorProduct.rid_symm_apply]
        simp [hpx]
      have hg' := hmut.1 R (LinearMap.mem_ker.mpr hx')
      have hg'0 := LinearMap.mem_ker.mp hg'
      have hg'' := congrArg (TensorProduct.rid R (Q : Type w)) hg'0
      simpa [TensorProduct.rid_symm_apply] using hg''
    let e : (F : Type w) ⧸ LinearMap.ker p' ≃ₗ[R] (P : Type w) :=
      p'.quotKerEquivOfSurjective hp
    let g' : (P : Type w) →ₗ[R] (Q : Type w) :=
      (LinearMap.ker p').liftQ g hker |>.comp e.symm.toLinearMap
    have hg' : g'.comp p' = g := by
      apply LinearMap.ext
      intro x
      simp [g', e]
    have hdom₁ : dominates g' f := by
      intro X _ _
      intro z hz
      have hz0 := LinearMap.mem_ker.mp hz
      obtain ⟨y, hy⟩ := LinearMap.rTensor_surjective X hp z
      have hyf : (f.comp p').rTensor X y = 0 := by
        rw [LinearMap.rTensor_comp_apply, hy, hz0]
      have hyg := LinearMap.mem_ker.mp (hmut.1 X (LinearMap.mem_ker.mpr hyf))
      have hcomp := congrArg (fun t => t.rTensor X) hg'
      rw [LinearMap.rTensor_comp] at hcomp
      apply LinearMap.mem_ker.mpr
      rw [← hy]
      have hcomp' := congrArg (fun t => t y) hcomp
      simpa [LinearMap.comp_apply, hyg] using hcomp'
    have hdom₂ : dominates f g' := by
      intro X _ _
      intro z hz
      have hz0 := LinearMap.mem_ker.mp hz
      obtain ⟨y, hy⟩ := LinearMap.rTensor_surjective X hp z
      have hcomp := congrArg (fun t => t.rTensor X) hg'
      rw [LinearMap.rTensor_comp] at hcomp
      have hyg : (g.rTensor X) y = 0 := by
        have hcomp' := congrArg (fun t => t y) hcomp
        rw [LinearMap.comp_apply, hy] at hcomp'
        exact hcomp'.symm.trans hz0
      have hyf := LinearMap.mem_ker.mp (hmut.2 X (LinearMap.mem_ker.mpr hyg))
      apply LinearMap.mem_ker.mpr
      rw [← hy]
      simpa [LinearMap.rTensor_comp_apply] using hyf
    exact ⟨Q, hQ, g', ⟨hdom₁, hdom₂⟩⟩

/-! ## Restriction of scalars and quotients -/

/-- Mittag-Lefflerness descends from a finite, finitely presented ring
extension to the base ring. -/
-/
theorem isMittagLefflerModule_of_restrictScalars
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.Finite f)
    (hfinitelyPresented : RingHom.FinitePresentation f)
    (M : ModuleCat.{w} S)
    (hM : IsMittagLefflerModule (R := S) M) :
    letI : Module R (M : Type w) := Module.compHom (M : Type w) f
    IsMittagLefflerModule (R := R) (ModuleCat.of R (M : Type w)) := by
  sorry

/-- For a finitely generated ideal, the Mittag-Leffler condition is unchanged
when passing between a ring and its quotient. -/
theorem isMittagLefflerModule_iff_quotient
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (M : ModuleCat.{w} (R ⧸ I)) :
    (letI : Module R (M : Type w) :=
      Module.compHom (M : Type w) (Ideal.Quotient.mk I);
      IsMittagLefflerModule (R := R) (ModuleCat.of R (M : Type w))) ↔
      IsMittagLefflerModule (R := R ⧸ I) M := by
  sorry

/-! ## The dual-number warning -/

/-- Restriction of scalars along the canonical inclusion into the dual
numbers. -/
def dualNumberRestriction
    {R : Type u} [CommRing R] :
    ModuleCat.{w} (DualNumber R) ⥤ ModuleCat.{w} R :=
  ModuleCat.restrictScalars (algebraMap R (DualNumber R))

/-- The dual-number construction witnesses that restriction of scalars does
not reflect the Mittag-Leffler condition in general. -/
theorem exists_dualNumber_restriction_counterexample
    {R : Type u} [CommRing R]
    (h : ∃ M₀ : ModuleCat.{w} R, ¬ IsMittagLefflerModule M₀) :
    RingHom.Finite (algebraMap R (DualNumber R)) ∧
      RingHom.FinitePresentation (algebraMap R (DualNumber R)) ∧
      ∃ M : ModuleCat.{w} (DualNumber R),
        IsMittagLefflerModule (dualNumberRestriction.obj M) ∧
          ¬ IsMittagLefflerModule M := by
  sorry

end

end Formalization.Books.Algebra.Unit88
