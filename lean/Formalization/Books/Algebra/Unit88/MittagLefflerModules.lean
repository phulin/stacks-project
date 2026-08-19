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

/-- Tensor-kernel inclusion only needs to be tested on finitely presented
modules. -/
private structure GeneralFilteredColimit
    {R : Type u} [CommRing R] (N : ModuleCat.{w} R) where
  index : Type (max u w)
  [indexCategory : Category.{max u w} index]
  [indexFiltered : IsFiltered index]
  presentation : ColimitPresentation index N
  underlyingIsColimit :
    IsColimit ((forget (ModuleCat.{w} R)).mapCocone presentation.cocone)
  finitelyPresented : ∀ i, Module.FinitePresentation R (presentation.diag.obj i)

private local instance generalFilteredColimitIndexCategory
    {R : Type u} [CommRing R] {N : ModuleCat.{w} R}
    (C : GeneralFilteredColimit N) : Category.{max u w} C.index :=
  C.indexCategory

private local instance generalFilteredColimitIndexFiltered
    {R : Type u} [CommRing R] {N : ModuleCat.{w} R}
    (C : GeneralFilteredColimit N) : IsFiltered C.index :=
  C.indexFiltered

private theorem exists_generalFilteredColimit
    {R : Type u} [CommRing R] (N : ModuleCat.{w} R) :
    Nonempty (GeneralFilteredColimit N) := by
  sorry
/-
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
    indexCategory := inferInstance
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
private lemma tensor_rep
    {R : Type u} [CommRing R] {P : Type w} [AddCommGroup P] [Module R P]
    {Q : ModuleCat.{w} R} (C : GeneralFilteredColimit Q) :
    ∀ x : TensorProduct R P (Q : Type w),
        ∃ (i : C.index) (y : TensorProduct R P
          (C.presentation.diag.obj i : Type w)),
        (C.presentation.ι.app i).hom.lTensor P y = x := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero =>
      let i : C.index := IsFiltered.nonempty.some
      exact ⟨i, 0, by simp⟩
  | tmul p q =>
      obtain ⟨i, qi, hqi⟩ :=
        Types.jointly_surjective_of_isColimit C.underlyingIsColimit q
      refine ⟨i, p ⊗ₜ[R] qi, ?_⟩
      have hqi' : (C.presentation.ι.app i).hom qi = q := by
        change (ConcreteCategory.hom
          (((forget (ModuleCat.{w} R)).mapCocone C.presentation.cocone).ι.app i)) qi = q
        exact hqi
      simp [hqi']
  | add x y hx hy =>
      obtain ⟨i, xi, hxi⟩ := hx
      obtain ⟨j, yj, hyj⟩ := hy
      obtain ⟨k, a, b, _⟩ := IsFilteredOrEmpty.cocone_objs i j
      let yk := (C.presentation.diag.map a).hom.lTensor P xi +
        (C.presentation.diag.map b).hom.lTensor P yj
      refine ⟨k, yk, ?_⟩
      dsimp [yk]
      rw [map_add, ← hxi, ← hyj]
      have ha0 : (C.presentation.ι.app k).hom.comp
          (C.presentation.diag.map a).hom = (C.presentation.ι.app i).hom := by
        apply LinearMap.ext
        intro v
        have hnat := congrArg ModuleCat.Hom.hom (C.presentation.ι.naturality a)
        dsimp at hnat
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
          congrArg (fun h : (C.presentation.diag.obj i : Type w) →ₗ[R]
            (Q : Type w) => h v) hnat
      have hb0 : (C.presentation.ι.app k).hom.comp
          (C.presentation.diag.map b).hom = (C.presentation.ι.app j).hom := by
        apply LinearMap.ext
        intro v
        have hnat := congrArg ModuleCat.Hom.hom (C.presentation.ι.naturality b)
        dsimp at hnat
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
          congrArg (fun h : (C.presentation.diag.obj j : Type w) →ₗ[R]
            (Q : Type w) => h v) hnat
      have ha := congrArg (fun t => t.lTensor P) ha0
      have hb := congrArg (fun t => t.lTensor P) hb0
      rw [LinearMap.lTensor_comp] at ha hb
      rw [← ha, ← hb]
      simp only [LinearMap.comp_apply]

private lemma eventually_zero
    {R : Type u} [CommRing R] {Q : ModuleCat.{w} R}
    (C : GeneralFilteredColimit Q) {i : C.index} (x : C.presentation.diag.obj i) :
    (C.presentation.ι.app i).hom x = 0 →
      ∃ (j : C.index) (h : i ⟶ j),
        (C.presentation.diag.map h).hom x = 0 := by
  intro hx
  obtain ⟨j, h, hh⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' C.underlyingIsColimit x 0).1
      (hx.trans (by simp))
  exact ⟨j, h, by simpa using hh⟩

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
  · intro hd Q _ _
    intro x y hxy
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
      (pushout.desc (ModuleCat.ofHom q) 0 (by sorry)).hom
    Function.Exact (ModuleCat.Hom.hom (pushout.inr ff gg)) π ∧
      Function.Surjective π := by
  sorry
/-
  dsimp
  let ff := ModuleCat.ofHom f
  let gg := ModuleCat.ofHom g
  let p := pushout ff gg
  let q : N →ₗ[R] (N ⧸ LinearMap.range f) := Submodule.mkQ _
  let π : (p : Type w) →ₗ[R] (N ⧸ LinearMap.range f) :=
    (pushout.desc (ModuleCat.ofHom q) 0 (by
      ext x
      simp [q])).hom
  have hqcol := ModuleCat.cokernelIsColimit ff
  let cπ : CokernelCofork (pushout.inr ff gg) :=
    CokernelCofork.ofπ (ModuleCat.ofHom π) (by
      ext x
      simp [π])
  have hcπ : IsColimit cπ := by
    refine Cofork.IsColimit.mk _ ?_ ?_ ?_
    · intro s
      let k : N ⟶ s.pt := pushout.inl ff gg ≫ s.π
      have hk : ff ≫ k = 0 := by
        rw [← pushout.condition_assoc]
        simp [k, s.condition]
      exact hqcol.desc (CokernelCofork.ofπ k hk)
    · intro s
      apply (pushoutIsPushout ff gg).hom_ext
      · simp
      · simp [π, s.condition]
    · intro s m hm
      haveI : Epi hqcol.π := epi_of_isColimit_cofork hqcol
      apply (cancel_epi hqcol.π).1
      calc
        hqcol.π ≫ m = pushout.inl ff gg ≫ π ≫ m := by simp [π]
        _ = pushout.inl ff gg ≫ s.π := by rw [hm]
        _ = hqcol.π ≫ hqcol.desc
            (CokernelCofork.ofπ (pushout.inl ff gg ≫ s.π) (by
              rw [← pushout.condition_assoc]
              simp [s.condition])) := by
          symm
          exact Cofork.IsColimit.π_desc hqcol
  let S' := ShortComplex.moduleCatMk
    (ModuleCat.Hom.hom (pushout.inr ff gg)) π (by
      ext x
      simp [π])
  have hS' : S'.Exact := S'.exact_of_g_is_cokernel hcπ
  exact ⟨(S'.moduleCat_exact_iff_function_exact).mp hS',
    ModuleCat.epi_iff_surjective.mp (epi_of_isColimit_cofork hcπ)⟩
-/

theorem dominates_iff_factors_of_finitelyPresented_cokernel
    {R : Type u} [CommRing R] {M N N' : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] N) (g : M →ₗ[R] N')
    (h : Module.FinitePresentation R
      (N ⧸ LinearMap.range f)) :
    dominates g f ↔ ∃ h' : N →ₗ[R] N', g = h'.comp f := by
  sorry
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
    (P : ColimitPresentation I M) (hflat : Module.Flat R M)
    (hfree : ∀ i, Module.Free R (P.diag.obj i))
    (hfinite : ∀ i, Module.Finite R (P.diag.obj i))
    (hdual : (homInverseSystem P.diag (ModuleCat.of R R)).IsMittagLeffler) :
    IsMittagLefflerModule M := by
  sorry
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
