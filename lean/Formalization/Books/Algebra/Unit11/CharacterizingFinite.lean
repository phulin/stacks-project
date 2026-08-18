import Formalization.Books.Algebra.Unit10.InternalHom
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Presentation

/-!
# Commutative Algebra, Chapter 11: Characterizing finite and finitely presented modules

The source characterizes finite and finitely presented modules by the behavior of
`Hom`.  The filtered diagrams and their colimits below use Mathlib's category of
modules and its canonical internal-hom functor.  A small interface records an
arbitrary filtered colimit together with the comparison to its target module.
-/

namespace Formalization.Books.Algebra.Unit11

open CategoryTheory
open CategoryTheory.Limits
open scoped BigOperators

universe u

/-! ## Filtered colimits and the Hom comparison map -/

/-- A filtered colimit presentation of an `R`-module object.

 The presentation field reuses Mathlib's canonical colimit-presentation
 interface; the filtered wrapper records the source's directedness hypothesis.
-/
structure FilteredModuleColimit {R : Type u} [CommRing R]
    (N : ModuleCat.{u} R) where
  index : Type u
  [indexCategory : Category.{u} index]
  [indexFiltered : IsFiltered index]
  presentation : ColimitPresentation index N

/-- The module-valued functor `Hom_R(N, -)` used in the source. -/
abbrev moduleHomFunctor {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (Formalization.Books.Algebra.Unit10.internalHomFunctor (R := R)).obj
    (Opposite.op N)

/-- The canonical map
`colim Hom_R(N, M_i) → Hom_R(N, colim M_i)` for a filtered colimit presentation. -/
noncomputable def filteredModuleHomColimitMap
    {R : Type u} [CommRing R] {N : ModuleCat.{u} R}
    (C : FilteredModuleColimit N) :
    letI : Category.{u} C.index := C.indexCategory
    letI : HasColimit C.presentation.diag := C.presentation.hasColimit
    colimit (C.presentation.diag ⋙ moduleHomFunctor N) ⟶ (moduleHomFunctor N).obj N := by
  letI : Category.{u} C.index := C.indexCategory
  letI : IsFiltered C.index := C.indexFiltered
  letI : HasColimit C.presentation.diag := C.presentation.hasColimit
  let e : colimit C.presentation.diag ≅ N :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit C.presentation.diag)
      C.presentation.isColimit
  exact colimit.post C.presentation.diag (moduleHomFunctor N) ≫
    (moduleHomFunctor N).map e.hom

private def finiteSubsetQuotientMap
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    {E F : Finset M} (hEF : E ≤ F) :
    ModuleCat.of R (M ⧸ Submodule.span R (E : Set M)) ⟶
      ModuleCat.of R (M ⧸ Submodule.span R (F : Set M)) :=
  ModuleCat.ofHom <|
    (Submodule.span R (E : Set M)).mapQ (Submodule.span R (F : Set M))
      LinearMap.id (Submodule.span_mono fun x hx => hEF hx)

private abbrev finiteSubsetDiagram
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] :
    Finset M ⥤ ModuleCat.{u} R where
  obj E := ModuleCat.of R (M × (M ⧸ Submodule.span R (E : Set M)))
  map := fun {E F} hEF =>
    ModuleCat.ofHom <|
      (LinearMap.id : M →ₗ[R] M).prodMap
        (finiteSubsetQuotientMap (leOfHom hEF)).hom
  map_id E := by
    apply ModuleCat.hom_ext
    change (LinearMap.id : M →ₗ[R] M).prodMap
        (finiteSubsetQuotientMap (leOfHom (𝟙 E))).hom = LinearMap.id
    simp only [finiteSubsetQuotientMap, Submodule.mapQ_id]
    exact LinearMap.prodMap_id
  map_comp := by
    intro E F G hEF hFG
    apply ModuleCat.hom_ext
    change (LinearMap.id : M →ₗ[R] M).prodMap
        (finiteSubsetQuotientMap (leOfHom (hEF ≫ hFG))).hom =
      ((LinearMap.id : M →ₗ[R] M).prodMap
          (finiteSubsetQuotientMap (leOfHom hFG)).hom).comp
        ((LinearMap.id : M →ₗ[R] M).prodMap
          (finiteSubsetQuotientMap (leOfHom hEF)).hom)
    rw [LinearMap.prodMap_comp]
    congr 1
    simpa [finiteSubsetQuotientMap] using
      (Submodule.mapQ_comp (Submodule.span R (E : Set M))
        (Submodule.span R (F : Set M)) (Submodule.span R (G : Set M))
        LinearMap.id LinearMap.id (leOfHom hEF) (leOfHom hFG))

private abbrev finiteSubsetCocone
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] :
    Cocone (finiteSubsetDiagram (R := R) (M := M)) where
  pt := ModuleCat.of R M
  ι :=
    { app := fun E =>
        ModuleCat.ofHom <|
          LinearMap.fst R M (M ⧸ Submodule.span R (E : Set M))
      naturality := by
        intro E F hEF
        apply ModuleCat.hom_ext
        ext x
        change x.1 = x.1
        rfl }

private def finiteSubsetCocone_isColimit
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] :
    IsColimit (finiteSubsetCocone (R := R) (M := M)) := by
  classical
  refine
    { desc := fun s => by
        let l : M →ₗ[R] ↑((finiteSubsetDiagram (R := R) (M := M)).obj ∅) :=
          { toFun := fun x => (x, 0)
            map_add' := by intro x y; simp
            map_smul' := by intro r x; simp }
        exact ModuleCat.ofHom <|
          (s.ι.app ∅).hom.comp l
      fac := ?_
      uniq := ?_ }
  · intro s E
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rcases z with ⟨x, q⟩
    obtain ⟨y, rfl⟩ :=
      (Submodule.span R (E : Set M)).mkQ_surjective q
    let F : Finset M := insert y E
    have hEF : E ≤ F := by
      intro z hz
      exact Finset.mem_insert_of_mem hz
    have hy : y ∈ Submodule.span R (F : Set M) := by
      apply Submodule.subset_span
      simp [F]
    have hy' : y ∈ Submodule.span R (insert y (E : Set M)) := by
      simpa [F] using hy
    have hzero :
        (finiteSubsetDiagram (R := R) (M := M)).map (homOfLE hEF)
            (0, Submodule.mkQ (Submodule.span R (E : Set M)) y) = 0 := by
      change (0, _) = (0, _)
      simp [finiteSubsetDiagram, finiteSubsetQuotientMap, F,
        Submodule.Quotient.mk_eq_zero, hy']
    have hnat := s.ι.naturality (homOfLE hEF)
    have hqzero : (s.ι.app E).hom (0, Submodule.mkQ (Submodule.span R (E : Set M)) y) = 0 := by
      have := congrArg (fun k => k.hom (0, Submodule.mkQ
        (Submodule.span R (E : Set M)) y)) hnat
      change (s.ι.app F).hom
          (((finiteSubsetDiagram (R := R) (M := M)).map (homOfLE hEF)).hom
            (0, Submodule.mkQ (Submodule.span R (E : Set M)) y)) =
        (s.ι.app E).hom (0, Submodule.mkQ (Submodule.span R (E : Set M)) y) at this
      rw [hzero] at this
      simpa using this.symm
    rw [show (x, Submodule.mkQ (Submodule.span R (E : Set M)) y) =
        (x, 0) + (0, Submodule.mkQ (Submodule.span R (E : Set M)) y) by
      simp]
    change (s.ι.app ∅).hom (x, 0) =
      (s.ι.app E).hom ((x, 0) +
        (0, Submodule.mkQ (Submodule.span R (E : Set M)) y))
    rw [map_add, hqzero, add_zero]
    simpa using (congrArg (fun k => k.hom (x, 0))
      (s.ι.naturality (homOfLE (show (∅ : Finset M) ≤ E by simp))))
  · intro s m hm
    apply ModuleCat.hom_ext
    ext x
    simpa using congrArg (fun k => k.hom (x, 0)) (hm ∅)

/-- A finite module is characterized by injectivity of `Hom` on every filtered
colimit, as in Lemma `lemma-characterize-finite-module-hom`. -/
theorem finite_iff_hom_filteredColimit_injective
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    Module.Finite R N ↔
      ∀ (C : FilteredModuleColimit N),
        Function.Injective (filteredModuleHomColimitMap C).hom := by
  constructor
  · intro h C
    letI : Category.{u} C.index := C.indexCategory
    letI : IsFiltered C.index := C.indexFiltered
    letI : HasColimit C.presentation.diag := C.presentation.hasColimit
    have map_apply {A B : ModuleCat R} (f : A ⟶ B) (g : N ⟶ A) :
        (moduleHomFunctor N).map f g = g ≫ f := by
      change (ihom N).map f g = _
      exact ModuleCat.ihom_map_apply f g
    intro f g hfg
    obtain ⟨i, fi, hfi⟩ :=
      Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget (ModuleCat R))
          (colimit.isColimit (C.presentation.diag ⋙ moduleHomFunctor N))) f
    obtain ⟨j, gj, hgj⟩ :=
      Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget (ModuleCat R))
          (colimit.isColimit (C.presentation.diag ⋙ moduleHomFunctor N))) g
    let e : colimit C.presentation.diag ≅ N :=
      IsColimit.coconePointUniqueUpToIso (colimit.isColimit C.presentation.diag)
        C.presentation.isColimit
    rw [← hfi, ← hgj] at hfg
    have map_apply' {A B : ModuleCat R} (f : A ⟶ B)
        (g : (moduleHomFunctor N).obj A) :
        (ModuleCat.Hom.hom ((moduleHomFunctor N).map f)) g =
          ModuleCat.ofHom (f.hom.comp (ModuleCat.Hom.hom g)) := by
      change (ihom N).map f g = _
      exact ModuleCat.ihom_map_apply f g
    change (ModuleCat.Hom.hom ((moduleHomFunctor N).map e.hom)) _ =
      (ModuleCat.Hom.hom ((moduleHomFunctor N).map e.hom)) _ at hfg
    rw [map_apply' e.hom, map_apply' e.hom] at hfg
    have hi_map :
        ModuleCat.Hom.hom
            ((colimit.post C.presentation.diag (moduleHomFunctor N)).hom'
              ((ConcreteCategory.hom (((forget (ModuleCat R)).mapCocone
                (colimit.cocone (C.presentation.diag ⋙ moduleHomFunctor N))).ι.app i)) fi)) =
          (colimit.ι C.presentation.diag i).hom.comp fi.hom := by
      have hi := colimit.ι_post C.presentation.diag (moduleHomFunctor N) i
      have hi'' := congrArg (fun q => q.hom (ModuleCat.ofHom fi.hom)) hi
      rw [map_apply' (colimit.ι C.presentation.diag i) (ModuleCat.ofHom fi.hom)] at hi''
      have hi''' := congrArg ModuleCat.Hom.hom hi''
      change ModuleCat.Hom.hom
          ((colimit.post C.presentation.diag (moduleHomFunctor N)).hom'
            ((ConcreteCategory.hom (((forget (ModuleCat R)).mapCocone
              (colimit.cocone (C.presentation.diag ⋙ moduleHomFunctor N))).ι.app i)) fi)) =
        (colimit.ι C.presentation.diag i).hom.comp fi.hom at hi'''
      exact hi'''
    have hj_map :
        ModuleCat.Hom.hom
            ((colimit.post C.presentation.diag (moduleHomFunctor N)).hom'
              ((ConcreteCategory.hom (((forget (ModuleCat R)).mapCocone
                (colimit.cocone (C.presentation.diag ⋙ moduleHomFunctor N))).ι.app j)) gj)) =
          (colimit.ι C.presentation.diag j).hom.comp gj.hom := by
      have hj := colimit.ι_post C.presentation.diag (moduleHomFunctor N) j
      have hj'' := congrArg (fun q => q.hom (ModuleCat.ofHom gj.hom)) hj
      rw [map_apply' (colimit.ι C.presentation.diag j) (ModuleCat.ofHom gj.hom)] at hj''
      have hj''' := congrArg ModuleCat.Hom.hom hj''
      change ModuleCat.Hom.hom
          ((colimit.post C.presentation.diag (moduleHomFunctor N)).hom'
            ((ConcreteCategory.hom (((forget (ModuleCat R)).mapCocone
              (colimit.cocone (C.presentation.diag ⋙ moduleHomFunctor N))).ι.app j)) gj)) =
        (colimit.ι C.presentation.diag j).hom.comp gj.hom at hj'''
      exact hj'''
    rw [hi_map, hj_map] at hfg
    let fi' : N ⟶ C.presentation.diag.obj i := fi
    let gj' : N ⟶ C.presentation.diag.obj j := gj
    have hcomp_cat :
        ModuleCat.ofHom ((colimit.ι C.presentation.diag i).hom.comp fi'.hom) =
          ModuleCat.ofHom ((colimit.ι C.presentation.diag j).hom.comp gj'.hom) := by
      apply (cancel_mono e.hom).1
      rw [← ModuleCat.ofHom_hom e.hom]
      rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
      exact hfg
    have hcomp :
        (colimit.ι C.presentation.diag i).hom.comp fi'.hom =
          (colimit.ι C.presentation.diag j).hom.comp gj'.hom := by
      have hcomp' := congrArg ModuleCat.Hom.hom hcomp_cat
      simpa only [ModuleCat.hom_ofHom] using hcomp'
    obtain ⟨n, gen, hgen⟩ := Module.Finite.exists_fin' R N
    let x : Fin n → N := fun k => gen (Pi.single k 1)
    have hx (k : Fin n) :
        (colimit.ι C.presentation.diag i).hom (fi'.hom (x k)) =
          (colimit.ι C.presentation.diag j).hom (gj'.hom (x k)) := by
      exact congrArg (fun q : N →ₗ[R] ↑(colimit C.presentation.diag) => q (x k)) hcomp
    have hk (k : Fin n) :
        ∃ (l : C.index) (u : i ⟶ l) (v : j ⟶ l),
          (C.presentation.diag.map u) (fi'.hom (x k)) =
            (C.presentation.diag.map v) (gj'.hom (x k)) := by
      exact (Types.FilteredColimit.isColimit_eq_iff _
        (isColimitOfPreserves (forget (ModuleCat R))
          (colimit.isColimit C.presentation.diag))).1 (hx k)
    classical
    choose l u v huv using hk
    let O : Finset C.index := insert i (insert j (Finset.univ.image l))
    have mi : i ∈ O := by simp [O]
    have mj : j ∈ O := by simp [O]
    have ml (k : Fin n) : l k ∈ O := by simp [O]
    let H : Finset (Σ' (X Y : C.index) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
      Finset.univ.image (fun k =>
        (⟨i, l k, mi, ml k, u k⟩ :
          Σ' (X Y : C.index) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y)) ∪
      Finset.univ.image (fun k =>
        (⟨j, l k, mj, ml k, v k⟩ :
          Σ' (X Y : C.index) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y))
    obtain ⟨s, T, hT⟩ := IsFiltered.sup_exists O H
    have huT (k : Fin n) : u k ≫ T (ml k) = T mi := by
      apply hT mi (ml k)
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    have hvT (k : Fin n) : v k ≫ T (ml k) = T mj := by
      apply hT mj (ml k)
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    let a : i ⟶ s := T mi
    let b : j ⟶ s := T mj
    have hab (k : Fin n) :
        (C.presentation.diag.map a) (fi'.hom (x k)) =
          (C.presentation.diag.map b) (gj'.hom (x k)) := by
      have hh := congrArg (fun z => (C.presentation.diag.map (T (ml k))).hom z)
        (huv k)
      have hh' :
          (C.presentation.diag.map (u k ≫ T (ml k))).hom (fi'.hom (x k)) =
            (C.presentation.diag.map (v k ≫ T (ml k))).hom (gj'.hom (x k)) := by
        simpa only [Functor.map_comp, ModuleCat.comp_apply] using hh
      rw [huT k, hvT k] at hh'
      exact hh'
    let fa : N ⟶ C.presentation.diag.obj s := fi' ≫ C.presentation.diag.map a
    let gb : N ⟶ C.presentation.diag.obj s := gj' ≫ C.presentation.diag.map b
    have hbase (k : Fin n) :
        (fa.hom.comp gen) (Pi.single k 1) =
          (gb.hom.comp gen) (Pi.single k 1) := by
      simpa only [fa, gb, ModuleCat.hom_comp, LinearMap.comp_apply, x] using hab k
    have hgen_maps : fa.hom.comp gen = gb.hom.comp gen := by
      apply LinearMap.ext
      intro z
      rw [show z = ∑ k : Fin n, Pi.single k (z k) by
        ext k
        simp]
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [show Pi.single k (z k) = z k • Pi.single k 1 by
        ext q
        by_cases hq : q = k <;> simp [hq]]
      simp only [map_smul]
      rw [hbase k]
    have hstage_hom : fa.hom = gb.hom := by
      apply LinearMap.ext
      intro z
      obtain ⟨w, rfl⟩ := hgen z
      have hz := congrArg (fun q => q w) hgen_maps
      simpa only [LinearMap.comp_apply] using hz
    have hstage : fa = gb := ModuleCat.hom_ext hstage_hom
    have hmaps :
        (moduleHomFunctor N).map (C.presentation.diag.map a) fi =
          (moduleHomFunctor N).map (C.presentation.diag.map b) gj := by
      change (moduleHomFunctor N).map (C.presentation.diag.map a) fi' =
        (moduleHomFunctor N).map (C.presentation.diag.map b) gj'
      rw [map_apply (C.presentation.diag.map a), map_apply (C.presentation.diag.map b)]
      exact hstage
    rw [← hfi, ← hgj]
    apply (Types.FilteredColimit.isColimit_eq_iff _
      (isColimitOfPreserves (forget (ModuleCat R))
        (colimit.isColimit (C.presentation.diag ⋙ moduleHomFunctor N)))).2
    exact ⟨s, a, b, hmaps⟩
  · intro h
    sorry

/-! ## Relations -/

/-- A relation among the entries of `x` is a coefficient vector whose linear
combination of those entries vanishes.  `Fin n` supplies the source's
`n`-element indexing, including the case `n = 0`. -/
def IsRelation {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (x : Fin n → M) (f : Fin n → R) : Prop :=
  ∑ i, f i • x i = 0

/-! ## Filtered colimits of finitely presented modules -/

/-- A filtered colimit presentation whose stages are finitely presented. -/
structure FilteredFinitelyPresentedModuleColimit
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    extends FilteredModuleColimit N where
  finitelyPresented : ∀ i, Module.FinitePresentation R (presentation.diag.obj i)

/-- Every module is a filtered colimit of finitely presented modules, as in
Lemma `lemma-module-colimit-fp`. -/
theorem exists_filteredColimit_finitelyPresented
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    Nonempty (FilteredFinitelyPresentedModuleColimit N) := by
  sorry

/-! ## The finitely presented characterization -/

/-- A module is finitely presented exactly when `Hom` commutes with every
filtered colimit. -/
theorem finitePresentation_iff_hom_filteredColimit_bijective
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    Module.FinitePresentation R N ↔
      ∀ (C : FilteredModuleColimit N),
        Function.Bijective (filteredModuleHomColimitMap C).hom := by
  sorry

end Formalization.Books.Algebra.Unit11
