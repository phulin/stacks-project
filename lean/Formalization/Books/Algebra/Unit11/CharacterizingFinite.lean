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
    dsimp [finiteSubsetCocone]
    rw [show (x, Submodule.Quotient.mk y) =
        (x, (0 : M ⧸ Submodule.span R (E : Set M))) +
          ((0 : M), Submodule.Quotient.mk y) by
      simp]
    have hqzero' :
        (s.ι.app E).hom
            ((0 : M), Submodule.Quotient.mk y) = 0 := by
      simpa using hqzero
    calc
      (s.ι.app ∅).hom (x, 0) = (s.ι.app E).hom (x, 0) := by
        symm
        simpa using congrArg (fun k => k.hom (x, 0))
          (s.ι.naturality (homOfLE (show (∅ : Finset M) ≤ E by simp)))
      _ = (s.ι.app E).hom
          ((x, (0 : M ⧸ Submodule.span R (E : Set M))) +
            ((0 : M), Submodule.Quotient.mk y)) := by
        rw [(s.ι.app E).hom.map_add, hqzero']
        simp
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
    let P : ColimitPresentation (Finset (N : Type u)) N :=
      { diag := finiteSubsetDiagram (R := R) (M := (N : Type u))
        ι := finiteSubsetCocone.ι
        isColimit := finiteSubsetCocone_isColimit }
    let c := (⟨Finset (N : Type u), P⟩ : FilteredModuleColimit N)
    letI : Category.{u} c.index := c.indexCategory
    letI : IsFiltered c.index := c.indexFiltered
    letI : HasColimit c.presentation.diag := c.presentation.hasColimit
    have hc := h c
    let E0 : Finset (N : Type u) := ∅
    let q : N ⟶ c.presentation.diag.obj E0 :=
      ModuleCat.ofHom <|
        (LinearMap.inr R (N : Type u)
          ((N : Type u) ⧸ Submodule.span R (E0 : Set (N : Type u)))).comp
          (Submodule.mkQ (Submodule.span R (E0 : Set (N : Type u))))
    have hqι : q ≫ c.presentation.ι.app E0 = 0 := by
      apply ModuleCat.hom_ext
      change (LinearMap.fst R (N : Type u)
          ((N : Type u) ⧸ Submodule.span R (E0 : Set (N : Type u)))).comp
          ((LinearMap.inr R (N : Type u)
            ((N : Type u) ⧸ Submodule.span R (E0 : Set (N : Type u)))).comp
            (Submodule.mkQ (Submodule.span R (E0 : Set (N : Type u))))) = 0
      apply LinearMap.ext
      intro x
      rfl
    let e : colimit c.presentation.diag ≅ N :=
      IsColimit.coconePointUniqueUpToIso (colimit.isColimit c.presentation.diag)
        c.presentation.isColimit
    have he := (colimit.isColimit c.presentation.diag).comp_coconePointUniqueUpToIso_hom
      c.presentation.isColimit E0
    have he' : colimit.ι c.presentation.diag E0 ≫ e.hom =
        c.presentation.ι.app E0 := by
      simpa [e] using he
    have hpost := colimit.ι_post c.presentation.diag (moduleHomFunctor N) E0
    have hpost_apply :
        (colimit.post c.presentation.diag (moduleHomFunctor N)).hom'
            ((colimit.ι (c.presentation.diag ⋙ moduleHomFunctor N) E0).hom q) =
          (moduleHomFunctor N).map (colimit.ι c.presentation.diag E0) q := by
      have hh := congrArg (fun k => k.hom q) hpost
      change (colimit.post c.presentation.diag (moduleHomFunctor N)).hom'
          ((colimit.ι (c.presentation.diag ⋙ moduleHomFunctor N) E0).hom q) =
        (moduleHomFunctor N).map (colimit.ι c.presentation.diag E0) q at hh
      exact hh
    have map_apply {A B : ModuleCat R} (f : A ⟶ B) (g : N ⟶ A) :
        (moduleHomFunctor N).map f g = g ≫ f := by
      change (ihom N).map f g = _
      exact ModuleCat.ihom_map_apply f g
    have hzero : (moduleHomFunctor N).map (c.presentation.ι.app E0) q = 0 := by
      change q ≫ c.presentation.ι.app E0 = 0
      exact hqι
    rw [map_apply] at hzero
    have hq :
        (filteredModuleHomColimitMap c).hom
            ((colimit.ι (c.presentation.diag ⋙ moduleHomFunctor N) E0).hom q) = 0 := by
      change ModuleCat.Hom.hom ((moduleHomFunctor N).map e.hom)
        ((colimit.post c.presentation.diag (moduleHomFunctor N)).hom'
          ((colimit.ι (c.presentation.diag ⋙ moduleHomFunctor N) E0).hom q)) = 0
      rw [hpost_apply, map_apply, map_apply]
      rw [Category.assoc, he']
      exact hzero
    have hqeq :
        (filteredModuleHomColimitMap c).hom
            ((colimit.ι (c.presentation.diag ⋙ moduleHomFunctor N) E0).hom q) =
          (filteredModuleHomColimitMap c).hom
            ((colimit.ι (c.presentation.diag ⋙ moduleHomFunctor N) E0).hom 0) := by
      simpa using hq
    have hqcol :
        (colimit.ι (c.presentation.diag ⋙ moduleHomFunctor N) E0).hom q =
          (colimit.ι (c.presentation.diag ⋙ moduleHomFunctor N) E0).hom 0 :=
      hc hqeq
    have hqcol' :
        (ConcreteCategory.hom
            (((forget (ModuleCat R)).mapCocone
              (colimit.cocone (c.presentation.diag ⋙ moduleHomFunctor N))).ι.app E0)) q =
          (ConcreteCategory.hom
            (((forget (ModuleCat R)).mapCocone
              (colimit.cocone (c.presentation.diag ⋙ moduleHomFunctor N))).ι.app E0)) 0 := by
      change (colimit.ι (c.presentation.diag ⋙ moduleHomFunctor N) E0).hom q =
        (colimit.ι (c.presentation.diag ⋙ moduleHomFunctor N) E0).hom 0
      exact hqcol
    obtain ⟨F, f, g, hfg⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff _
        (isColimitOfPreserves (forget (ModuleCat R))
          (colimit.isColimit (c.presentation.diag ⋙ moduleHomFunctor N)))).1 hqcol'
    have hmk (x : (N : Type u)) :
        Submodule.mkQ (Submodule.span R (F : Set (N : Type u))) x = 0 := by
      have hfg0 :
          (moduleHomFunctor N).map (c.presentation.diag.map f) q = 0 := by
        change (ConcreteCategory.hom
            (((c.presentation.diag ⋙ moduleHomFunctor N) ⋙ forget (ModuleCat R)).map f)) q =
          (ConcreteCategory.hom
            (((c.presentation.diag ⋙ moduleHomFunctor N) ⋙ forget (ModuleCat R)).map g)) 0 at hfg
        simpa using hfg
      have hfg' :
          (moduleHomFunctor N).map (c.presentation.diag.map f) q =
            (moduleHomFunctor N).map (c.presentation.diag.map g)
              (0 : N ⟶ c.presentation.diag.obj E0) := by
        calc
          _ = 0 := hfg0
          _ = _ := by rw [map_apply]; simp; rfl
      have hfg'' :
          q ≫ c.presentation.diag.map f =
            (0 : N ⟶ c.presentation.diag.obj E0) ≫ c.presentation.diag.map g := by
        rw [map_apply (c.presentation.diag.map f) q,
          map_apply (c.presentation.diag.map g)
            (0 : N ⟶ c.presentation.diag.obj E0)] at hfg'
        exact hfg'
      have hx := congrArg (fun z => z.hom x) hfg''
      simpa [c, P, finiteSubsetDiagram, finiteSubsetQuotientMap, q,
        Submodule.Quotient.mk_eq_zero] using hx
    have htop : Submodule.span R (F : Set (N : Type u)) = ⊤ := by
      apply top_unique
      intro x _
      exact (Submodule.Quotient.mk_eq_zero _).mp (hmk x)
    refine ⟨?_⟩
    rw [← htop]
    exact Submodule.fg_span F.finite_toSet

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
  classical
  let M := (N : Type u)
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
  let Index : Type u :=
    Σ S : Finset M, {E : Finset (S →₀ R) //
      ∀ e ∈ E, Finsupp.linearCombination R (fun s : S => (s : M)) e = 0}
  let indexLE : Index → Index → Prop := fun a b =>
    ∃ hST : a.1 ≤ b.1, ∀ e ∈ a.2.1,
      extend a.1 b.1 hST e ∈ b.2.1
  letI : LE Index := ⟨indexLE⟩
  letI : Preorder Index := {
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
  let stage (a : Index) : ModuleCat R :=
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
  let D : Index ⥤ ModuleCat R := {
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
      change Submodule.Quotient.mk
          (extend a.1 c.1 hfg.choose x) =
        Submodule.Quotient.mk
          (extend b.1 c.1 hg.choose
            (extend a.1 b.1 hf.choose x))
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
  have hc : IsColimit ((forget (ModuleCat R)).mapCocone c) := by
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
      isColimit := isColimitOfReflects (forget (ModuleCat R)) hc }
  exact ⟨{
    index := Index
    indexCategory := inferInstance
    indexFiltered := index_filtered
    presentation := P
    finitelyPresented := by
      intro a
      change Module.FinitePresentation R
        ((a.1 →₀ R) ⧸ Submodule.span R (a.2.1 : Set (a.1 →₀ R)))
      apply Module.finitePresentation_of_surjective (Submodule.mkQ _)
      · exact Submodule.mkQ_surjective _
      · rw [Submodule.ker_mkQ]
        exact Submodule.fg_span a.2.1.finite_toSet }⟩

/-! ## The finitely presented characterization -/

/-- A module is finitely presented exactly when `Hom` commutes with every
filtered colimit. -/
theorem finitePresentation_iff_hom_filteredColimit_bijective
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    Module.FinitePresentation R N ↔
      ∀ (C : FilteredModuleColimit N),
        Function.Bijective (filteredModuleHomColimitMap C).hom := by
  constructor
  · intro hfp C
    let _ : Category.{u} C.index := C.indexCategory
    let _ : IsFiltered C.index := C.indexFiltered
    let _ : HasColimit C.presentation.diag := C.presentation.hasColimit
    let _ : Module.FinitePresentation R N := hfp
    constructor
    · exact (finite_iff_hom_filteredColimit_injective N).1 inferInstance C
    · intro φ
      classical
      obtain ⟨n, m, p, q, hp, hpq⟩ := Module.FinitePresentation.exists_fin' R N
      let φ' : N ⟶ N := ModuleCat.ofHom <| by
        change (N : Type u) →ₗ[R] (N : Type u)
        exact ModuleCat.Hom.hom φ
      let φp : (Fin n → R) →ₗ[R] (N : Type u) := φ'.hom.comp p
      let e : colimit C.presentation.diag ≅ N :=
        IsColimit.coconePointUniqueUpToIso (colimit.isColimit C.presentation.diag)
          C.presentation.isColimit
      let φpC : (Fin n → R) →ₗ[R] (↑(colimit C.presentation.diag) : Type u) :=
        e.inv.hom.comp φp
      have hk (k : Fin n) :
          ∃ (i : C.index) (x : C.presentation.diag.obj i),
            (colimit.ι C.presentation.diag i).hom x = φpC (Pi.single k 1) := by
        exact Types.jointly_surjective_of_isColimit
          (isColimitOfPreserves (forget (ModuleCat R))
            (colimit.isColimit C.presentation.diag)) (φpC (Pi.single k 1))
      choose i xi hxi using hk
      let O : Finset C.index := Finset.univ.image i
      obtain ⟨s, T⟩ := IsFiltered.sup_objs_exists O
      let a (k : Fin n) : i k ⟶ s :=
        (T (show i k ∈ O by simp [O])).some
      let y (k : Fin n) : C.presentation.diag.obj s :=
        (C.presentation.diag.map (a k)).hom (xi k)
      let r : (Fin n → R) →ₗ[R] (C.presentation.diag.obj s) :=
        (Finsupp.linearCombination R y).comp
          (Finsupp.linearEquivFunOnFinite R R (Fin n)).symm.toLinearMap
      have hy (k : Fin n) :
          (colimit.ι C.presentation.diag s).hom (y k) =
            φpC (Pi.single k 1) := by
        have hw := congrArg (fun z => z.hom (xi k))
          (colimit.w C.presentation.diag (a k))
        have hw' :
            (colimit.ι C.presentation.diag s).hom
                ((C.presentation.diag.map (a k)).hom (xi k)) =
              (colimit.ι C.presentation.diag (i k)).hom (xi k) := by
          simpa only [ModuleCat.comp_apply] using hw
        exact hw'.trans (hxi k)
      have hrbasis (k : Fin n) :
          (colimit.ι C.presentation.diag s).hom (r (Pi.single k 1)) =
            φpC (Pi.single k 1) := by
        simpa [r] using hy k
      have hr :
          (colimit.ι C.presentation.diag s).hom.comp r = φpC := by
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
        simp only [LinearMap.comp_apply]
        rw [hrbasis k]
      have hφpq : φp.comp q = 0 := by
        dsimp [φp]
        rw [LinearMap.comp_assoc, hpq.linearMap_comp_eq_zero]
        simp
      have hφpCq : φpC.comp q = 0 := by
        dsimp [φpC]
        rw [LinearMap.comp_assoc, hφpq]
        simp
      have hqcol :
          (colimit.ι C.presentation.diag s).hom.comp (r.comp q) = 0 := by
        rw [← LinearMap.comp_assoc, hr, hφpCq]
      have hqcol' (k : Fin m) :
          (colimit.ι C.presentation.diag s).hom
              (r (q (Pi.single k 1))) = 0 := by
        have hk := congrArg (fun z => z (Pi.single k 1)) hqcol
        simpa [LinearMap.comp_apply] using hk
      have hkzero (k : Fin m) :
          ∃ (l : C.index) (u : s ⟶ l),
            (C.presentation.diag.map u).hom
                (r (q (Pi.single k 1))) = 0 := by
        have heq :
            (colimit.ι C.presentation.diag s).hom
                (r (q (Pi.single k 1))) =
              (colimit.ι C.presentation.diag s).hom 0 := by
          simpa using hqcol' k
        obtain ⟨l, u, v, huv⟩ :=
          (Types.FilteredColimit.isColimit_eq_iff _
            (isColimitOfPreserves (forget (ModuleCat R))
              (colimit.isColimit C.presentation.diag))).1 heq
        refine ⟨l, u, ?_⟩
        simpa using huv
      choose l u hu using hkzero
      let O' : Finset C.index := insert s (Finset.univ.image l)
      have ms : s ∈ O' := by simp [O']
      have ml (k : Fin m) : l k ∈ O' := by simp [O']
      let H' : Finset (Σ' (X Y : C.index) (_ : X ∈ O') (_ : Y ∈ O'),
          X ⟶ Y) :=
        Finset.univ.image (fun k =>
          (⟨s, l k, ms, ml k, u k⟩ :
            Σ' (X Y : C.index) (_ : X ∈ O') (_ : Y ∈ O'), X ⟶ Y))
      obtain ⟨t, T', hT'⟩ := IsFiltered.sup_exists O' H'
      let c : s ⟶ t := T' ms
      have hTc (k : Fin m) : u k ≫ T' (ml k) = c := by
        apply hT' ms (ml k)
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
      have hqzero (k : Fin m) :
          ModuleCat.Hom.hom (C.presentation.diag.map c)
              (r (q (Pi.single k 1))) = 0 := by
        let z := r (q (Pi.single k 1))
        have hcomp :
            ModuleCat.Hom.hom
                (C.presentation.diag.map (u k ≫ T' (ml k))) z =
              ModuleCat.Hom.hom (C.presentation.diag.map (T' (ml k)))
                (ModuleCat.Hom.hom (C.presentation.diag.map (u k)) z) := by
          have hh := congrArg (fun w => w.hom z)
            (Functor.map_comp C.presentation.diag (u k) (T' (ml k)))
          simpa only [ModuleCat.comp_apply] using hh
        calc
          ModuleCat.Hom.hom (C.presentation.diag.map c) z =
              ModuleCat.Hom.hom
                (C.presentation.diag.map (u k ≫ T' (ml k))) z := by
            rw [hTc k]
          _ = ModuleCat.Hom.hom (C.presentation.diag.map (T' (ml k)))
                (ModuleCat.Hom.hom (C.presentation.diag.map (u k)) z) := hcomp
          _ = 0 := by rw [hu k]; simp
      let r' : (Fin n → R) →ₗ[R] (C.presentation.diag.obj t) :=
        (C.presentation.diag.map c).hom.comp r
      have hrq' : r'.comp q = 0 := by
        apply LinearMap.ext
        intro z
        rw [show z = ∑ k : Fin m, Pi.single k (z k) by
          ext k
          simp]
        simp only [map_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [show Pi.single k (z k) = z k • Pi.single k 1 by
          ext q'
          by_cases hq' : q' = k <;> simp [hq']]
        simp only [map_smul]
        simp only [r', LinearMap.comp_apply]
        rw [hqzero k]
        simp
      have hker : LinearMap.ker p ≤ LinearMap.ker r' := by
        rw [hpq.linearMap_ker_eq]
        intro z hz
        obtain ⟨w, rfl⟩ := hz
        have hw := congrArg (fun z => z w) hrq'
        apply LinearMap.mem_ker.mpr
        simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hw
      let eP := p.quotKerEquivOfSurjective hp
      let ψ : N →ₗ[R] (C.presentation.diag.obj t) :=
        (LinearMap.ker p).liftQ r' hker |>.comp eP.symm.toLinearMap
      have hψp : ψ.comp p = r' := by
        ext z
        simp [ψ, eP]
      have hcι :
          (colimit.ι C.presentation.diag t).hom.comp
              (C.presentation.diag.map c).hom =
            (colimit.ι C.presentation.diag s).hom := by
        apply LinearMap.ext
        intro z
        change (colimit.ι C.presentation.diag t).hom
              ((C.presentation.diag.map c).hom z) =
            (colimit.ι C.presentation.diag s).hom z
        have hh := congrArg (fun w => w.hom z)
          (colimit.w C.presentation.diag c)
        simpa only [ModuleCat.comp_apply] using hh
      have hcolc :
          (colimit.ι C.presentation.diag t).hom.comp r' = φpC := by
        dsimp [r']
        rw [← LinearMap.comp_assoc, hcι, hr]
      let out : N →ₗ[R] (N : Type u) :=
        e.hom.hom.comp ((colimit.ι C.presentation.diag t).hom.comp ψ)
      have houtp : out.comp p = φp := by
        calc
          out.comp p = e.hom.hom.comp
              ((colimit.ι C.presentation.diag t).hom.comp (ψ.comp p)) := by
            simp [out, LinearMap.comp_assoc]
          _ = e.hom.hom.comp
              ((colimit.ι C.presentation.diag t).hom.comp r') := by rw [hψp]
          _ = e.hom.hom.comp φpC := by rw [hcolc]
          _ = φp := by
            dsimp [φpC]
            apply LinearMap.ext
            intro z
            change e.hom.hom (e.inv.hom (φp z)) = φp z
            have hz := congrArg (fun k => k.hom (φp z)) e.inv_hom_id
            change e.hom.hom (e.inv.hom (φp z)) = φp z at hz
            exact hz
      have hout : out = φ'.hom := by
        apply LinearMap.ext
        intro y0
        obtain ⟨z0, hz0⟩ := hp y0
        have hz := congrArg (fun k => k z0) houtp
        simpa [φp, hz0] using hz
      let ψcat : N ⟶ C.presentation.diag.obj t := ModuleCat.ofHom ψ
      refine ⟨(colimit.ι (C.presentation.diag ⋙ moduleHomFunctor N) t).hom ψcat, ?_⟩
      have map_apply' {A B : ModuleCat R} (f : A ⟶ B)
          (g : (moduleHomFunctor N).obj A) :
          ModuleCat.Hom.hom ((moduleHomFunctor N).map f) g =
            ModuleCat.ofHom (f.hom.comp (ModuleCat.Hom.hom g)) := by
        change (ihom N).map f g = _
        exact ModuleCat.ihom_map_apply f g
      have hpostψ :
          (colimit.post C.presentation.diag (moduleHomFunctor N)).hom'
              ((colimit.ι (C.presentation.diag ⋙ moduleHomFunctor N) t).hom ψcat) =
            (moduleHomFunctor N).map (colimit.ι C.presentation.diag t) ψcat := by
        have hh := colimit.ι_post C.presentation.diag (moduleHomFunctor N) t
        have hh' := congrArg (fun k => k.hom ψcat) hh
        change (colimit.post C.presentation.diag (moduleHomFunctor N)).hom'
            ((colimit.ι (C.presentation.diag ⋙ moduleHomFunctor N) t).hom ψcat) =
          (moduleHomFunctor N).map (colimit.ι C.presentation.diag t) ψcat at hh'
        exact hh'
      change ModuleCat.Hom.hom ((moduleHomFunctor N).map e.hom)
          ((colimit.post C.presentation.diag (moduleHomFunctor N)).hom'
            ((colimit.ι (C.presentation.diag ⋙ moduleHomFunctor N) t).hom ψcat)) =
        φ
      rw [hpostψ, map_apply' e.hom,
        map_apply' (colimit.ι C.presentation.diag t) ψcat]
      have hout' := congrArg (fun z : (N : Type u) →ₗ[R] (N : Type u) =>
        ModuleCat.ofHom z) hout
      change ModuleCat.ofHom out = ModuleCat.ofHom (ModuleCat.Hom.hom φ)
      exact hout'
  · intro h
    obtain ⟨C⟩ := exists_filteredColimit_finitelyPresented N
    let _ : Category.{u} C.index := C.indexCategory
    let _ : IsFiltered C.index := C.indexFiltered
    let _ : HasColimit C.presentation.diag := C.presentation.hasColimit
    have hc := h C.toFilteredModuleColimit
    let idHom : (moduleHomFunctor N).obj N :=
      ModuleCat.ofHom (LinearMap.id : (N : Type u) →ₗ[R] (N : Type u))
    obtain ⟨x, hx⟩ := hc.2 idHom
    obtain ⟨i, fi, hfi⟩ :=
      Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget (ModuleCat R))
          (colimit.isColimit (C.presentation.diag ⋙ moduleHomFunctor N))) x
    let e : colimit C.presentation.diag ≅ N :=
      IsColimit.coconePointUniqueUpToIso (colimit.isColimit C.presentation.diag)
        C.presentation.isColimit
    have map_apply {A B : ModuleCat R} (f : A ⟶ B) (g : N ⟶ A) :
        (moduleHomFunctor N).map f g = g ≫ f := by
      change (ihom N).map f g = _
      exact ModuleCat.ihom_map_apply f g
    have map_apply' {A B : ModuleCat R} (f : A ⟶ B)
        (g : (moduleHomFunctor N).obj A) :
        ModuleCat.Hom.hom ((moduleHomFunctor N).map f) g =
          ModuleCat.ofHom (f.hom.comp (ModuleCat.Hom.hom g)) := by
      change (ihom N).map f g = _
      exact ModuleCat.ihom_map_apply f g
    have hpost_apply :
        (colimit.post C.presentation.diag (moduleHomFunctor N)).hom'
            ((colimit.ι (C.presentation.diag ⋙ moduleHomFunctor N) i).hom fi) =
          (moduleHomFunctor N).map (colimit.ι C.presentation.diag i) fi := by
      have hh := colimit.ι_post C.presentation.diag (moduleHomFunctor N) i
      have hh' := congrArg (fun k => k.hom fi) hh
      change (colimit.post C.presentation.diag (moduleHomFunctor N)).hom'
          ((colimit.ι (C.presentation.diag ⋙ moduleHomFunctor N) i).hom fi) =
        (moduleHomFunctor N).map (colimit.ι C.presentation.diag i) fi at hh'
      exact hh'
    have hfi' :
        (colimit.ι (C.presentation.diag ⋙ moduleHomFunctor N) i).hom fi = x := by
      exact hfi
    have hmap :
        (filteredModuleHomColimitMap C.toFilteredModuleColimit).hom
            ((colimit.ι (C.presentation.diag ⋙ moduleHomFunctor N) i).hom fi) =
          idHom := by
      rw [hfi']
      exact hx
    change ModuleCat.Hom.hom ((moduleHomFunctor N).map e.hom)
        ((colimit.post C.presentation.diag (moduleHomFunctor N)).hom'
          ((colimit.ι (C.presentation.diag ⋙ moduleHomFunctor N) i).hom fi)) =
      idHom at hmap
    rw [hpost_apply, map_apply' e.hom,
      map_apply' (colimit.ι C.presentation.diag i) fi] at hmap
    let g : C.presentation.diag.obj i ⟶ N := colimit.ι C.presentation.diag i ≫ e.hom
    have hgf : g.hom.comp fi.hom = LinearMap.id := by
      have hmap' := congrArg ModuleCat.Hom.hom hmap
      simpa [idHom, g, Category.assoc] using hmap'
    let _ : Module.FinitePresentation R (C.presentation.diag.obj i) :=
      C.finitelyPresented i
    have hker : Module.FinitePresentation R (LinearMap.ker g.hom) := by
      apply Module.finitePresentation_of_split_exact
        (Submodule.subtype (LinearMap.ker g.hom)) g.hom fi.hom
      · exact hgf
      · exact (Submodule.injective_subtype _)
      · exact LinearMap.exact_subtype_ker_map g.hom
    let _ : Module.FinitePresentation R (LinearMap.ker g.hom) := hker
    have hkerfg : (LinearMap.ker g.hom).FG := Submodule.FG.of_finite
    have hg : Function.Surjective g.hom := by
      intro y
      refine ⟨fi.hom y, ?_⟩
      exact congrArg (fun k => k y) hgf
    exact Module.finitePresentation_of_surjective g.hom hg hkerfg

end Formalization.Books.Algebra.Unit11
