import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Categories, Chapter 26: Categorically compact objects

The source calls an object categorically compact when its hom functor preserves
filtered colimits.  Mathlib's `IsFinitelyPresentable` is the canonical API for
this condition (and is explicitly documented there as the compact-object
notion), so the source terminology is exposed below as an alias rather than a
parallel definition.
-/

namespace Formalization.Books.Categories.Unit26

open CategoryTheory
open CategoryTheory.Limits

universe u v u' v'

noncomputable section

/-! ## Categorically compact objects -/

/-- The source's terminology for Mathlib's finitely presentable objects. -/
abbrev IsCategoricallyCompact {C : Type u} [Category.{v} C] (X : C) : Prop :=
  IsFinitelyPresentable.{v} X

/-! ## Finitely presented modules -/

/-- Finitely presented modules form an essentially small object property. -/
theorem module_finitePresentation_essentiallySmall
    (R : Type u) [Ring R] :
    ObjectProperty.EssentiallySmall.{u}
      (fun M : ModuleCat.{u} R => Module.FinitePresentation R (M : Type u)) := by
  let X : (Σ n : ℕ, Submodule R (Fin n → R)) → ModuleCat.{u} R :=
    fun i => ModuleCat.of R ((Fin i.1 → R) ⧸ i.2)
  let Q : ObjectProperty (ModuleCat.{u} R) := ObjectProperty.ofObj X
  have hQ : ObjectProperty.Small.{u} Q := by
    dsimp [Q]
    infer_instance
  refine ⟨Q, hQ, ?_⟩
  intro M hM
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R (M : Type u)
  refine ⟨X ⟨n, K⟩, ?_, ?_⟩
  · exact ObjectProperty.ofObj_apply X ⟨n, K⟩
  · exact ⟨e.toModuleIso⟩

/-- Every module is an `ObjectProperty.ind` filtered colimit of finitely presented modules. -/
theorem module_finitePresentation_ind
    {R : Type u} [Ring R] (N : ModuleCat.{u} R) :
    ObjectProperty.ind.{u}
      (fun M : ModuleCat.{u} R => Module.FinitePresentation R (M : Type u)) N := by
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
  let : LE Index := ⟨indexLE⟩
  let : Preorder Index := {
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
  refine ⟨Index, inferInstance, index_filtered,
    { diag := D
      ι := c.ι
      isColimit := isColimitOfReflects (forget (ModuleCat R)) hc }, ?_⟩
  intro a
  change Module.FinitePresentation R
    ((a.1 →₀ R) ⧸ Submodule.span R (a.2.1 : Set (a.1 →₀ R)))
  apply Module.finitePresentation_of_surjective (Submodule.mkQ _)
  · exact Submodule.mkQ_surjective _
  · rw [Submodule.ker_mkQ]
    exact Submodule.fg_span a.2.1.finite_toSet

/--
An extension of a functor on a small full subcategory which commutes with
filtered colimits.  The restriction is recorded up to natural isomorphism,
which is the categorical meaning of extension in the source lemma.
-/
structure FilteredColimitExtension
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    (P : ObjectProperty C) (F' : P.FullSubcategory ⥤ D) where
  /-- The extended functor on the ambient category. -/
  functor : C ⥤ D
  /-- The extended functor commutes with filtered colimits of the source size. -/
  preservesFilteredColimits : PreservesFilteredColimitsOfSize.{v, v} functor
  /-- Its restriction to the full subcategory agrees with `F'`. -/
  restrictionIso : P.ι ⋙ functor ≅ F'

/--
Every functor from an essentially small full subcategory of categorically compact objects
which generates `C` under filtered colimits extends to a functor on `C` that
commutes with filtered colimits of the source size.  Such an extension is unique up to the
unique natural isomorphism compatible with the chosen restriction isomorphisms.

`ObjectProperty.ind` is Mathlib's canonical presentation of an object as a
filtered colimit of objects satisfying an object property.
-/
theorem exists_filteredColimitExtension_unique_up_to_iso
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    [HasFilteredColimits C] [HasFilteredColimitsOfSize.{v, v} D]
    (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{v} P]
    (hcompact : ∀ X : C, P X → IsCategoricallyCompact X)
    (hgenerated : ∀ X : C, ObjectProperty.ind.{v} P X)
    (F' : P.FullSubcategory ⥤ D) :
    ∃ E : FilteredColimitExtension P F',
      ∀ E' : FilteredColimitExtension P F',
        ∃! e : E.functor ≅ E'.functor,
          Functor.isoWhiskerLeft P.ι e ≪≫ E'.restrictionIso = E.restrictionIso := by
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  have final_of_presentation
      {X : C} {J : Type v} [SmallCategory J] [IsFiltered J]
      (pres : ColimitPresentation J X)
      (hp : ∀ j, P (pres.diag.obj j)) :
      (let Q : J ⥤ P.FullSubcategory :=
        { obj := fun j => ⟨pres.diag.obj j, hp j⟩
          map := fun f => P.homMk (pres.diag.map f) }
       Q.toCostructuredArrow P.ι X (fun j => pres.ι.app j) (by
         intro i j f
         exact pres.w f)).Final := by
    let Q : J ⥤ P.FullSubcategory :=
      { obj := fun j => ⟨pres.diag.obj j, hp j⟩
        map := fun f => P.homMk (pres.diag.map f) }
    let t : J ⥤ CostructuredArrow P.ι X :=
      Q.toCostructuredArrow P.ι X (fun j => pres.ι.app j) (by
        intro i j f
        exact pres.w f)
    change t.Final
    let : ∀ d, IsFiltered (StructuredArrow d t) := by
      intro d
      apply isFiltered_structuredArrow_of_isFiltered_of_exists t d
      · have : IsFinitelyPresentable d.left.obj := hcompact _ d.left.property
        obtain ⟨j, f, hf⟩ :=
          IsFinitelyPresentable.exists_hom_of_isColimit (X := d.left.obj)
            pres.isColimit d.hom
        exact ⟨j, ⟨CostructuredArrow.homMk (P.homMk f) hf⟩⟩
      · intro c s s'
        change d ⟶ CostructuredArrow.mk (S := P.ι) (T := X) (Y := Q.obj c)
          (pres.ι.app c) at s s'
        have : IsFinitelyPresentable d.left.obj := hcompact _ d.left.property
        obtain ⟨j, u, v, h⟩ :=
          IsFinitelyPresentable.exists_eq_of_isColimit (X := d.left.obj)
            pres.isColimit s.left.hom s'.left.hom (by
              change s.left.hom ≫ pres.ι.app c = s'.left.hom ≫ pres.ι.app c
              exact (CostructuredArrow.w s).trans (CostructuredArrow.w s').symm)
        let r := u ≫ IsFiltered.coeqHom u v
        refine ⟨IsFiltered.coeq u v, r, ?_⟩
        apply CostructuredArrow.ext _ _
        apply P.hom_ext
        change s.left.hom ≫ pres.diag.map r = s'.left.hom ≫ pres.diag.map r
        calc
          s.left.hom ≫ pres.diag.map r =
              s.left.hom ≫ pres.diag.map u ≫ pres.diag.map (IsFiltered.coeqHom u v) := by
                simp only [r, Functor.map_comp]
          _ = s'.left.hom ≫ pres.diag.map v ≫
              pres.diag.map (IsFiltered.coeqHom u v) := by
                rw [← Category.assoc, h]
                simp only [Category.assoc]
          _ = s'.left.hom ≫ pres.diag.map r := by
            simp only [r, Functor.map_comp]
            rw [← pres.diag.map_comp, ← pres.diag.map_comp,
              IsFiltered.coeq_condition]
    exact Functor.final_of_isFiltered_structuredArrow t
  let : P.ι.HasPointwiseLeftKanExtension F' := by
    intro X
    obtain ⟨J, _, _, pres, hp⟩ := hgenerated X
    let Q : J ⥤ P.FullSubcategory :=
      { obj := fun j => ⟨pres.diag.obj j, hp j⟩
        map := fun f => P.homMk (pres.diag.map f) }
    let t : J ⥤ CostructuredArrow P.ι X :=
      Q.toCostructuredArrow P.ι X (fun j => pres.ι.app j) (by
        intro i j f
        exact pres.w f)
    let hFinal : t.Final := by
      simpa [t, Q] using (final_of_presentation pres hp)
    let _ := hFinal
    let c : ColimitCocone (Q ⋙ F') := getColimitCocone (Q ⋙ F')
    let G : CostructuredArrow P.ι X ⥤ D :=
      CostructuredArrow.proj P.ι X ⋙ F'
    let c' : Cocone (t ⋙ G) := by
      change Cocone ((t ⋙ CostructuredArrow.proj P.ι X) ⋙ F')
      rw [Functor.toCostructuredArrow_comp_proj]
      exact c.cocone
    refine ⟨⟨(Functor.Final.extendCocone (F := t) (G := G)).obj c', ?_⟩⟩
    exact (Functor.Final.isColimitExtendCoconeEquiv t c').symm
      (by
        change IsColimit c.cocone
        exact c.isColimit)
  let Efun := P.ι.pointwiseLeftKanExtension F'
  let alpha := P.ι.pointwiseLeftKanExtensionUnit F'
  let Eext : Functor.LeftExtension P.ι F' :=
    Functor.LeftExtension.mk Efun alpha
  let hpoint : Eext.IsPointwiseLeftKanExtension :=
    Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension P.ι F'
  have preserve_one :
      ∀ {J : Type v} [SmallCategory J] [IsFiltered J]
        {K : J ⥤ C} {c : Cocone K}, IsColimit c →
          IsColimit (Efun.mapCocone c) := by
    intro J _ _ K c hc
    have hfac : ∀ d : CostructuredArrow P.ι c.pt,
        ∃ (j : J) (f : d.left.obj ⟶ K.obj j),
          f ≫ c.ι.app j = d.hom := by
      intro d
      have : IsFinitelyPresentable d.left.obj := hcompact _ d.left.property
      exact IsFinitelyPresentable.exists_hom_of_isColimit (X := d.left.obj) hc d.hom
    choose jfac ffac hffac using hfac
    have hleg_eq (s : Cocone (K ⋙ Efun))
        (d : CostructuredArrow P.ι c.pt)
        (j j' : J) (f : d.left.obj ⟶ K.obj j)
        (f' : d.left.obj ⟶ K.obj j')
        (hf : f ≫ c.ι.app j = d.hom)
        (hf' : f' ≫ c.ι.app j' = d.hom) :
        alpha.app d.left ≫ Efun.map f ≫ s.ι.app j =
          alpha.app d.left ≫ Efun.map f' ≫ s.ι.app j' := by
      let : IsFinitelyPresentable (P.ι.obj d.left) := hcompact _ d.left.property
      obtain ⟨k, u, v, huv⟩ :=
        IsFinitelyPresentable.exists_eq_of_isColimit (X := P.ι.obj d.left)
          hc f f' (hf.trans hf'.symm)
      have hu : Efun.map (K.map u) ≫ s.ι.app k = s.ι.app j := by
        simpa using s.ι.naturality u
      have hv : Efun.map (K.map v) ≫ s.ι.app k = s.ι.app j' := by
        simpa using s.ι.naturality v
      calc
        alpha.app d.left ≫ Efun.map f ≫ s.ι.app j =
            alpha.app d.left ≫ Efun.map f ≫ Efun.map (K.map u) ≫ s.ι.app k := by
              rw [← hu]
        _ = alpha.app d.left ≫ Efun.map (f ≫ K.map u) ≫ s.ι.app k := by
              simp only [Functor.map_comp, Category.assoc]
        _ = alpha.app d.left ≫ Efun.map (f' ≫ K.map v) ≫ s.ι.app k := by
              rw [huv]
        _ = alpha.app d.left ≫ Efun.map f' ≫ Efun.map (K.map v) ≫ s.ι.app k := by
              simp only [Functor.map_comp, Category.assoc]
        _ = alpha.app d.left ≫ Efun.map f' ≫ s.ι.app j' := by
              rw [hv]
    let r : (s : Cocone (K ⋙ Efun)) →
        Cocone (CostructuredArrow.proj P.ι c.pt ⋙ F') :=
      fun s =>
        { pt := s.pt
          ι :=
            { app := fun d =>
                alpha.app d.left ≫ Efun.map (ffac d) ≫ s.ι.app (jfac d)
              naturality := by
                intro d d' q
                have hq : q.left.hom ≫ ffac d' ≫ c.ι.app (jfac d') = d.hom := by
                  calc
                    q.left.hom ≫ ffac d' ≫ c.ι.app (jfac d') =
                        q.left.hom ≫ d'.hom := by rw [hffac d']
                    _ = d.hom := CostructuredArrow.w q
                have hq' :
                    (q.left.hom ≫ ffac d') ≫ c.ι.app (jfac d') = d.hom := by
                  simpa only [Category.assoc] using hq
                have heq := hleg_eq s d (jfac d) (jfac d')
                  (ffac d) (q.left.hom ≫ ffac d') (hffac d) hq'
                dsimp
                change F'.map q.left ≫
                    (alpha.app d'.left ≫ Efun.map (ffac d') ≫ s.ι.app (jfac d')) =
                  (alpha.app d.left ≫ Efun.map (ffac d) ≫ s.ι.app (jfac d)) ≫ 𝟙 s.pt
                rw [heq]
                dsimp only [Functor.const]
                simp only [Category.comp_id]
                simpa only [Functor.comp_map, ObjectProperty.ι_map, Functor.map_comp,
                  Category.assoc] using
                  congrArg
                    (fun z => z ≫ Efun.map (ffac d') ≫ s.ι.app (jfac d'))
                    (alpha.naturality q.left)
          }
        }
    let hdesc (s : Cocone (K ⋙ Efun)) : Efun.obj c.pt ⟶ s.pt :=
      (hpoint c.pt).desc (r s)
    refine
      { desc := hdesc
        fac := ?_
        uniq := ?_ }
    · intro s j
      apply (hpoint (K.obj j)).hom_ext'
      intro X f
      let d : CostructuredArrow P.ι c.pt :=
        CostructuredArrow.mk (f ≫ c.ι.app j)
      have hd : f ≫ c.ι.app j = d.hom := by rfl
      change alpha.app X ≫ Efun.map f ≫ Efun.map (c.ι.app j) ≫ hdesc s =
        alpha.app X ≫ Efun.map f ≫ s.ι.app j
      calc
        alpha.app X ≫ Efun.map f ≫ Efun.map (c.ι.app j) ≫ hdesc s =
            alpha.app X ≫ Efun.map (f ≫ c.ι.app j) ≫ hdesc s := by
              simp only [Functor.map_comp, Category.assoc]
        _ = (Eext.coconeAt c.pt).ι.app d ≫ hdesc s := by
          simp [Eext, Functor.LeftExtension.coconeAt,
            Functor.LeftExtension.mk, d, Category.assoc]
        _ = (r s).ι.app d := by
          simpa [hdesc] using (hpoint c.pt).fac (r s) d
        _ = alpha.app X ≫ Efun.map (ffac d) ≫ s.ι.app (jfac d) := by rfl
        _ = alpha.app X ≫ Efun.map f ≫ s.ι.app j := by
          exact hleg_eq s d (jfac d) j (ffac d) f (hffac d) hd
    · intro s m hm
      apply (hpoint c.pt).hom_ext'
      intro X f
      let d : CostructuredArrow P.ι c.pt :=
        CostructuredArrow.mk f
      change alpha.app X ≫ Efun.map f ≫ m =
        alpha.app X ≫ Efun.map f ≫ hdesc s
      calc
        alpha.app X ≫ Efun.map f ≫ m =
            alpha.app X ≫ Efun.map (ffac d) ≫
              Efun.map (c.ι.app (jfac d)) ≫ m := by
                change alpha.app X ≫ Efun.map d.hom ≫ m = _
                rw [← hffac d, Functor.map_comp]
                simp only [Category.assoc]
        _ = alpha.app X ≫ Efun.map (ffac d) ≫
              s.ι.app (jfac d) := by
                have hm' : Efun.map (c.ι.app (jfac d)) ≫ m =
                    s.ι.app (jfac d) := by
                  simpa using hm (jfac d)
                rw [hm']
        _ = (r s).ι.app d := by rfl
        _ = (Eext.coconeAt c.pt).ι.app d ≫ hdesc s := by
          simpa [hdesc] using (hpoint c.pt).fac (r s) d |>.symm
        _ = alpha.app X ≫ Efun.map f ≫ hdesc s := by
          simp [Eext, Functor.LeftExtension.coconeAt,
            Functor.LeftExtension.mk, d, Category.assoc]
  let hpreserve : PreservesFilteredColimitsOfSize.{v, v} Efun :=
    { preserves_filtered_colimits := fun J _ _ =>
        { preservesColimit := by
            intro K
            constructor
            intro c hc
            exact ⟨preserve_one hc⟩ } }
  let restrictionIso : P.ι ⋙ Efun ≅ F' :=
    NatIso.ofComponents (fun X => by
      have : IsIso (alpha.app X) :=
        Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isIso_hom_app
          Eext (hpoint (P.ι.obj X))
      exact (asIso (alpha.app X)).symm)
      (by
        intro X Y f
        have : IsIso (alpha.app X) := by
          change IsIso (Eext.hom.app X)
          exact Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isIso_hom_app
            Eext (hpoint (P.ι.obj X))
        have : IsIso (alpha.app Y) := by
          change IsIso (Eext.hom.app Y)
          exact Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isIso_hom_app
            Eext (hpoint (P.ι.obj Y))
        apply (cancel_mono (alpha.app Y)).1
        simp only [Functor.comp_map, ObjectProperty.ι_map, Iso.symm_hom]
        simp only [Category.assoc]
        have hNat : F'.map f ≫ alpha.app Y =
            alpha.app X ≫ Efun.map f.hom := by
          simpa only [Functor.comp_map, ObjectProperty.ι_map] using alpha.naturality f
        rw [hNat]
        simp)
  let : Efun.IsLeftKanExtension alpha := hpoint.isLeftKanExtension
  have hPointE' (E' : FilteredColimitExtension P F') :
      (Functor.LeftExtension.mk E'.functor E'.restrictionIso.inv).IsPointwiseLeftKanExtension := by
    letI : PreservesFilteredColimitsOfSize.{v, v} E'.functor :=
      E'.preservesFilteredColimits
    intro X
    apply Nonempty.some
    obtain ⟨J, _, _, pres, hp⟩ := hgenerated X
    let Q : J ⥤ P.FullSubcategory :=
      { obj := fun j => ⟨pres.diag.obj j, hp j⟩
        map := fun f => P.homMk (pres.diag.map f) }
    let t : J ⥤ CostructuredArrow P.ι X :=
      Q.toCostructuredArrow P.ι X (fun j => pres.ι.app j) (by
        intro i j f
        exact pres.w f)
    let hFinal : t.Final := by
      simpa [t, Q] using (final_of_presentation pres hp)
    let _ := hFinal
    let cE : Cocone (Q ⋙ P.ι ⋙ E'.functor) := by
      change Cocone (pres.diag ⋙ E'.functor)
      exact E'.functor.mapCocone pres.cocone
    let hcE : IsColimit cE := by
      change IsColimit (E'.functor.mapCocone pres.cocone)
      exact isColimitOfPreserves E'.functor pres.isColimit
    let e : (t ⋙ CostructuredArrow.proj P.ι X ⋙ F') ≅
        (t ⋙ CostructuredArrow.proj P.ι X ⋙ P.ι ⋙ E'.functor) :=
      NatIso.ofComponents (fun j => (E'.restrictionIso.app ((t.obj j).left)).symm)
        (by
          intro i j f
          change F'.map ((t.map f).left) ≫ E'.restrictionIso.inv.app ((t.obj j).left) =
            E'.restrictionIso.inv.app ((t.obj i).left) ≫
              (P.ι ⋙ E'.functor).map ((t.map f).left)
          exact E'.restrictionIso.inv.naturality ((t.map f).left))
    let cX :=
      (Functor.LeftExtension.mk E'.functor E'.restrictionIso.inv).coconeAt X
    exact ⟨(Functor.Final.isColimitWhiskerEquiv (F := t) cX).1
      (by
        have hc' := (IsColimit.precomposeHomEquiv e cE).symm hcE
        exact IsColimit.ofIsoColimit hc' (Cocone.ext (Iso.refl _) (by
          intro j
          simp only [Iso.refl_hom]
          simp [NatIso.ofComponents_hom_app, Cocone.precompose, Cocone.whisker, e, cE, cX,
            t, Q, Functor.LeftExtension.coconeAt])))⟩
  let E : FilteredColimitExtension P F' :=
    { functor := Efun
      preservesFilteredColimits := hpreserve
      restrictionIso := restrictionIso }
  refine ⟨E, ?_⟩
  intro E'
  let : E'.functor.IsLeftKanExtension E'.restrictionIso.inv :=
    (hPointE' E').isLeftKanExtension
  let e : Efun ≅ E'.functor :=
    Functor.leftKanExtensionUnique Efun alpha E'.functor E'.restrictionIso.inv
  have hefac : alpha ≫ Functor.whiskerLeft P.ι e.hom = E'.restrictionIso.inv := by
    simpa [e, Functor.leftKanExtensionUnique, Functor.leftKanExtensionUniqueOfIso] using
      (Functor.descOfIsLeftKanExtension_fac
        (F' := Efun) (α := alpha) E'.functor E'.restrictionIso.inv)
  have hcompat :
      Functor.isoWhiskerLeft P.ι e ≪≫ E'.restrictionIso = restrictionIso := by
    ext X
    have : IsIso (alpha.app X) :=
      Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isIso_hom_app
        Eext (hpoint (P.ι.obj X))
    apply (cancel_epi (alpha.app X)).1
    simp only [Functor.isoWhiskerLeft_hom, Iso.trans_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app]
    have hfacX : alpha.app X ≫ e.hom.app (P.ι.obj X) =
        E'.restrictionIso.inv.app X := by
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using
        NatTrans.congr_app hefac X
    have hres : restrictionIso.inv.app X = alpha.app X := by
      simp [restrictionIso, NatIso.ofComponents_inv_app]
    rw [← Category.assoc, hfacX, Iso.inv_hom_id_app, ← hres,
      Iso.inv_hom_id_app]
  refine ⟨e, ?_, ?_⟩
  · simpa [E] using hcompat
  · intro e' he'
    change Functor.isoWhiskerLeft P.ι e' ≪≫ E'.restrictionIso = restrictionIso at he'
    have hcomp :
        Functor.whiskerLeft P.ι e'.hom ≫ E'.restrictionIso.hom =
          Functor.whiskerLeft P.ι e.hom ≫ E'.restrictionIso.hom := by
      have hIso := congrArg Iso.hom (he'.trans hcompat.symm)
      simpa only [Functor.isoWhiskerLeft_hom, Iso.trans_hom] using hIso
    apply Iso.ext
    apply Functor.hom_ext_of_isLeftKanExtension Efun alpha
    apply (cancel_mono E'.restrictionIso.hom).1
    simpa only [Category.assoc] using
      congrArg (fun z => alpha ≫ z) hcomp

end

end Formalization.Books.Categories.Unit26
