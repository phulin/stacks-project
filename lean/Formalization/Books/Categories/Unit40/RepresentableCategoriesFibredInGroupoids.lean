import Formalization.Books.Categories.Unit39.CategoriesFibredInSetoids
import Mathlib.CategoryTheory.Equivalence

/-!
# Categories, Chapter 40: Representable categories fibred in groupoids

The source's representable fibred categories are expressed using the
universe-polymorphic fibred-equivalence interface from Units 35--37.  A
presentation records an object of the base and an equivalence with the usual
slice.  The object-class presheaf condition uses the setoid quotient from
Unit 39 and Mathlib's representability predicate for presheaves.
-/

namespace Formalization.Books.Categories.Unit40

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Functor
open Opposite
open Formalization.Books.Categories.Unit03
open Formalization.Books.Categories.Unit29
open Formalization.Books.Categories.Unit33
open Formalization.Books.Categories.Unit35
open Formalization.Books.Categories.Unit36
open Formalization.Books.Categories.Unit37
open Formalization.Books.Categories.Unit38
open Formalization.Books.Categories.Unit39

universe vC uC vS uS vT uT

noncomputable section

/-! ## The slice and representability -/

theorem sliceProjection_isFibredInGroupoids
    {C : Type uC} [Category.{vC} C] (X : C) :
    (Over.forget X).IsFibredInGroupoids := by
  exact (sliceProjection_isFibredInSets X).1

theorem sliceProjection_fibres_are_setoids
    {C : Type uC} [Category.{vC} C] (X : C) :
    ∀ U : C, IsSetoid (Functor.Fiber (Over.forget X) U) := by
  intro U
  let hdiscrete : IsDiscrete (Functor.Fiber (Over.forget X) U) :=
    (sliceProjection_isFibredInSets X).2 U
  exact ⟨((fibredInGroupoids_iff_fibred_groupoid_fibres
    (Over.forget X)).mp (sliceProjection_isFibredInSets X).1).1 U,
    fun A f => @Subsingleton.elim _ (hdiscrete.subsingleton A A) _ _⟩

theorem sliceMap_mapsStronglyCartesian
    {C : Type uC} [Category.{vC} C] {X Y : C} (f : X ⟶ Y) :
    MapsStronglyCartesian (Over.forget X) (Over.forget Y) (Over.map f) := by
  intro a b φ _hφ
  exact fibredInGroupoids_all_morphisms_stronglyCartesian
    (Over.forget Y) (sliceProjection_isFibredInSets Y).1 ((Over.map f).map φ)

def sliceFibredMorphism
    {C : Type uC} [Category.{vC} C] {X Y : C} (f : X ⟶ Y) :
    FibredMorphism (Over.forget X) (Over.forget Y) where
  functor := Over.map f
  over := Over.mapForget_eq f
  preserves := sliceMap_mapsStronglyCartesian f

/- A presentation exposes the representing object and the actual functor `j`.
   `isEquivalence` is the fixed-functor form of the existing
   `IsFibredEquivalenceOver` predicate. -/
structure RepresentablePresentation
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) where
  representingObject : C
  equivalence : FibredMorphism p (Over.forget representingObject)
  isEquivalence : IsFibredEquivalenceOverMap equivalence

/-- Forget the book-facing wrapper and expose the shared presentation used by
the universe-polymorphic 2-Yoneda infrastructure. -/
noncomputable def RepresentablePresentation.toFibredSlicePresentation
    {S C : Type*} [Category* S] [Category* C] {p : S ⥤ C}
    (P : RepresentablePresentation p) : Unit36.FibredSlicePresentation p :=
  Unit36.FibredSlicePresentation.ofEquivalenceOverMap P.representingObject
    P.equivalence P.isEquivalence

def IsRepresentableCategoryFibredInGroupoids
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) : Prop :=
  p.IsFibredInGroupoids ∧ Nonempty (RepresentablePresentation p)

theorem isRepresentable_invariant_under_fibredEquivalenceOver
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (hp : p.IsFibredInGroupoids)
    (hq : q.IsFibredInGroupoids)
    (h : IsFibredEquivalenceOver p q) :
    IsRepresentableCategoryFibredInGroupoids p ↔
      IsRepresentableCategoryFibredInGroupoids q := by
  have hsymm : IsFibredEquivalenceOver q p := by
    rcases h with ⟨F, G, hF, hG, hFcart, hGcart, hFG, hGF⟩
    exact ⟨G, F, hG, hF, hGcart, hFcart, hGF, hFG⟩
  constructor
  · rintro ⟨_, ⟨P⟩⟩
    have hP : IsFibredEquivalenceOver p
        (Over.forget P.representingObject) :=
      (isFibredEquivalenceOver_iff_exists_fibredMorphism
        p (Over.forget P.representingObject)).mpr
        ⟨P.equivalence, P.isEquivalence⟩
    have hqSlice : IsFibredEquivalenceOver q
        (Over.forget P.representingObject) :=
      isFibredEquivalenceOver_trans hsymm hP
    obtain ⟨F, hF⟩ :=
      (isFibredEquivalenceOver_iff_exists_fibredMorphism
        q (Over.forget P.representingObject)).mp hqSlice
    exact ⟨hq, ⟨{
      representingObject := P.representingObject
      equivalence := F
      isEquivalence := hF }⟩⟩
  · rintro ⟨_, ⟨Q⟩⟩
    have hQ : IsFibredEquivalenceOver q
        (Over.forget Q.representingObject) :=
      (isFibredEquivalenceOver_iff_exists_fibredMorphism
        q (Over.forget Q.representingObject)).mpr
        ⟨Q.equivalence, Q.isEquivalence⟩
    have hpSlice : IsFibredEquivalenceOver p
        (Over.forget Q.representingObject) :=
      isFibredEquivalenceOver_trans h hQ
    obtain ⟨F, hF⟩ :=
      (isFibredEquivalenceOver_iff_exists_fibredMorphism
        p (Over.forget Q.representingObject)).mp hpSlice
    exact ⟨hp, ⟨{
      representingObject := Q.representingObject
      equivalence := F
      isEquivalence := hF }⟩⟩

theorem isRepresentableCategoryFibredInGroupoids_iff_exists_slice_equivalence
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) :
    IsRepresentableCategoryFibredInGroupoids p ↔
      p.IsFibredInGroupoids ∧
        ∃ X : C, IsFibredEquivalenceOver p (Over.forget X) := by
  constructor
  · rintro ⟨hp, ⟨P⟩⟩
    refine ⟨hp, P.representingObject, ?_⟩
    exact (isFibredEquivalenceOver_iff_exists_fibredMorphism
      p (Over.forget P.representingObject)).mpr
      ⟨P.equivalence, P.isEquivalence⟩
  · rintro ⟨hp, X, hX⟩
    obtain ⟨F, hF⟩ :=
      (isFibredEquivalenceOver_iff_exists_fibredMorphism
        p (Over.forget X)).mp hX
    exact ⟨hp, ⟨{ representingObject := X, equivalence := F, isEquivalence := hF }⟩⟩

/-! ## The object-class presheaf characterization -/

/- Unit 39 chooses the presheaf whose value at `U` is the set of isomorphism
   classes in the fibre over `U`.  Keeping its setoid-fibre hypothesis
   explicit makes the source's two conjuncts a dependent existential. -/
noncomputable def objectClassPresheaf
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSetoids p) :
    Cᵒᵖ ⥤ Type uS :=
  fibredSetoidObjectPresheaf p hp

def IsRepresentableObjectClassPresheaf
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSetoids p) 
    : Prop :=
  Functor.IsRepresentable (objectClassPresheaf p hp)

def HasRepresentableObjectClassPresheaf
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) : Prop :=
  ∃ hp : IsCategoryFibredInSetoids p,
    IsRepresentableObjectClassPresheaf p hp

theorem objectClassPresheaf_obj_equiv
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSetoids p) (U : C) :
    Nonempty
      ((objectClassPresheaf p hp).obj (Opposite.op U) ≃
        SetoidObjectClasses (Functor.Fiber p U)) := by
  exact fibredSetoidObjectPresheaf_obj_equiv p hp U

/- A fibred equivalence to a slice transports the discreteness of the slice
fibres back to setoidness of the source fibres. -/
theorem isCategoryFibredInSetoids_of_fibredEquivalence_slice
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (X : C)
    (h : IsFibredEquivalenceOver p (Over.forget X)) :
    IsCategoryFibredInSetoids p := by
  rcases h with ⟨F, G, hF, hG, hFcart, hGcart,
    ⟨eFG, overFG, hFG⟩, ⟨eGF, overGF, hGF⟩⟩
  refine (equivalence_to_fibredInSets_gives_setoidFibres
    p (Over.forget X) F hF ?_ (sliceProjection_isFibredInSets X)).1
  exact ⟨G, hF, hG, ⟨eFG, overFG, hFG⟩, ⟨eGF, overGF, hGF⟩⟩

theorem isRepresentableCategoryFibredInGroupoids_iff_setoid_and_objectClassPresheaf
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) :
    IsRepresentableCategoryFibredInGroupoids p ↔
      HasRepresentableObjectClassPresheaf p := by
  rw [isRepresentableCategoryFibredInGroupoids_iff_exists_slice_equivalence]
  constructor
  · rintro ⟨_, X, hX⟩
    let hp := isCategoryFibredInSetoids_of_fibredEquivalence_slice p X hX
    refine ⟨hp, ?_⟩
    exact (fibredSetoidObjectPresheaf_isRepresentable_iff_exists_slice
      p hp).2 ⟨X, hX⟩
  · rintro ⟨hp, hrep⟩
    refine ⟨hp.1, ?_⟩
    exact (fibredSetoidObjectPresheaf_isRepresentable_iff_exists_slice
      p hp).1 hrep

/- An isomorphism of presentations includes the base-object isomorphism and
   a vertical comparison after transporting one slice along it. -/
structure RepresentablePresentationIso
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    {p : S ⥤ C}
    (P Q : RepresentablePresentation p) where
  objectIso : P.representingObject ≅ Q.representingObject
  comparison :
    ∃ e : (P.equivalence.functor ⋙
        (sliceFibredMorphism objectIso.hom).functor) ≅
      Q.equivalence.functor,
      ∃ h :
          (P.equivalence.functor ⋙
              (sliceFibredMorphism objectIso.hom).functor) ⋙
            Over.forget Q.representingObject =
          Q.equivalence.functor ⋙ Over.forget Q.representingObject,
        IsNatIsoOver (Over.forget Q.representingObject) e h

private theorem slice_functor_over_isomorphic_to_map
    {C : Type uC} [Category.{vC} C] {X Y : C}
    (F : Over X ⥤ Over Y)
    (hF : F ⋙ Over.forget Y = Over.forget X) :
    ∃ f : X ⟶ Y, ∃ e : F ≅ Over.map f,
      ∃ over : F ⋙ Over.forget Y = (Over.map f) ⋙ Over.forget Y,
        IsNatIsoOver (Over.forget Y) e over := by
  let hobj : ∀ U : Over X, (F.obj U).left = U.left := fun U =>
    Functor.congr_obj hF U
  let f : X ⟶ Y :=
    eqToHom (hobj (Over.mk (𝟙 X))).symm ≫
      (F.obj (Over.mk (𝟙 X))).hom
  let eapp : ∀ U : Over X, F.obj U ≅ (Over.map f).obj U := fun U => by
    refine Over.isoMk (eqToIso (hobj U)) ?_
    let u : U ⟶ Over.mk (𝟙 X) := Over.homMk U.hom
    have hu := Functor.congr_hom hF u
    change (F.map u).left =
      eqToHom (hobj U) ≫ u.left ≫
        eqToHom (hobj (Over.mk (𝟙 X))).symm at hu
    rw [← Over.w (F.map u), hu]
    dsimp [f, u]
    simp [Category.assoc]
  let e : F ≅ Over.map f := NatIso.ofComponents eapp (by
    intro U V k
    apply (Over.forget Y).map_injective
    have hk := Functor.congr_hom hF k
    change (F.map k).left =
      eqToHom (hobj U) ≫ k.left ≫ eqToHom (hobj V).symm at hk
    change (F.map k).left ≫ eqToHom (hobj V) =
      eqToHom (hobj U) ≫ k.left
    rw [hk]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
  let over : F ⋙ Over.forget Y = (Over.map f) ⋙ Over.forget Y :=
    hF.trans (Over.mapForget_eq f).symm
  refine ⟨f, e, over, ?_⟩
  intro U
  change (eapp U).hom.left =
    eqToHom (congrArg (fun L : Over X ⥤ C => L.obj U) over)
  dsimp [e, eapp, over, hobj]
  simp

private theorem slice_map_isIso_of_isEquivalence
    {C : Type uC} [Category.{vC} C] {X Y : C} (f : X ⟶ Y)
    [hF : (Over.map f).IsEquivalence] : IsIso f := by
  let hmono : Mono f := by
    constructor
    intro Z a b hab
    let A : Over X := Over.mk a
    let B : Over X := Over.mk b
    let m : (Over.map f).obj A ⟶ (Over.map f).obj B :=
      Over.homMk (𝟙 Z) (by simpa [A, B] using hab.symm)
    obtain ⟨k, hk⟩ := (Functor.Full.map_surjective m)
    have hkleft : k.left = 𝟙 Z := by
      have hkl := congrArg CommaMorphism.left hk
      simpa [m] using hkl
    simpa [A, B, hkleft] using (Over.w k).symm
  let : Mono f := hmono
  obtain ⟨U, ⟨e⟩⟩ :=
    Functor.EssSurj.mem_essImage (F := Over.map f) (Over.mk (𝟙 Y))
  let : IsIso e.hom.left := by
    change IsIso ((Over.forget Y).map e.hom)
    infer_instance
  let g : Y ⟶ X := inv e.hom.left ≫ U.hom
  have hgf : g ≫ f = 𝟙 Y := by
    have he := Over.w e.hom
    dsimp [g]
    simpa [Category.assoc] using congrArg (fun t => inv e.hom.left ≫ t) he.symm
  have hfg : f ≫ g = 𝟙 X := by
    apply (cancel_mono f).1
    simp [g, hgf, Category.assoc]
  exact ⟨⟨g, hfg, hgf⟩⟩

private theorem isNatIsoOver_comp
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (q : B ⥤ D) {F G K : A ⥤ B}
    (e : F ≅ G) (over : F ⋙ q = G ⋙ q)
    (h : IsNatIsoOver q e over)
    (e' : G ≅ K) (over' : G ⋙ q = K ⋙ q)
    (h' : IsNatIsoOver q e' over') :
    IsNatIsoOver q (e ≪≫ e') (over.trans over') := by
  intro Z
  change q.map (e.hom.app Z ≫ e'.hom.app Z) = _
  rw [Functor.map_comp]
  rw [h Z, h' Z]
  simp only [eqToHom_trans]

private theorem isNatIsoOver_whiskerLeft
    {A B D E : Type*} [Category* A] [Category* B]
      [Category* D] [Category* E]
    (q : B ⥤ D) {F G : A ⥤ B} (e : F ≅ G)
    (over : F ⋙ q = G ⋙ q) (h : IsNatIsoOver q e over)
      (L : E ⥤ A) :
    IsNatIsoOver q (Functor.isoWhiskerLeft L e)
      ((Functor.assoc L F q).trans
        ((congrArg (fun K : A ⥤ D => L ⋙ K) over).trans
          (Functor.assoc L G q).symm)) := by
  intro Z
  change q.map (e.hom.app (L.obj Z)) = _
  simpa only [eqToHom_trans] using h (L.obj Z)

private theorem isNatIsoOver_symm
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (q : B ⥤ D) {F G : A ⥤ B} (e : F ≅ G)
    (over : F ⋙ q = G ⋙ q) (h : IsNatIsoOver q e over) :
    IsNatIsoOver q e.symm over.symm := by
  intro Z
  apply (cancel_mono (q.map (e.hom.app Z))).1
  rw [← q.map_comp]
  simp [h Z]

theorem representablePresentations_are_isomorphic
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    {p : S ⥤ C}
    (_h : IsRepresentableCategoryFibredInGroupoids p)
    (P Q : RepresentablePresentation p) :
    Nonempty (RepresentablePresentationIso P Q) := by
  rcases P.isEquivalence with
    ⟨P_inv, ⟨P_unit, P_unit_over, hP_unit⟩,
      ⟨P_counit, P_counit_over, hP_counit⟩⟩
  rcases Q.isEquivalence with
    ⟨Q_inv, ⟨Q_unit, Q_unit_over, hQ_unit⟩,
      ⟨Q_counit, Q_counit_over, hQ_counit⟩⟩
  let : P.equivalence.functor.IsEquivalence :=
    Functor.IsEquivalence.mk' P_inv.functor P_unit.symm P_counit
  let : P_inv.functor.IsEquivalence :=
    Functor.IsEquivalence.mk' P.equivalence.functor
      P_counit.symm P_unit
  let : Q.equivalence.functor.IsEquivalence :=
    Functor.IsEquivalence.mk' Q_inv.functor Q_unit.symm Q_counit
  let H : Over P.representingObject ⥤ Over Q.representingObject :=
    P_inv.functor ⋙ Q.equivalence.functor
  have hH : H ⋙ Over.forget Q.representingObject =
      Over.forget P.representingObject := by
    dsimp [H]
    rw [Functor.assoc, Q.equivalence.over, P_inv.over]
  let : H.IsEquivalence := inferInstance
  obtain ⟨f, e, over, he⟩ :=
    slice_functor_over_isomorphic_to_map H hH
  let : (Over.map f).Faithful := Functor.Faithful.of_iso e
  let : (Over.map f).Full := Functor.Full.of_iso e
  let : (Over.map f).EssSurj := Functor.essSurj_of_iso e
  let : (Over.map f).IsEquivalence :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  let : IsIso f := slice_map_isIso_of_isEquivalence f
  let objectIso : P.representingObject ≅ Q.representingObject :=
    ⟨f, inv f, IsIso.hom_inv_id f, IsIso.inv_hom_id f⟩
  let ePQ : P.equivalence.functor ⋙ H ≅ Q.equivalence.functor :=
    (Functor.associator P.equivalence.functor P_inv.functor
      Q.equivalence.functor).symm ≪≫
      Functor.isoWhiskerRight P_unit Q.equivalence.functor ≪≫
      Functor.leftUnitor Q.equivalence.functor
  let comparison' :
      P.equivalence.functor ⋙ Over.map f ≅ Q.equivalence.functor :=
    (Functor.isoWhiskerLeft P.equivalence.functor e).symm ≪≫ ePQ
  let overComparison' :
      (P.equivalence.functor ⋙ Over.map f) ⋙
          Over.forget Q.representingObject =
      Q.equivalence.functor ⋙ Over.forget Q.representingObject := by
    rw [Functor.assoc, Over.mapForget_eq, P.equivalence.over,
      Q.equivalence.over]
  let overPQ :
      (P.equivalence.functor ⋙ H) ⋙
          Over.forget Q.representingObject =
        Q.equivalence.functor ⋙ Over.forget Q.representingObject := by
    dsimp [H]
    calc
      (P.equivalence.functor ⋙ (P_inv.functor ⋙ Q.equivalence.functor)) ⋙
          Over.forget Q.representingObject =
          (P.equivalence.functor ⋙ P_inv.functor) ⋙
            (Q.equivalence.functor ⋙ Over.forget Q.representingObject) := by
        simp [Functor.assoc]
      _ = (P.equivalence.functor ⋙ P_inv.functor) ⋙ p := by
        rw [Q.equivalence.over]
      _ = (𝟭 S) ⋙ p := P_unit_over
      _ = (𝟭 S) ⋙ (Q.equivalence.functor ⋙
          Over.forget Q.representingObject) := by
        rw [Q.equivalence.over]
      _ = Q.equivalence.functor ⋙ Over.forget Q.representingObject := by
        rw [Functor.id_comp]
  let hcomparison' : IsNatIsoOver (Over.forget Q.representingObject)
      comparison' overComparison' := by
    have hE := isNatIsoOver_whiskerLeft
      (Over.forget Q.representingObject) e over he P.equivalence.functor
    have hE' := isNatIsoOver_symm
      (Over.forget Q.representingObject)
      (Functor.isoWhiskerLeft P.equivalence.functor e)
      ((Functor.assoc _ _ _).trans
        ((congrArg (fun K : Over P.representingObject ⥤ C =>
          P.equivalence.functor ⋙ K) over).trans
          (Functor.assoc _ _ _).symm)) hE
    have hPQ : IsNatIsoOver (Over.forget Q.representingObject)
        ePQ overPQ := by
      intro Z
      dsimp [ePQ, overPQ]
      dsimp [H]
      simp only [Category.id_comp, Category.comp_id]
      have hQ_obj (X : S) :
          (Q.equivalence.functor.obj X).left = p.obj X := by
        simpa only [Functor.comp_obj, Over.forget_obj] using
          Functor.congr_obj Q.equivalence.over X
      have hQmap :
          Over.Hom.left (Q.equivalence.functor.map (P_unit.hom.app Z)) =
            eqToHom (hQ_obj ((P.equivalence.functor ⋙ P_inv.functor).obj Z)) ≫
              p.map (P_unit.hom.app Z) ≫
                eqToHom (hQ_obj ((𝟭 S).obj Z)).symm := by
        have hQmap := Functor.congr_hom Q.equivalence.over
          (P_unit.hom.app Z)
        simpa only [Functor.comp_map, Over.forget_map, Functor.comp_obj,
          Over.forget_obj] using hQmap
      rw [hQmap, hP_unit Z]
      simp [eqToHom_trans]
    have hcomp := isNatIsoOver_comp
      (Over.forget Q.representingObject)
      (Functor.isoWhiskerLeft P.equivalence.functor e).symm _ hE'
      ePQ overPQ hPQ
    simpa [comparison', overComparison'] using hcomp
  refine ⟨{
    objectIso := objectIso
    comparison := ⟨by simpa [objectIso, sliceFibredMorphism] using comparison',
      by simpa [objectIso, sliceFibredMorphism] using overComparison', ?_⟩ }⟩
  change ∀ Z : S, _
  intro Z
  simpa [objectIso, sliceFibredMorphism] using hcomparison' Z

/-- The represented 2-Yoneda equivalence, obtained directly from the shared
universe-polymorphic presentation and quotient infrastructure in Unit 36. -/
theorem representable_morphism_classes_equiv
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : RepresentablePresentation p)
    (Q : RepresentablePresentation q) :
    Nonempty
      (FibredMorphismsModuloTwoIsomorphism p q ≃
        (P.representingObject ⟶ Q.representingObject)) := by
  exact ⟨Unit36.fibredSliceMorphismClassesEquiv
    P.toFibredSlicePresentation Q.toFibredSlicePresentation
    (fun φ => sliceMap_mapsStronglyCartesian φ)⟩

noncomputable def representableMorphismClassesEquiv
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : RepresentablePresentation p)
    (Q : RepresentablePresentation q) :
    FibredMorphismsModuloTwoIsomorphism p q ≃
      (P.representingObject ⟶ Q.representingObject) :=
  Classical.choice (representable_morphism_classes_equiv P Q)

def FibredMorphismInducesRepresentingMorphismOnObjectClasses
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : RepresentablePresentation p)
    (Q : RepresentablePresentation q)
    (F : FibredMorphism p q)
    (φ : P.representingObject ⟶ Q.representingObject) : Prop :=
  Unit36.FibredMorphismInducesRepresentingMorphismOnObjectClasses
    P.toFibredSlicePresentation Q.toFibredSlicePresentation
      (fun ψ => sliceMap_mapsStronglyCartesian ψ) F φ

/-- Existence and uniqueness follow from the shared presentation theorem in
Unit 36.  The target fibres are thin because `Q` identifies `q` with a slice;
Unit 39 transfers that property across the equivalence. -/
theorem representable_morphism_exists_and_unique
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : RepresentablePresentation p)
    (Q : RepresentablePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject) :
    ∃ F : FibredMorphism p q,
      FibredMorphismInducesRepresentingMorphismOnObjectClasses P Q F φ ∧
        ∀ G : FibredMorphism p q,
          FibredMorphismInducesRepresentingMorphismOnObjectClasses P Q G φ →
            ∃! η : F.functor ⟶ G.functor,
              FibredMorphismNatTrans η ∧ IsIso η := by
  let P' := P.toFibredSlicePresentation
  let Q' := Q.toFibredSlicePresentation
  obtain ⟨Qinv, ⟨Qunit, QunitOver, hQunit⟩,
    ⟨Qcounit, QcounitOver, hQcounit⟩⟩ := Q.isEquivalence
  have hQ : IsEquivalenceOverFunctor q
      (Over.forget Q.representingObject) Q.equivalence.functor :=
    ⟨Qinv.functor, Q.equivalence.over, Qinv.over,
      ⟨Qunit, QunitOver, hQunit⟩, ⟨Qcounit, QcounitOver, hQcounit⟩⟩
  have hqSetoid : IsCategoryFibredInSetoids q :=
    (equivalence_to_fibredInSets_gives_setoidFibres q
      (Over.forget Q.representingObject) Q.equivalence.functor
      Q.equivalence.over hQ
      (sliceProjection_isFibredInSets Q.representingObject)).1
  have hhom : ∀ (U : C) (X Y : Functor.Fiber q U),
      Subsingleton (X ⟶ Y) := fun U X Y =>
    (isSetoid_iff_isGroupoid_and_hom_subsingleton.mp (hqSetoid.2 U)).2 X Y
  exact Unit36.fibredSlicePresentation_morphism_existsAndUnique P' Q'
    (fun ψ => sliceMap_mapsStronglyCartesian ψ) hhom φ

end

end Formalization.Books.Categories.Unit40
