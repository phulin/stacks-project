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

/-! ## Universe-polymorphic fibred morphisms -/

/- The fixed-base wrapper from Unit 33 is convenient when all categories have
   one common universe.  The textbook statement is universe-polymorphic, so
   this small raw interface keeps the strict triangle and preservation field
   without imposing that restriction. -/
structure FibredMorphism
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    (p : S ⥤ C) (q : T ⥤ C) where
  functor : S ⥤ T
  over : functor ⋙ q = p
  preserves : MapsStronglyCartesian p q functor

def IsFibredEquivalenceOverMap
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} (F : FibredMorphism p q) : Prop :=
  ∃ G : T ⥤ S,
    G ⋙ p = q ∧
      MapsStronglyCartesian q p G ∧
      (∃ e : F.functor ⋙ G ≅ 𝟭 S,
        ∃ over : (F.functor ⋙ G) ⋙ p = (𝟭 S) ⋙ p,
          IsNatIsoOver p e over) ∧
      (∃ e : G ⋙ F.functor ≅ 𝟭 T,
        ∃ over : (G ⋙ F.functor) ⋙ q = (𝟭 T) ⋙ q,
          IsNatIsoOver q e over)

theorem isFibredEquivalenceOver_iff_exists_fibredMorphism
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    (p : S ⥤ C) (q : T ⥤ C) :
    IsFibredEquivalenceOver p q ↔
      ∃ F : FibredMorphism p q, IsFibredEquivalenceOverMap F := by
  constructor
  · rintro ⟨F, G, hF, hG, hFcart, hGcart, hFG, hGF⟩
    refine ⟨{ functor := F, over := hF, preserves := hFcart }, ?_⟩
    exact ⟨G, hG, hGcart, hFG, hGF⟩
  · rintro ⟨F, hF⟩
    rcases hF with ⟨G, hG, hGcart, hFG, hGF⟩
    exact ⟨F.functor, G, F.over, hG, F.preserves, hGcart, hFG, hGF⟩

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
   fibres back to setoidness of the source fibres.

   Proof roadmap:

   1. Unpack `h` and use its forward functor to the slice.  Its strict
      equation over `C` supplies the `over` witness expected by
      `equivalence_to_fibredInSets_gives_setoidFibres`.
   2. Package the inverse functor and the vertical unit/counit isomorphisms as
      `IsEquivalenceOverFunctor`; the cartesian-preservation fields are not
      needed for the fibrewise equivalence itself.
   3. Apply `equivalence_to_fibredInSets_gives_setoidFibres` with
      `sliceProjection_isFibredInSets X` and retain its first component. -/
theorem isCategoryFibredInSetoids_of_fibredEquivalence_slice
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (X : C)
    (h : IsFibredEquivalenceOver p (Over.forget X)) :
    IsCategoryFibredInSetoids p := by
  rcases h with ⟨F, G, hF, hG, hFcart, hGcart,
    ⟨eFG, overFG, hFG⟩, ⟨eGF, overGF, hGF⟩⟩
  refine (equivalence_to_fibredInSets_gives_setoidFibres
    p (Over.forget X) F F.over ?_ (sliceProjection_isFibredInSets X)).1
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

theorem representablePresentations_are_isomorphic
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    {p : S ⥤ C}
    (h : IsRepresentableCategoryFibredInGroupoids p)
    (P Q : RepresentablePresentation p) :
    Nonempty (RepresentablePresentationIso P Q) := by
  sorry

/-! ## Fibred morphisms modulo 2-isomorphism -/

def FibredMorphismNatTrans
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    {F G : FibredMorphism p q}
    (η : F.functor ⟶ G.functor) : Prop :=
  ∀ Z : S,
    q.map (η.app Z) =
      eqToHom (congrArg (fun H : S ⥤ C => H.obj Z)
        (F.over.trans G.over.symm))

def FibredMorphismTwoIsomorphismRelation
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (F G : FibredMorphism p q) : Prop :=
  ∃ η : F.functor ⟶ G.functor,
    FibredMorphismNatTrans η ∧ IsIso η

abbrev FibredMorphismsModuloTwoIsomorphism
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    (p : S ⥤ C) (q : T ⥤ C) :=
  Quot (FibredMorphismTwoIsomorphismRelation (p := p) (q := q))

theorem fibredMorphismTwoIsomorphismRelation_isEquivalence
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} :
    Equivalence
      (FibredMorphismTwoIsomorphismRelation (p := p) (q := q)) := by
  constructor
  · intro F
    refine ⟨𝟙 F.functor, ?_, inferInstance⟩
    intro Z
    simp [FibredMorphismNatTrans]
  · intro F G hFG
    rcases hFG with ⟨η, hη, hηiso⟩
    refine ⟨inv η, ?_, inferInstance⟩
    intro Z
    rw [Functor.map_inv, hη]
    simp [FibredMorphismNatTrans]
  · intro F G K hFG hGK
    rcases hFG with ⟨η, hη, hηiso⟩
    rcases hGK with ⟨θ, hθ, hθiso⟩
    refine ⟨η ≫ θ, ?_, inferInstance⟩
    intro Z
    rw [Functor.map_comp, hη, hθ]
    simp [FibredMorphismNatTrans, Category.assoc]

/- The source's displayed equality is represented by an equivalence of the
   quotient type with the hom type in the base. -/
theorem representable_morphism_classes_equiv
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (hp : p.IsFibredInGroupoids)
    (hq : q.IsFibredInGroupoids)
    (P : RepresentablePresentation p)
    (Q : RepresentablePresentation q) :
    Nonempty
      (FibredMorphismsModuloTwoIsomorphism p q ≃
        (P.representingObject ⟶ Q.representingObject)) := by
  sorry

noncomputable def representableMorphismClassesEquiv
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (hp : p.IsFibredInGroupoids)
    (hq : q.IsFibredInGroupoids)
    (P : RepresentablePresentation p)
    (Q : RepresentablePresentation q) :
    FibredMorphismsModuloTwoIsomorphism p q ≃
      (P.representingObject ⟶ Q.representingObject) :=
  Classical.choice (representable_morphism_classes_equiv hp hq P Q)

noncomputable def fibredMorphismObjectClassMap
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (F : FibredMorphism p q) (U : C) :
    SetoidObjectClasses (Functor.Fiber p U) →
      SetoidObjectClasses (Functor.Fiber q U) :=
  objectIsoClassMap (fibreFunctor p q F.functor F.over U)

def FibredMorphismInducesRepresentingMorphismOnObjectClasses
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : RepresentablePresentation p)
    (Q : RepresentablePresentation q)
    (F : FibredMorphism p q)
    (φ : P.representingObject ⟶ Q.representingObject) : Prop :=
  ∀ U : C,
    fibredMorphismObjectClassMap Q.equivalence U ∘
        fibredMorphismObjectClassMap F U =
      fibredMorphismObjectClassMap (sliceFibredMorphism φ) U ∘
        fibredMorphismObjectClassMap P.equivalence U

theorem representable_morphism_exists_and_unique
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (hp : p.IsFibredInGroupoids)
    (hq : q.IsFibredInGroupoids)
    (P : RepresentablePresentation p)
    (Q : RepresentablePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject) :
    ∃ F : FibredMorphism p q,
      FibredMorphismInducesRepresentingMorphismOnObjectClasses P Q F φ ∧
        ∀ G : FibredMorphism p q,
          FibredMorphismInducesRepresentingMorphismOnObjectClasses P Q G φ →
            ∃! η : F.functor ⟶ G.functor,
              FibredMorphismNatTrans η ∧ IsIso η := by
  sorry

end

end Formalization.Books.Categories.Unit40
