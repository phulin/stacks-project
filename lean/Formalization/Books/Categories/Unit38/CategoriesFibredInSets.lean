import Formalization.Books.Categories.Unit03.Opposite
import Formalization.Books.Categories.Unit37.PresheavesOfGroupoids
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Groupoid.Discrete

/-!
# Categories, Chapter 38: Categories fibred in sets

The source's discrete fibres are Mathlib's `IsDiscrete` categories.  The
category associated to a set-valued presheaf is the existing
CoGrothendieck construction from Units 36 and 37, specialized to the
canonical discrete category on each value of the presheaf.
-/

namespace Formalization.Books.Categories.Unit38

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Functor
open CategoryTheory.ObjectProperty
open Opposite
open Formalization.Books.Categories.Unit03
open Formalization.Books.Categories.Unit29
open Formalization.Books.Categories.Unit30
open Formalization.Books.Categories.Unit31
open Formalization.Books.Categories.Unit32
open Formalization.Books.Categories.Unit33
open Formalization.Books.Categories.Unit35
open Formalization.Books.Categories.Unit36
open Formalization.Books.Categories.Unit37

universe vC uC vS uS u₁ v₁ v u

noncomputable section

/-! ## Discrete fibres -/

/- Mathlib's `IsDiscrete` is exactly the source definition: a morphism forces
   its endpoints to be equal, and every hom type is subsingleton.  We use it
   directly below instead of introducing a parallel predicate. -/

theorem isDiscrete_iff_every_morphism_is_eqToHom
    {C : Type*} [Category* C] :
    IsDiscrete C ↔
      ∀ {X Y : C} (f : X ⟶ Y), ∃ h : X = Y, f = eqToHom h := by
  constructor
  · intro h X Y f
    exact ⟨h.eq_of_hom f, @Subsingleton.elim _ (h.subsingleton X Y) _ _⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro X Y
      constructor
      intro f g
      rcases h f with ⟨hf, hff⟩
      rcases h g with ⟨hg, hgg⟩
      rw [hff, hgg]
    · intro X Y f
      exact (h f).choose

/-- A functor is a category fibred in sets when it is fibred in groupoids and
all its fibre categories are discrete. -/
def IsCategoryFibredInSets
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) : Prop :=
  p.IsFibredInGroupoids ∧
    ∀ U : C, IsDiscrete (Functor.Fiber p U)

theorem isCategoryFibredInSets_iff_isFibered_and_discreteFibres
    {S C : Type*} [Category* S] [Category* C] (p : S ⥤ C) :
    IsCategoryFibredInSets p ↔
      p.IsFibered ∧ ∀ U : C, IsDiscrete (Functor.Fiber p U) := by
  constructor
  · rintro ⟨hp, hdiscrete⟩
    have h := (fibredInGroupoids_iff_fibred_groupoid_fibres p).mp hp
    exact ⟨h.2, hdiscrete⟩
  · rintro ⟨hfibred, hdiscrete⟩
    refine ⟨(fibredInGroupoids_iff_fibred_groupoid_fibres p).mpr ?_, hdiscrete⟩
    exact ⟨fun U => by
      refine ⟨fun {X Y} f => ?_⟩
      have hf : f = eqToHom ((hdiscrete U).eq_of_hom f) :=
        @Subsingleton.elim _ ((hdiscrete U).subsingleton X Y) _ _
      rw [hf]
      infer_instance, hfibred⟩

/-! ## The fixed-base 2-category -/

/-- The object property selecting categories fibred in sets in the fixed-base
fibred-category interface from Unit 33. -/
def IsDiscreteFibredCategoryOver {C : Cat.{v, u}}
    (X : FibredCategoryOver C) : Prop :=
  ∀ U : C, IsDiscrete (Functor.Fiber (structureFunctor X.underlying) U)

def categoriesFibredInSetsObjectProperty {C : Cat.{v, u}} :
    ObjectProperty (FibredCategoryOver C) :=
  IsDiscreteFibredCategoryOver

theorem discreteFibredCategoryOver_isCategoryFibredInSets
    {C : Cat.{v, u}} (X : FibredCategoryOver C)
    (hX : IsDiscreteFibredCategoryOver X) :
    IsCategoryFibredInSets (structureFunctor X.underlying) := by
  exact (isCategoryFibredInSets_iff_isFibered_and_discreteFibres _).mpr
    ⟨inferInstance, hX⟩

/-- The source's 2-category of categories fibred in sets over a fixed base. -/
abbrev CategoriesFibredInSetsOver (C : Cat.{v, u}) :=
  FullSubTwoCategory (FibredCategoryOver C)
    (categoriesFibredInSetsObjectProperty (C := C))

/- A functor over the base automatically preserves strongly cartesian arrows
when its target has discrete fibres: all arrows in a category fibred in
groupoids are strongly cartesian. -/
theorem mapsStronglyCartesian_to_discreteFibred
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsDiscreteFibredCategoryOver Y)
    (F : CategoryOverHom X.underlying Y.underlying) :
    MapsStronglyCartesian
      (structureFunctor X.underlying) (structureFunctor Y.underlying)
      (overFunctor F) := by
  intro a b φ _hφ
  exact fibredInGroupoids_all_morphisms_stronglyCartesian
    (structureFunctor Y.underlying)
    (discreteFibredCategoryOver_isCategoryFibredInSets Y hY).1
    ((overFunctor F).map φ)

/- A vertical natural transformation between functors into a discrete fibre
   is automatically invertible.  This is the source's observation that the
   fixed-base 2-category is in fact a (2, 1)-category. -/
theorem discreteFibredCategoryOver_two_morphism_isIso
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsDiscreteFibredCategoryOver Y)
    {F G : FibredCategoryOverHom X Y} (η : F ⟶ G) : IsIso η := by
  have hη : IsIso η.toNatTrans := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Z
    let U := (structureFunctor X.underlying).obj Z
    let z : Functor.Fiber (structureFunctor X.underlying) U := ⟨Z, rfl⟩
    let _ : IsDiscrete (Functor.Fiber (structureFunctor Y.underlying) U) := hY U
    change IsIso (Functor.Fiber.fiberInclusion.map
      ((overMorphismFiberNatTrans η U).app z))
    infer_instance
  let e : overFunctor F.underlying ≅ overFunctor G.underlying :=
    { hom := η.toNatTrans
      inv := inv η.toNatTrans
      hom_inv_id := by simp
      inv_hom_id := by simp }
  let E : F.underlying ≅ G.underlying :=
    overNatIsoOfUnderlying e (by
      intro Z
      exact η.over Z)
  let E' : F ≅ G := fibredHomIsoOfUnderlying E
  have hE : E'.hom = η := by
    apply OverNatTrans.ext
    rfl
  rw [← hE]
  infer_instance

/- The stronger locally-discrete form records the source's assertion that a
   vertical 2-morphism is an identity after identifying its source and target
   1-morphisms. -/
theorem discreteFibredCategoryOver_two_morphism_is_eqToHom
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsDiscreteFibredCategoryOver Y)
    {F G : FibredCategoryOverHom X Y} (η : F ⟶ G) :
    ∃ h : F = G, η = eqToHom h := by
  have hη : IsIso η.toNatTrans := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Z
    let U := (structureFunctor X.underlying).obj Z
    let z : Functor.Fiber (structureFunctor X.underlying) U := ⟨Z, rfl⟩
    let _ : IsDiscrete (Functor.Fiber (structureFunctor Y.underlying) U) := hY U
    change IsIso (Functor.Fiber.fiberInclusion.map
      ((overMorphismFiberNatTrans η U).app z))
    infer_instance
  let _ : IsIso η.toNatTrans := hη
  let e : overFunctor F.underlying ≅ overFunctor G.underlying :=
    { hom := η.toNatTrans
      inv := inv η.toNatTrans
      hom_inv_id := by simp
      inv_hom_id := by simp }
  have hobj : ∀ Z, (overFunctor F.underlying).obj Z =
      (overFunctor G.underlying).obj Z := by
    intro Z
    let U := (structureFunctor X.underlying).obj Z
    let z : Functor.Fiber (structureFunctor X.underlying) U := ⟨Z, rfl⟩
    let α := (overMorphismFiberNatTrans η U).app z
    have hα := (hY U).eq_of_hom α
    exact congrArg (fun q : Functor.Fiber (structureFunctor Y.underlying) U => q.1) hα
  have happ : ∀ Z, η.toNatTrans.app Z = eqToHom (hobj Z) := by
    intro Z
    let U := (structureFunctor X.underlying).obj Z
    let z : Functor.Fiber (structureFunctor X.underlying) U := ⟨Z, rfl⟩
    let α := (overMorphismFiberNatTrans η U).app z
    have hα := (hY U).eq_of_hom α
    have hαhom : α = eqToHom hα := by
      exact @Subsingleton.elim _ ((hY U).subsingleton _ _) _ _
    have hαmap := congrArg (Functor.Fiber.fiberInclusion.map) hαhom
    have hm := CategoryTheory.eqToHom_map
      (Functor.Fiber.fiberInclusion
        (p := structureFunctor Y.underlying) (S := U)) hα
    calc
      η.toNatTrans.app Z = Functor.Fiber.fiberInclusion.map α := by rfl
      _ = Functor.Fiber.fiberInclusion.map (eqToHom hα) := hαmap
      _ = eqToHom
          (congrArg
            (fun q : Functor.Fiber (structureFunctor Y.underlying) U => q.1) hα) := hm
      _ = eqToHom (hobj Z) := by congr 1
  have heq : overFunctor F.underlying = overFunctor G.underlying :=
    Functor.ext_of_iso e hobj (happ := happ)
  have hleft : F.underlying.leftHom = G.underlying.leftHom := by
    apply Cat.Hom.ext
    exact heq
  have hunder : F.underlying = G.underlying := by
    apply CategoryOver.Hom.ext
    apply Over.OverMorphism.ext
    exact hleft
  have h : F = G := FibredCategoryOverHom.ext hunder
  refine ⟨h, ?_⟩
  cases h
  apply OverNatTrans.ext
  apply NatTrans.ext
  funext Z
  simpa using happ Z

/-- The source-facing constructor for a 1-morphism over the base; the
preservation field is automatic for a discrete-fibred target. -/
def fibredCategoryOverHomOfDiscrete
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsDiscreteFibredCategoryOver Y)
    (F : CategoryOverHom X.underlying Y.underlying) :
    FibredCategoryOverHom X Y where
  underlying := F
  preserves := mapsStronglyCartesian_to_discreteFibred hY F

/-- The 2-morphisms in the fixed-base 2-category are identities, expressed as
local discreteness of all its hom-categories. -/
theorem categoriesFibredInSetsOver_is_locallyDiscrete
    (C : Cat.{v, u}) :
    Bicategory.IsLocallyDiscrete (CategoriesFibredInSetsOver C) := by
  intro X Y
  apply (isDiscrete_iff_every_morphism_is_eqToHom).mpr
  intro F G η
  rcases discreteFibredCategoryOver_two_morphism_is_eqToHom
      (X := X.obj) (Y := Y.obj) Y.property η.hom with ⟨h, hη⟩
  have h' : F = G := Bicategory.InducedBicategory.hom_ext h
  refine ⟨h', ?_⟩
  apply Bicategory.InducedBicategory.hom₂_ext
  exact hη

theorem categoriesFibredInSetsOver_is_two_one_category
    (C : Cat.{v, u}) :
    IsTwoOneCategory (CategoriesFibredInSetsOver C) := by
  intro X Y
  let _ : IsDiscrete (X ⟶ Y) := categoriesFibredInSetsOver_is_locallyDiscrete C X Y
  infer_instance

/-! ## 2-fibre products -/

/-- The Unit 35 two-fibre product package with the additional assertion that
all fibres of its apex are discrete. -/
structure FibredInSetsTwoFibreProduct
    {C : Cat.{v, u}} {X Y S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) where
  product : FibredTwoFibreProduct.{u₁, v₁, v, u} F G
  fibres_are_discrete : ∀ U : C,
    IsDiscrete (Functor.Fiber product.diagram.base U)

theorem fibredInSetsTwoFibreProduct_apex_isCategoryFibredInSets
    {C : Cat.{v, u}} {X Y S : FibredCategoryOver C}
    {F : FibredCategoryOverHom X S} {G : FibredCategoryOverHom Y S}
    (P : FibredInSetsTwoFibreProduct F G) :
    IsCategoryFibredInSets P.product.diagram.base := by
  exact (isCategoryFibredInSets_iff_isFibered_and_discreteFibres _).mpr
    ⟨P.product.apex_fibred, P.fibres_are_discrete⟩

private lemma categoriesFibredInSets_stronglyCartesian_map_of
    {X C : Type*} [Category* X] [Category* C]
    {p : X ⥤ C} {R S : C} {a b : X}
    (f : R ⟶ S) (φ : a ⟶ b)
    (h : p.IsStronglyCartesian f φ) :
    p.IsStronglyCartesian (p.map φ) φ := by
  let : p.IsStronglyCartesian f φ := h
  refine { toIsHomLift := ?_, universal_property' := ?_ }
  · exact Functor.IsHomLift.map _
  · intro c g τ hτ
    let : p.IsHomLift (g ≫ p.map φ) τ := hτ
    let hdom := CategoryTheory.IsHomLift.domain_eq p f φ
    let hcod := CategoryTheory.IsHomLift.codomain_eq p f φ
    let g' : p.obj c ⟶ R := g ≫ eqToHom hdom
    have hφmap : p.map φ = eqToHom hdom ≫ f ≫ eqToHom hcod.symm :=
      CategoryTheory.IsHomLift.fac' p f φ
    have hτmap : p.map τ = g ≫ p.map φ := by
      simpa using CategoryTheory.IsHomLift.fac' p (g ≫ p.map φ) τ
    have hτ' : p.IsHomLift (g' ≫ f) τ := by
      apply CategoryTheory.IsHomLift.of_fac' p (g' ≫ f) τ rfl hcod
      rw [hτmap, hφmap]
      simp [g', Category.assoc]
    let : p.IsHomLift (g' ≫ f) τ := hτ'
    obtain ⟨χ, ⟨hχ, hχfac⟩, hχuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property p f φ g'
        (g' ≫ f) rfl τ
    have hχg : p.IsHomLift g χ := by
      apply CategoryTheory.IsHomLift.of_fac' p g χ rfl rfl
      have h := CategoryTheory.IsHomLift.fac' p g' χ
      dsimp [g'] at h
      simpa [Category.assoc] using h
    refine ⟨χ, ⟨hχg, hχfac⟩, ?_⟩
    intro χ' hχ'
    let : p.IsHomLift g χ' := hχ'.1
    have hχ'base : p.IsHomLift g' χ' := by
      apply CategoryTheory.IsHomLift.of_fac' p g' χ' rfl hdom
      have h := CategoryTheory.IsHomLift.fac' p g χ'
      dsimp [g']
      simpa [Category.assoc] using h
    exact hχuniq χ' ⟨hχ'base, hχ'.2⟩

theorem categoriesFibredInSets_have_twoFibreProducts
    {C : Cat.{v, u}} (X Y S : FibredCategoryOver C)
    (hX : IsDiscreteFibredCategoryOver X)
    (hY : IsDiscreteFibredCategoryOver Y)
    (hS : IsDiscreteFibredCategoryOver S)
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) :
    Nonempty (FibredInSetsTwoFibreProduct F G) := by
  let D := twoFibreProductOverDiagram F.underlying G.underlying
  let product : FibredTwoFibreProduct F G :=
    { diagram := D
      apex_fibred := by
        refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
        intro ξ R f
        rcases ξ.property with ⟨U, hX, hY, hξ⟩
        subst U
        change (structureFunctor Y.underlying).obj ξ.obj.obj.right =
            (structureFunctor X.underlying).obj ξ.obj.obj.left at hY
        change R ⟶ (structureFunctor X.underlying).obj ξ.obj.obj.left at f
        obtain ⟨x', φ, hφ⟩ :=
          (fibred_category_iff_exists_stronglyCartesian
            (structureFunctor X.underlying)).mp inferInstance
            ξ.obj.obj.left R f
        let fY := f ≫ eqToHom hY.symm
        obtain ⟨y', ψ, hψ⟩ :=
          (fibred_category_iff_exists_stronglyCartesian
            (structureFunctor Y.underlying)).mp inferInstance
            ξ.obj.obj.right R fY
        let : (structureFunctor X.underlying).IsStronglyCartesian f φ := hφ
        let : (structureFunctor Y.underlying).IsStronglyCartesian fY ψ := hψ
        have hdomX : (structureFunctor X.underlying).obj x' = R :=
          CategoryTheory.IsHomLift.domain_eq
            (structureFunctor X.underlying) f φ
        have hdomY : (structureFunctor Y.underlying).obj y' = R :=
          CategoryTheory.IsHomLift.domain_eq
            (structureFunctor Y.underlying) fY ψ
        subst R
        have hφ' := categoriesFibredInSets_stronglyCartesian_map_of f φ hφ
        have hψ' := categoriesFibredInSets_stronglyCartesian_map_of fY ψ hψ
        have hFstrong := F.preserves φ hφ'
        let : (structureFunctor S.underlying).IsStronglyCartesian
            ((structureFunctor S.underlying).map
              ((overFunctor F.underlying).map φ))
            ((overFunctor F.underlying).map φ) := hFstrong
        have hGstrong := G.preserves ψ hψ'
        let : (structureFunctor S.underlying).IsStronglyCartesian
            ((structureFunctor S.underlying).map
              ((overFunctor G.underlying).map ψ))
            ((overFunctor G.underlying).map ψ) := hGstrong
        let : (structureFunctor S.underlying).IsHomLift
            (𝟙 ((structureFunctor X.underlying).obj ξ.obj.obj.left))
            ξ.obj.obj.hom := hξ
        let hFx' := congrArg (fun K : X.underlying.left ⥤ C => K.obj x')
          (overFunctor_comm F.underlying)
        let hFx := congrArg (fun K : X.underlying.left ⥤ C =>
          K.obj ξ.obj.obj.left) (overFunctor_comm F.underlying)
        let hGy' := congrArg (fun K : Y.underlying.left ⥤ C => K.obj y')
          (overFunctor_comm G.underlying)
        let hGy := congrArg (fun K : Y.underlying.left ⥤ C =>
          K.obj ξ.obj.obj.right) (overFunctor_comm G.underlying)
        have hFmap : (structureFunctor S.underlying).map
            ((overFunctor F.underlying).map φ) =
            eqToHom hFx' ≫ (structureFunctor X.underlying).map φ ≫
              eqToHom hFx.symm := by
          exact Functor.congr_hom (overFunctor_comm F.underlying) φ
        have hGmap : (structureFunctor S.underlying).map
            ((overFunctor G.underlying).map ψ) =
            eqToHom hGy' ≫ (structureFunctor Y.underlying).map ψ ≫
              eqToHom hGy.symm := by
          exact Functor.congr_hom (overFunctor_comm G.underlying) ψ
        have hmapφ : (structureFunctor X.underlying).map φ =
            f := by
          simpa using CategoryTheory.IsHomLift.fac'
            (structureFunctor X.underlying) f φ
        have hmapψ : (structureFunctor Y.underlying).map ψ =
            eqToHom hdomY ≫ fY := by
          simpa using CategoryTheory.IsHomLift.fac'
            (structureFunctor Y.underlying) fY ψ
        let hFa := hFx
        let hGa := hGy.trans hY
        have hξfac := CategoryTheory.IsHomLift.fac'
          (structureFunctor S.underlying)
          (𝟙 ((structureFunctor X.underlying).obj ξ.obj.obj.left))
          ξ.obj.obj.hom
        have hξt : eqToHom hFa.symm ≫
            (structureFunctor S.underlying).map ξ.obj.obj.hom ≫
            eqToHom hGa = 𝟙 ((structureFunctor X.underlying).obj ξ.obj.obj.left) := by
          rw [hξfac]
          simp
        have hξleft : eqToHom hFa.symm ≫
            (structureFunctor S.underlying).map ξ.obj.obj.hom =
            eqToHom hGa.symm := by
          calc
            eqToHom hFa.symm ≫
                (structureFunctor S.underlying).map ξ.obj.obj.hom =
                (eqToHom hFa.symm ≫
                  (structureFunctor S.underlying).map ξ.obj.obj.hom ≫
                  eqToHom hGa) ≫ eqToHom hGa.symm := by
                    simp [Category.assoc]
            _ = 𝟙 _ ≫ eqToHom hGa.symm := by rw [hξt]
            _ = eqToHom hGa.symm := by simp
        let hsource := hFx'.trans
          (hdomY.symm.trans hGy'.symm)
        have hfactor : (structureFunctor S.underlying).map
            (((overFunctor F.underlying).map φ) ≫ ξ.obj.obj.hom) =
            eqToHom hsource ≫ (structureFunctor S.underlying).map
              ((overFunctor G.underlying).map ψ) := by
          calc
            (structureFunctor S.underlying).map
                (((overFunctor F.underlying).map φ) ≫ ξ.obj.obj.hom) =
                (structureFunctor S.underlying).map
                  ((overFunctor F.underlying).map φ) ≫
                  (structureFunctor S.underlying).map ξ.obj.obj.hom := by
                    rw [Functor.map_comp]
            _ = (eqToHom hFx' ≫ f ≫ eqToHom hFx.symm) ≫
                  (structureFunctor S.underlying).map ξ.obj.obj.hom := by
                    rw [hFmap, hmapφ]
            _ = eqToHom hFx' ≫ f ≫
                  (eqToHom hFa.symm ≫
                    (structureFunctor S.underlying).map ξ.obj.obj.hom) := by
                    simp [Category.assoc]
            _ = eqToHom hFx' ≫ f ≫ eqToHom hGa.symm := by
                    rw [hξleft]
            _ = eqToHom hsource ≫
                  (eqToHom hGy' ≫ (eqToHom hdomY ≫ fY) ≫
                    eqToHom hGy.symm) := by
                    dsimp [hsource, fY, hGa]
                    simp [Category.assoc]
            _ = eqToHom hsource ≫ (structureFunctor S.underlying).map
                  ((overFunctor G.underlying).map ψ) := by
                    rw [hGmap, hmapψ]
        obtain ⟨β, ⟨hβ, hβeq⟩, hβuniq⟩ :=
          Functor.IsStronglyCartesian.universal_property
            (structureFunctor S.underlying)
            ((structureFunctor S.underlying).map
              ((overFunctor G.underlying).map ψ))
            ((overFunctor G.underlying).map ψ) (eqToHom hsource)
            ((structureFunctor S.underlying).map
              (((overFunctor F.underlying).map φ) ≫ ξ.obj.obj.hom)) hfactor
            (((overFunctor F.underlying).map φ) ≫ ξ.obj.obj.hom)
        have hβmap : eqToHom hsource =
            (structureFunctor S.underlying).map β :=
          CategoryTheory.IsHomLift.eq_of_isHomLift
            (structureFunctor S.underlying) (eqToHom hsource) β
        have hβvertical : (structureFunctor S.underlying).IsHomLift
            (𝟙 ((structureFunctor X.underlying).obj x')) β := by
          apply CategoryTheory.IsHomLift.of_fac'
            (structureFunctor S.underlying)
            (𝟙 ((structureFunctor X.underlying).obj x')) β
            (hFx'.trans rfl) (hGy'.trans hdomY)
          simpa [hsource, Category.assoc] using hβmap.symm
        let : (structureFunctor S.underlying).IsStronglyCartesian
            (𝟙 ((structureFunctor X.underlying).obj ξ.obj.obj.left))
            ξ.obj.obj.hom := by
          infer_instance
        have hξstrong : (structureFunctor S.underlying).IsStronglyCartesian
            ((structureFunctor S.underlying).map ξ.obj.obj.hom)
            ξ.obj.obj.hom := by
          exact categoriesFibredInSets_stronglyCartesian_map_of
            (𝟙 ((structureFunctor X.underlying).obj ξ.obj.obj.left))
            ξ.obj.obj.hom inferInstance
        let : (structureFunctor S.underlying).IsStronglyCartesian
            ((structureFunctor S.underlying).map
              ((overFunctor F.underlying).map φ))
            ((overFunctor F.underlying).map φ) := hFstrong
        let : (structureFunctor S.underlying).IsStronglyCartesian
            ((structureFunctor S.underlying).map ξ.obj.obj.hom)
            ξ.obj.obj.hom := hξstrong
        have hαstrong : (structureFunctor S.underlying).IsStronglyCartesian
            ((structureFunctor S.underlying).map
              ((overFunctor F.underlying).map φ ≫ ξ.obj.obj.hom))
            ((overFunctor F.underlying).map φ ≫ ξ.obj.obj.hom) := by
          simpa only [Functor.map_comp] using
            (stronglyCartesian_comp (structureFunctor S.underlying)
              (φ := (overFunctor F.underlying).map φ)
              (ψ := ξ.obj.obj.hom))
        let : (structureFunctor S.underlying).IsHomLift
            (eqToHom hsource) β := hβ
        have hβcomp : (structureFunctor S.underlying).IsStronglyCartesian
            (eqToHom hsource ≫ (structureFunctor S.underlying).map
              ((overFunctor G.underlying).map ψ))
            (β ≫ (overFunctor G.underlying).map ψ) := by
          rw [hβeq, ← hfactor]
          exact hαstrong
        let : (structureFunctor S.underlying).IsStronglyCartesian
            (eqToHom hsource ≫ (structureFunctor S.underlying).map
              ((overFunctor G.underlying).map ψ))
            (β ≫ (overFunctor G.underlying).map ψ) := hβcomp
        have hβstrong : (structureFunctor S.underlying).IsStronglyCartesian
            (eqToHom hsource) β := by
          exact Functor.IsStronglyCartesian.of_comp
            (p := structureFunctor S.underlying)
            (f := eqToHom hsource)
            (g := (structureFunctor S.underlying).map
              ((overFunctor G.underlying).map ψ))
            (φ := β) (ψ := (overFunctor G.underlying).map ψ)
        let : IsIso β := stronglyCartesian_of_base_isIso
          (structureFunctor S.underlying) (eqToHom hsource) β
        let b : TwoFibreProductOverCategory F.underlying G.underlying :=
          { obj :=
              { obj :=
                  { left := x'
                    right := y'
                    hom := β }
                property := by
                  change IsIso β
                  infer_instance }
            property := by
              refine ⟨(structureFunctor X.underlying).obj x', rfl,
                hdomY, hβvertical⟩ }
        let φ₀ : b ⟶ ξ :=
          ObjectProperty.homMk
            (ObjectProperty.homMk
              { left := φ
                right := ψ
                w := hβeq.symm })
        have hbase : D.base.IsHomLift f φ₀ := by
          apply CategoryTheory.IsHomLift.of_fac'
            D.base f φ₀ rfl rfl
          dsimp [D, twoFibreProductOverDiagram, twoFibreProductOverLeft,
            φ₀, b, ObjectProperty.homMk, isoCommaLeft]
          change (structureFunctor X.underlying).map φ = _
          rw [hmapφ]
          change f =
            eqToHom (rfl : (structureFunctor X.underlying).obj x' =
              (structureFunctor X.underlying).obj x') ≫ f ≫
              eqToHom (rfl : (structureFunctor X.underlying).obj ξ.obj.obj.left =
                (structureFunctor X.underlying).obj ξ.obj.obj.left)
          simp
        refine ⟨b, φ₀, ?_⟩
        refine { toIsHomLift := hbase, universal_property' := ?_ }
        intro ζ g τ hτ
        let : D.base.IsHomLift (g ≫ f) τ := hτ
        have hτX : (structureFunctor X.underlying).IsHomLift
            (g ≫ f) τ.hom.hom.left := by
          apply CategoryTheory.IsHomLift.of_fac'
            (structureFunctor X.underlying) (g ≫ f) τ.hom.hom.left rfl rfl
          have hfac := CategoryTheory.IsHomLift.fac'
            D.base (g ≫ f) τ
          dsimp [D, twoFibreProductOverDiagram, twoFibreProductOverLeft,
            isoCommaLeft] at hfac
          exact hfac
        let : (structureFunctor X.underlying).IsHomLift
            (g ≫ f) τ.hom.hom.left := hτX
        obtain ⟨χleft, ⟨hχleft, hχleftfac⟩, hχleftuniq⟩ :=
          Functor.IsStronglyCartesian.universal_property
            (structureFunctor X.underlying) f φ g (g ≫ f) rfl τ.hom.hom.left
        obtain ⟨Uζ, hζX, hζY, hζhom⟩ := ζ.property
        change (structureFunctor X.underlying).obj ζ.obj.obj.left = Uζ at hζX
        change (structureFunctor Y.underlying).obj ζ.obj.obj.right = Uζ at hζY
        obtain ⟨U₀, U₁, hζX', hζY', hξX', hξY', hs⟩ :=
          twoFibreProductOver_morphism_base_description τ
        change (structureFunctor X.underlying).obj ζ.obj.obj.left = U₀ at hζX'
        change (structureFunctor Y.underlying).obj ζ.obj.obj.right = U₀ at hζY'
        change (structureFunctor X.underlying).obj ξ.obj.obj.left = U₁ at hξX'
        change (structureFunctor Y.underlying).obj ξ.obj.obj.right = U₁ at hξY'
        change (structureFunctor X.underlying).obj ζ.obj.obj.left ⟶
            (structureFunctor X.underlying).obj x' at g
        let gY : (structureFunctor Y.underlying).obj ζ.obj.obj.right ⟶
            (structureFunctor X.underlying).obj x' :=
          eqToHom hζY' ≫ eqToHom hζX'.symm ≫ g
        have hτmapX : g ≫ f =
            (structureFunctor X.underlying).map τ.hom.hom.left := by
          have h := CategoryTheory.IsHomLift.eq_of_isHomLift
            D.base (g ≫ f) τ
          simpa [D, twoFibreProductOverDiagram, twoFibreProductOverLeft,
            isoCommaLeft] using h
        have hτYfac : (structureFunctor Y.underlying).map τ.hom.hom.right =
            gY ≫ fY := by
          have htransport :
              (structureFunctor Y.underlying).map τ.hom.hom.right =
                eqToHom hζY' ≫ eqToHom hζX'.symm ≫
                  (structureFunctor X.underlying).map τ.hom.hom.left ≫
                  eqToHom hξX' ≫ eqToHom hξY'.symm := by
            calc
                (structureFunctor Y.underlying).map τ.hom.hom.right =
                    𝟙 _ ≫ (structureFunctor Y.underlying).map τ.hom.hom.right ≫ 𝟙 _ := by
                      simp
                _ = (eqToHom hζY' ≫ eqToHom hζY'.symm) ≫
                    (structureFunctor Y.underlying).map τ.hom.hom.right ≫
                    (eqToHom hξY' ≫ eqToHom hξY'.symm) := by
                      simp
                _ = eqToHom hζY' ≫
                    (eqToHom hζY'.symm ≫
                      (structureFunctor Y.underlying).map τ.hom.hom.right ≫
                      eqToHom hξY') ≫ eqToHom hξY'.symm := by
                      simp [Category.assoc]
                _ = eqToHom hζY' ≫
                    (eqToHom hζX'.symm ≫
                      (structureFunctor X.underlying).map τ.hom.hom.left ≫
                      eqToHom hξX') ≫ eqToHom hξY'.symm := by
                      rw [hs.symm]
                _ = eqToHom hζY' ≫ eqToHom hζX'.symm ≫
                    (structureFunctor X.underlying).map τ.hom.hom.left ≫
                    eqToHom hξX' ≫ eqToHom hξY'.symm := by
                      simp [Category.assoc]
          rw [htransport, ← hτmapX]
          dsimp [gY, fY]
          have hξtransport :
              eqToHom hξX' ≫ eqToHom hξY'.symm = eqToHom hY.symm := by
            simp only [eqToHom_trans]
          rw [hξtransport]
          change
            eqToHom hζY' ≫ eqToHom hζX'.symm ≫ (g ≫ f) ≫ eqToHom hY.symm =
              (eqToHom hζY' ≫ eqToHom hζX'.symm ≫ g) ≫ f ≫ eqToHom hY.symm
          let eY := eqToHom hζY'
          let eX := eqToHom hζX'.symm
          let eH := eqToHom hY.symm
          change eY ≫ eX ≫ (g ≫ f) ≫ eH = (eY ≫ eX ≫ g) ≫ f ≫ eH
          convert congrArg (fun k => eY ≫ k ≫ eH)
            (Category.assoc eX g f).symm using 1 <;>
            simp only [Category.assoc]
        have hτY : (structureFunctor Y.underlying).IsHomLift
            (gY ≫ fY) τ.hom.hom.right := by
          apply CategoryTheory.IsHomLift.of_fac'
            (structureFunctor Y.underlying) (gY ≫ fY)
            τ.hom.hom.right rfl rfl
          simpa using hτYfac
        let : (structureFunctor Y.underlying).IsHomLift
            (gY ≫ fY) τ.hom.hom.right := hτY
        obtain ⟨χright, ⟨hχright, hχrightfac⟩, hχrightuniq⟩ :=
          Functor.IsStronglyCartesian.universal_property
            (structureFunctor Y.underlying) fY ψ gY (gY ≫ fY) rfl
            τ.hom.hom.right
        have hFζ :
            (overFunctor F.underlying ⋙ structureFunctor S.underlying).obj
                ζ.obj.obj.left =
              (structureFunctor X.underlying).obj ζ.obj.obj.left :=
          congrArg (fun K : X.underlying.left ⥤ C => K.obj ζ.obj.obj.left)
            (overFunctor_comm F.underlying)
        have hGζ :
            (overFunctor G.underlying ⋙ structureFunctor S.underlying).obj
                ζ.obj.obj.right =
              (structureFunctor Y.underlying).obj ζ.obj.obj.right :=
          congrArg (fun K : Y.underlying.left ⥤ C => K.obj ζ.obj.obj.right)
            (overFunctor_comm G.underlying)
        have hFζ' :
            (structureFunctor S.underlying).obj
                ((overFunctor F.underlying).obj ζ.obj.obj.left) =
              (structureFunctor X.underlying).obj ζ.obj.obj.left := by
          simpa only [Functor.comp_obj] using hFζ
        have hGζ' :
            (structureFunctor S.underlying).obj
                ((overFunctor G.underlying).obj ζ.obj.obj.right) =
              (structureFunctor Y.underlying).obj ζ.obj.obj.right := by
          simpa only [Functor.comp_obj] using hGζ
        let _ : (structureFunctor S.underlying).IsHomLift
            (𝟙 Uζ) ζ.obj.obj.hom := hζhom
        let hdomζ := CategoryTheory.IsHomLift.domain_eq
          (structureFunctor S.underlying) (𝟙 Uζ) ζ.obj.obj.hom
        let hcodζ := CategoryTheory.IsHomLift.codomain_eq
          (structureFunctor S.underlying) (𝟙 Uζ) ζ.obj.obj.hom
        have hdomζ_eq : hdomζ = hFζ'.trans hζX := Subsingleton.elim _ _
        have hcodζ_eq : hcodζ = hGζ'.trans hζY := Subsingleton.elim _ _
        let hζtarget0 := (hFζ'.trans hζX).trans
          (hGζ'.trans hζY).symm
        let hζtarget := (hFζ'.trans hζX').trans
          (hGζ'.trans hζY').symm
        have hζmap0 : (structureFunctor S.underlying).map ζ.obj.obj.hom =
            eqToHom hζtarget0 := by
          have hfac := CategoryTheory.IsHomLift.fac'
            (structureFunctor S.underlying) (𝟙 Uζ) ζ.obj.obj.hom
          simpa only [hdomζ_eq, hcodζ_eq, Category.id_comp, Category.comp_id,
            eqToHom_refl, eqToHom_trans] using hfac
        have hζmap : (structureFunctor S.underlying).map ζ.obj.obj.hom =
            eqToHom hζtarget := by
          have htarget : hζtarget0 = hζtarget := Subsingleton.elim _ _
          simpa [htarget] using hζmap0
        have hχrightmap :
            (structureFunctor Y.underlying).map χright =
              gY ≫ eqToHom hdomY.symm := by
          simpa using CategoryTheory.IsHomLift.fac'
            (structureFunctor Y.underlying) gY χright
        have hχrightmap' :
            (structureFunctor Y.underlying).map χright =
              eqToHom hζY' ≫ eqToHom hζX'.symm ≫ g ≫
                eqToHom hdomY.symm := by
          rw [hχrightmap]
          dsimp [gY]
          calc
            (eqToHom hζY' ≫
                (eqToHom hζX'.symm ≫ g)) ≫ eqToHom hdomY.symm =
                eqToHom hζY' ≫
                  ((eqToHom hζX'.symm ≫ g) ≫ eqToHom hdomY.symm) := by
              rw [Category.assoc]
            _ = eqToHom hζY' ≫
                  (eqToHom hζX'.symm ≫
                    (g ≫ eqToHom hdomY.symm)) := by
              exact congrArg (fun k => eqToHom hζY' ≫ k)
                (Category.assoc (eqToHom hζX'.symm) g
                  (eqToHom hdomY.symm))
        have hGmapχright :
            (structureFunctor S.underlying).map
                ((overFunctor G.underlying).map χright) =
              eqToHom hGζ ≫ (structureFunctor Y.underlying).map χright ≫
                eqToHom hGy'.symm := by
          exact Functor.congr_hom (overFunctor_comm G.underlying) χright
        have hχleftmap :
            (structureFunctor X.underlying).map χleft = g := by
          exact (@CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
            (structureFunctor X.underlying) _ _ g χleft hχleft).symm
        have hFmapχleft :
            (structureFunctor S.underlying).map
                ((overFunctor F.underlying).map χleft) =
              eqToHom hFζ' ≫ (structureFunctor X.underlying).map χleft ≫
                eqToHom hFx'.symm := by
          exact Functor.congr_hom (overFunctor_comm F.underlying) χleft
        let gS :
            (structureFunctor S.underlying).obj
                ((overFunctor F.underlying).obj ζ.obj.obj.left) ⟶
              (structureFunctor S.underlying).obj
                ((overFunctor G.underlying).obj y') :=
          (structureFunctor S.underlying).map
              ((overFunctor F.underlying).map χleft) ≫ eqToHom hsource
        have hcancel :
            eqToHom hζtarget ≫ eqToHom hGζ ≫ eqToHom hζY' ≫
                eqToHom hζX'.symm = eqToHom hFζ' := by
          simp [eqToHom_trans]
        have hsource_comp :
            eqToHom hFx'.symm ≫ eqToHom hsource =
              eqToHom hdomY.symm ≫ eqToHom hGy'.symm := by
          simp [eqToHom_trans]
        have hrightfacEq :
            eqToHom hζtarget ≫ eqToHom hGζ ≫ eqToHom hζY' ≫
                eqToHom hζX'.symm ≫ g ≫ eqToHom hdomY.symm ≫
                eqToHom hGy'.symm =
              eqToHom hFζ' ≫ g ≫ eqToHom hFx'.symm ≫ eqToHom hsource := by
          calc
            eqToHom hζtarget ≫ eqToHom hGζ ≫ eqToHom hζY' ≫
                  eqToHom hζX'.symm ≫ g ≫ eqToHom hdomY.symm ≫
                  eqToHom hGy'.symm =
                  eqToHom hFζ' ≫ g ≫ eqToHom hdomY.symm ≫
                  eqToHom hGy'.symm := by
              convert congrArg
                (fun k => k ≫ g ≫ eqToHom hdomY.symm ≫ eqToHom hGy'.symm)
                hcancel using 1; simp only [Category.assoc]
            _ = eqToHom hFζ' ≫ g ≫ eqToHom hFx'.symm ≫
                  eqToHom hsource := by
              exact congrArg
                (fun k => eqToHom hFζ' ≫ g ≫ k) hsource_comp.symm
        have hleft : (structureFunctor S.underlying).IsHomLift gS
            (((overFunctor F.underlying).map χleft) ≫ β) := by
          dsimp [gS]
          let _ : (structureFunctor S.underlying).IsHomLift
              ((structureFunctor S.underlying).map
                ((overFunctor F.underlying).map χleft))
              ((overFunctor F.underlying).map χleft) :=
            Functor.IsHomLift.map ((overFunctor F.underlying).map χleft)
          let _ : (structureFunctor S.underlying).IsHomLift
              (eqToHom hsource) β := hβ
          exact inferInstance
        have hright : (structureFunctor S.underlying).IsHomLift gS
            (ζ.obj.obj.hom ≫ (overFunctor G.underlying).map χright) := by
          apply CategoryTheory.IsHomLift.of_fac'
            (structureFunctor S.underlying) gS
            (ζ.obj.obj.hom ≫ (overFunctor G.underlying).map χright) rfl rfl
          dsimp [gS]
          rw [Functor.map_comp, hζmap, hGmapχright, hχrightmap']
          rw [hFmapχleft, hχleftmap]
          simp only [Functor.comp_obj, Category.id_comp, Category.comp_id]
          have hcat_left :
              (eqToHom hζY' ≫ eqToHom hζX'.symm ≫ g ≫
                eqToHom hdomY.symm) ≫ eqToHom hGy'.symm =
                  eqToHom hζY' ≫ eqToHom hζX'.symm ≫ g ≫
                  eqToHom hdomY.symm ≫ eqToHom hGy'.symm := by
            simp only [Category.assoc]
          have hcat_right :
              (eqToHom hFζ' ≫ g ≫ eqToHom hFx'.symm) ≫
                  eqToHom hsource =
                eqToHom hFζ' ≫ g ≫ eqToHom hFx'.symm ≫
                  eqToHom hsource := by
            simp only [Category.assoc]
          exact (congrArg
            (fun k => eqToHom hζtarget ≫ eqToHom hGζ ≫ k) hcat_left).trans
            (hrightfacEq.trans hcat_right.symm)
        let _ : (structureFunctor S.underlying).IsHomLift gS
            (((overFunctor F.underlying).map χleft) ≫ β) := hleft
        let _ : (structureFunctor S.underlying).IsHomLift gS
            (ζ.obj.obj.hom ≫ (overFunctor G.underlying).map χright) := hright
        have hκw :
            (overFunctor F.underlying).map χleft ≫ β =
              ζ.obj.obj.hom ≫ (overFunctor G.underlying).map χright := by
          apply Functor.IsStronglyCartesian.ext
            (structureFunctor S.underlying)
            ((structureFunctor S.underlying).map
              ((overFunctor G.underlying).map ψ))
            ((overFunctor G.underlying).map ψ) gS
          calc
            (((overFunctor F.underlying).map χleft) ≫ β) ≫
                (overFunctor G.underlying).map ψ =
                (overFunctor F.underlying).map χleft ≫
                  (β ≫ (overFunctor G.underlying).map ψ) := by
                    simp [Category.assoc]
            _ = (overFunctor F.underlying).map χleft ≫
                ((overFunctor F.underlying).map φ ≫ ξ.obj.obj.hom) := by
                  rw [hβeq]
            _ = (overFunctor F.underlying).map
                  (χleft ≫ φ) ≫ ξ.obj.obj.hom := by
                  rw [Functor.map_comp]
                  simp [Category.assoc]
            _ = (overFunctor F.underlying).map τ.hom.hom.left ≫
                  ξ.obj.obj.hom := by
                  rw [hχleftfac]
            _ = ζ.obj.obj.hom ≫
                  (overFunctor G.underlying).map τ.hom.hom.right :=
                  τ.hom.hom.w
            _ = ζ.obj.obj.hom ≫
                  (overFunctor G.underlying).map
                    (χright ≫ ψ) := by
                  rw [hχrightfac]
            _ = (ζ.obj.obj.hom ≫
                  (overFunctor G.underlying).map χright) ≫
                (overFunctor G.underlying).map ψ := by
                  simp [Functor.map_comp, Category.assoc]
        let κ : ζ ⟶ b :=
          ObjectProperty.homMk
            (ObjectProperty.homMk
              { left := χleft
                right := χright
                w := hκw })
        have hκbase : D.base.IsHomLift g κ := by
          apply CategoryTheory.IsHomLift.of_fac'
            D.base g κ rfl rfl
          let _ : (structureFunctor X.underlying).IsHomLift g χleft := hχleft
          have hfac := CategoryTheory.IsHomLift.fac'
            (structureFunctor X.underlying) g χleft
          dsimp [D, twoFibreProductOverDiagram, twoFibreProductOverLeft,
            κ, ObjectProperty.homMk, isoCommaLeft] at hfac ⊢
          exact hfac
        have hκfac : κ ≫ φ₀ = τ := by
          apply ObjectProperty.hom_ext
          apply ObjectProperty.hom_ext
          apply Comma.hom_ext
          · dsimp [κ, φ₀, ObjectProperty.homMk]
            exact hχleftfac
          · dsimp [κ, φ₀, ObjectProperty.homMk]
            exact hχrightfac
        refine ⟨κ, ⟨hκbase, hκfac⟩, ?_⟩
        intro m hm
        rcases hm with ⟨hmBase, hmFac⟩
        let _ : D.base.IsHomLift g m := hmBase
        have hmLeft : (structureFunctor X.underlying).IsHomLift g
            m.hom.hom.left := by
          apply CategoryTheory.IsHomLift.of_fac'
            (structureFunctor X.underlying) g m.hom.hom.left rfl rfl
          have hfac := CategoryTheory.IsHomLift.fac' D.base g m
          dsimp [D, twoFibreProductOverDiagram, twoFibreProductOverLeft,
            isoCommaLeft] at hfac
          exact hfac
        have hmLeftFac : m.hom.hom.left ≫ φ = τ.hom.hom.left := by
          have hh := congrArg (fun k => k.hom.hom.left) hmFac
          simpa [φ₀, ObjectProperty.homMk] using hh
        have hmLeftEq : m.hom.hom.left = χleft :=
          hχleftuniq m.hom.hom.left ⟨hmLeft, hmLeftFac⟩
        have hmRightFac : m.hom.hom.right ≫ ψ = τ.hom.hom.right := by
          have hh := congrArg (fun k => k.hom.hom.right) hmFac
          simpa [φ₀, ObjectProperty.homMk] using hh
        have hmFmap : (structureFunctor S.underlying).map
            ((overFunctor F.underlying).map m.hom.hom.left) =
            eqToHom hFζ' ≫ (structureFunctor X.underlying).map
              m.hom.hom.left ≫ eqToHom hFx'.symm := by
          exact Functor.congr_hom (overFunctor_comm F.underlying)
            m.hom.hom.left
        have hmGmap : (structureFunctor S.underlying).map
            ((overFunctor G.underlying).map m.hom.hom.right) =
            eqToHom hGζ ≫ (structureFunctor Y.underlying).map
              m.hom.hom.right ≫ eqToHom hGy'.symm := by
          exact Functor.congr_hom (overFunctor_comm G.underlying)
            m.hom.hom.right
        have hmWmap : (structureFunctor S.underlying).map
              ((overFunctor F.underlying).map m.hom.hom.left) ≫
              (structureFunctor S.underlying).map β =
            (structureFunctor S.underlying).map ζ.obj.obj.hom ≫
              (structureFunctor S.underlying).map
                ((overFunctor G.underlying).map m.hom.hom.right) := by
          rw [← (structureFunctor S.underlying).map_comp,
            ← (structureFunctor S.underlying).map_comp]
          exact congrArg (structureFunctor S.underlying).map m.hom.hom.w
        let _ : (structureFunctor X.underlying).IsHomLift g
            m.hom.hom.left := hmLeft
        have hmLeftMap : (structureFunctor X.underlying).map
            m.hom.hom.left = g := by
          exact (@CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
            (structureFunctor X.underlying) _ _ g m.hom.hom.left hmLeft).symm
        rw [hmFmap, ← hβmap, hζmap, hmGmap, hmLeftMap] at hmWmap
        have hmWmap' :
            (eqToHom hFζ' ≫ g ≫ eqToHom hFx'.symm) ≫ eqToHom hsource =
              eqToHom hζtarget ≫ eqToHom hGζ ≫
                (structureFunctor Y.underlying).map m.hom.hom.right ≫
                  eqToHom hGy'.symm := by
          exact hmWmap
        have hmRightMap : (structureFunctor Y.underlying).map
            m.hom.hom.right = gY ≫ eqToHom hdomY.symm := by
          have hmWmap'' :
              eqToHom hζtarget ≫ eqToHom hGζ ≫
                  (structureFunctor Y.underlying).map m.hom.hom.right ≫
                  eqToHom hGy'.symm =
                eqToHom hζtarget ≫ eqToHom hGζ ≫ gY ≫
                  eqToHom hdomY.symm ≫ eqToHom hGy'.symm := by
            calc
              eqToHom hζtarget ≫ eqToHom hGζ ≫
                    (structureFunctor Y.underlying).map m.hom.hom.right ≫
                    eqToHom hGy'.symm =
                  (eqToHom hFζ' ≫ g ≫ eqToHom hFx'.symm) ≫
                    eqToHom hsource := by
                simpa only [Category.assoc] using hmWmap'.symm
              _ = eqToHom hζtarget ≫ eqToHom hGζ ≫ gY ≫
                    eqToHom hdomY.symm ≫ eqToHom hGy'.symm := by
                convert hrightfacEq.symm using 1 <;>
                  simp only [gY, Category.assoc]
          apply (cancel_epi (eqToHom hζtarget ≫ eqToHom hGζ)).1
          apply (cancel_mono (eqToHom hGy'.symm)).1
          simpa only [Category.assoc] using hmWmap''
        have hmRight : (structureFunctor Y.underlying).IsHomLift gY
            m.hom.hom.right := by
          apply CategoryTheory.IsHomLift.of_fac'
            (structureFunctor Y.underlying) gY m.hom.hom.right rfl hdomY
          simpa using hmRightMap
        have hmRightEq : m.hom.hom.right = χright :=
          hχrightuniq m.hom.hom.right ⟨hmRight, hmRightFac⟩
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext
        · dsimp [κ, ObjectProperty.homMk]
          exact hmLeftEq
        · dsimp [κ, ObjectProperty.homMk]
          exact hmRightEq
      is_two_fibre_product :=
        twoFibreProductOver_is_twoFibreProduct F.underlying G.underlying }
  refine ⟨{ product := product, fibres_are_discrete := ?_ }⟩
  intro U
  let _ : IsDiscrete (Functor.Fiber (structureFunctor X.underlying) U) := hX U
  let _ : IsDiscrete (Functor.Fiber (structureFunctor Y.underlying) U) := hY U
  let _ : IsDiscrete (Functor.Fiber (structureFunctor S.underlying) U) := hS U
  have hcomma :
      IsDiscrete (twoFibreProductOverFibreCategory F.underlying G.underlying U) := by
    apply (isDiscrete_iff_every_morphism_is_eqToHom).mpr
    intro A B f
    have hleft : A.obj.left = B.obj.left :=
      IsDiscrete.eq_of_hom f.hom.left
    have hright : A.obj.right = B.obj.right :=
      IsDiscrete.eq_of_hom f.hom.right
    have hAB : A = B := by
      apply ObjectProperty.FullSubcategory.ext
      cases A with
      | mk A hA =>
        cases B with
        | mk B hB =>
          cases A with
          | mk Aleft Aright Ahom =>
            cases B with
            | mk Bleft Bright Bhom =>
              dsimp at hleft hright ⊢
              cases hleft
              cases hright
              have hhom : Ahom = Bhom := Subsingleton.elim _ _
              cases hhom
              rfl
    subst B
    refine ⟨rfl, ?_⟩
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
  let _ : IsDiscrete (twoFibreProductOverFibreCategory F.underlying G.underlying U) := hcomma
  change IsDiscrete (Functor.Fiber D.base U)
  obtain ⟨e⟩ := twoFibreProductOver_fibre_equivalent
    F.underlying G.underlying U
  apply (isDiscrete_iff_every_morphism_is_eqToHom).mpr
  intro A B f
  let leftA : Functor.Fiber (structureFunctor X.underlying) U :=
    ⟨D.left.obj A.1, by
      change D.base.obj A.1 = U
      exact A.2⟩
  let leftB : Functor.Fiber (structureFunctor X.underlying) U :=
    ⟨D.left.obj B.1, by
      change D.base.obj B.1 = U
      exact B.2⟩
  let rightA : Functor.Fiber (structureFunctor Y.underlying) U :=
    ⟨D.right.obj A.1, by
      have h := congrArg (fun H : TwoFibreProductOverCategory F.underlying
          G.underlying ⥤ C => H.obj A.1) D.right_over
      exact h.trans A.2⟩
  let rightB : Functor.Fiber (structureFunctor Y.underlying) U :=
    ⟨D.right.obj B.1, by
      have h := congrArg (fun H : TwoFibreProductOverCategory F.underlying
          G.underlying ⥤ C => H.obj B.1) D.right_over
      exact h.trans B.2⟩
  let _ : D.base.IsHomLift (𝟙 U) f.1 := f.2
  let leftF : leftA ⟶ leftB :=
    ⟨D.left.map f.1, by
      apply CategoryTheory.IsHomLift.of_fac'
        (structureFunctor X.underlying) (𝟙 U) (D.left.map f.1)
        leftA.2 leftB.2
      change (structureFunctor X.underlying).map (D.left.map f.1) =
        eqToHom leftA.2 ≫ 𝟙 U ≫ eqToHom leftB.2.symm
      exact CategoryTheory.IsHomLift.fac' D.base (𝟙 U) f.1⟩
  let rightF : rightA ⟶ rightB :=
    ⟨D.right.map f.1, by
      have h := CategoryTheory.IsHomLift.fac' D.base (𝟙 U) f.1
      have r := Functor.congr_obj D.right_over A.1
      have r' := Functor.congr_obj D.right_over B.1
      have hgoal : (structureFunctor Y.underlying).map (D.right.map f.1) =
          eqToHom rightA.2 ≫ 𝟙 U ≫ eqToHom rightB.2.symm := by
        calc
          (structureFunctor Y.underlying).map (D.right.map f.1) =
              (D.right ⋙ structureFunctor Y.underlying).map f.1 := rfl
          _ = eqToHom r ≫ D.base.map f.1 ≫ eqToHom r'.symm :=
            Functor.congr_hom D.right_over f.1
          _ = eqToHom r ≫
              (eqToHom A.2 ≫ 𝟙 U ≫ eqToHom B.2.symm) ≫ eqToHom r'.symm := by
            rw [h]
          _ = eqToHom rightA.2 ≫ 𝟙 U ≫ eqToHom rightB.2.symm := by
            simp [rightA, rightB, eqToHom_trans]
      apply CategoryTheory.IsHomLift.of_fac'
        (structureFunctor Y.underlying) (𝟙 U) (D.right.map f.1)
        rightA.2 rightB.2
      exact hgoal⟩
  have hleft : leftA = leftB := (hX U).eq_of_hom leftF
  have hright : rightA = rightB := (hY U).eq_of_hom rightF
  have hleft' : D.left.obj A.1 = D.left.obj B.1 :=
    congrArg (fun z : Functor.Fiber (structureFunctor X.underlying) U => z.1) hleft
  have hright' : D.right.obj A.1 = D.right.obj B.1 :=
    congrArg (fun z : Functor.Fiber (structureFunctor Y.underlying) U => z.1) hright
  have hleftRaw : A.1.obj.obj.left = B.1.obj.obj.left := by
    simpa [D, twoFibreProductOverDiagram, twoFibreProductOverLeft, isoCommaLeft]
      using hleft'
  have hrightRaw : A.1.obj.obj.right = B.1.obj.obj.right := by
    simpa [D, twoFibreProductOverDiagram, twoFibreProductOverRight, isoCommaRight]
      using hright'
  have hAB : A = B := by
    apply Subtype.ext
    cases A with
    | mk A0 Aproof =>
      cases B with
      | mk B0 Bproof =>
        apply ObjectProperty.FullSubcategory.ext
        cases A0 with
        | mk Aobj Aprop =>
          cases B0 with
          | mk Bobj Bprop =>
            cases Aobj with
            | mk Acomma Aiso =>
              cases Bobj with
              | mk Bcomma Biso =>
                cases Acomma with
                | mk Aleft Aright Ahom =>
                  cases Bcomma with
                  | mk Bleft Bright Bhom =>
                have hleftAB : Aleft = Bleft := by
                  simpa [D, twoFibreProductOverDiagram, twoFibreProductOverLeft,
                    isoCommaLeft] using hleft'
                have hrightAB : Aright = Bright := by
                  simpa [D, twoFibreProductOverDiagram, twoFibreProductOverRight,
                    isoCommaRight] using hright'
                cases hleftAB
                cases hrightAB
                rcases Aprop with ⟨UA, hXA, hYA, hAhom⟩
                rcases Bprop with ⟨UB, hXB, hYB, hBhom⟩
                have hU : UA = UB := hXA.symm.trans hXB
                cases hU
                let aleft : Functor.Fiber (structureFunctor S.underlying) UA :=
                  ⟨(overFunctor F.underlying).obj Aleft, by
                    change (overFunctor F.underlying ⋙ structureFunctor S.underlying).obj
                      Aleft = UA
                    rw [congrArg (fun H : X.underlying.left ⥤ C => H.obj Aleft)
                      (overFunctor_comm F.underlying)]
                    exact hXA⟩
                let aright : Functor.Fiber (structureFunctor S.underlying) UA :=
                  ⟨(overFunctor G.underlying).obj Aright, by
                    change (overFunctor G.underlying ⋙ structureFunctor S.underlying).obj
                      Aright = UA
                    rw [congrArg (fun H : Y.underlying.left ⥤ C => H.obj Aright)
                      (overFunctor_comm G.underlying)]
                    exact hYA⟩
                let ahom : aleft ⟶ aright := ⟨Ahom, hAhom⟩
                let bhom : aleft ⟶ aright := ⟨Bhom, hBhom⟩
                have habhom : ahom = bhom :=
                  @Subsingleton.elim _ ((hS UA).subsingleton _ _) _ _
                have : Ahom = Bhom := congrArg (fun k => k.1) habhom
                cases this
                rfl
  refine ⟨hAB, ?_⟩
  apply e.functor.map_injective
  exact @Subsingleton.elim _ (hcomma.subsingleton _ _) _ _

/-! ## The presheaf construction -/

/-- Turn a set-valued presheaf into a presheaf of discrete categories. -/
def setPresheafToCat
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) :
    Cᵒᵖ ⥤ Cat.{uS, uS} :=
  F ⋙ CategoryTheory.typeToCat

/-- The category `\mathcal S_F` associated to a set-valued presheaf. -/
abbrev setPresheafCategory
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) :=
  groupoidPresheafCategory (setPresheafToCat F)

/-- The value of a CoGrothendieck object in the underlying set-valued
presheaf.  This is the source's displayed object `(U, x)`. -/
def setPresheafObjectValue
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (X : setPresheafCategory F) :
    F.obj (Opposite.op X.base) :=
  Discrete.as X.fiber

@[simp]
theorem setPresheafObjectValue_mk
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (U : C) (x : F.obj (Opposite.op U)) :
    setPresheafObjectValue F
        (⟨U, Discrete.mk x⟩ : setPresheafCategory F) = x :=
  rfl

theorem setPresheaf_object_description
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (X : setPresheafCategory F) :
    ∃ x : F.obj (Opposite.op X.base),
      X = (⟨X.base, Discrete.mk x⟩ : setPresheafCategory F) := by
  refine ⟨Discrete.as X.fiber, ?_⟩
  cases X with
  | mk base fiber =>
    cases fiber
    rfl

/-- The morphism with prescribed base arrow and the corresponding equality in
the set-valued presheaf.  The fibre component is the unique arrow in the
canonical discrete fibre. -/
def setPresheafHomOf
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y : setPresheafCategory F} (f : X.base ⟶ Y.base)
    (h : F.map f.op (setPresheafObjectValue F Y) =
      setPresheafObjectValue F X) : X ⟶ Y where
  base := f
  fiber := by
    change X.fiber ⟶ Discrete.mk (F.map f.op (Discrete.as Y.fiber))
    exact Discrete.eqToHom h.symm

theorem setPresheafHom_fibre_condition
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y : setPresheafCategory F} (f : X ⟶ Y) :
    F.map f.base.op (setPresheafObjectValue F Y) =
      setPresheafObjectValue F X := by
  exact (Discrete.eq_of_hom f.fiber).symm

theorem setPresheafHom_exists_iff
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y : setPresheafCategory F} (f : X.base ⟶ Y.base) :
    (∃ h : X ⟶ Y, h.base = f) ↔
      F.map f.op (setPresheafObjectValue F Y) =
        setPresheafObjectValue F X := by
  constructor
  · rintro ⟨h, rfl⟩
    exact setPresheafHom_fibre_condition F h
  · intro h
    exact ⟨setPresheafHomOf F f h, rfl⟩

theorem setPresheaf_morphism_description
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y : setPresheafCategory F} (f : X ⟶ Y) :
    ∃ h : F.map f.base.op (setPresheafObjectValue F Y) =
        setPresheafObjectValue F X,
      f = setPresheafHomOf F (X := X) (Y := Y) f.base h := by
  sorry

theorem setPresheafHom_ext
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y : setPresheafCategory F} {f g : X ⟶ Y}
    (h : f.base = g.base) : f = g := by
  sorry

/-- The projection `p_F : \mathcal S_F ⥤ C`. -/
abbrev setPresheafProjection
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) :
    setPresheafCategory F ⥤ C :=
  groupoidPresheafProjection (setPresheafToCat F)

/-- The restriction functor corresponding to a base arrow. -/
abbrev setPresheafRestriction
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) {V U : C} (f : V ⟶ U) :=
  groupoidPresheafRestriction (setPresheafToCat F) f

@[simp]
theorem setPresheafRestriction_obj
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) {V U : C} (f : V ⟶ U)
    (x : F.obj (Opposite.op U)) :
    (setPresheafRestriction F f).obj (Discrete.mk x) =
      Discrete.mk (F.map f.op x) :=
  rfl

theorem setPresheafRestriction_comp
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {W V U : C} (g : W ⟶ V) (f : V ⟶ U) :
    setPresheafRestriction F (g ≫ f) =
      setPresheafRestriction F f ⋙ setPresheafRestriction F g := by
  exact groupoidPresheafRestriction_comp (setPresheafToCat F) g f

@[simp]
theorem setPresheafRestriction_id_obj
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (U : C)
    (x : F.obj (Opposite.op U)) :
    (setPresheafRestriction F (𝟙 U)).obj (Discrete.mk x) = Discrete.mk x := by
  change Discrete.mk (F.map (𝟙 U).op x) = Discrete.mk x
  simp

@[simp]
theorem setPresheafProjection_obj
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (X : setPresheafCategory F) :
    (setPresheafProjection F).obj X = X.base :=
  rfl

@[simp]
theorem setPresheafProjection_map
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y : setPresheafCategory F} (f : X ⟶ Y) :
    (setPresheafProjection F).map f = f.base :=
  rfl

@[simp]
theorem setPresheaf_id_base
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (X : setPresheafCategory F) :
    (𝟙 X : X ⟶ X).base = 𝟙 X.base :=
  rfl

@[simp]
theorem setPresheaf_comp_base
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y Z : setPresheafCategory F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

/- The fibre component of composition is the canonical CoGrothendieck
   composition; this is the displayed composition rule in the source. -/
theorem setPresheaf_comp_fiber
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y Z : setPresheafCategory F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fiber =
      f.fiber ≫
        ((splitFibredPseudofunctor (setPresheafToCat F)).map
            f.base.op.toLoc).toFunctor.map g.fiber ≫
        ((splitFibredPseudofunctor (setPresheafToCat F)).mapComp
            g.base.op.toLoc f.base.op.toLoc).inv.toNatTrans.app Z.fiber :=
  rfl

/- The CoGrothendieck category has the source's displayed object and
   morphism data: its objects have a base object and a value in the fibre,
   while its morphisms have a base arrow and a fibre arrow. -/
theorem setPresheaf_fibre_is_discrete
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (U : C) :
    IsDiscrete (Functor.Fiber (setPresheafProjection F) U) := by
  sorry

/- The construction is already fibred in groupoids by the generic
   CoGrothendieck lifting theorem from Unit 37.  The extra assertion here
   isolates the first part of the source's conclusion before adding the
   discrete-fibre condition. -/
theorem setPresheaf_category_isFibredInGroupoids
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) :
    (setPresheafProjection F).IsFibredInGroupoids := by
  apply groupoidPresheafProjection_isFibredInGroupoids
  intro U
  change IsGroupoid (Discrete (F.obj (Opposite.op U)))
  infer_instance

/- The source's final conclusion combines the preceding groupoid and
   discrete-fibre assertions. -/
theorem setPresheaf_category_isFibredInSets
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) :
    IsCategoryFibredInSets (setPresheafProjection F) := by
  exact ⟨setPresheaf_category_isFibredInGroupoids F,
    setPresheaf_fibre_is_discrete F⟩

theorem setPresheaf_fibre_equivalent_to_discrete
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (U : C) :
    Nonempty
      (Discrete (F.obj (Opposite.op U)) ≌
        Functor.Fiber (setPresheafProjection F) U) := by
  exact ⟨(Functor.Fiber.inducedFunctor
    (Pseudofunctor.CoGrothendieck.comp_const
      (splitFibredPseudofunctor (setPresheafToCat F)) U)).asEquivalence⟩

/-! ## The presheaf correspondence -/

/- The source's ordinary category of categories fibred in sets uses strict
   functors over the fixed base.  This is the full subcategory of `Over C`;
   it is distinct from the fixed-base bicategory above, whose 2-morphisms
   record the source's natural transformations over `C`. -/
def categoriesFibredInSetsOverObjectProperty {C : Cat.{v, u}} :
    ObjectProperty (Over C) :=
  fun X => IsCategoryFibredInSets X.hom.toFunctor

abbrev CategoriesFibredInSetsOverCategory (C : Cat.{v, u}) :=
  (categoriesFibredInSetsOverObjectProperty (C := C)).FullSubcategory

theorem categoriesFibredInSetsOver_equivalent_to_presheaves
    {C : Type uC} [Category.{vC} C] :
    Nonempty
      (Presheaf C ≌
        CategoriesFibredInSetsOverCategory (Cat.of C)) := by
  sorry

/-- A chosen equivalence in the source's presheaf correspondence.  The
existence theorem above is kept as the proposition-level interface, while
this definition makes the equivalence directly usable by later statements. -/
noncomputable def categoriesFibredInSetsOverEquivalence
    {C : Type uC} [Category.{vC} C] :
    Presheaf C ≌
      CategoriesFibredInSetsOverCategory (Cat.of C) :=
  Classical.choice (categoriesFibredInSetsOver_equivalent_to_presheaves (C := C))

/-- Every category fibred in sets is equivalent over its base to the
CoGrothendieck category of a set-valued presheaf.  This is the usable
objectwise form of the source's equivalence of categories. -/
theorem fibredInSets_equivalent_to_presheaf_construction
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSets p) :
    ∃ F : Cᵒᵖ ⥤ Type uS,
      IsFibredEquivalenceOver p (setPresheafProjection F) := by
  sorry

/-- The object-valued presheaf attached to a fibred category in sets exists;
its value at `U` is the object type of the fibre over `U`. -/
theorem fibredInSets_object_presheaf_exists
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSets p) :
    ∃ F : Cᵒᵖ ⥤ Type uS,
      ∀ U : C, Nonempty (F.obj (Opposite.op U) ≃ Functor.Fiber p U) := by
  sorry

noncomputable def fibredInSetsObjectPresheaf
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSets p) :
    Cᵒᵖ ⥤ Type uS :=
  Classical.choose (fibredInSets_object_presheaf_exists p hp)

theorem fibredInSetsObjectPresheaf_obj_equiv
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSets p) (U : C) :
    Nonempty
      ((fibredInSetsObjectPresheaf p hp).obj (Opposite.op U) ≃
        Functor.Fiber p U) := by
  exact (Classical.choose_spec (fibredInSets_object_presheaf_exists p hp)) U

/- The source warns that representability of the associated presheaf is not
   invariant under equivalence of categories fibred in groupoids.  This is
   motivation for the later equivalence-invariant treatment, rather than a
   separate predicate; the precise correspondence is recorded above. -/

/-! ## The representable example -/

@[simp]
theorem sliceProjection_object_of_hom
    {C : Type uC} [Category.{vC} C] (X U : C) (h : U ⟶ X) :
    (Over.forget X).obj (Over.mk h) = U :=
  rfl

theorem sliceProjection_fibre_object_description
    {C : Type uC} [Category.{vC} C] (X U : C)
    (x : Functor.Fiber (Over.forget X) U) :
    ∃ h : U ⟶ X, x.1 = Over.mk h := by
  sorry

theorem sliceProjection_fibre_is_discrete
    {C : Type uC} [Category.{vC} C] (X U : C) :
    IsDiscrete (Functor.Fiber (Over.forget X) U) := by
  sorry

theorem sliceProjection_isFibredInSets
    {C : Type uC} [Category.{vC} C] (X : C) :
    IsCategoryFibredInSets (Over.forget X) := by
  sorry

/-- The representable presheaf corresponds to the slice category `C/X`. -/
theorem representable_presheaf_slice_equivalence
    {C : Type uC} [Category.{vC} C] (X : C) :
    IsFibredEquivalenceOver (Over.forget X)
      (setPresheafProjection (representablePresheaf X)) := by
  sorry

end

end Formalization.Books.Categories.Unit38
