import Formalization.Books.Categories.Unit33.FibredCategories

/-!
# Categories, Chapter 34: Inertia

The relative inertia category is presented directly by its source-facing
objects and morphisms.  Its map to the base is the canonical functor obtained
from the source projection.  The surrounding over-`C` and 2-fibre-product
interfaces reuse the category-over and iso-comma constructions from the
preceding chapters.
-/

namespace Formalization.Books.Categories.Unit34

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.ObjectProperty
open Formalization.Books.Categories.Unit29
open Formalization.Books.Categories.Unit31
open Formalization.Books.Categories.Unit32
open Formalization.Books.Categories.Unit33

universe v u

noncomputable section

/-! ## Relative inertia as a category -/

/- The source's pair `(x, α)` is a genuinely different category from the
   ambient iso-comma category: its morphisms have one underlying arrow, not
   an independently chosen pair of arrows.  We therefore retain the
   canonical category-over data and define this source-facing category
   explicitly. -/

structure RelativeInertiaObject {C : Cat.{v, u}}
    {X Y : CategoryOver C} (F : CategoryOverHom X Y) where
  carrier : X.left
  automorphism : carrier ≅ carrier
  map_eq_id : (overFunctor F).map automorphism.hom =
    𝟙 ((overFunctor F).obj carrier)

structure RelativeInertiaHom {C : Cat.{v, u}}
    {X Y : CategoryOver C} {F : CategoryOverHom X Y}
    (A B : RelativeInertiaObject F) where
  hom : A.carrier ⟶ B.carrier
  comm : A.automorphism.hom ≫ hom = hom ≫ B.automorphism.hom

namespace RelativeInertiaHom

@[ext]
lemma ext {C : Cat.{v, u}} {X Y : CategoryOver C}
    {F : CategoryOverHom X Y}
    {A B : RelativeInertiaObject F} {f g : RelativeInertiaHom A B}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

end RelativeInertiaHom

instance relativeInertiaCategory {C : Cat.{v, u}}
    {X Y : CategoryOver C} (F : CategoryOverHom X Y) :
    Category (RelativeInertiaObject F) where
  Hom A B := RelativeInertiaHom A B
  id A :=
    { hom := 𝟙 A.carrier
      comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm := by
        rw [← Category.assoc, f.comm, Category.assoc, g.comm,
          ← Category.assoc] }
  id_comp f := by
    apply RelativeInertiaHom.ext
    simp
  comp_id f := by
    apply RelativeInertiaHom.ext
    simp
  assoc f g h := by
    apply RelativeInertiaHom.ext
    simp [Category.assoc]

abbrev RelativeInertiaCategory {C : Cat.{v, u}}
    {X Y : CategoryOver C} (F : CategoryOverHom X Y) :=
  RelativeInertiaObject F

/- The canonical projection and its base functor. -/

def relativeInertiaStructureMap {C : Cat.{v, u}}
    {X Y : CategoryOver C} (F : CategoryOverHom X Y) :
    RelativeInertiaCategory F ⥤ X.left where
  obj A := A.carrier
  map f := f.hom
  map_id := by
    intro A
    rfl
  map_comp := by
    intro A B D f g
    rfl

def relativeInertiaBase {C : Cat.{v, u}}
    {X Y : CategoryOver C} (F : CategoryOverHom X Y) :
    RelativeInertiaCategory F ⥤ C :=
  relativeInertiaStructureMap F ⋙ structureFunctor X

@[simp]
theorem relativeInertiaBase_obj {C : Cat.{v, u}}
    {X Y : CategoryOver C} (F : CategoryOverHom X Y)
    (A : RelativeInertiaCategory F) :
    (relativeInertiaBase F).obj A = (structureFunctor X).obj A.carrier :=
  rfl

def categoryOverToBase {C : Cat.{v, u}} (X : CategoryOver C) :
    CategoryOverHom X (CategoryOver.of (𝟙 C)) :=
  { toOver := Over.homMk X.hom (by simp [CategoryOver.of]) }

/- A universe-polymorphic interface for a functor over the fixed base.  The
   inertia category need not live in the same object universe as a bundled
   `CategoryOver`, so this is the appropriate carrier for its 1-morphisms. -/
structure FibredFunctorOver {C : Cat.{v, u}}
    {A B : Type*} [Category* A] [Category* B]
    (p : A ⥤ C) (q : B ⥤ C) where
  functor : A ⥤ B
  over : functor ⋙ q = p
  preserves : MapsStronglyCartesian p q functor

/- Natural isomorphisms in the 2-category of categories over a base have
   vertical components.  This generic form is needed here because the
   full-subcategory presentations of the inertia categories can have larger
   universes than `CategoryOver` permits. -/
def IsOverNaturalIso {A C : Type*}
    [Category* A] [Category* C]
    (p : A ⥤ C) {F G : A ⥤ A}
    (h : F ⋙ p = G ⋙ p) (e : F ≅ G) : Prop :=
  ∀ x, p.map (e.hom.app x) =
    eqToHom (congrArg (fun H : A ⥤ C => H.obj x) h)

def IsEquivalentOverBase {A B C : Type*}
    [Category* A] [Category* B] [Category* C]
    (p : A ⥤ C) (q : B ⥤ C) : Prop :=
  ∃ (F : A ⥤ B) (G : B ⥤ A),
    F ⋙ q = p ∧ G ⋙ p = q ∧
      (∃ (e : F ⋙ G ≅ 𝟭 A)
        (h : (F ⋙ G) ⋙ p = (𝟭 A) ⋙ p),
        IsOverNaturalIso p h e) ∧
      (∃ (e : G ⋙ F ≅ 𝟭 B)
        (h : (G ⋙ F) ⋙ q = (𝟭 B) ⋙ q),
        IsOverNaturalIso q h e)

/-! ## The diagonal and the 2-fibre-product description -/

/- The diagonal sends `x` to `(x, x, id)` in the iso-comma presentation of
   the 2-fibre product.  The object property records that both entries lie
   over the same base object and that the comparison arrow is vertical. -/
noncomputable def fibredCategoryDiagonalFunctor {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    X.underlying.left ⥤
      TwoFibreProductOverCategory F.underlying F.underlying where
  obj x :=
    { obj := (isoCommaDiagonal (overFunctor F.underlying)).obj x
      property := by
        refine ⟨(structureFunctor X.underlying).obj x, rfl, rfl, ?_⟩
        exact IsHomLift.id
          (congrArg (fun K : X.underlying.left ⥤ C => K.obj x)
            (overFunctor_comm F.underlying)) }
  map f :=
    ObjectProperty.homMk
      ((isoCommaDiagonal (overFunctor F.underlying)).map f)
  map_id := by
    intro x
    apply ObjectProperty.hom_ext
    rfl
  map_comp := by
    intro x y z f g
    apply ObjectProperty.hom_ext
    rfl

def fibredCategoryDiagonalOver {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    FibredFunctorOver
      (structureFunctor X.underlying)
      (twoFibreProductOverBaseFunctor F.underlying F.underlying) where
  functor := fibredCategoryDiagonalFunctor F
  over := by rfl
  preserves := by
    intro a b f hf
    let p := structureFunctor X.underlying
    let q := twoFibreProductOverBaseFunctor F.underlying F.underlying
    let D := fibredCategoryDiagonalFunctor F
    refine { toIsHomLift := ?_, universal_property' := ?_ }
    · exact Functor.IsHomLift.map _
    · intro c g τ hτ
      have hτeq :=
        @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _ q _ _
          (g ≫ q.map (D.map f)) τ hτ
      sorry

def VerticalIsoCommaProperty {A B S C : Type*}
    [Category* A] [Category* B] [Category* S] [Category* C]
    (F : A ⥤ S) (G : B ⥤ S)
    (pA : A ⥤ C) (pB : B ⥤ C) (pS : S ⥤ C)
    (_hF : F ⋙ pS = pA) (_hG : G ⋙ pS = pB) :
    ObjectProperty (IsoComma F G) :=
  fun ξ =>
    ∃ U : C,
      IsObjectLift pA U ξ.obj.left ∧
      IsObjectLift pB U ξ.obj.right ∧
      IsMorphismLift pS (𝟙 U) ξ.obj.hom

abbrev VerticalIsoComma {A B S C : Type*}
    [Category* A] [Category* B] [Category* S] [Category* C]
    (F : A ⥤ S) (G : B ⥤ S)
    (pA : A ⥤ C) (pB : B ⥤ C) (pS : S ⥤ C)
    (hF : F ⋙ pS = pA) (hG : G ⋙ pS = pB) :=
  (VerticalIsoCommaProperty F G pA pB pS hF hG).FullSubcategory

def verticalIsoCommaBase {A B S C : Type*}
    [Category* A] [Category* B] [Category* S] [Category* C]
    (F : A ⥤ S) (G : B ⥤ S)
  (pA : A ⥤ C) (pB : B ⥤ C) (pS : S ⥤ C)
    (hF : F ⋙ pS = pA) (hG : G ⋙ pS = pB) :
    VerticalIsoComma F G pA pB pS hF hG ⥤ C :=
  (VerticalIsoCommaProperty F G pA pB pS hF hG).ι ⋙
    isoCommaLeft F G ⋙ pA

theorem fibredCategoryDiagonal_over_base {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    fibredCategoryDiagonalFunctor F ⋙
      twoFibreProductOverBaseFunctor F.underlying F.underlying =
      structureFunctor X.underlying := by
  rfl

/- The category obtained by taking the 2-fibre product of the two diagonal
   maps is the source's iterated diagonal 2-fibre product. -/
def relativeInertiaDiagonalProductCategory {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :=
  VerticalIsoComma
    (fibredCategoryDiagonalFunctor F) (fibredCategoryDiagonalFunctor F)
    (structureFunctor X.underlying) (structureFunctor X.underlying)
    (twoFibreProductOverBaseFunctor F.underlying F.underlying)
    (fibredCategoryDiagonal_over_base F) (fibredCategoryDiagonal_over_base F)

theorem relativeInertia_equivalent_to_diagonal_product {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    IsEquivalentOverBase
      (relativeInertiaBase F.underlying)
      (verticalIsoCommaBase
        (fibredCategoryDiagonalFunctor F) (fibredCategoryDiagonalFunctor F)
        (structureFunctor X.underlying) (structureFunctor X.underlying)
        (twoFibreProductOverBaseFunctor F.underlying F.underlying)
        (fibredCategoryDiagonal_over_base F)
        (fibredCategoryDiagonal_over_base F)) := by
  sorry

/- A cartesian lift in the relative inertia can be chosen with an underlying
   cartesian lift in the source category. -/
private theorem relativeInertia_exists_stronglyCartesian {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S)
    (b : RelativeInertiaCategory F.underlying) (R : C)
    (f : R ⟶ (relativeInertiaBase F.underlying).obj b) :
    ∃ (a : X.underlying.left) (φ : a ⟶ b.carrier),
      (structureFunctor X.underlying).IsStronglyCartesian f φ ∧
      ∃ (a' : RelativeInertiaCategory F.underlying) (κ : a' ⟶ b),
        (relativeInertiaBase F.underlying).IsStronglyCartesian f κ ∧
          ∃ (h : a'.carrier = a), κ.hom = eqToHom h ≫ φ := by
  change R ⟶ (structureFunctor X.underlying).obj b.carrier at f
  obtain ⟨a, φ, hφ⟩ :=
    (fibred_category_iff_exists_stronglyCartesian
      (structureFunctor X.underlying)).mp inferInstance
      b.carrier R f
  have hdom : (structureFunctor X.underlying).obj a = R :=
    CategoryTheory.IsHomLift.domain_eq
      (structureFunctor X.underlying) f φ
  subst R
  have hauto : (structureFunctor X.underlying).map b.automorphism.hom =
      𝟙 _ := by
    have h := congrArg (structureFunctor S.underlying).map b.map_eq_id
    rw [← Functor.comp_map] at h
    have hcomp := Functor.congr_hom
      (overFunctor_comm F.underlying) b.automorphism.hom
    rw [hcomp] at h
    have h' := congrArg (fun k => k ≫ eqToHom
      (Functor.congr_obj (overFunctor_comm F.underlying) b.carrier)) h
    apply (cancel_epi (eqToHom
      (Functor.congr_obj (overFunctor_comm F.underlying) b.carrier))).1
    simpa using h'
  let : (structureFunctor X.underlying).IsStronglyCartesian f φ := hφ
  have hφauto : (structureFunctor X.underlying).IsHomLift f
      (φ ≫ b.automorphism.hom) := by
    have hcomp : (structureFunctor X.underlying).IsHomLift
        (f ≫ (structureFunctor X.underlying).map b.automorphism.hom)
        (φ ≫ b.automorphism.hom) := by infer_instance
    simpa [hauto] using hcomp
  let : (structureFunctor X.underlying).IsHomLift
      (𝟙 _ ≫ f) (φ ≫ b.automorphism.hom) := by
    simpa using hφauto
  obtain ⟨β, hβprop, hβuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property'
      (p := structureFunctor X.underlying)
      (f := f) (φ := φ) (𝟙 _) (φ ≫ b.automorphism.hom)
  rcases hβprop with ⟨hβ, hβfac⟩
  have hauto_inv :
      (structureFunctor X.underlying).map b.automorphism.inv = 𝟙 _ := by
    calc
      (structureFunctor X.underlying).map b.automorphism.inv =
          (structureFunctor X.underlying).map b.automorphism.inv ≫ 𝟙 _ := by simp
      _ = (structureFunctor X.underlying).map b.automorphism.inv ≫
          (structureFunctor X.underlying).map b.automorphism.hom := by
            rw [hauto]
      _ = (structureFunctor X.underlying).map
          (b.automorphism.inv ≫ b.automorphism.hom) := by
            rw [Functor.map_comp]
      _ = (structureFunctor X.underlying).map (𝟙 b.carrier) := by
            rw [b.automorphism.inv_hom_id]
      _ = 𝟙 _ := by simp
  have hφauto_inv : (structureFunctor X.underlying).IsHomLift f
      (φ ≫ b.automorphism.inv) := by
    have hcomp : (structureFunctor X.underlying).IsHomLift
        (f ≫ (structureFunctor X.underlying).map b.automorphism.inv)
        (φ ≫ b.automorphism.inv) := by infer_instance
    simpa [hauto_inv] using hcomp
  let : (structureFunctor X.underlying).IsHomLift
      (𝟙 _ ≫ f) (φ ≫ b.automorphism.inv) := by
    simpa using hφauto_inv
  obtain ⟨βinv, hβinvprop, hβinvuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property'
      (p := structureFunctor X.underlying)
      (f := f) (φ := φ) (𝟙 _) (φ ≫ b.automorphism.inv)
  rcases hβinvprop with ⟨hβinv, hβinvfac⟩
  let : (structureFunctor X.underlying).IsHomLift
      (𝟙 _) β := hβ
  let : (structureFunctor X.underlying).IsHomLift
      (𝟙 _) βinv := hβinv
  have hββinv : β ≫ βinv = 𝟙 a := by
    apply Functor.IsStronglyCartesian.ext
      (structureFunctor X.underlying) f φ (𝟙 _)
    rw [Category.assoc, hβinvfac, ← Category.assoc, hβfac,
      Category.assoc, b.automorphism.hom_inv_id, Category.comp_id]
    simp
  have hβinvβ : βinv ≫ β = 𝟙 a := by
    apply Functor.IsStronglyCartesian.ext
      (structureFunctor X.underlying) f φ (𝟙 _)
    rw [Category.assoc, hβfac, ← Category.assoc, hβinvfac,
      Category.assoc, b.automorphism.inv_hom_id, Category.comp_id]
    simp
  have hf : f = (structureFunctor X.underlying).map φ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift
      (structureFunctor X.underlying) f φ
  have hφ' : (structureFunctor X.underlying).IsStronglyCartesian
      ((structureFunctor X.underlying).map φ) φ := by
    simpa [hf] using hφ
  have hFφ := F.preserves φ hφ'
  have hβmap : (structureFunctor X.underlying).map β = 𝟙 _ :=
    (CategoryTheory.IsHomLift.eq_of_isHomLift
      (structureFunctor X.underlying) (𝟙 _) β).symm
  have hβtarget :
      (structureFunctor S.underlying).map
          ((overFunctor F.underlying).map β) = 𝟙 _ := by
    rw [← Functor.comp_map]
    rw [Functor.congr_hom (overFunctor_comm F.underlying), hβmap]
    simp
  have hβfac_target :
      (overFunctor F.underlying).map β ≫
          (overFunctor F.underlying).map φ =
        (overFunctor F.underlying).map φ := by
    have h := congrArg (overFunctor F.underlying).map hβfac
    simpa [Functor.map_comp, b.map_eq_id] using h
  have hβtarget_lift :
      (structureFunctor S.underlying).IsHomLift
        (𝟙 ((structureFunctor S.underlying).obj
          ((overFunctor F.underlying).obj a)))
        ((overFunctor F.underlying).map β) := by
    have h := Functor.IsHomLift.map
      (p := structureFunctor S.underlying)
      ((overFunctor F.underlying).map β)
    simpa [hβtarget] using h
  have hβmap_target :
      (overFunctor F.underlying).map β = 𝟙 _ := by
    let : (structureFunctor S.underlying).IsStronglyCartesian
        ((structureFunctor S.underlying).map
          ((overFunctor F.underlying).map φ))
        ((overFunctor F.underlying).map φ) := hFφ
    apply Functor.IsStronglyCartesian.ext
      (p := structureFunctor S.underlying)
      (f := (structureFunctor S.underlying).map
        ((overFunctor F.underlying).map φ))
      (φ := (overFunctor F.underlying).map φ)
      (𝟙 ((structureFunctor S.underlying).obj
        ((overFunctor F.underlying).obj a)))
    simp [hβfac_target]
  let βiso : a ≅ a :=
    { hom := β
      inv := βinv
      hom_inv_id := hββinv
      inv_hom_id := hβinvβ }
  let a' : RelativeInertiaCategory F.underlying :=
    { carrier := a
      automorphism := βiso
      map_eq_id := hβmap_target }
  let κ : a' ⟶ b :=
    { hom := by simpa [a'] using φ
      comm := by simpa [a', βiso] using hβfac }
  refine ⟨a, φ, hφ, a', κ, ?_, ?_⟩
  · have hκ : (relativeInertiaBase F.underlying).IsHomLift f κ := by
      let ha : (structureFunctor X.underlying).obj a'.carrier =
          (relativeInertiaBase F.underlying).obj a' := rfl
      let hb : (structureFunctor X.underlying).obj b.carrier =
          (relativeInertiaBase F.underlying).obj b := rfl
      refine CategoryTheory.IsHomLift.of_fac'
        (relativeInertiaBase F.underlying) f κ ha hb ?_
      have hφeq := CategoryTheory.IsHomLift.eq_of_isHomLift
        (structureFunctor X.underlying) f φ
      dsimp [relativeInertiaBase, relativeInertiaStructureMap, κ]
      have ha' : ha = rfl := Subsingleton.elim _ _
      rw [ha', hφeq]
      simp
    refine { toIsHomLift := hκ, universal_property' := ?_ }
    intro c g ψ hψ
    let : (relativeInertiaBase F.underlying).IsHomLift
        (g ≫ f) ψ := hψ
    let ha : (structureFunctor X.underlying).obj c.carrier =
        (relativeInertiaBase F.underlying).obj c := rfl
    let g₀ : (structureFunctor X.underlying).obj c.carrier ⟶
        (structureFunctor X.underlying).obj a :=
      eqToHom ha ≫ g
    have hψ' : (structureFunctor X.underlying).IsHomLift
        (g₀ ≫ f) ψ.hom := by
      refine CategoryTheory.IsHomLift.of_fac'
        (structureFunctor X.underlying)
        (R := (structureFunctor X.underlying).obj c.carrier)
        (S := (structureFunctor X.underlying).obj b.carrier)
        (g₀ ≫ f) ψ.hom rfl rfl ?_
      have hfac := CategoryTheory.IsHomLift.fac'
        (relativeInertiaBase F.underlying)
        (g ≫ f) ψ
      have hd := CategoryTheory.IsHomLift.domain_eq
        (relativeInertiaBase F.underlying)
        (g ≫ f) ψ
      rw [eqToHom_refl _ hd] at hfac
      dsimp [relativeInertiaBase, relativeInertiaStructureMap] at hfac
      have hg₀ : g₀ = g := by
        dsimp [g₀]
        exact eq_of_heq (eqToHom_comp_heq g ha)
      convert hfac using 1
      · rw [hg₀]
        simp
    let : (structureFunctor X.underlying).IsStronglyCartesian f φ := hφ
    let : (structureFunctor X.underlying).IsHomLift (g₀ ≫ f) ψ.hom := hψ'
    obtain ⟨χ, hχprop, hχuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property'
        (p := structureFunctor X.underlying)
        (f := f) (φ := φ) g₀ ψ.hom
    rcases hχprop with ⟨hχ, hχfac⟩
    have hauto_c :
        (structureFunctor X.underlying).map c.automorphism.hom = 𝟙 _ := by
      have h := congrArg (structureFunctor S.underlying).map c.map_eq_id
      rw [← Functor.comp_map] at h
      have hcomp := Functor.congr_hom
        (overFunctor_comm F.underlying) c.automorphism.hom
      rw [hcomp] at h
      have h' := congrArg (fun k => k ≫ eqToHom
        (Functor.congr_obj (overFunctor_comm F.underlying) c.carrier)) h
      apply (cancel_epi (eqToHom
        (Functor.congr_obj (overFunctor_comm F.underlying) c.carrier))).1
      simpa using h'
    let : (structureFunctor X.underlying).IsHomLift
        (𝟙 ((structureFunctor X.underlying).obj c.carrier))
        c.automorphism.hom := by
      rw [← hauto_c]
      exact Functor.IsHomLift.map _
    let : (structureFunctor X.underlying).IsHomLift g₀ χ := hχ
    have hcomm : c.automorphism.hom ≫ χ = χ ≫ β := by
      apply Functor.IsStronglyCartesian.ext
        (p := structureFunctor X.underlying) (f := f) (φ := φ) g₀
      calc
        (c.automorphism.hom ≫ χ) ≫ φ =
            c.automorphism.hom ≫ (χ ≫ φ) := by simp [Category.assoc]
        _ = c.automorphism.hom ≫ ψ.hom := by rw [hχfac]
        _ = ψ.hom ≫ b.automorphism.hom := ψ.comm
        _ = (χ ≫ φ) ≫ b.automorphism.hom := by rw [hχfac]
        _ = χ ≫ (φ ≫ b.automorphism.hom) := by simp [Category.assoc]
        _ = χ ≫ (β ≫ φ) := by rw [hβfac]
        _ = (χ ≫ β) ≫ φ := by simp [Category.assoc]
    let χ' : c ⟶ a' :=
      { hom := χ
        comm := by simpa [a', βiso] using hcomm }
    refine ⟨χ', ⟨?_, ?_⟩, ?_⟩
    · have hχ' : (relativeInertiaBase F.underlying).IsHomLift g χ' := by
        let hb : (structureFunctor X.underlying).obj a'.carrier =
            (relativeInertiaBase F.underlying).obj a' := rfl
        refine CategoryTheory.IsHomLift.of_fac'
          (relativeInertiaBase F.underlying) g χ' ha hb ?_
        have hχeq := CategoryTheory.IsHomLift.eq_of_isHomLift
          (structureFunctor X.underlying) g₀ χ
        dsimp [relativeInertiaBase, relativeInertiaStructureMap, χ']
        convert hχeq.symm using 1
        apply eq_of_heq
        exact
          (eqToHom_comp_heq (g ≫ eqToHom hb.symm) ha).trans
            ((comp_eqToHom_heq g hb.symm).trans
              (eqToHom_comp_heq g ha).symm)
      exact hχ'
    · apply RelativeInertiaHom.ext
      change χ ≫ φ = ψ.hom
      exact hχfac
    · intro ζ hζ
      rcases hζ with ⟨hζ, hζfac⟩
      apply RelativeInertiaHom.ext
      have hζeq :=
        @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
          (relativeInertiaBase F.underlying) _ _ g ζ hζ
      dsimp [relativeInertiaBase, relativeInertiaStructureMap] at hζeq
      change g = (structureFunctor X.underlying).map ζ.hom at hζeq
      have hζ₀' : (structureFunctor X.underlying).IsHomLift g₀ ζ.hom := by
        have ha' : ha = rfl := Subsingleton.elim _ _
        have hζeq' : g₀ = (structureFunctor X.underlying).map ζ.hom := by
          dsimp [g₀]
          rw [ha']
          exact eq_of_heq ((eqToHom_comp_heq g ha).trans (heq_of_eq hζeq))
        change (structureFunctor X.underlying).IsHomLift g₀ ζ.hom
        rw [hζeq']
        exact Functor.IsHomLift.map _
      let : (structureFunctor X.underlying).IsHomLift g₀ ζ.hom := hζ₀'
      have hζfac' : ζ.hom ≫ φ = ψ.hom := by
        dsimp [κ] at hζfac
        exact congrArg (fun k => k.hom) hζfac
      exact hχuniq ζ.hom ⟨hζ₀', hζfac'⟩
  · refine ⟨rfl, ?_⟩
    simp [κ, a']

/- The fibredness assertion in the source lemma. -/
theorem relativeInertia_isFibred {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    (relativeInertiaBase F.underlying).IsFibered := by
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro b R f
  obtain ⟨a, φ, hφ, a', κ, hκ, -⟩ :=
    relativeInertia_exists_stronglyCartesian F b R f
  exact ⟨a', κ, hκ⟩

/-! ## Relative and absolute inertia -/

/- The identity category over `C` is the target used in the absolute case.
   Its fibredness is an earlier standard fact about the identity functor; it
   is kept as an interface so the inertia definitions themselves have real
   structure bodies. -/
private theorem identityFunctor_isStronglyCartesian {C : Cat.{v, u}}
    {R S : C} (f : R ⟶ S) :
    (𝟭 C).IsStronglyCartesian f f := by
  let hf : (𝟭 C).IsHomLift f f := by
    exact Functor.IsHomLift.map f
  refine { toIsHomLift := hf, universal_property' := ?_ }
  intro c g φ hφ
  refine ⟨g, ⟨Functor.IsHomLift.map g, ?_⟩, ?_⟩
  · simpa using (CategoryTheory.IsHomLift.eq_of_isHomLift (𝟭 C) (g ≫ f) φ)
  · intro χ hχ
    simpa using
      (@CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
        (𝟭 C) _ _ g χ hχ.1).symm

theorem identityCategoryOver_isFibred (C : Cat.{v, u}) :
    (structureFunctor (CategoryOver.of (𝟙 C))).IsFibered := by
  change (𝟭 C).IsFibered
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro a R f
  refine ⟨R, f, ?_⟩
  exact identityFunctor_isStronglyCartesian f

def identityFibredCategoryOver (C : Cat.{v, u}) : FibredCategoryOver C where
  underlying := CategoryOver.of (𝟙 C)
  isFibred := identityCategoryOver_isFibred C

def toBaseFibredHom {C : Cat.{v, u}}
    (X : FibredCategoryOver C) :
    FibredCategoryOverHom X (identityFibredCategoryOver C) where
  underlying := categoryOverToBase X.underlying
  preserves := by
    intro a b φ hφ
    change (𝟭 C).IsStronglyCartesian
      ((structureFunctor X.underlying).map φ)
      ((structureFunctor X.underlying).map φ)
    exact identityFunctor_isStronglyCartesian _

abbrev RelativeInertia {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :=
  RelativeInertiaCategory F.underlying

abbrev Inertia {C : Cat.{v, u}} (X : FibredCategoryOver C) :=
  RelativeInertia (toBaseFibredHom X)

/-! ## Structure maps and neutral sections -/

def relativeInertiaStructureOver {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    FibredFunctorOver (relativeInertiaBase F.underlying)
      (structureFunctor X.underlying) where
  functor := relativeInertiaStructureMap F.underlying
  over := rfl
  preserves := by
    intro a b κ hκ
    obtain ⟨c, φ, hφ, c', κ₀, hκ₀, hcar, hhom⟩ :=
      relativeInertia_exists_stronglyCartesian F b
        ((relativeInertiaBase F.underlying).obj a)
        ((relativeInertiaBase F.underlying).map κ)
    cases hcar
    have hhom' : κ₀.hom = φ := by
      simpa using hhom
    let p := relativeInertiaBase F.underlying
    let U := relativeInertiaStructureMap F.underlying
    let q := structureFunctor X.underlying
    have hκp : p.IsStronglyCartesian (p.map κ) κ := hκ
    have hκ₀p : p.IsStronglyCartesian (p.map κ) κ₀ := hκ₀
    let e := @Functor.IsStronglyCartesian.domainIsoOfBaseIso
      _ _ _ _ p (p.obj a) (p.obj a) (p.obj b) a c' b
      (p.map κ) (p.map κ) (Iso.refl (p.obj a)) (by simp)
      κ κ₀ hκp hκ₀p
    have he_fac : e.hom ≫ κ = κ₀ := by
      dsimp [e, Functor.IsStronglyCartesian.domainIsoOfBaseIso]
      exact Functor.IsStronglyCartesian.fac p (p.map κ) κ (by simp) κ₀
    have he_inv_fac : e.inv ≫ κ₀ = κ := by
      apply RelativeInertiaHom.ext
      change e.inv.hom ≫ κ₀.hom = κ.hom
      have h := congrArg (fun k => k.hom) he_fac
      change e.hom.hom ≫ κ.hom = κ₀.hom at h
      have hinv : e.inv.hom ≫ e.hom.hom = 𝟙 _ :=
        congrArg (fun k => k.hom) e.inv_hom_id
      calc
        e.inv.hom ≫ κ₀.hom =
            e.inv.hom ≫ (e.hom.hom ≫ κ.hom) := by rw [h]
        _ = (e.inv.hom ≫ e.hom.hom) ≫ κ.hom := by
          simp [Category.assoc]
        _ = κ.hom := by rw [hinv]; simp
    have hκ₀q : q.IsStronglyCartesian (p.map κ) κ₀.hom := by
      simpa [hhom', q, p] using hφ
    let eX : c'.carrier ≅ a.carrier := U.mapIso e
    have hp_e : p.IsHomLift (𝟙 (p.obj a)) e.inv := by
      simpa [e] using
        (@Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift
          _ _ _ _ p (p.obj a) (p.obj a) (p.obj b) a c' b
          (p.map κ) (p.map κ) (Iso.refl (p.obj a)) (by simp)
          κ κ₀ hκp hκ₀p)
    have hq_e : q.IsHomLift (𝟙 (q.obj a.carrier)) eX.symm.hom := by
      let hb : q.obj c'.carrier = q.obj a.carrier :=
        @CategoryTheory.IsHomLift.codomain_eq _ _ _ _ p
          (p.obj a) (p.obj a) a c' (𝟙 (p.obj a)) e.inv hp_e
      refine CategoryTheory.IsHomLift.of_fac' q
        (𝟙 (q.obj a.carrier)) eX.symm.hom rfl hb ?_
      have hfac :=
        @CategoryTheory.IsHomLift.fac' _ _ _ _ p
          (p.obj a) (p.obj a) a c' (𝟙 (p.obj a)) e.inv hp_e
      have hc :
          (@CategoryTheory.IsHomLift.codomain_eq _ _ _ _ p
            (p.obj a) (p.obj a) a c' (𝟙 (p.obj a)) e.inv hp_e) = hb :=
        Subsingleton.elim _ _
      have hd :
          (@CategoryTheory.IsHomLift.domain_eq _ _ _ _ p
            (p.obj a) (p.obj a) a c' (𝟙 (p.obj a)) e.inv hp_e) = rfl :=
        Subsingleton.elim _ _
      rw [hd, hc] at hfac
      dsimp [eX, U]
      change q.map ((relativeInertiaStructureMap F.underlying).map e.inv) =
        eqToHom rfl ≫ 𝟙 _ ≫ eqToHom hb.symm
      change q.map ((relativeInertiaStructureMap F.underlying).map e.inv) =
        eqToHom rfl ≫ 𝟙 _ ≫ eqToHom hb.symm at hfac
      exact hfac
    have heXq : q.IsStronglyCartesian (𝟙 (q.obj a.carrier)) eX.symm.hom :=
      Functor.IsStronglyCartesian.of_iso q (𝟙 (q.obj a.carrier)) eX.symm
    have heX_fac : eX.symm.hom ≫ κ₀.hom = κ.hom := by
      have h := congrArg (fun k => k.hom) he_inv_fac
      dsimp [eX, U]
      change e.inv.hom ≫ κ₀.hom = κ.hom
      change e.inv.hom ≫ κ₀.hom = κ.hom at h
      exact h
    have hcomp : q.IsStronglyCartesian
        ((𝟙 (q.obj a.carrier)) ≫ p.map κ)
        (eX.symm.hom ≫ κ₀.hom) := by
      exact @Functor.IsStronglyCartesian.comp _ _ _ _ q
        (q.obj a.carrier) (q.obj a.carrier) (q.obj b.carrier)
        a.carrier c'.carrier b.carrier
        (𝟙 (q.obj a.carrier)) (p.map κ)
        eX.symm.hom κ₀.hom heXq hκ₀q
    rw [heX_fac] at hcomp
    simpa [p, q, U, relativeInertiaBase, relativeInertiaStructureMap] using hcomp

private theorem relativeInertia_isStronglyCartesian_of_underlying
    {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S)
    {a b : RelativeInertiaCategory F.underlying} (κ : a ⟶ b)
    (hκ : (structureFunctor X.underlying).IsStronglyCartesian
      ((structureFunctor X.underlying).map κ.hom) κ.hom) :
    (relativeInertiaBase F.underlying).IsStronglyCartesian
      ((relativeInertiaBase F.underlying).map κ) κ := by
  let p := relativeInertiaBase F.underlying
  let q := structureFunctor X.underlying
  refine { toIsHomLift := ?_, universal_property' := ?_ }
  · refine CategoryTheory.IsHomLift.of_fac' p (p.map κ) κ rfl rfl ?_
    let : q.IsHomLift (q.map κ.hom) κ.hom :=
      Functor.IsHomLift.map κ.hom
    have hfac := CategoryTheory.IsHomLift.fac q (q.map κ.hom) κ.hom
    dsimp [p, q, relativeInertiaBase, relativeInertiaStructureMap]
    change q.map κ.hom = eqToHom rfl ≫ q.map κ.hom ≫ eqToHom rfl
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hfac ⊢
  · intro c g τ hτ
    have hτeq :=
      @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _ p _ _
        (g ≫ p.map κ) τ hτ
    dsimp [p, q, relativeInertiaBase, relativeInertiaStructureMap] at hτeq
    change g ≫ q.map κ.hom = q.map τ.hom at hτeq
    have hτq : q.IsHomLift (g ≫ q.map κ.hom) τ.hom := by
      rw [hτeq]
      exact Functor.IsHomLift.map _
    obtain ⟨χ, hχprop, hχuniq⟩ :=
      @Functor.IsStronglyCartesian.universal_property' _ _ _ _ q
        (q.obj a.carrier) (q.obj b.carrier) a.carrier b.carrier
        (q.map κ.hom) κ.hom hκ c.carrier g τ.hom hτq
    rcases hχprop with ⟨hχ, hχfac⟩
    have hauto (x : RelativeInertiaCategory F.underlying) :
        q.map x.automorphism.hom = 𝟙 _ := by
      change (structureFunctor X.underlying).map x.automorphism.hom = 𝟙 _
      have h := congrArg (structureFunctor S.underlying).map x.map_eq_id
      rw [← Functor.comp_map] at h
      have hcomp := Functor.congr_hom
        (overFunctor_comm F.underlying) x.automorphism.hom
      rw [hcomp] at h
      have h' := congrArg (fun k => k ≫ eqToHom
        (Functor.congr_obj (overFunctor_comm F.underlying) x.carrier)) h
      apply (cancel_epi (eqToHom
        (Functor.congr_obj (overFunctor_comm F.underlying) x.carrier))).1
      simpa [q] using h'
    let : q.IsHomLift (𝟙 (q.obj c.carrier)) c.automorphism.hom := by
      rw [← hauto c]
      exact Functor.IsHomLift.map _
    let : q.IsHomLift g χ := hχ
    have hχleft : q.IsHomLift g (c.automorphism.hom ≫ χ) := by
      exact CategoryTheory.IsHomLift.comp_lift_id_left' q
        (q.obj c.carrier) c.automorphism.hom g χ
    let : q.IsHomLift (𝟙 (q.obj a.carrier)) a.automorphism.hom := by
      rw [← hauto a]
      exact Functor.IsHomLift.map _
    have hχright : q.IsHomLift g (χ ≫ a.automorphism.hom) := by
      exact CategoryTheory.IsHomLift.comp_lift_id_right' q
        g χ (q.obj a.carrier) a.automorphism.hom
    let : q.IsHomLift g (c.automorphism.hom ≫ χ) := hχleft
    let : q.IsHomLift g (χ ≫ a.automorphism.hom) := hχright
    have hcomm : c.automorphism.hom ≫ χ =
        χ ≫ a.automorphism.hom := by
      apply @Functor.IsStronglyCartesian.ext _ _ _ _ q
        (q.obj a.carrier) (q.obj b.carrier) a.carrier b.carrier
        (q.map κ.hom) κ.hom hκ
        (q.obj c.carrier) c.carrier g
        (c.automorphism.hom ≫ χ) (χ ≫ a.automorphism.hom)
        hχleft hχright
      calc
        (c.automorphism.hom ≫ χ) ≫ κ.hom =
            c.automorphism.hom ≫ (χ ≫ κ.hom) := by simp [Category.assoc]
        _ = c.automorphism.hom ≫ τ.hom := by rw [hχfac]
        _ = τ.hom ≫ b.automorphism.hom := by exact τ.comm
        _ = (χ ≫ κ.hom) ≫ b.automorphism.hom := by rw [hχfac]
        _ = χ ≫ (κ.hom ≫ b.automorphism.hom) := by simp [Category.assoc]
        _ = χ ≫ (a.automorphism.hom ≫ κ.hom) := by rw [κ.comm]
        _ = (χ ≫ a.automorphism.hom) ≫ κ.hom := by simp [Category.assoc]
    let χ' : c ⟶ a :=
      { hom := χ
        comm := hcomm }
    have hχ' : p.IsHomLift g χ' := by
      let ha : q.obj c.carrier = p.obj c := rfl
      let hb : q.obj a.carrier = p.obj a := rfl
      refine CategoryTheory.IsHomLift.of_fac' p g χ' ha hb ?_
      have hχeq :=
        @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _ q _ _ g χ hχ
      dsimp [p, q, relativeInertiaBase, relativeInertiaStructureMap, χ']
      rw [hχeq]
      exact eq_of_heq <|
        (comp_eqToHom_heq (q.map χ) hb.symm).symm.trans
          (eqToHom_comp_heq (q.map χ ≫ eqToHom hb.symm) ha).symm
    refine ⟨χ', ⟨hχ', ?_⟩, ?_⟩
    · apply RelativeInertiaHom.ext
      change χ ≫ κ.hom = τ.hom
      exact hχfac
    · intro ζ hζ
      apply RelativeInertiaHom.ext
      have hζeq :=
        @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _ p _ _ g ζ hζ.1
      dsimp [p, q, relativeInertiaBase, relativeInertiaStructureMap] at hζeq
      change g = q.map ζ.hom at hζeq
      have hζq : q.IsHomLift g ζ.hom := by
        rw [hζeq]
        exact Functor.IsHomLift.map _
      have hζfac : ζ.hom ≫ κ.hom = τ.hom := by
        exact congrArg (fun k => k.hom) hζ.2
      exact hχuniq ζ.hom ⟨hζq, hζfac⟩

abbrev inertiaStructureMap {C : Cat.{v, u}}
    (X : FibredCategoryOver C) :
    Inertia X ⥤ X.underlying.left :=
  relativeInertiaStructureMap (toBaseFibredHom X).underlying

abbrev inertiaStructureOver {C : Cat.{v, u}}
    (X : FibredCategoryOver C) :
    FibredFunctorOver (relativeInertiaBase (toBaseFibredHom X).underlying)
      (structureFunctor X.underlying) :=
  relativeInertiaStructureOver (toBaseFibredHom X)

def relativeInertiaNeutralSection {C : Cat.{v, u}}
    {X S : CategoryOver C} (F : CategoryOverHom X S) :
    X.left ⥤ RelativeInertiaCategory F where
  obj x :=
    { carrier := x
      automorphism := Iso.refl x
      map_eq_id := by simp }
  map f :=
    { hom := f
      comm := by simp }
  map_id := by
    intro x
    apply RelativeInertiaHom.ext
    rfl
  map_comp := by
    intro x y z f g
    apply RelativeInertiaHom.ext
    rfl

def relativeInertiaNeutralSectionOver {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    FibredFunctorOver (structureFunctor X.underlying)
      (relativeInertiaBase F.underlying) where
  functor := relativeInertiaNeutralSection F.underlying
  over := by rfl
  preserves := by
    intro a b φ hφ
    change Functor.IsStronglyCartesian
      (relativeInertiaBase F.underlying)
      ((structureFunctor X.underlying).map φ)
      ((relativeInertiaNeutralSection F.underlying).map φ)
    let : Functor.IsStronglyCartesian
        (structureFunctor X.underlying)
        ((structureFunctor X.underlying).map φ) φ := hφ
    let : (relativeInertiaBase F.underlying).IsHomLift
        ((structureFunctor X.underlying).map φ)
        ((relativeInertiaNeutralSection F.underlying).map φ) := by
      change (relativeInertiaBase F.underlying).IsHomLift
        ((relativeInertiaBase F.underlying).map
          ((relativeInertiaNeutralSection F.underlying).map φ))
        ((relativeInertiaNeutralSection F.underlying).map φ)
      exact Functor.IsHomLift.map _
    refine { universal_property' := ?_ }
    intro c g ψ hψ
    let : (relativeInertiaBase F.underlying).IsHomLift
        (g ≫ (relativeInertiaBase F.underlying).map
          ((relativeInertiaNeutralSection F.underlying).map φ)) ψ := hψ
    have hψ' : (structureFunctor X.underlying).IsHomLift
        (g ≫ (structureFunctor X.underlying).map φ) ψ.hom := by
      let ha : (structureFunctor X.underlying).obj c.carrier =
          (relativeInertiaBase F.underlying).obj c := rfl
      let hb : (structureFunctor X.underlying).obj
            ((relativeInertiaNeutralSection F.underlying).obj b).carrier =
          (relativeInertiaBase F.underlying).obj
            ((relativeInertiaNeutralSection F.underlying).obj b) := rfl
      refine CategoryTheory.IsHomLift.of_fac'
        (structureFunctor X.underlying)
        (R := (relativeInertiaBase F.underlying).obj c)
        (S := (relativeInertiaBase F.underlying).obj
          ((relativeInertiaNeutralSection F.underlying).obj b))
        (g ≫ (structureFunctor X.underlying).map φ) ψ.hom
        ha hb ?_
      have hfac := CategoryTheory.IsHomLift.fac'
        (relativeInertiaBase F.underlying)
        (g ≫ (relativeInertiaBase F.underlying).map
          ((relativeInertiaNeutralSection F.underlying).map φ)) ψ
      have hd := CategoryTheory.IsHomLift.domain_eq
        (relativeInertiaBase F.underlying)
        (g ≫ (relativeInertiaBase F.underlying).map
          ((relativeInertiaNeutralSection F.underlying).map φ)) ψ
      have hc := CategoryTheory.IsHomLift.codomain_eq
        (relativeInertiaBase F.underlying)
        (g ≫ (relativeInertiaBase F.underlying).map
          ((relativeInertiaNeutralSection F.underlying).map φ)) ψ
      rw [eqToHom_refl _ hd, eqToHom_refl _ hc] at hfac
      dsimp [relativeInertiaBase, relativeInertiaStructureMap,
        relativeInertiaNeutralSection] at hfac
      dsimp [relativeInertiaNeutralSection]
      convert hfac using 1
      · rfl
      · rfl
    have hauto : (structureFunctor X.underlying).map c.automorphism.hom =
        𝟙 _ := by
      have h := congrArg (structureFunctor S.underlying).map c.map_eq_id
      rw [← Functor.comp_map] at h
      have hcomp := Functor.congr_hom
        (overFunctor_comm F.underlying) c.automorphism.hom
      rw [hcomp] at h
      have h' := congrArg (fun k => k ≫ eqToHom
        (Functor.congr_obj (overFunctor_comm F.underlying) c.carrier)) h
      apply (cancel_epi (eqToHom
        (Functor.congr_obj (overFunctor_comm F.underlying) c.carrier))).1
      simpa using h'
    let : (structureFunctor X.underlying).IsHomLift
        (𝟙 ((structureFunctor X.underlying).obj c.carrier))
        c.automorphism.hom := by
      rw [← hauto]
      exact Functor.IsHomLift.map _
    let g₀ : (structureFunctor X.underlying).obj c.carrier ⟶
        (structureFunctor X.underlying).obj a := g
    let ψ₀ : c.carrier ⟶ b := ψ.hom
    have hψ₀ : (structureFunctor X.underlying).IsHomLift
        (g₀ ≫ (structureFunctor X.underlying).map φ) ψ₀ := by
      change (structureFunctor X.underlying).IsHomLift
        (g ≫ (structureFunctor X.underlying).map φ) ψ.hom
      exact hψ'
    let : (structureFunctor X.underlying).IsHomLift
        (g₀ ≫ (structureFunctor X.underlying).map φ) ψ₀ := hψ₀
    obtain ⟨χ, hχprop, hχuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property'
        (p := structureFunctor X.underlying)
        (R := (structureFunctor X.underlying).obj a)
        (S := (structureFunctor X.underlying).obj b)
        (a := a) (b := b) (f := (structureFunctor X.underlying).map φ)
        (φ := φ) (a' := c.carrier) g₀ ψ₀
    rcases hχprop with ⟨hχ, hχfac⟩
    let : (structureFunctor X.underlying).IsHomLift g₀ χ := hχ
    have hcomm : c.automorphism.hom ≫ χ = χ := by
      apply Functor.IsStronglyCartesian.ext
        (structureFunctor X.underlying)
        ((structureFunctor X.underlying).map φ) φ g₀
      simpa [Category.assoc, hχfac, ψ₀, relativeInertiaNeutralSection] using ψ.comm
    let χ' : c ⟶ (relativeInertiaNeutralSection F.underlying).obj a :=
      { hom := χ
        comm := by simpa [relativeInertiaNeutralSection] using hcomm }
    refine ⟨χ', ⟨?_, ?_⟩, ?_⟩
    · have hχ' : (relativeInertiaBase F.underlying).IsHomLift g χ' := by
        let ha : (structureFunctor X.underlying).obj c.carrier =
            (relativeInertiaBase F.underlying).obj c := rfl
        let hb : (structureFunctor X.underlying).obj
              ((relativeInertiaNeutralSection F.underlying).obj a).carrier =
            (relativeInertiaBase F.underlying).obj
              ((relativeInertiaNeutralSection F.underlying).obj a) := rfl
        refine CategoryTheory.IsHomLift.of_fac'
          (relativeInertiaBase F.underlying) g χ' ha hb ?_
        have hχeq := CategoryTheory.IsHomLift.eq_of_isHomLift
          (structureFunctor X.underlying) g₀ χ
        dsimp [relativeInertiaBase, relativeInertiaStructureMap,
          relativeInertiaNeutralSection]
        convert hχeq.symm using 1
        · rfl
        · apply eq_of_heq
          exact
            (eqToHom_comp_heq (g ≫ eqToHom hb.symm) ha).trans
              (comp_eqToHom_heq g hb.symm)
      exact hχ'
    · apply RelativeInertiaHom.ext
      change χ ≫ φ = ψ.hom
      exact hχfac
    · intro ζ hζ
      rcases hζ with ⟨hζ, hζfac⟩
      apply RelativeInertiaHom.ext
      have hζ₀ : (structureFunctor X.underlying).IsHomLift g₀ ζ.hom := by
        have hζeq :=
          @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
            (relativeInertiaBase F.underlying) _ _ g ζ hζ
        dsimp [relativeInertiaBase, relativeInertiaStructureMap,
          relativeInertiaNeutralSection] at hζeq
        change g = (structureFunctor X.underlying).map ζ.hom at hζeq
        change (structureFunctor X.underlying).IsHomLift g ζ.hom
        rw [hζeq]
        exact Functor.IsHomLift.map _
      let : (structureFunctor X.underlying).IsHomLift g₀ ζ.hom := hζ₀
      have hζfac' : ζ.hom ≫ φ = ψ.hom := by
        dsimp [relativeInertiaCategory, relativeInertiaNeutralSection] at hζfac
        exact congrArg (fun k => k.hom) hζfac
      apply hχuniq ζ.hom
      exact ⟨hζ₀, hζfac'⟩

abbrev inertiaNeutralSection {C : Cat.{v, u}}
    (X : FibredCategoryOver C) :
    X.underlying.left ⥤ Inertia X :=
  relativeInertiaNeutralSection (toBaseFibredHom X).underlying

abbrev inertiaNeutralSectionOver {C : Cat.{v, u}}
    (X : FibredCategoryOver C) :
    FibredFunctorOver (structureFunctor X.underlying)
      (relativeInertiaBase (toBaseFibredHom X).underlying) :=
  relativeInertiaNeutralSectionOver (toBaseFibredHom X)

theorem relativeInertiaNeutralSection_rightInverse {C : Cat.{v, u}}
    {X S : CategoryOver C} (F : CategoryOverHom X S) :
    relativeInertiaNeutralSection F ⋙ relativeInertiaStructureMap F = 𝟭 X.left := by
  rfl

theorem inertiaNeutralSection_rightInverse {C : Cat.{v, u}}
    (X : FibredCategoryOver C) :
    inertiaNeutralSection X ⋙ inertiaStructureMap X = 𝟭 X.underlying.left := by
  rfl

/-! ## Functoriality and comparison -/

/- A `TwoCommutativeDiagram` with bottom edge `bottom` and right edge `right`
   is exactly the source's 2-commutative square: its left edge is the source
   map `F₁`, and its right edge is the top map `G`. -/
def relativeInertiaFunctoriality {C : Cat.{v, u}}
    {A B T : FibredCategoryOver C}
    (bottom : FibredCategoryOverHom A T)
    (right : FibredCategoryOverHom B T)
    (D : TwoCommutativeDiagram (C := FibredCategoryOver C) bottom right) :
    RelativeInertiaCategory D.left.underlying ⥤
      RelativeInertiaCategory right.underlying where
  obj x :=
    { carrier := (overFunctor D.right.underlying).obj x.carrier
      automorphism := (overFunctor D.right.underlying).mapIso x.automorphism
      map_eq_id := by
        let η := D.comparison.toNatTrans.app x.carrier
        have hleft := congrArg (overFunctor bottom.underlying).map x.map_eq_id
        have hleft' :
            (overFunctor (D.left ≫ bottom).underlying).map
                x.automorphism.hom = 𝟙 _ := by
          change (overFunctor bottom.underlying).map
              ((overFunctor D.left.underlying).map x.automorphism.hom) = 𝟙 _
          rw [hleft]
          simp
        have hnat := D.comparison.toNatTrans.naturality
          x.automorphism.hom
        rw [hleft'] at hnat
        let ηinv := (inv D.comparison).toNatTrans.app x.carrier
        have hη : η ≫ ηinv = 𝟙 _ := by
          change D.comparison.toNatTrans.app x.carrier ≫
            (inv D.comparison).toNatTrans.app x.carrier = 𝟙 _
          exact congrArg (fun z => z.toNatTrans.app x.carrier)
            (IsIso.hom_inv_id D.comparison)
        have hη' : ηinv ≫ η = 𝟙 _ := by
          change (inv D.comparison).toNatTrans.app x.carrier ≫
            D.comparison.toNatTrans.app x.carrier = 𝟙 _
          exact congrArg (fun z => z.toNatTrans.app x.carrier)
            (IsIso.inv_hom_id D.comparison)
        have htarget :
            (overFunctor (D.right ≫ right).underlying).map
                x.automorphism.hom = 𝟙 _ := by
          have hnat' : η ≫
              (overFunctor (D.right ≫ right).underlying).map
                x.automorphism.hom = η := by
            simpa [η] using hnat.symm
          calc
            (overFunctor (D.right ≫ right).underlying).map
                x.automorphism.hom =
                𝟙 _ ≫ (overFunctor (D.right ≫ right).underlying).map
                  x.automorphism.hom := by simp
            _ = (ηinv ≫ η) ≫
                (overFunctor (D.right ≫ right).underlying).map
                  x.automorphism.hom := by rw [hη']
            _ = ηinv ≫ (η ≫
                (overFunctor (D.right ≫ right).underlying).map
                  x.automorphism.hom) := by simp [Category.assoc]
            _ = ηinv ≫ η := by rw [hnat']
            _ = 𝟙 _ := hη'
        convert htarget using 1 <;> rfl }
  map f :=
    { hom := (overFunctor D.right.underlying).map f.hom
      comm := by
        simpa only [Functor.mapIso_hom, Functor.map_comp] using
          congrArg (overFunctor D.right.underlying).map f.comm }
  map_id := by
    intro x
    apply RelativeInertiaHom.ext
    change (overFunctor D.right.underlying).map (𝟙 x.carrier) = 𝟙 _
    simp
  map_comp := by
    intro x y z f g
    apply RelativeInertiaHom.ext
    change (overFunctor D.right.underlying).map (f.hom ≫ g.hom) =
      (overFunctor D.right.underlying).map f.hom ≫
        (overFunctor D.right.underlying).map g.hom
    simp

def relativeInertiaFunctorialityOver {C : Cat.{v, u}}
    {A B T : FibredCategoryOver C}
    (bottom : FibredCategoryOverHom A T)
    (right : FibredCategoryOverHom B T)
    (D : TwoCommutativeDiagram (C := FibredCategoryOver C) bottom right) :
    FibredFunctorOver
      (relativeInertiaBase D.left.underlying)
      (relativeInertiaBase right.underlying) where
  functor := relativeInertiaFunctoriality bottom right D
  over := by
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro x
      exact congrArg (fun K : D.vertex.underlying.left ⥤ C => K.obj x.carrier)
        (overFunctor_comm D.right.underlying)
    · intro x y f
      exact Functor.congr_hom (overFunctor_comm D.right.underlying) f.hom
  preserves := by
    intro a b κ hκ
    apply relativeInertia_isStronglyCartesian_of_underlying right
    apply D.right.preserves
    exact (relativeInertiaStructureOver D.left).preserves κ hκ

def inertiaFunctoriality {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C}
    (G : FibredCategoryOverHom X Y) : Inertia X ⥤ Inertia Y where
  obj x :=
    { carrier := (overFunctor G.underlying).obj x.carrier
      automorphism := (overFunctor G.underlying).mapIso x.automorphism
      map_eq_id := by
        have h := x.map_eq_id
        change (structureFunctor X.underlying).map x.automorphism.hom = 𝟙 _ at h
        have hcomp := Functor.congr_hom
          (overFunctor_comm G.underlying) x.automorphism.hom
        change (structureFunctor Y.underlying).map
          ((overFunctor G.underlying).map x.automorphism.hom) = 𝟙 _
        rw [← Functor.comp_map]
        rw [hcomp, h]
        simp }
  map f :=
    { hom := (overFunctor G.underlying).map f.hom
      comm := by
        simpa only [Functor.mapIso_hom, Functor.map_comp] using
          congrArg (overFunctor G.underlying).map f.comm }
  map_id := by
    intro x
    apply RelativeInertiaHom.ext
    change (overFunctor G.underlying).map (𝟙 x.carrier) = 𝟙 _
    simp
  map_comp := by
    intro x y z f g
    apply RelativeInertiaHom.ext
    change (overFunctor G.underlying).map (f.hom ≫ g.hom) =
      (overFunctor G.underlying).map f.hom ≫
        (overFunctor G.underlying).map g.hom
    simp

def inertiaFunctorialityOver {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C}
    (G : FibredCategoryOverHom X Y) :
    FibredFunctorOver
      (relativeInertiaBase (toBaseFibredHom X).underlying)
      (relativeInertiaBase (toBaseFibredHom Y).underlying) where
  functor := inertiaFunctoriality G
  over := by
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro x
      exact congrArg (fun K : X.underlying.left ⥤ C => K.obj x.carrier)
        (overFunctor_comm G.underlying)
    · intro x y f
      exact Functor.congr_hom (overFunctor_comm G.underlying) f.hom
  preserves := by
    intro a b κ hκ
    apply relativeInertia_isStronglyCartesian_of_underlying (toBaseFibredHom Y)
    apply G.preserves
    exact (relativeInertiaStructureOver (toBaseFibredHom X)).preserves κ hκ

def relativeInertiaComparison {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    RelativeInertiaCategory F.underlying ⥤ Inertia X where
  obj x :=
    { carrier := x.carrier
      automorphism := x.automorphism
      map_eq_id := by
        have h := congrArg (structureFunctor S.underlying).map x.map_eq_id
        rw [← Functor.comp_map] at h
        have hcomp := Functor.congr_hom
          (overFunctor_comm F.underlying) x.automorphism.hom
        rw [hcomp] at h
        have h' := congrArg (fun k => k ≫ eqToHom
          (Functor.congr_obj (overFunctor_comm F.underlying) x.carrier)) h
        change (structureFunctor X.underlying).map x.automorphism.hom = 𝟙 _
        apply (cancel_epi (eqToHom
          (Functor.congr_obj (overFunctor_comm F.underlying) x.carrier))).1
        simpa using h' }
  map f :=
    { hom := f.hom
      comm := f.comm }
  map_id := by
    intro x
    apply RelativeInertiaHom.ext
    rfl
  map_comp := by
    intro x y z f g
    apply RelativeInertiaHom.ext
    rfl

def relativeInertiaComparisonOver {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    FibredFunctorOver
      (relativeInertiaBase F.underlying)
      (relativeInertiaBase (toBaseFibredHom X).underlying) where
  functor := relativeInertiaComparison F
  over := by rfl
  preserves := by
    intro a b κ hκ
    apply relativeInertia_isStronglyCartesian_of_underlying (toBaseFibredHom X)
    exact (relativeInertiaStructureOver F).preserves κ hκ

theorem relativeInertiaComparison_structure {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    relativeInertiaComparison F ⋙ inertiaStructureMap X =
      relativeInertiaStructureMap F.underlying := by
  rfl

theorem relativeInertiaComparison_neutral {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    relativeInertiaNeutralSection F.underlying ⋙
        relativeInertiaComparison F = inertiaNeutralSection X := by
  rfl

theorem relativeInertiaFunctoriality_comparison {C : Cat.{v, u}}
    {A B T : FibredCategoryOver C}
    (bottom : FibredCategoryOverHom A T)
    (right : FibredCategoryOverHom B T)
    (D : TwoCommutativeDiagram (C := FibredCategoryOver C) bottom right) :
      relativeInertiaFunctoriality bottom right D ⋙
        relativeInertiaComparison right =
      relativeInertiaComparison D.left ⋙ inertiaFunctoriality D.right := by
  rfl

/-! ## The relative inertia square -/

def relativeInertiaToTarget {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    RelativeInertiaCategory F.underlying ⥤ S.underlying.left :=
  relativeInertiaStructureMap F.underlying ⋙ overFunctor F.underlying

private noncomputable def relativeInertia_fibreProduct_square_commutes_canonical
    {C : Cat.{v, u}} {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    relativeInertiaToTarget F ⋙ inertiaNeutralSection S ≅
      relativeInertiaComparison F ⋙ inertiaFunctoriality F :=
  NatIso.ofComponents (fun x =>
    { hom :=
        { hom := 𝟙 ((overFunctor F.underlying).obj x.carrier)
          comm := by
            change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫
              (overFunctor F.underlying).map x.automorphism.hom
            simpa using x.map_eq_id.symm }
      inv :=
        { hom := 𝟙 ((overFunctor F.underlying).obj x.carrier)
          comm := by
            change (overFunctor F.underlying).map x.automorphism.hom ≫ 𝟙 _ =
              𝟙 _ ≫ 𝟙 _
            simpa using x.map_eq_id }
      hom_inv_id := by
        apply RelativeInertiaHom.ext
        change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        simp
      inv_hom_id := by
        apply RelativeInertiaHom.ext
        change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        simp }) (by
      intro x y f
      apply RelativeInertiaHom.ext
      dsimp [Functor.comp, relativeInertiaToTarget, inertiaNeutralSection,
        relativeInertiaComparison, inertiaFunctoriality,
        relativeInertiaNeutralSection, relativeInertiaStructureMap]
      change (overFunctor F.underlying).map f.hom ≫ 𝟙 _ =
        𝟙 _ ≫ (overFunctor F.underlying).map f.hom
      simp)

theorem relativeInertia_fibreProduct_square_commutes_exists {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    Nonempty
      (relativeInertiaToTarget F ⋙ inertiaNeutralSection S ≅
        relativeInertiaComparison F ⋙ inertiaFunctoriality F) := by
  exact ⟨relativeInertia_fibreProduct_square_commutes_canonical F⟩

noncomputable def relativeInertia_fibreProduct_square_commutes
    {C : Cat.{v, u}} {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    relativeInertiaToTarget F ⋙ inertiaNeutralSection S ≅
      relativeInertiaComparison F ⋙ inertiaFunctoriality F :=
  relativeInertia_fibreProduct_square_commutes_canonical F

theorem relativeInertia_is_twoFibreProduct {C : Cat.{v, u}}
    {X S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) :
    IsTwoCartesianSquare
      (relativeInertiaComparison F)
      (relativeInertiaToTarget F)
      (inertiaFunctoriality F)
      (inertiaNeutralSection S)
      (relativeInertia_fibreProduct_square_commutes F) := by
  sorry

end
