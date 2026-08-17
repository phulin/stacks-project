import Formalization.Books.Categories.Unit34.Inertia
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Widesubcategory

namespace CategoryTheory.Functor

/-- The two lifting conditions in the source definition of a category fibred
in groupoids. -/
class IsFibredInGroupoids
    {S C : Type*} [Category* S] [Category* C] (p : S ⥤ C) : Prop where
  exists_lift : ∀ {V U : C} (f : V ⟶ U) {x : S}, p.obj x = U →
    ∃ (y : S) (φ : y ⟶ x), p.IsHomLift f φ
  unique_lift : ∀ {x y z : S} (φ : y ⟶ x) (ψ : z ⟶ x)
    {f : p.obj z ⟶ p.obj y}, f ≫ p.map φ = p.map ψ →
    ∃! χ : z ⟶ y, p.IsHomLift f χ ∧ χ ≫ φ = ψ

end CategoryTheory.Functor

/-!
# Categories, Chapter 35: Categories fibred in groupoids

The source defines a category fibred in groupoids directly by its lifting
properties, and then compares that definition with Mathlib's `IsFibered`
and `Functor.Fiber`.  The declarations below retain that source-facing
predicate while reusing the canonical Mathlib and earlier-chapter APIs for
fibres, cartesian arrows, categories over a fixed base, inertia, and
2-fibre products.
-/

namespace Formalization.Books.Categories.Unit35

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Formalization.Books.Categories.Unit29
open Formalization.Books.Categories.Unit30
open Formalization.Books.Categories.Unit31
open Formalization.Books.Categories.Unit32
open Formalization.Books.Categories.Unit33
open Formalization.Books.Categories.Unit34

universe v u v' u' u₁ v₁

noncomputable section

/-! ## The lifting definition -/

theorem fibredInGroupoids_exists_lift
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibredInGroupoids]
    {V : C} {x : S} (f : V ⟶ p.obj x) :
    ∃ (y : S) (φ : y ⟶ x), p.IsHomLift f φ := by
  exact Functor.IsFibredInGroupoids.exists_lift f rfl

theorem fibredInGroupoids_unique_lift
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibredInGroupoids]
    {x y z : S} (φ : y ⟶ x) (ψ : z ⟶ x)
    {f : p.obj z ⟶ p.obj y} (h : f ≫ p.map φ = p.map ψ) :
    ∃! χ : z ⟶ y, p.IsHomLift f χ ∧ χ ≫ φ = ψ := by
  exact Functor.IsFibredInGroupoids.unique_lift φ ψ h

/-- The comparison isomorphism between a chosen lift of `g ≫ f` and the
two-step lift through chosen lifts of `f` and `g`. -/
theorem fibredInGroupoids_composite_lift_isomorphic
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibredInGroupoids]
    {W V U : C} (g : W ⟶ V) (f : V ⟶ U)
    {x y z z' : S} (φ : y ⟶ x) (ψ : z ⟶ y) (γ : z' ⟶ x)
    (hφ : p.IsHomLift f φ) (hψ : p.IsHomLift g ψ)
    (hγ : p.IsHomLift (g ≫ f) γ) :
    ∃ e : z ≅ z',
      p.IsHomLift (𝟙 (p.obj z)) e.hom ∧
        p.IsHomLift (𝟙 (p.obj z')) e.inv ∧
        e.hom ≫ γ = ψ ≫ φ ∧ e.inv ≫ (ψ ≫ φ) = γ := by
  sorry

/-! ## Equivalence with fibred categories with groupoid fibres -/

theorem fibredInGroupoids_iff_fibred_groupoid_fibres
    {S C : Type*} [Category* S] [Category* C] (p : S ⥤ C) :
    p.IsFibredInGroupoids ↔
      (∀ U : C, IsGroupoid (Functor.Fiber p U)) ∧ p.IsFibered := by
  sorry

theorem fibredInGroupoids_all_morphisms_stronglyCartesian
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) (hp : p.IsFibredInGroupoids)
    {x y : S} (φ : x ⟶ y) :
    Functor.IsStronglyCartesian p (p.map φ) φ := by
  sorry

/- The chosen-pullback construction from Unit 33 is the source's
`f^* x → x` data.  The additional field records that the values are
groupoids, so the pseudofunctor is source-faithfully groupoid-valued. -/
structure FibredInGroupoidsPseudofunctorData
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) where
  data : PullbackPseudofunctorData p P
  fibre_is_groupoid : ∀ U : C, IsGroupoid (Functor.Fiber p U)

theorem fibredInGroupoids_pseudofunctor_exists
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered]
    (hp : p.IsFibredInGroupoids) (P : PullbackChoice p) :
    Nonempty (FibredInGroupoidsPseudofunctorData p P) := by
  sorry

/-! ## The strongly-cartesian wide subcategory -/

def stronglyCartesianMorphismProperty
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) : MorphismProperty S :=
  fun {_x _y} φ => Functor.IsStronglyCartesian p (p.map φ) φ

instance stronglyCartesianMorphismProperty_isMultiplicative
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] :
    (stronglyCartesianMorphismProperty p).IsMultiplicative where
  id_mem := by
    intro x
    change Functor.IsStronglyCartesian p (p.map (𝟙 x)) (𝟙 x)
    infer_instance
  comp_mem := by
    intro x y z f g hf hg
    change Functor.IsStronglyCartesian p (p.map (f ≫ g)) (f ≫ g)
    rw [p.map_comp]
    exact @Functor.IsStronglyCartesian.comp _ _ _ _ p
      (p.obj x) (p.obj y) (p.obj z) x y z (p.map f) (p.map g) f g hf hg

abbrev StronglyCartesianSubcategory
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] :=
  WideSubcategory (stronglyCartesianMorphismProperty p)

def stronglyCartesianSubcategoryInclusion
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] :
    StronglyCartesianSubcategory p ⥤ S :=
  wideSubcategoryInclusion (stronglyCartesianMorphismProperty p)

def stronglyCartesianSubcategoryProjection
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] :
    StronglyCartesianSubcategory p ⥤ C :=
  stronglyCartesianSubcategoryInclusion p ⋙ p

theorem stronglyCartesianSubcategory_hom_property
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered]
    {x y : StronglyCartesianSubcategory p} (φ : x ⟶ y) :
    Functor.IsStronglyCartesian p (p.map φ.hom) φ.hom :=
  φ.property

theorem stronglyCartesianSubcategory_isFibredInGroupoids
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] :
    (stronglyCartesianSubcategoryProjection p).IsFibredInGroupoids := by
  sorry

/-! ## Examples -/

theorem groupHomomorphism_fibredInGroupoids_iff_surjective
    {G H : Type*} [Group G] [Group H] (p : G →* H) :
    (MonoidHom.toFunctor p).IsFibredInGroupoids ↔ Function.Surjective p := by
  sorry

theorem groupHomomorphism_fibre_is_kernel_groupoid
    {G H : Type*} [Group G] [Group H] (p : G →* H) :
    Nonempty
      (Functor.Fiber (MonoidHom.toFunctor p) (SingleObj.star H) ≌
        SingleObj (MonoidHom.ker p)) := by
  sorry

/-- The base category in the finite counterexample has the chain
`A → B → T`, with the composite as its unique arrow `A → T`. -/
inductive FiniteExampleBase
  | A | B | T
  deriving DecidableEq

def finiteExampleBaseLE : FiniteExampleBase → FiniteExampleBase → Prop
  | .A, .A | .B, .B | .T, .T | .A, .B | .B, .T | .A, .T => True
  | _, _ => False

instance finiteExampleBasePartialOrder : PartialOrder FiniteExampleBase where
  le := finiteExampleBaseLE
  le_refl := by
    intro x
    cases x <;> trivial
  le_trans := by
    intro x y z hxy hyz
    change finiteExampleBaseLE x y at hxy
    change finiteExampleBaseLE y z at hyz
    cases x <;> cases y <;> cases z <;> simp_all [finiteExampleBaseLE]
  le_antisymm := by
    intro x y hxy hyx
    change finiteExampleBaseLE x y at hxy
    change finiteExampleBaseLE y x at hyx
    cases x <;> cases y <;> simp_all [finiteExampleBaseLE]

inductive FiniteExampleSource
  | A | B | T
  deriving DecidableEq

def finiteExampleSourceLE : FiniteExampleSource → FiniteExampleSource → Prop
  | .A, .A | .B, .B | .T, .T | .A, .T | .B, .T => True
  | _, _ => False

instance finiteExampleSourcePartialOrder : PartialOrder FiniteExampleSource where
  le := finiteExampleSourceLE
  le_refl := by
    intro x
    cases x <;> trivial
  le_trans := by
    intro x y z hxy hyz
    change finiteExampleSourceLE x y at hxy
    change finiteExampleSourceLE y z at hyz
    cases x <;> cases y <;> cases z <;> simp_all [finiteExampleSourceLE]
  le_antisymm := by
    intro x y hxy hyx
    change finiteExampleSourceLE x y at hxy
    change finiteExampleSourceLE y x at hyx
    cases x <;> cases y <;> simp_all [finiteExampleSourceLE]

def finiteExampleSourceToBase : FiniteExampleSource → FiniteExampleBase
  | .A => .A
  | .B => .B
  | .T => .T

theorem finiteExample_source_le_implies_base_le
    {x y : FiniteExampleSource} (h : x ≤ y) :
    finiteExampleSourceToBase x ≤ finiteExampleSourceToBase y := by
  change finiteExampleSourceLE x y at h
  change finiteExampleBaseLE (finiteExampleSourceToBase x)
    (finiteExampleSourceToBase y)
  cases x <;> cases y <;> simp_all [finiteExampleSourceLE, finiteExampleBaseLE,
    finiteExampleSourceToBase]

def finiteExampleFunctor : FiniteExampleSource ⥤ FiniteExampleBase where
  obj := finiteExampleSourceToBase
  map f := homOfLE (finiteExample_source_le_implies_base_le f.le)
  map_id := by
    intro x
    apply Subsingleton.elim
  map_comp := by
    intro x y z f g
    apply Subsingleton.elim

def finiteExampleBaseF : FiniteExampleBase.A ⟶ FiniteExampleBase.B :=
  homOfLE (by
    change finiteExampleBaseLE .A .B
    trivial)

theorem finiteExample_fibre_categories_are_groupoids :
    ∀ U : FiniteExampleBase,
      IsGroupoid (Functor.Fiber finiteExampleFunctor U) := by
  sorry

theorem finiteExample_no_lift_of_f :
    ¬ ∃ (y : FiniteExampleSource) (φ : y ⟶ FiniteExampleSource.B),
      finiteExampleFunctor.IsHomLift finiteExampleBaseF φ := by
  sorry

theorem finiteExample_not_fibredInGroupoids :
    ¬ finiteExampleFunctor.IsFibredInGroupoids := by
  sorry

/-- The second finite example is detected when distinct lifts become equal
after a common postcomposition. -/
theorem two_distinct_lifts_with_equal_postcomposition_not_fibredInGroupoids
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) {x y z : S} (f : p.obj x ⟶ p.obj y)
    (φ ψ : x ⟶ y) (hφ : p.IsHomLift f φ) (hψ : p.IsHomLift f ψ)
    (k : y ⟶ z) (hcomp : φ ≫ k = ψ ≫ k)
    (hne : φ ≠ ψ) :
    ¬ p.IsFibredInGroupoids := by
  sorry

/-! ## The fixed-base 2-category -/

/-- The groupoid-fibre object property on the fixed-base fibred-category
interface from Unit 33. -/
def IsGroupoidFibredCategoryOver {C : Cat.{v, u}}
    (X : FibredCategoryOver C) : Prop :=
  ∀ U : C, IsGroupoid (Functor.Fiber (structureFunctor X.underlying) U)

def groupoidFibredObjectProperty {C : Cat.{v, u}} :
    ObjectProperty (FibredCategoryOver C) :=
  IsGroupoidFibredCategoryOver

/-- The source's 2-category of categories fibred in groupoids over `C`.
It is the full sub-2-category on the groupoid-fibre objects. -/
abbrev CategoriesFibredInGroupoidsOver (C : Cat.{v, u}) :=
  FullSubTwoCategory (FibredCategoryOver C) (groupoidFibredObjectProperty (C := C))

theorem fibredInGroupoids_two_morphism_isIso
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsGroupoidFibredCategoryOver Y)
    {F G : FibredCategoryOverHom X Y} (η : F ⟶ G) : IsIso η := by
  sorry

theorem categoriesFibredInGroupoidsOver_is_two_one_category
    (C : Cat.{v, u}) :
    IsTwoOneCategory
      (CategoriesFibredInGroupoidsOver C) := by
  sorry

/-! ## 2-fibre products over a fixed base -/

structure FibredInGroupoidsTwoFibreProduct
    {C : Cat.{v, u}} {X Y S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) where
  product : FibredTwoFibreProduct.{u₁, v₁, v, u} F G
  fibres_are_groupoids : ∀ U : C,
    IsGroupoid (Functor.Fiber product.diagram.base U)

theorem categoriesFibredInGroupoids_have_twoFibreProducts
    {C : Cat.{v, u}} (X Y S : FibredCategoryOver C)
    (hX : IsGroupoidFibredCategoryOver X)
    (hY : IsGroupoidFibredCategoryOver Y)
    (hS : IsGroupoidFibredCategoryOver S)
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) :
    Nonempty (FibredInGroupoidsTwoFibreProduct F G) := by
  sorry

/-- The two descriptions of the category-valued 2-fibre product in the
source are canonically equivalent for categories fibred in groupoids: the
fixed-base presentation remembers a base object, while `IsoComma` remembers
only the isomorphism. -/
theorem twoFibreProductOverCategory_canonically_equivalent
    {C : Cat.{v, u}} {X Y S : FibredCategoryOver C}
    (hX : IsGroupoidFibredCategoryOver X)
    (hY : IsGroupoidFibredCategoryOver Y)
    (hS : IsGroupoidFibredCategoryOver S)
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) :
    Nonempty
      (TwoFibreProductOverCategory F.underlying G.underlying ≌
        IsoComma (overFunctor F.underlying) (overFunctor G.underlying)) := by
  sorry

/-! ## Fibrewise functors and equivalences -/

/-- The functor induced on fibre categories by a functor over the base. -/
def fibreFunctor
    {S S' C : Type*} [Category* S] [Category* S'] [Category* C]
    (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (over : G ⋙ p' = p) (U : C) :
    Functor.Fiber p U ⥤ Functor.Fiber p' U where
  obj x :=
    ⟨G.obj x.1,
      (congrArg (fun H : S ⥤ C => H.obj x.1) over).trans x.2⟩
  map {x y} f :=
    ⟨G.map f.1, by
      let hx := (congrArg (fun H : S ⥤ C => H.obj x.1) over).trans x.2
      let hy := (congrArg (fun H : S ⥤ C => H.obj y.1) over).trans y.2
      exact IsHomLift.of_commsq p' (𝟙 U) (G.map f.1) hx hy <|
        by
          simpa [hx, hy,
            @IsHomLift.fac' _ _ _ _ p U U x.1 y.1 (𝟙 U) f.1 f.2,
            Category.assoc] using
            congrArg (fun k => k ≫ eqToHom y.2)
              ((eqToIso over).hom.naturality f.1)⟩
  map_id := by
    intro x
    apply Functor.Fiber.hom_ext
    change G.map (𝟙 x.1) = 𝟙 (G.obj x.1)
    simp
  map_comp := by
    intro x y z f g
    apply Functor.Fiber.hom_ext
    change G.map (f.1 ≫ g.1) = G.map f.1 ≫ G.map g.1
    simp

theorem fibredInGroupoids_faithful_iff_fibrewise
    {S S' C : Type*} [Category* S] [Category* S'] [Category* C]
    (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (over : G ⋙ p' = p)
    (hp : p.IsFibredInGroupoids) (hp' : p'.IsFibredInGroupoids) :
    G.Faithful ↔ ∀ U : C, (fibreFunctor p p' G over U).Faithful := by
  sorry

theorem fibredInGroupoids_fullyFaithful_iff_fibrewise
    {S S' C : Type*} [Category* S] [Category* S'] [Category* C]
    (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (over : G ⋙ p' = p)
    (hp : p.IsFibredInGroupoids) (hp' : p'.IsFibredInGroupoids) :
    Nonempty G.FullyFaithful ↔
      ∀ U : C, Nonempty (fibreFunctor p p' G over U).FullyFaithful := by
  sorry

theorem fibredInGroupoids_equivalence_iff_fibrewise
    {S S' C : Type*} [Category* S] [Category* S'] [Category* C]
    (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (over : G ⋙ p' = p)
    (hp : p.IsFibredInGroupoids) (hp' : p'.IsFibredInGroupoids) :
    G.IsEquivalence ↔
      ∀ U : C, (fibreFunctor p p' G over U).IsEquivalence := by
  sorry

/-- Equivalence over the fixed base, expressed in the category of fibred
category morphisms.  Its isomorphisms are precisely the vertical natural
isomorphisms used as 2-morphisms in the source. -/
def IsEquivalenceOverHom {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) : Prop :=
  ∃ G : FibredCategoryOverHom Y X,
    Nonempty (FibredCategoryOverHom.comp F G ≅
      FibredCategoryOverHom.id X) ∧
      Nonempty (FibredCategoryOverHom.comp G F ≅
        FibredCategoryOverHom.id Y)

theorem equivalence_fibredInGroupoids_is_equivalence_over
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hX : IsGroupoidFibredCategoryOver X)
    (hY : IsGroupoidFibredCategoryOver Y)
    (F : FibredCategoryOverHom X Y)
    (hF : Nonempty (overFunctor F.underlying).IsEquivalence) :
    IsEquivalenceOverHom F := by
  sorry

theorem fibredInGroupoids_fullyFaithful_iff_diagonal_isEquivalence
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hX : IsGroupoidFibredCategoryOver X)
    (hY : IsGroupoidFibredCategoryOver Y)
    (F : FibredCategoryOverHom X Y) :
    Nonempty (overFunctor F.underlying).FullyFaithful ↔
      (fibredCategoryDiagonalFunctor F).IsEquivalence := by
  sorry

/-! ## Equivalences and functor categories -/

/-- Pre- and postcomposition is the functor appearing in the source's
invariance statement for morphism categories. -/
def prePostcompositionFunctor
    {C : Cat.{v, u}} {X₁ X₂ X₃ X₄ : FibredCategoryOver C}
    (φ : FibredCategoryOverHom X₁ X₂)
    (ψ : FibredCategoryOverHom X₃ X₄) :
    FibredCategoryOverHom X₂ X₃ ⥤ FibredCategoryOverHom X₁ X₄ where
  obj α := FibredCategoryOverHom.comp φ
    (FibredCategoryOverHom.comp α ψ)
  map η := fibredWhiskerLeft φ (fibredWhiskerRight η ψ)
  map_id := by
    intro α
    rw [show fibredWhiskerRight (𝟙 α) ψ =
        𝟙 (FibredCategoryOverHom.comp α ψ) by
      exact @Bicategory.id_whiskerRight (FibredCategoryOver C) _
        X₂ X₃ X₄ α ψ]
    exact @Bicategory.whiskerLeft_id (FibredCategoryOver C) _
      X₁ X₂ X₄ φ (FibredCategoryOverHom.comp α ψ)
  map_comp := by
    sorry

theorem morphisms_equivalent_fibred_groupoids
    {C : Cat.{v, u}} {X₁ X₂ X₃ X₄ : FibredCategoryOver C}
    (hX₁ : IsGroupoidFibredCategoryOver X₁)
    (hX₂ : IsGroupoidFibredCategoryOver X₂)
    (hX₃ : IsGroupoidFibredCategoryOver X₃)
    (hX₄ : IsGroupoidFibredCategoryOver X₄)
    (φ : FibredCategoryOverHom X₁ X₂)
    (ψ : FibredCategoryOverHom X₃ X₄)
    (hφ : Nonempty (overFunctor φ.underlying).IsEquivalence)
    (hψ : Nonempty (overFunctor ψ.underlying).IsEquivalence) :
    (prePostcompositionFunctor φ ψ).IsEquivalence := by
  sorry

/-! ## Inertia, slices, composites, and fibre products -/

theorem inertia_isFibredInGroupoids
    {C : Cat.{v, u}} (X : FibredCategoryOver C)
    (hX : IsGroupoidFibredCategoryOver X) :
    (relativeInertiaBase (toBaseFibredHom X).underlying).IsFibredInGroupoids := by
  sorry

theorem fibredInGroupoids_over_slice
    {S C : Type*} [Category* S] [Category* C]
    (U : C) (p : S ⥤ C) (p' : S ⥤ Over U)
    (factor : p' ⋙ Over.forget U = p)
    (hp : p.IsFibredInGroupoids) :
    p'.IsFibredInGroupoids := by
  sorry

theorem fibredInGroupoids_over_fibred
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (p : A ⥤ B) (q : B ⥤ C)
    (hp : p.IsFibredInGroupoids) (hq : q.IsFibredInGroupoids) :
    (p ⋙ q).IsFibredInGroupoids := by
  sorry

theorem fibredInGroupoids_fibre_product_goes_up
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) (hp : p.IsFibredInGroupoids)
    {x y z : S} (f : x ⟶ y) (g : z ⟶ y)
    [HasPullback (p.map f) (p.map g)] :
    ∃ (w : S) (a : w ⟶ z) (b : w ⟶ x),
      p.obj w = pullback (p.map f) (p.map g) ∧
        Functor.IsStronglyCartesian p
          (pullback.snd (p.map f) (p.map g)) a ∧
        IsPullback b a f g := by
  sorry

/-! ## The amelioration factorization -/

/-- The source-facing strengthened factorization package.  The middle
category is groupoid-fibred over `C`, the first map is an equivalence over
`C`, and the second map is groupoid-fibred over `Y`. -/
structure GroupoidAmeliorationFactorization
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y) where
  middle : FibredCategoryOver C
  u : FibredCategoryOverHom X middle
  v : FibredCategoryOverHom middle Y
  factorization : F.underlying =
    CategoryOver.comp u.underlying v.underlying
  middle_groupoid_fibred : IsGroupoidFibredCategoryOver middle
  u_equivalence_over_C : IsEquivalenceOverHom u
  v_groupoid_fibred_over_Y :
    (overFunctor v.underlying).IsFibredInGroupoids

abbrev GroupoidAmeliorationCategory
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y) :=
  AmeliorationCategory F

theorem groupoidAmelioration_object_description
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y)
    (ξ : GroupoidAmeliorationCategory F) :
    ∃ U : C,
      IsObjectLift (structureFunctor Y.underlying) U ξ.obj.left ∧
      IsObjectLift (structureFunctor X.underlying) U ξ.obj.right ∧
        IsMorphismLift (structureFunctor Y.underlying) (𝟙 U) ξ.obj.hom :=
  amelioration_object_description F ξ

theorem groupoidAmelioration_morphism_description
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y)
    {ξ ξ' : GroupoidAmeliorationCategory F} (h : ξ ⟶ ξ') :
    h.hom.left ≫ ξ'.obj.hom =
      ξ.obj.hom ≫ (overFunctor F.underlying).map h.hom.right :=
  amelioration_morphism_description F h

theorem groupoidAmelioration_object_isIso
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsGroupoidFibredCategoryOver Y)
    (F : FibredCategoryOverHom X Y)
    (ξ : GroupoidAmeliorationCategory F) : IsIso ξ.obj.hom := by
  sorry

theorem ameliorate_morphism_categories_fibred_in_groupoids
    {C : Cat.{v, u}} (X Y : FibredCategoryOver C)
    (hX : IsGroupoidFibredCategoryOver X)
    (hY : IsGroupoidFibredCategoryOver Y)
    (F : FibredCategoryOverHom X Y) :
    Nonempty (GroupoidAmeliorationFactorization F) := by
  sorry

/-! ## Uniqueness of the amelioration -/

/-- A fixed-base form of the 2-commutative diagram used in the final source
lemma.  The two triangle fields are the two 2-commutativity assumptions. -/
structure AmeliorationUniquenessData
    {C : Cat.{v, u}} {X X' X'' Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y) where
  x_groupoid_fibred_over_C : IsGroupoidFibredCategoryOver X
  y_groupoid_fibred_over_C : IsGroupoidFibredCategoryOver Y
  f : FibredCategoryOverHom X' Y
  g : FibredCategoryOverHom X'' Y
  a : FibredCategoryOverHom X X'
  b : FibredCategoryOverHom X X''
  f_groupoid_fibred_over_Y :
    (overFunctor f.underlying).IsFibredInGroupoids
  g_groupoid_fibred_over_Y :
    (overFunctor g.underlying).IsFibredInGroupoids
  a_equivalence_over_C : IsEquivalenceOverHom a
  b_equivalence_over_C : IsEquivalenceOverHom b
  left_triangle :
    Formalization.Books.Categories.Unit31.IsTwoCommutative
      (C := FibredCategoryOver C) a (FibredCategoryOverHom.id X) f F
  right_triangle :
    Formalization.Books.Categories.Unit31.IsTwoCommutative
      (C := FibredCategoryOver C) b (FibredCategoryOverHom.id X) g F

/-- A natural isomorphism is over a target functor when its components map
to the transported identity in that target. -/
def IsNatIsoOver
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (q : B ⥤ D) {H K : A ⥤ B} (e : H ≅ K)
    (over : H ⋙ q = K ⋙ q) : Prop :=
  ∀ Z : A, q.map (e.hom.app Z) =
    eqToHom (congrArg (fun L : A ⥤ D => L.obj Z) over)

/-- An equivalence over a target functor, with the chosen functor displayed.
The quasi-inverse isomorphisms are required to be over the same target. -/
def IsEquivalenceOverFunctor
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (p : A ⥤ D) (q : B ⥤ D) (h : A ⥤ B) : Prop :=
  ∃ k : B ⥤ A,
    h ⋙ q = p ∧ k ⋙ p = q ∧
      (∃ e : h ⋙ k ≅ 𝟭 A,
        ∃ over : (h ⋙ k) ⋙ p = (𝟭 A) ⋙ p,
          IsNatIsoOver p e over) ∧
      (∃ e : k ⋙ h ≅ 𝟭 B,
        ∃ over : (k ⋙ h) ⋙ q = (𝟭 B) ⋙ q,
          IsNatIsoOver q e over)

def underlyingIsoOfFibredHomIso
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    {F G : FibredCategoryOverHom X Y} (e : F ≅ G) :
    overFunctor F.underlying ≅ overFunctor G.underlying where
  hom := e.hom.toNatTrans
  inv := e.inv.toNatTrans
  hom_inv_id := by
    change e.hom.toNatTrans ≫ e.inv.toNatTrans =
      𝟙 (overFunctor F.underlying)
    exact congrArg
      (fun η : OverNatTrans F.underlying F.underlying => η.toNatTrans)
      e.hom_inv_id
  inv_hom_id := by
    change e.inv.toNatTrans ≫ e.hom.toNatTrans =
      𝟙 (overFunctor G.underlying)
    exact congrArg
      (fun η : OverNatTrans G.underlying G.underlying => η.toNatTrans)
      e.inv_hom_id

theorem amelioration_unique
    {C : Cat.{v, u}} {X X' X'' Y : FibredCategoryOver C}
    {F : FibredCategoryOverHom X Y}
  (D : AmeliorationUniquenessData F) :
    ∃ h : FibredCategoryOverHom X'' X',
      IsEquivalenceOverFunctor (overFunctor D.g.underlying)
        (overFunctor D.f.underlying) (overFunctor h.underlying) ∧
      Nonempty (FibredCategoryOverHom.comp D.b h ≅ D.a) := by
  sorry

theorem amelioration_unique_when_strictly_commutative
    {C : Cat.{v, u}} {X X' X'' Y : FibredCategoryOver C}
    {F : FibredCategoryOverHom X Y}
    (D : AmeliorationUniquenessData F)
    (left_strict : CategoryOver.comp D.a.underlying D.f.underlying =
      F.underlying)
    (right_strict : CategoryOver.comp D.b.underlying D.g.underlying =
      F.underlying) :
    ∃ h : FibredCategoryOverHom X'' X',
      IsEquivalenceOverFunctor (overFunctor D.g.underlying)
        (overFunctor D.f.underlying) (overFunctor h.underlying) ∧
      ∃ e : FibredCategoryOverHom.comp D.b h ≅ D.a,
        ∃ overY :
          overFunctor (FibredCategoryOverHom.comp D.b h).underlying ⋙
              overFunctor D.f.underlying =
            overFunctor D.a.underlying ⋙ overFunctor D.f.underlying,
          IsNatIsoOver (overFunctor D.f.underlying)
            (underlyingIsoOfFibredHomIso e) overY := by
  sorry

end
