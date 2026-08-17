import Formalization.Books.Categories.Unit22.EssentiallyConstantSystems
import Formalization.Books.Derived.Unit12.CanonicalDeltaFunctor
import Formalization.Books.Homology.Unit31.InverseSystems
import Mathlib.CategoryTheory.Category.ULift

/-!
# Derived Categories, Chapter 42: essentially constant systems

The source studies inverse systems in triangulated categories and in derived
categories.  Inverse systems are represented by `NatInverseSystem`, their
essential constancy by the canonical Categories 22 predicate, and pro-maps by
the functor `proLim`.  The displayed finite direct sums use Mathlib's
canonical binary biproducts.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit22
open Formalization.Books.Categories.Unit21
open Formalization.Books.Derived.Unit11
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit31
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u

namespace Formalization.Books.Derived.Unit42

/-! ## Pro-objects and tails of inverse systems -/

/- The pro-object represented by a positive-integer inverse system.  The
   `AsSmall` is the canonical universe adjustment required by `proLim`, whose
   index category lives in the ambient hom universe. -/
noncomputable abbrev liftedNatInverseSystem
    {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) : AsSmall.{v} (ℕ+ᵒᵖ) ⥤ C :=
  CategoryTheory.AsSmall.down ⋙ F

noncomputable abbrev proObject
    {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) : ProCategory C :=
  (proLim (AsSmall.{v} (ℕ+ᵒᵖ))).obj (liftedNatInverseSystem F)

noncomputable def proMap
    {C : Type u} [Category.{v} C]
    {F G : NatInverseSystem C} (φ : F ⟶ G) :
    proObject F ⟶ proObject G :=
  (proLim (AsSmall.{v} (ℕ+ᵒᵖ))).map
    (Functor.whiskerLeft CategoryTheory.AsSmall.down φ)

/- A value of an inverse system is expressed using the canonical embedding into
   the pro-category. -/
noncomputable def IsProValue
    {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) (X : C) : Prop :=
  Nonempty (proObject F ≅ (proEmbedding (C := C)).obj X)

/- The source's phrase “pro-zero” means essentially constant with value zero. -/
def IsProZero
    {C : Type u} [Category.{v} C] [HasZeroObject C]
    (F : NatInverseSystem C) : Prop :=
  Formalization.Books.Homology.Unit31.IsEssentiallyConstant F ∧
    IsProValue F (0 : C)

/- The full tail of an inverse system beginning at `n`. -/
def natTailEmbedding (n : ℕ+) : Set.Ici n →o ℕ+ where
  toFun j := j.1
  monotone' _ _ h := h

def natTailInclusion (n : ℕ+) : Set.Ici n ⥤ ℕ+ :=
  (natTailEmbedding n).monotone.functor

abbrev natTailInverseSystem
    {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) (n : ℕ+) :
    Formalization.Books.Categories.Unit21.InverseSystem (Set.Ici n) C :=
  (natTailInclusion n).op ⋙ F

abbrev natTailConstant
    {C : Type u} [Category.{v} C]
    (n : ℕ+) (X : C) : (Set.Ici n)ᵒᵖ ⥤ C :=
  (Functor.const (Set.Ici n)ᵒᵖ).obj X

noncomputable abbrev liftedNatTailInverseSystem
    {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) (n : ℕ+) :
    AsSmall.{v} ((Set.Ici n)ᵒᵖ) ⥤ C :=
  CategoryTheory.AsSmall.down ⋙ natTailInverseSystem F n

noncomputable def tailProMap
    {C : Type u} [Category.{v} C]
    {F : NatInverseSystem C} {n : ℕ+}
    {X : C} (η : natTailInverseSystem F n ⟶ natTailConstant n X) :
    (proLim (AsSmall.{v} ((Set.Ici n)ᵒᵖ))).obj
        (liftedNatTailInverseSystem F n) ⟶
      (proLim (AsSmall.{v} ((Set.Ici n)ᵒᵖ))).obj
        (CategoryTheory.AsSmall.down ⋙ natTailConstant n X) :=
  (proLim (AsSmall.{v} ((Set.Ici n)ᵒᵖ))).map
    (Functor.whiskerLeft CategoryTheory.AsSmall.down η)

/- A map from a tail to a constant system, together with the component formula
   forced by a map from the stage `n`.  The final field says that its induced
   map in the pro-category is an isomorphism. -/
noncomputable def IsTailProIsomorphism
    {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) (n : ℕ+)
    {X : C} (f : F.obj (Opposite.op n) ⟶ X) : Prop :=
  ∃ (η : natTailInverseSystem F n ⟶ natTailConstant n X),
    (∀ (j : Set.Ici n),
      η.app (Opposite.op j) =
        transitionMap F j.2 ≫ f) ∧
      IsIso (tailProMap η)

/-! ## Splittings of essentially constant systems -/

/- This is the direct-sum decomposition appearing in the first source lemma.
   The transported transition map is literally diagonal: identity on the
   stable summand and a complementary map `z` on the second summand. -/
def HasEventualBiproductDecomposition
    {C : Type u} [Category.{v} C]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    (F : NatInverseSystem C) : Prop :=
  ∃ (n : ℕ+) (A : C) (Z : ℕ+ → C)
    (b : ∀ (j : ℕ+) (_ : n ≤ j), BinaryBiproductData A (Z j))
    (e : ∀ (j : ℕ+) (hj : n ≤ j),
      (b j hj).bicone.pt ≅ F.obj (Opposite.op j))
    (z : ∀ {j j' : ℕ+}, j ≤ j' → (Z j' ⟶ Z j)),
    (∀ {j j' : ℕ+} (hj : n ≤ j) (hj' : n ≤ j') (h : j ≤ j'),
      let q := (e j' hj').hom ≫ transitionMap F h ≫ (e j hj).inv
      q ≫ (b j hj).bicone.fst = (b j' hj').bicone.fst ∧
        q ≫ (b j hj).bicone.snd = (b j' hj').bicone.snd ≫ z h ∧
        (b j' hj').bicone.inl ≫ q = (b j hj).bicone.inl ∧
        (b j' hj').bicone.inr ≫ q = z h ≫ (b j hj).bicone.inr) ∧
      (∀ (j : ℕ+) (_hj : n ≤ j),
        ∃ (j' : ℕ+) (hjj' : j ≤ j'), z hjj' = 0)

theorem essentiallyConstant_iff_eventual_biproduct_decomposition
    {C : Type u} [Category.{v} C]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [CategoryTheory.IsTriangulated C]
    (F : NatInverseSystem C) :
    Formalization.Books.Homology.Unit31.IsEssentiallyConstant F ↔
      HasEventualBiproductDecomposition F := by
  sorry

/-! ## Inverse systems of distinguished triangles -/

def IsDistinguishedTriangleSystem
    {C : Type u} [Category.{v} C]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    (T : NatInverseSystem (Triangle C)) : Prop :=
  ∀ n : ℕ+, T.obj (Opposite.op n) ∈ distTriang C

abbrev triangleFirstSystem
    {C : Type u} [Category.{v} C]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    (T : NatInverseSystem (Triangle C)) : NatInverseSystem C :=
  T ⋙ Triangle.π₁

abbrev triangleMiddleSystem
    {C : Type u} [Category.{v} C]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    (T : NatInverseSystem (Triangle C)) : NatInverseSystem C :=
  T ⋙ Triangle.π₂

abbrev triangleThirdSystem
    {C : Type u} [Category.{v} C]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    (T : NatInverseSystem (Triangle C)) : NatInverseSystem C :=
  T ⋙ Triangle.π₃

abbrev triangleFirstToMiddle
    {C : Type u} [Category.{v} C]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    (T : NatInverseSystem (Triangle C)) :
    triangleFirstSystem T ⟶ triangleMiddleSystem T :=
  Functor.whiskerLeft T Triangle.π₁Toπ₂

abbrev triangleMiddleToThird
    {C : Type u} [Category.{v} C]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    (T : NatInverseSystem (Triangle C)) :
    triangleMiddleSystem T ⟶ triangleThirdSystem T :=
  Functor.whiskerLeft T Triangle.π₂Toπ₃

/- The source's “map of distinguished triangles” is a morphism in Mathlib's
   category of triangles.  Its three components are required to induce
   isomorphisms from the corresponding tail systems to constant systems. -/
theorem essentiallyConstant_triangle_2_out_of_3
    {C : Type u} [Category.{v} C]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [CategoryTheory.IsTriangulated C]
    (T : NatInverseSystem (Triangle C))
    (hT : IsDistinguishedTriangleSystem T)
    (hA : Formalization.Books.Homology.Unit31.IsEssentiallyConstant
      (triangleFirstSystem T))
    (hC : Formalization.Books.Homology.Unit31.IsEssentiallyConstant
      (triangleThirdSystem T)) :
    Formalization.Books.Homology.Unit31.IsEssentiallyConstant
        (triangleMiddleSystem T) ∧
      ∃ (A B C₀ : C) (f : A ⟶ B) (g : B ⟶ C₀)
        (h : C₀ ⟶ A⟦(1 : ℤ)⟧),
        IsProValue (triangleFirstSystem T) A ∧
          IsProValue (triangleMiddleSystem T) B ∧
          IsProValue (triangleThirdSystem T) C₀ ∧
          Triangle.mk f g h ∈ distTriang C ∧
          ∃ (n : ℕ+) (φ : T.obj (Opposite.op n) ⟶ Triangle.mk f g h),
            IsTailProIsomorphism (triangleFirstSystem T) n φ.hom₁ ∧
              IsTailProIsomorphism (triangleMiddleSystem T) n φ.hom₂ ∧
              IsTailProIsomorphism (triangleThirdSystem T) n φ.hom₃ := by
  sorry

/-! ## Cohomology of bounded systems -/

abbrev derivedCohomologySystem
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C]
    (F : NatInverseSystem (DerivedCategory C)) (i : ℤ) :
    NatInverseSystem C :=
  F ⋙ derivedCohomologyFunctor C i

def HasBoundedDerivedCohomology
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C]
    (F : NatInverseSystem (DerivedCategory C)) : Prop :=
  ∃ (a b : ℤ), a ≤ b ∧
    ∀ (n : ℕ+) (i : ℤ), i ∉ Set.Icc a b →
      IsZero ((derivedCohomologySystem F i).obj (Opposite.op n))

theorem essentiallyConstant_derived_of_bounded_cohomology
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C]
    (F : NatInverseSystem (DerivedCategory C))
    (hbounded : HasBoundedDerivedCohomology F)
    (hcohom : ∀ i : ℤ,
      Formalization.Books.Homology.Unit31.IsEssentiallyConstant
        (derivedCohomologySystem F i)) :
    ∃ A : DerivedCategory C,
      Formalization.Books.Homology.Unit31.IsEssentiallyConstant F ∧
        ∀ i : ℤ,
          IsProValue (derivedCohomologySystem F i)
            ((derivedCohomologyFunctor C i).obj A) := by
  sorry

/-! ## Pro-isomorphisms from distinguished triangles -/

theorem pro_isomorphism_of_pro_zero
    {C : Type u} [Category.{v} C]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [CategoryTheory.IsTriangulated C]
    (T : NatInverseSystem (Triangle C))
    (hT : IsDistinguishedTriangleSystem T)
    (hC : IsProZero (triangleThirdSystem T)) :
    IsIso (proMap (triangleFirstToMiddle T)) := by
  sorry

/-! ## Pro-isomorphisms detected by cohomology -/

abbrev derivedCohomologySystemMap
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C]
    {F G : NatInverseSystem (DerivedCategory C)}
    (φ : F ⟶ G) (i : ℤ) :
    derivedCohomologySystem F i ⟶ derivedCohomologySystem G i :=
  Functor.whiskerRight φ (derivedCohomologyFunctor C i)

theorem pro_isomorphism_of_cohomology_pro_isomorphisms
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C]
    {F G : NatInverseSystem (DerivedCategory C)}
    (φ : F ⟶ G)
    (hF : HasBoundedDerivedCohomology F)
    (hG : HasBoundedDerivedCohomology G)
    (hcohom : ∀ i : ℤ,
      IsIso (proMap (derivedCohomologySystemMap φ i))) :
    IsIso (proMap φ) := by
  sorry

end Formalization.Books.Derived.Unit42
