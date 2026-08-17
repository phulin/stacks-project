import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Formalization.Books.Derived.Unit04.ElementaryResults
import Formalization.Books.Derived.Unit09.ConesAndTermwiseSplitSequences
import Formalization.Books.Homology.Unit18.DoubleComplexes

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit03
open Formalization.Books.Derived.Unit04
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit09
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit18

universe v u v' u'

namespace Formalization.Books.Derived.Unit10

instance doubleComplexMapAddCommGroup
    {C : Type u} [Category.{v} C] [Preadditive C]
    (A B : DoubleComplex C) : AddCommGroup (DoubleComplexMap A B) where
  add f g :=
    { f := fun p q => f.f p q + g.f p q
      comm1 := by
        intro p q
        simp only [Preadditive.add_comp, Preadditive.comp_add]
        rw [f.comm1, g.comm1]
      comm2 := by
        intro p q
        simp only [Preadditive.add_comp, Preadditive.comp_add]
        rw [f.comm2, g.comm2] }
  add_assoc f g h := by
    apply DoubleComplexMap.ext _ _
    intro p q
    change (f.f p q + g.f p q) + h.f p q = f.f p q + (g.f p q + h.f p q)
    simp only [add_assoc]
  zero :=
    { f := fun p q => 0
      comm1 := by simp
      comm2 := by simp }
  zero_add f := by
    apply DoubleComplexMap.ext _ _
    intro p q
    change 0 + f.f p q = f.f p q
    simp
  add_zero f := by
    apply DoubleComplexMap.ext _ _
    intro p q
    change f.f p q + 0 = f.f p q
    simp
  neg f :=
    { f := fun p q => -f.f p q
      comm1 := by
        intro p q
        simp only [Preadditive.comp_neg, Preadditive.neg_comp]
        rw [f.comm1]
      comm2 := by
        intro p q
        simp only [Preadditive.comp_neg, Preadditive.neg_comp]
        rw [f.comm2] }
  sub f g :=
    { f := fun p q => f.f p q - g.f p q
      comm1 := by
        intro p q
        simp only [Preadditive.sub_comp, Preadditive.comp_sub]
        rw [f.comm1, g.comm1]
      comm2 := by
        intro p q
        simp only [Preadditive.sub_comp, Preadditive.comp_sub]
        rw [f.comm2, g.comm2] }
  nsmul := fun n f =>
    { f := fun p q => n • f.f p q
      comm1 := by
        intro p q
        simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul]
        rw [f.comm1]
      comm2 := by
        intro p q
        simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul]
        rw [f.comm2] }
  zsmul := fun n f =>
    { f := fun p q => n • f.f p q
      comm1 := by
        intro p q
        simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
        rw [f.comm1]
      comm2 := by
        intro p q
        simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
        rw [f.comm2] }
  neg_add_cancel f := by
    apply DoubleComplexMap.ext _ _
    intro p q
    change -f.f p q + f.f p q = 0
    simp
  add_comm f g := by
    apply DoubleComplexMap.ext _ _
    intro p q
    change f.f p q + g.f p q = g.f p q + f.f p q
    simp [add_comm]
  nsmul_zero f := by
    apply DoubleComplexMap.ext _ _
    intro p q
    change (0 : ℕ) • f.f p q = 0
    simp
  nsmul_succ n f := by
    apply DoubleComplexMap.ext _ _
    intro p q
    change (n + 1) • f.f p q = n • f.f p q + f.f p q
    rw [add_nsmul]
    simp
  sub_eq_add_neg f g := by
    apply DoubleComplexMap.ext _ _
    intro p q
    change f.f p q - g.f p q = f.f p q + -g.f p q
    exact sub_eq_add_neg _ _
  zsmul_zero' f := by
    apply DoubleComplexMap.ext _ _
    intro p q
    change (0 : ℤ) • f.f p q = 0
    simp
  zsmul_succ' n f := by
    apply DoubleComplexMap.ext _ _
    intro p q
    change ((n : ℤ) + 1) • f.f p q = (n : ℤ) • f.f p q + f.f p q
    simpa only [one_zsmul] using (add_zsmul (f.f p q) (n : ℤ) 1)
  zsmul_neg' n f := by
    apply DoubleComplexMap.ext _ _
    intro p q
    change (Int.negSucc n) • f.f p q = -((Int.ofNat n.succ) • f.f p q)
    rw [negSucc_zsmul]
    simp only [Int.ofNat_eq_natCast, natCast_zsmul]

instance doubleComplexPreadditive
    {C : Type u} [Category.{v} C] [Preadditive C] :
    Preadditive (DoubleComplex C) where
  homGroup A B := doubleComplexMapAddCommGroup A B
  add_comp := by
    intro A B D f g h
    apply DoubleComplexMap.ext _ _
    intro p q
    change (f.f p q + g.f p q) ≫ h.f p q =
      f.f p q ≫ h.f p q + g.f p q ≫ h.f p q
    exact Preadditive.add_comp _ _ _ _ _ _
  comp_add := by
    intro A B D f g h
    apply DoubleComplexMap.ext _ _
    intro p q
    change f.f p q ≫ (g.f p q + h.f p q) =
      f.f p q ≫ g.f p q + f.f p q ≫ h.f p q
    exact Preadditive.comp_add _ _ _ _ _ _

/-! ## Distinguished triangles in the homotopy category -/

/-- The quotient functor from complexes to the source's homotopy category. -/
abbrev homotopyQuotient
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    BookComplex C ⥤ BookHomotopyCategory C :=
  HomotopyCategory.quotient C (ComplexShape.up ℤ)

/-- Mathlib's distinguished-triangle predicate, used for the source's
definition of distinguished triangles in `K(𝒜)`. -/
abbrev sourceDistinguishedTriangle
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    (T : Triangle (BookHomotopyCategory C)) : Prop :=
  T ∈ distTriang (BookHomotopyCategory C)

/-- The corresponding distinguished-triangle predicate on `K⁺(𝒜)`. -/
abbrev sourceDistinguishedTrianglePlus
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    (T : Triangle (KPlus C)) : Prop :=
  T ∈ distTriang (KPlus C)

/-- The corresponding distinguished-triangle predicate on `K⁻(𝒜)`. -/
abbrev sourceDistinguishedTriangleMinus
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    (T : Triangle (KMinus C)) : Prop :=
  T ∈ distTriang (KMinus C)

/-- The corresponding distinguished-triangle predicate on `Kᵇ(𝒜)`. -/
abbrev sourceDistinguishedTriangleBounded
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    (T : Triangle (KBounded C)) : Prop :=
  T ∈ distTriang (KBounded C)

/-- The source's definition is the canonical Mathlib characterization by
triangles associated to degreewise split short complexes. -/
theorem distinguished_iff_degreewise_split
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    (T : Triangle (BookHomotopyCategory C)) :
    sourceDistinguishedTriangle T ↔
      ∃ S σ, Nonempty (T ≅ CochainComplex.trianglehOfDegreewiseSplit S σ) := by
  simpa [sourceDistinguishedTriangle] using
    (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit T)

/-- The cone triangle is distinguished, matching the source's convention
`(K, L, C(f), f, i, -p)`. -/
theorem cone_triangle_source_distinguished
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    sourceDistinguishedTriangle (coneTriangleh f) := by
  exact coneTriangleh_distinguished f

/-- A triangle attached to a termwise split exact sequence is distinguished. -/
theorem termwise_split_triangle_source_distinguished
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    sourceDistinguishedTriangle (termwiseSplitTriangleh S) := by
  rw [distinguished_iff_degreewise_split]
  exact ⟨termwiseSplitShortComplex S, S.splitting, ⟨Iso.refl _⟩⟩

/- The generic witness in Unit 04 asks for an `AdditiveCategory` structure on
  the ambient category.  Homotopy categories canonically have the weaker
  preadditive structure used by their triangulated API, so this is the same
  source-facing witness with only the necessary hypotheses. -/
structure HomotopyOctahedronWitness
    {E : Type u} [Category.{v} E] [Preadditive E] [HasZeroObject E]
    [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated E] {X Y Z : E} (f : X ⟶ Y) (g : Y ⟶ Z) where
  Qone : E
  Qtwo : E
  Qthree : E
  pone : Y ⟶ Qone
  done : Qone ⟶ X⟦(1 : ℤ)⟧
  ptwo : Z ⟶ Qtwo
  dtwo : Qtwo ⟶ X⟦(1 : ℤ)⟧
  pthree : Z ⟶ Qthree
  dthree : Qthree ⟶ Y⟦(1 : ℤ)⟧
  h₁₂ : Triangle.mk f pone done ∈ distTriang E
  h₁₃ : Triangle.mk (f ≫ g) ptwo dtwo ∈ distTriang E
  h₂₃ : Triangle.mk g pthree dthree ∈ distTriang E
  octahedron :
    Nonempty (Triangulated.Octahedron (C := E) (by rfl) h₁₂ h₂₃ h₁₃)

/- The split-injection form of TR4 used in the source proof. -/
theorem two_split_injections_tr4
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (α : A ⟶ B) (β : B ⟶ D)
    (hα : termwiseSplitInjection α) (hβ : termwiseSplitInjection β) :
    Nonempty (HomotopyOctahedronWitness
      ((homotopyQuotient C).map α) ((homotopyQuotient C).map β)) := by
  sorry

/-- The homotopy category with its canonical distinguished triangles is
triangulated. -/
theorem homotopy_category_is_triangulated
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    CategoryTheory.IsTriangulated (BookHomotopyCategory C) := by
  infer_instance

/-! ## Bounded homotopy categories and exact functors -/

/-- The natural inclusions of the bounded homotopy categories into `K`. -/
abbrev homotopyPlusInclusion
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    KPlus C ⥤ BookHomotopyCategory C :=
  HomotopyCategory.Plus.ι C

abbrev homotopyMinusInclusion
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    KMinus C ⥤ BookHomotopyCategory C :=
  (boundedAboveHomotopyProperty C).ι

abbrev homotopyBoundedInclusion
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    KBounded C ⥤ BookHomotopyCategory C :=
  (boundedHomotopyProperty C).ι

/-- The boundedness part of the source's cone argument. -/
theorem cone_preserves_complex_boundedness
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    (IsBoundedBelow K → IsBoundedBelow L → IsBoundedBelow (Cone f)) ∧
      (IsBoundedAbove K → IsBoundedAbove L → IsBoundedAbove (Cone f)) ∧
      (IsBounded K → IsBounded L → IsBounded (Cone f)) := by
  sorry

/-- The bounded homotopy categories carry the same triangulated structures as
  the ambient homotopy category; boundedness of cones is the source's direct
  construction behind these instances. -/
theorem bounded_homotopy_categories_are_triangulated
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    CategoryTheory.IsTriangulated (KPlus C) ∧
      CategoryTheory.IsTriangulated (KMinus C) ∧
      CategoryTheory.IsTriangulated (KBounded C) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- `K⁺`, `K⁻`, and `Kᵇ` are full triangulated subcategories of `K`. -/
theorem bounded_homotopy_full_triangulated_subcategories
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    (homotopyPlusInclusion C).Full ∧
      (homotopyMinusInclusion C).Full ∧
      (homotopyBoundedInclusion C).Full ∧
      CategoryTheory.IsTriangulated (KPlus C) ∧
      CategoryTheory.IsTriangulated (KMinus C) ∧
      CategoryTheory.IsTriangulated (KBounded C) := by
  exact ⟨inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

/-- The additive functor induced on the unbounded homotopy category. -/
def additiveHomotopyFunctor
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    (F : C ⥤ D) [F.Additive] :
    BookHomotopyCategory C ⥤ BookHomotopyCategory D :=
  F.mapHomotopyCategory (ComplexShape.up ℤ)

/-- The additive functor induced on the bounded-below homotopy category. -/
def additiveHomotopyPlusFunctor
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    (F : C ⥤ D) [F.Additive] :
    KPlus C ⥤ KPlus D :=
  F.mapHomotopyCategoryPlus

/-- Preservation of the bounded-above property needed to restrict the
  ambient functor to `K⁻`. -/
theorem additive_homotopy_preserves_bounded_above
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    (F : C ⥤ D) [F.Additive] (X : KMinus C) :
    boundedAboveHomotopyProperty D
      ((additiveHomotopyFunctor F).obj ((homotopyMinusInclusion C).obj X)) := by
  sorry

/-- Preservation of the bounded property needed to restrict the ambient
  functor to `Kᵇ`. -/
theorem additive_homotopy_preserves_bounded
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    (F : C ⥤ D) [F.Additive] (X : KBounded C) :
    boundedHomotopyProperty D
      ((additiveHomotopyFunctor F).obj ((homotopyBoundedInclusion C).obj X)) := by
  sorry

/-- The additive functor induced on the bounded-above homotopy category. -/
def additiveHomotopyMinusFunctor
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    (F : C ⥤ D) [F.Additive] :
    KMinus C ⥤ KMinus D :=
  ObjectProperty.lift (boundedAboveHomotopyProperty D)
    (homotopyMinusInclusion C ⋙ additiveHomotopyFunctor F)
    (fun X => additive_homotopy_preserves_bounded_above F X)

/-- The additive functor induced on the bounded homotopy category. -/
def additiveHomotopyBoundedFunctor
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    (F : C ⥤ D) [F.Additive] :
    KBounded C ⥤ KBounded D :=
  ObjectProperty.lift (boundedHomotopyProperty D)
    (homotopyBoundedInclusion C ⋙ additiveHomotopyFunctor F)
    (fun X => additive_homotopy_preserves_bounded F X)

/-- A source-facing package for a functor commuting with shifts and carrying
  distinguished triangles to distinguished triangles. -/
structure ExactTriangulatedFunctorData
    {E F : Type*} [Category* E] [Category* F]
    [Preadditive E] [Preadditive F] [HasZeroObject E] [HasZeroObject F]
    [HasShift E ℤ] [HasShift F ℤ]
    [∀ n : ℤ, (shiftFunctor E n).Additive]
    [∀ n : ℤ, (shiftFunctor F n).Additive]
    [Pretriangulated E] [Pretriangulated F] (G : E ⥤ F) where
  commShift : G.CommShift ℤ
  isTriangulated : let _ := commShift; G.IsTriangulated

/-- The four induced functors in the source's additive exact-functor lemma. -/
theorem additive_homotopy_functors_are_exact
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    (F : C ⥤ D) [F.Additive] :
    Nonempty (ExactTriangulatedFunctorData (additiveHomotopyFunctor F)) ∧
      Nonempty (ExactTriangulatedFunctorData (additiveHomotopyPlusFunctor F)) ∧
      Nonempty (ExactTriangulatedFunctorData (additiveHomotopyMinusFunctor F)) ∧
      Nonempty (ExactTriangulatedFunctorData (additiveHomotopyBoundedFunctor F)) := by
  sorry

/-! ## Improving distinguished triangles -/

/-- A distinguished triangle can be represented by a termwise split short
  exact sequence without changing its outer complexes or the connecting map. -/
theorem improve_distinguished_triangle_homotopy
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C}
    (a : (homotopyQuotient C).obj A ⟶ (homotopyQuotient C).obj B)
    (b : (homotopyQuotient C).obj B ⟶ (homotopyQuotient C).obj D)
    (c : (homotopyQuotient C).obj D ⟶
      (shiftFunctor (BookHomotopyCategory C) (1 : ℤ)).obj
        ((homotopyQuotient C).obj A))
    (hT : sourceDistinguishedTriangle (Triangle.mk a b c)) :
    ∃ (B' : BookComplex C) (S : TermwiseSplitExactSequence A B' D),
      ∃ e : Triangle.mk a b c ≅ termwiseSplitTriangleh S,
        e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₃ = 𝟙 _ := by
  sorry

/-! ## Double complexes and totalization -/

/- Cochain complexes inherit binary biproducts degreewise.  This is the
  missing hypothesis for Mathlib's canonical triangulation of the nested
  homotopy categories used below. -/
noncomputable instance cochainComplex_hasBinaryBiproducts
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    HasBinaryBiproducts (CochainComplex C ℤ) where
  has_binary_biproduct _K _L := inferInstance

/-- The first complex-of-complexes presentation of double complexes. -/
abbrev FirstDoubleComplexCategory
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  CochainComplex (CochainComplex C ℤ) ℤ

/-- The second complex-of-complexes presentation of double complexes. -/
abbrev SecondDoubleComplexCategory
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  CochainComplex (CochainComplex C ℤ) ℤ

/-- The first homotopy category of double complexes, in its nested-complex
  presentation. -/
abbrev KFirstDoubleComplex
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  HomotopyCategory (CochainComplex C ℤ) (.up ℤ)

/-- The second homotopy category of double complexes, in its nested-complex
  presentation. -/
abbrev KSecondDoubleComplex
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  HomotopyCategory (CochainComplex C ℤ) (.up ℤ)

/-- Read a complex of rows as a commuting double complex. -/
def firstDoubleComplexOfComplexes
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    (X : FirstDoubleComplexCategory C) : DoubleComplex C where
  obj p q := (X.X q).X p
  d1 p q := (X.X q).d p (p + 1)
  d2 p q := (X.d q (q + 1)).f p
  d1_sq p q := by
    exact (X.X q).d_comp_d p (p + 1) (p + 1 + 1)
  d2_sq p q := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
      congrArg (fun k => k.f p) (X.d_comp_d q (q + 1) (q + 1 + 1))
  comm p q := (X.d q (q + 1)).comm' p (p + 1) (by simp)

/-- Read a complex of columns as a commuting double complex. -/
def secondDoubleComplexOfComplexes
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    (X : SecondDoubleComplexCategory C) : DoubleComplex C where
  obj p q := (X.X p).X q
  d1 p q := (X.d p (p + 1)).f q
  d2 p q := (X.X p).d q (q + 1)
  d1_sq p q := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
      congrArg (fun k => k.f q) (X.d_comp_d p (p + 1) (p + 1 + 1))
  d2_sq p q := (X.X p).d_comp_d q (q + 1) (q + 1 + 1)
  comm p q := (X.d p (p + 1)).comm' q (q + 1) (by simp) |>.symm

/-- Maps in the first nested presentation act componentwise on rows. -/
def firstDoubleComplexMap
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {X Y : FirstDoubleComplexCategory C} (f : X ⟶ Y) :
    firstDoubleComplexOfComplexes X ⟶ firstDoubleComplexOfComplexes Y where
  f p q := (f.f q).f p
  comm1 p q := (f.f q).comm' p (p + 1) (by simp) |>.symm
  comm2 p q := by
    exact (congrArg (fun k => k.f p) (f.comm' q (q + 1) (by simp))).symm

/-- Maps in the second nested presentation act componentwise on columns. -/
def secondDoubleComplexMap
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {X Y : SecondDoubleComplexCategory C} (f : X ⟶ Y) :
    secondDoubleComplexOfComplexes X ⟶ secondDoubleComplexOfComplexes Y where
  f p q := (f.f p).f q
  comm1 p q := by
    exact (congrArg (fun k => k.f q) (f.comm' p (p + 1) (by simp))).symm
  comm2 p q := (f.f p).comm' q (q + 1) (by simp) |>.symm

/-- The first presentation as a functor into double complexes. -/
def firstDoubleComplexFunctor
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    FirstDoubleComplexCategory C ⥤ DoubleComplex C where
  obj := firstDoubleComplexOfComplexes
  map := firstDoubleComplexMap
  map_id := by
    intro X
    apply DoubleComplexMap.ext _ _
    intro p q
    change 𝟙 ((X.X q).X p) = 𝟙 ((X.X q).X p)
    rfl
  map_comp := by
    intro X Y Z f g
    apply DoubleComplexMap.ext _ _
    intro p q
    change (f.f q).f p ≫ (g.f q).f p = (f.f q).f p ≫ (g.f q).f p
    rfl

/-- The second presentation as a functor into double complexes. -/
def secondDoubleComplexFunctor
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    SecondDoubleComplexCategory C ⥤ DoubleComplex C where
  obj := secondDoubleComplexOfComplexes
  map := secondDoubleComplexMap
  map_id := by
    intro X
    apply DoubleComplexMap.ext _ _
    intro p q
    change 𝟙 ((X.X p).X q) = 𝟙 ((X.X p).X q)
    rfl
  map_comp := by
    intro X Y Z f g
    apply DoubleComplexMap.ext _ _
    intro p q
    change (f.f p).f q ≫ (g.f p).f q = (f.f p).f q ≫ (g.f p).f q
    rfl

noncomputable instance firstDoubleComplexFunctor_additive
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    Functor.Additive (firstDoubleComplexFunctor C) where
  map_add := by
    intro X Y f g
    apply DoubleComplexMap.ext _ _
    intro p q
    change ((f + g).f q).f p = (f.f q).f p + (g.f q).f p
    rfl

noncomputable instance secondDoubleComplexFunctor_additive
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    Functor.Additive (secondDoubleComplexFunctor C) where
  map_add := by
    intro X Y f g
    apply DoubleComplexMap.ext _ _
    intro p q
    change ((f + g).f p).f q = (f.f p).f q + (g.f p).f q
    rfl

noncomputable instance totalizationFunctor_additive
    (C : Type u) [Category.{v} C] [AdditiveCategory C]
    [HasCountableCoproducts C] :
    Functor.Additive (totalizationFunctor (C := C)) where
  map_add := by
    intro A B f g
    apply HomologicalComplex.hom_ext _ _
    intro n
    apply Sigma.hom_ext _ _
    intro p
    change
      Sigma.ι (fun p : ℤ => A.obj p (n - p)) p ≫
          Sigma.desc (fun r =>
            (f + g).f r (n - r) ≫
              Sigma.ι (fun s : ℤ => B.obj s (n - s)) r) =
        Sigma.ι (fun p : ℤ => A.obj p (n - p)) p ≫
          (Sigma.desc (fun r =>
              f.f r (n - r) ≫
                Sigma.ι (fun s : ℤ => B.obj s (n - s)) r) +
            Sigma.desc (fun r =>
              g.f r (n - r) ≫
                Sigma.ι (fun s : ℤ => B.obj s (n - s)) r))
    rw [Sigma.ι_desc, Preadditive.comp_add, Sigma.ι_desc, Sigma.ι_desc]
    change
      (f.f p (n - p) + g.f p (n - p)) ≫
          Sigma.ι (fun s : ℤ => B.obj s (n - s)) p =
        f.f p (n - p) ≫ Sigma.ι (fun s : ℤ => B.obj s (n - s)) p +
          g.f p (n - p) ≫ Sigma.ι (fun s : ℤ => B.obj s (n - s)) p
    rw [Preadditive.add_comp]

/-- Totalization from the first complex-of-complexes presentation. -/
def firstDoubleComplexTotalizationFunctor
    (C : Type u) [Category.{v} C] [AdditiveCategory C]
    [HasCountableCoproducts C] :
    FirstDoubleComplexCategory C ⥤ CochainComplex C ℤ :=
  firstDoubleComplexFunctor C ⋙ totalizationFunctor (C := C)

/-- Totalization from the second complex-of-complexes presentation. -/
def secondDoubleComplexTotalizationFunctor
    (C : Type u) [Category.{v} C] [AdditiveCategory C]
    [HasCountableCoproducts C] :
    SecondDoubleComplexCategory C ⥤ CochainComplex C ℤ :=
  secondDoubleComplexFunctor C ⋙ totalizationFunctor (C := C)

noncomputable instance firstDoubleComplexTotalizationFunctor_additive
    (C : Type u) [Category.{v} C] [AdditiveCategory C]
    [HasCountableCoproducts C] :
    Functor.Additive (firstDoubleComplexTotalizationFunctor C) := by
  dsimp [firstDoubleComplexTotalizationFunctor]
  infer_instance

noncomputable instance secondDoubleComplexTotalizationFunctor_additive
    (C : Type u) [Category.{v} C] [AdditiveCategory C]
    [HasCountableCoproducts C] :
    Functor.Additive (secondDoubleComplexTotalizationFunctor C) := by
  dsimp [secondDoubleComplexTotalizationFunctor]
  infer_instance

/-- The two totalization functors descend to the two homotopy categories. -/
theorem first_totalization_respects_homotopy
    (C : Type u) [Category.{v} C] [AdditiveCategory C]
    [HasCountableCoproducts C]
    {X Y : FirstDoubleComplexCategory C} {f g : X ⟶ Y}
    (h : Homotopy f g) :
    (homotopyQuotient C).map
        ((firstDoubleComplexTotalizationFunctor C).map f) =
      (homotopyQuotient C).map
        ((firstDoubleComplexTotalizationFunctor C).map g) := by
  sorry

theorem second_totalization_respects_homotopy
    (C : Type u) [Category.{v} C] [AdditiveCategory C]
    [HasCountableCoproducts C]
    {X Y : SecondDoubleComplexCategory C} {f g : X ⟶ Y}
    (h : Homotopy f g) :
    (homotopyQuotient C).map
        ((secondDoubleComplexTotalizationFunctor C).map f) =
      (homotopyQuotient C).map
        ((secondDoubleComplexTotalizationFunctor C).map g) := by
  sorry

def firstDoubleHomotopyTotalizationFunctor
    (C : Type u) [Category.{v} C] [AdditiveCategory C]
    [HasCountableCoproducts C] :
    KFirstDoubleComplex C ⥤ BookHomotopyCategory C :=
  CategoryTheory.Quotient.lift
    (homotopic (CochainComplex C ℤ) (ComplexShape.up ℤ))
    (firstDoubleComplexTotalizationFunctor C ⋙ homotopyQuotient C)
    (by
      intro X Y f g h
      exact first_totalization_respects_homotopy C h.some)

def secondDoubleHomotopyTotalizationFunctor
    (C : Type u) [Category.{v} C] [AdditiveCategory C]
    [HasCountableCoproducts C] :
    KSecondDoubleComplex C ⥤ BookHomotopyCategory C :=
  CategoryTheory.Quotient.lift
    (homotopic (CochainComplex C ℤ) (ComplexShape.up ℤ))
    (secondDoubleComplexTotalizationFunctor C ⋙ homotopyQuotient C)
    (by
      intro X Y f g h
      exact second_totalization_respects_homotopy C h.some)

/-- Both totalization functors are exact triangulated functors. -/
theorem double_complex_totalizations_are_exact
    (C : Type u) [Category.{v} C] [AdditiveCategory C]
    [HasCountableCoproducts C] :
    Nonempty (ExactTriangulatedFunctorData
      (firstDoubleHomotopyTotalizationFunctor C)) ∧
      Nonempty (ExactTriangulatedFunctorData
        (secondDoubleHomotopyTotalizationFunctor C)) := by
  sorry

/-! ## Tensor products of double complexes -/

/-- With the first complex fixed, tensoring is a functor to double complexes. -/
def tensorProductDoubleComplexLeftFunctor
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [AdditiveCategory A] [AdditiveCategory B] [AdditiveCategory C]
    (T : BilinearFunctor A B C) (X : CochainComplex A ℤ) :
    CochainComplex B ℤ ⥤ DoubleComplex C where
  obj Y := tensorProductDoubleComplex T X Y
  map := fun {Y Y'} f =>
    { f := fun p q =>
        T.functor.map (Prod.mkHom (𝟙 (X.X p)) (f.f q))
      comm1 := by
        intro p q
        dsimp [tensorProductDoubleComplex]
        simp only [← T.functor.map_comp, prod_comp, Category.comp_id, Category.id_comp]
      comm2 := by
        intro p q
        dsimp [tensorProductDoubleComplex]
        simp only [← T.functor.map_comp, prod_comp, Category.comp_id]
        rw [← f.comm' q (q + 1) (by simp)] }
  map_id := by
    intro Y
    apply DoubleComplexMap.ext _ _
    intro p q
    change T.functor.map (Prod.mkHom (𝟙 (X.X p)) (𝟙 (Y.X q))) =
      𝟙 (T.functor.obj (X.X p, Y.X q))
    rw [← prod_id, T.functor.map_id]
  map_comp := by
    intro Y Y' Y'' f g
    apply DoubleComplexMap.ext _ _
    intro p q
    change T.functor.map (Prod.mkHom (𝟙 (X.X p)) (f.f q ≫ g.f q)) =
      T.functor.map (Prod.mkHom (𝟙 (X.X p)) (f.f q)) ≫
        T.functor.map (Prod.mkHom (𝟙 (X.X p)) (g.f q))
    rw [← T.functor.map_comp]
    congr 1
    ext <;> simp

/-- With the second complex fixed, tensoring is a functor to double complexes. -/
def tensorProductDoubleComplexRightFunctor
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [AdditiveCategory A] [AdditiveCategory B] [AdditiveCategory C]
    (T : BilinearFunctor A B C) (Y : CochainComplex B ℤ) :
    CochainComplex A ℤ ⥤ DoubleComplex C where
  obj X := tensorProductDoubleComplex T X Y
  map := fun {X X'} f =>
    { f := fun p q =>
        T.functor.map (Prod.mkHom (f.f p) (𝟙 (Y.X q)))
      comm1 := by
        intro p q
        dsimp [tensorProductDoubleComplex]
        simp only [← T.functor.map_comp, prod_comp, Category.comp_id]
        rw [← f.comm' p (p + 1) (by simp)]
      comm2 := by
        intro p q
        dsimp [tensorProductDoubleComplex]
        simp only [← T.functor.map_comp, prod_comp, Category.comp_id, Category.id_comp] }
  map_id := by
    intro X
    apply DoubleComplexMap.ext _ _
    intro p q
    change T.functor.map (Prod.mkHom (𝟙 (X.X p)) (𝟙 (Y.X q))) =
      𝟙 (T.functor.obj (X.X p, Y.X q))
    rw [← prod_id, T.functor.map_id]
  map_comp := by
    intro X X' X'' f g
    apply DoubleComplexMap.ext _ _
    intro p q
    change T.functor.map (Prod.mkHom (f.f p ≫ g.f p) (𝟙 (Y.X q))) =
      T.functor.map (Prod.mkHom (f.f p) (𝟙 (Y.X q))) ≫
        T.functor.map (Prod.mkHom (g.f p) (𝟙 (Y.X q)))
    rw [← T.functor.map_comp]
    congr 1
    ext <;> simp

/-- The tensor-product construction on both variables at once. -/
def tensorProductDoubleComplexBifunctor
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [AdditiveCategory A] [AdditiveCategory B] [AdditiveCategory C]
    (T : BilinearFunctor A B C) :
    (CochainComplex A ℤ × CochainComplex B ℤ) ⥤ DoubleComplex C where
  obj Z := tensorProductDoubleComplex T Z.1 Z.2
  map := fun {Z Z'} h =>
    { f := fun p q =>
        T.functor.map (Prod.mkHom (h.1.f p) (h.2.f q))
      comm1 := by
        intro p q
        dsimp [tensorProductDoubleComplex]
        simp only [← T.functor.map_comp, prod_comp, Category.comp_id,
          Category.id_comp]
        rw [← h.1.comm' p (p + 1) (by simp)]
      comm2 := by
        intro p q
        dsimp [tensorProductDoubleComplex]
        simp only [← T.functor.map_comp, prod_comp, Category.comp_id,
          Category.id_comp]
        rw [← h.2.comm' q (q + 1) (by simp)] }
  map_id := by
    intro Z
    apply DoubleComplexMap.ext _ _
    intro p q
    change T.functor.map (Prod.mkHom (𝟙 (Z.1.X p)) (𝟙 (Z.2.X q))) =
      𝟙 (T.functor.obj (Z.1.X p, Z.2.X q))
    rw [← prod_id, T.functor.map_id]
  map_comp := by
    intro Z Z' Z'' f g
    apply DoubleComplexMap.ext _ _
    intro p q
    change T.functor.map (Prod.mkHom (f.1.f p ≫ g.1.f p) (f.2.f q ≫ g.2.f q)) =
      T.functor.map (Prod.mkHom (f.1.f p) (f.2.f q)) ≫
        T.functor.map (Prod.mkHom (g.1.f p) (g.2.f q))
    rw [← T.functor.map_comp]
    congr 1

/-- The first fixed-variable tensor functor followed by totalization. -/
def tensorProductLeftTotalizationFunctor
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [AdditiveCategory A] [AdditiveCategory B] [AdditiveCategory C]
    [HasCountableCoproducts C]
    (T : BilinearFunctor A B C) (X : CochainComplex A ℤ) :
    CochainComplex B ℤ ⥤ BookHomotopyCategory C :=
  tensorProductDoubleComplexLeftFunctor T X ⋙
    totalizationFunctor (C := C) ⋙ homotopyQuotient C

/-- The second fixed-variable tensor functor followed by totalization. -/
def tensorProductRightTotalizationFunctor
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [AdditiveCategory A] [AdditiveCategory B] [AdditiveCategory C]
    [HasCountableCoproducts C]
    (T : BilinearFunctor A B C) (Y : CochainComplex B ℤ) :
    CochainComplex A ℤ ⥤ BookHomotopyCategory C :=
  tensorProductDoubleComplexRightFunctor T Y ⋙
    totalizationFunctor (C := C) ⋙ homotopyQuotient C

/-- Tensor totalization respects homotopies in the variable being varied. -/
theorem tensorProductLeft_respects_homotopy
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [AdditiveCategory A] [AdditiveCategory B] [AdditiveCategory C]
    [HasCountableCoproducts C]
    (T : BilinearFunctor A B C) (X : CochainComplex A ℤ)
    {Y Y' : CochainComplex B ℤ} {f g : Y ⟶ Y'}
    (h : Homotopy f g) :
    (tensorProductLeftTotalizationFunctor T X).map f =
      (tensorProductLeftTotalizationFunctor T X).map g := by
  sorry

theorem tensorProductRight_respects_homotopy
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [AdditiveCategory A] [AdditiveCategory B] [AdditiveCategory C]
    [HasCountableCoproducts C]
    (T : BilinearFunctor A B C) (Y : CochainComplex B ℤ)
    {X X' : CochainComplex A ℤ} {f g : X ⟶ X'}
    (h : Homotopy f g) :
    (tensorProductRightTotalizationFunctor T Y).map f =
      (tensorProductRightTotalizationFunctor T Y).map g := by
  sorry

/-- The exact functor `Y ↦ Tot(X ⊗ Y)` on homotopy categories. -/
def tensorProductLeftHomotopyFunctor
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [AdditiveCategory A] [AdditiveCategory B] [AdditiveCategory C]
    [HasCountableCoproducts C]
    (T : BilinearFunctor A B C) (X : CochainComplex A ℤ) :
    BookHomotopyCategory B ⥤ BookHomotopyCategory C :=
  CategoryTheory.Quotient.lift
    (homotopic B (ComplexShape.up ℤ))
    (tensorProductLeftTotalizationFunctor T X)
    (by
      intro Y Y' f g h
      exact tensorProductLeft_respects_homotopy T X h.some)

/-- The exact functor `X ↦ Tot(X ⊗ Y)` on homotopy categories. -/
def tensorProductRightHomotopyFunctor
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [AdditiveCategory A] [AdditiveCategory B] [AdditiveCategory C]
    [HasCountableCoproducts C]
    (T : BilinearFunctor A B C) (Y : CochainComplex B ℤ) :
    BookHomotopyCategory A ⥤ BookHomotopyCategory C :=
  CategoryTheory.Quotient.lift
    (homotopic A (ComplexShape.up ℤ))
    (tensorProductRightTotalizationFunctor T Y)
    (by
      intro X X' f g h
      exact tensorProductRight_respects_homotopy T Y h.some)

/-- Both fixed-variable tensor functors are exact, with the standard signed
  shift compatibility supplied by the total-complex construction. -/
theorem tensorProduct_homotopy_functors_are_exact
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [AdditiveCategory A] [AdditiveCategory B] [AdditiveCategory C]
    [HasCountableCoproducts C]
    (T : BilinearFunctor A B C) (X : CochainComplex A ℤ)
    (Y : CochainComplex B ℤ) :
    Nonempty (ExactTriangulatedFunctorData
      (tensorProductLeftHomotopyFunctor T X)) ∧
      Nonempty (ExactTriangulatedFunctorData
        (tensorProductRightHomotopyFunctor T Y)) := by
  sorry

/-- The shift isomorphism for the left tensor functor, including the signs on
  the diagonal total-complex summands. -/
theorem tensorProduct_left_shift_iso_signed
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [AdditiveCategory A] [AdditiveCategory B] [AdditiveCategory C]
    [HasCountableCoproducts C]
    (T : BilinearFunctor A B C) (X : CochainComplex A ℤ)
    (Y : CochainComplex B ℤ) :
    Nonempty ((tensorProductLeftHomotopyFunctor T X).obj
        ((homotopyQuotient B).obj (Y⟦(1 : ℤ)⟧)) ≅
      ((tensorProductLeftHomotopyFunctor T X).obj
        ((homotopyQuotient B).obj Y))⟦(1 : ℤ)⟧) := by
  sorry

/-- On each diagonal summand, the shift comparison used by the tensor
  totalization is multiplied by the existing `totalizationShiftSign`. -/
theorem tensorProduct_totalization_shift_sign
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [AdditiveCategory A] [AdditiveCategory B] [AdditiveCategory C]
    [HasCountableCoproducts C]
    (T : BilinearFunctor A B C) (X : CochainComplex A ℤ)
    (Y : CochainComplex B ℤ) (n p : ℤ) :
    ∃ γ :
        (shiftFunctor (CochainComplex C ℤ) ((0 : ℤ) + 1)).obj
            (totalComplex (tensorProductDoubleComplex T X Y)) ≅
          totalComplex
            (doubleComplexShift (tensorProductDoubleComplex T X Y) (0 : ℤ) 1),
      Sigma.ι
          (fun r : ℤ =>
            (tensorProductDoubleComplex T X Y).obj r
              (n + ((0 : ℤ) + 1) - r)) p ≫
          γ.hom.f n =
        totalizationShiftSign p (n + ((0 : ℤ) + 1) - p) (0 : ℤ) 1 •
          (eqToHom (by
            dsimp [doubleComplexShift]
            congr 1 <;> ring) ≫
            Sigma.ι
              (fun r : ℤ =>
                (doubleComplexShift
                    (tensorProductDoubleComplex T X Y) (0 : ℤ) 1).obj r
                  (n - r))
              (p - (0 : ℤ))) := by
  exact totalComplex_shift_component_formula
    (tensorProductDoubleComplex T X Y) (0 : ℤ) 1 n p

end Formalization.Books.Derived.Unit10
