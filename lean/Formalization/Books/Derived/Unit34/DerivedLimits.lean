import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Formalization.Books.Derived.Unit29.UnboundedComplexes
import Formalization.Books.Derived.Unit31.KInjectiveComplexes
import Formalization.Books.Derived.Unit33.DerivedColimits

/-!
# Derived Categories, Chapter 34: derived limits

The source defines homotopy limits by the standard `1 - f` triangle.  The
presentations below keep the product object and its projections explicit, so
the definition also works when only the particular product in question is
known to exist.  The substantive theorem proofs are deferred to the prove
stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit29
open Formalization.Books.Derived.Unit31
open Formalization.Books.Derived.Unit33
open Formalization.Books.Categories.Unit22
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit15
open scoped BigOperators CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u' w

namespace Formalization.Books.Derived.Unit34

/-! ## Inverse systems and the defining triangle -/

/-- A sequential inverse system, indexed by `ℕᵒᵖ`. -/
abbrev DerivedInverseSystem (C : Type u) [Category.{v} C] := ℕᵒᵖ ⥤ C

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The adjacent transition map `F(n + 1) ⟶ F(n)` in an inverse system. -/
def inverseSystemTransition (F : DerivedInverseSystem C) (n : ℕ) :
    F.obj (Opposite.op (n + 1)) ⟶ F.obj (Opposite.op n) :=
  F.map (opHomOfLE (Nat.le_succ n))

/-- The composite transition map `F(n) ⟶ F(m)` for `m ≤ n`. -/
def inverseSystemMap (F : DerivedInverseSystem C) {m n : ℕ} (h : m ≤ n) :
    F.obj (Opposite.op n) ⟶ F.obj (Opposite.op m) :=
  F.map (opHomOfLE h)

/-- A chosen product of the objects in an inverse system. -/
structure ProductPresentation (F : DerivedInverseSystem C) where
  product : C
  projection : ∀ n : ℕ, product ⟶ F.obj (Opposite.op n)
  isLimit : IsLimit (Fan.mk product projection)

/-- The canonical chosen product when the relevant product exists. -/
noncomputable def productPresentation (F : DerivedInverseSystem C)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))] : ProductPresentation F :=
  { product := ∏ᶜ fun n : ℕ => F.obj (Opposite.op n)
    projection := fun n => Pi.π (fun n : ℕ => F.obj (Opposite.op n)) n
    isLimit := limit.isLimit _ }

/-- The map `1 - f` on the product of an inverse system. -/
noncomputable def inverseSystemDifferenceMap (F : DerivedInverseSystem C)
    (P : ProductPresentation F) : P.product ⟶ P.product :=
  P.isLimit.lift
    (Fan.mk P.product (fun n =>
      P.projection n - P.projection (n + 1) ≫ inverseSystemTransition F n))

/-- The defining triangle data for a derived limit. -/
structure DerivedLimitPresentation (F : DerivedInverseSystem C) (K : C) where
  product : ProductPresentation F
  inclusion : K ⟶ product.product
  connecting : product.product ⟶ (shiftFunctor C (1 : ℤ)).obj K
  distinguished :
    Triangle.mk inclusion (inverseSystemDifferenceMap F product) connecting ∈
      distTriang C

/-- `K` is a derived (or homotopy) limit of `F`. -/
def IsDerivedLimit (F : DerivedInverseSystem C) (K : C) : Prop :=
  Nonempty (DerivedLimitPresentation F K)

/-- A chosen derived limit from an existence witness. -/
noncomputable def derivedLimit (F : DerivedInverseSystem C)
    (hF : ∃ K : C, IsDerivedLimit F K) : C :=
  Classical.choose hF

theorem derivedLimit_isDerivedLimit (F : DerivedInverseSystem C)
    (hF : ∃ K : C, IsDerivedLimit F K) :
    IsDerivedLimit F (derivedLimit F hF) := by
  exact Classical.choose_spec hF

/-- TR1 gives a derived limit as soon as the required product exists. -/
theorem exists_isDerivedLimit (F : DerivedInverseSystem C)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))] :
    ∃ K : C, IsDerivedLimit F K := by
  sorry

/-- TR3 uniqueness of a derived limit, up to a generally non-unique isomorphism. -/
theorem derivedLimit_unique_up_to_iso
    {F : DerivedInverseSystem C} {K L : C}
    (hK : IsDerivedLimit F K) (hL : IsDerivedLimit F L) :
    Nonempty (K ≅ L) := by
  sorry

/-- The source's example: once the standard countable-product infrastructure
for abelian groups is installed, every inverse system in `D(Ab)` has a
derived limit. -/
theorem derivedCategory_Ab_all_derived_limits
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    [HasCountableProducts (DerivedCategory (AddCommGrpCat.{u}))]
    (F : DerivedInverseSystem (DerivedCategory (AddCommGrpCat.{u}))) :
    ∃ K : DerivedCategory (AddCommGrpCat.{u}), IsDerivedLimit F K := by
  exact exists_isDerivedLimit F

/-! ## Bounded-below systems -/

/-- A system in `D⁺(A)`, regarded as a system in `D(A)`. -/
abbrev derivedPlusInverseSystem
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (F : DerivedInverseSystem (DPlus A)) :
    DerivedInverseSystem (DerivedCategory A) :=
  F ⋙ DerivedCategory.Plus.ι (C := A)

/-- In a category with countable products and enough injectives, an inverse
system of bounded-below derived objects has a derived limit. -/
theorem derivedLimit_exists_of_boundedBelow
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasCountableProducts A]
    [EnoughInjectives A]
    (F : DerivedInverseSystem (DPlus A)) :
    ∃ K : DerivedCategory A, IsDerivedLimit (derivedPlusInverseSystem F) K := by
  sorry

/-! ## Products in derived categories -/

section DerivedProducts

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] [HasCountableProducts A]
  [CountableAB4Star A]

/-- The termwise product of a countable family of complexes. -/
noncomputable def termwiseProductComplex
    {I : Type u'} [Countable I] (K : I → BookComplex A) : BookComplex A :=
  Formalization.Books.Derived.Unit31.productComplex K

/-- The projection from a termwise product of complexes. -/
noncomputable def termwiseProductComplexProjection
    {I : Type u'} [Countable I] (K : I → BookComplex A) (i : I) :
    termwiseProductComplex K ⟶ K i :=
  Formalization.Books.Derived.Unit31.productComplexProjection K i

/-- The derived-category fan represented by a termwise product. -/
noncomputable def derivedTermwiseProductFan
    {I : Type u'} [Countable I] (K : I → BookComplex A) :
    Fan (fun i => (DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj (K i)) :=
  Fan.mk
    ((DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj
      (termwiseProductComplex K))
    (fun i => (DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).map
      (termwiseProductComplexProjection K i))

/-- Exact countable products in `A` give countable products in `D(A)`. -/
instance derivedCategory_hasCountableProducts :
    HasCountableProducts (DerivedCategory A) := by
  sorry

/-- A termwise product of representatives is a product in the derived category. -/
theorem derivedTermwiseProductFan_isLimit
    {I : Type u'} [Countable I] (K : I → BookComplex A) :
    Nonempty (IsLimit (derivedTermwiseProductFan K)) := by
  sorry

/-- The cohomology of a countable derived product is the product of the
cohomologies.  The displayed equality in the source is represented by an
isomorphism in the abelian category. -/
theorem derivedProduct_cohomology_iso
    (K : ℕ → BookComplex A) (p : ℤ) :
    Nonempty
      (((DerivedCategory.homologyFunctor A p).obj
          ((DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj
            (termwiseProductComplex K))) ≅
        ∏ᶜ fun i : ℕ =>
          (DerivedCategory.homologyFunctor A p).obj
            ((DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj (K i))) := by
  sorry

theorem canonicalTruncation_product_cohomology_iso
    (K : BookComplex A) [∀ i : ℤ, K.HasHomology i] (p : ℤ) :
    Nonempty
      (((DerivedCategory.homologyFunctor A p).obj
          ((DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj
            (termwiseProductComplex (fun n : ℕ =>
              CochainComplex.canonicalTruncGE K (-((n : ℤ) + 1)))))) ≅
        ∏ᶜ fun n : ℕ =>
          (DerivedCategory.homologyFunctor A p).obj
            ((DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj
              (CochainComplex.canonicalTruncGE K (-((n : ℤ) + 1))))) := by
  sorry

end DerivedProducts

/-- The abelian-group example follows from the product theorem above with the
standard exact countable-product hypotheses on `AddCommGrpCat`. -/
theorem derivedCategory_Ab_all_derived_limits_of_exact_products
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    [HasCountableProducts (AddCommGrpCat.{u})]
    [CountableAB4Star (AddCommGrpCat.{u})]
    (F : DerivedInverseSystem (DerivedCategory (AddCommGrpCat.{u}))) :
    ∃ K : DerivedCategory (AddCommGrpCat.{u}), IsDerivedLimit F K := by
  exact derivedCategory_Ab_all_derived_limits F

/-- The exact sequence describing maps into a derived limit. -/
noncomputable abbrev homInverseSystemInto
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    (F : DerivedInverseSystem D) (L : D) :
    DerivedInverseSystem (AddCommGrpCat.{v'}) :=
  F ⋙ preadditiveCoyoneda.obj (Opposite.op L)

/-- The shifted system in the first term of the derived-limit Hom sequence. -/
abbrev shiftedInverseSystem (F : DerivedInverseSystem C) (n : ℤ) :
    DerivedInverseSystem C :=
  F ⋙ shiftFunctor C n

/-- The source's `R¹ lim` notation, using the established right-derived limit
functor on inverse systems of abelian groups. -/
noncomputable abbrev firstDerivedLimitInto
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    (F : DerivedInverseSystem D) (L : D)
    [HasInjectiveResolutions (DerivedInverseSystem (AddCommGrpCat.{v'}))] :
    AddCommGrpCat.{v'} :=
  Formalization.Books.Derived.Unit33.firstDerivedLimit
    (homInverseSystemInto F L)

theorem hom_into_derivedLimit_exact
    {F : DerivedInverseSystem C} {K L : C}
    (p : DerivedLimitPresentation F K)
    [HasInjectiveResolutions (DerivedInverseSystem (AddCommGrpCat.{v}))] :
    ∃ α : firstDerivedLimitInto (shiftedInverseSystem F (-1 : ℤ)) L ⟶
        (preadditiveCoyoneda.obj (Opposite.op L)).obj K,
      ∃ β : (preadditiveCoyoneda.obj (Opposite.op L)).obj K ⟶
        (lim : DerivedInverseSystem (AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}).obj
          (homInverseSystemInto F L),
    (ComposableArrows.mk₄
          (0 : (0 : AddCommGrpCat.{v}) ⟶
            firstDerivedLimitInto (shiftedInverseSystem F (-1 : ℤ)) L)
          α β
          (0 : (lim : DerivedInverseSystem (AddCommGrpCat.{v}) ⥤
            AddCommGrpCat.{v}).obj (homInverseSystemInto F L) ⟶
            (0 : AddCommGrpCat.{v}))).Exact := by
  sorry

/-- The projection from a presented derived limit to a stage of its system. -/
noncomputable def derivedLimitProjection
    {C : Type u'} [Category.{v'} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    {F : DerivedInverseSystem C} {R : C}
    (p : DerivedLimitPresentation F R) (n : ℕ) :
    R ⟶ F.obj (Opposite.op n) :=
  p.inclusion ≫ p.product.projection n

/-! ## The unused dual colimit interfaces -/

section DualColimitStatements

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasCountableProducts A] [CountableAB4Star A]

/-- The map from an inverse limit into the product of its stages. -/
noncomputable def inverseLimitToProduct
    (F : DerivedInverseSystem A)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))]
    [HasLimit F] :
    limit F ⟶ ∏ᶜ fun n : ℕ => F.obj (Opposite.op n) :=
  Pi.lift (fun n => limit.π F (Opposite.op n))

/-- The dual of the source's short exact sequence computing a sequential
colimit. -/
noncomputable def inverseLimitProductExactSequence
    (F : DerivedInverseSystem A)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))]
    [HasLimit F] : ComposableArrows A 4 :=
  ComposableArrows.mk₄
    (0 : (0 : A) ⟶ limit F)
    (inverseLimitToProduct F)
    (inverseSystemDifferenceMap F (productPresentation F))
    (0 : (∏ᶜ fun n : ℕ => F.obj (Opposite.op n)) ⟶ (0 : A))

theorem inverseLimit_product_exact
    (F : DerivedInverseSystem A)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))]
    [HasLimit F] :
    (inverseLimitProductExactSequence F).Exact := by
  sorry

/-- The termwise inverse limit of a system of complexes. -/
noncomputable def termwiseInverseLimitComplex
    (L : DerivedInverseSystem (BookComplex A)) [HasLimit L] : BookComplex A :=
  limit L

/-- The derived-category system attached to a system of complexes. -/
abbrev derivedComplexInverseSystem
    [HasDerivedCategory.{w} A] (L : DerivedInverseSystem (BookComplex A)) :
    DerivedInverseSystem (DerivedCategory A) :=
  L ⋙ (DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A)

theorem termwiseInverseLimit_isDerivedLimit
    [HasDerivedCategory.{w} A]
    (L : DerivedInverseSystem (BookComplex A)) [HasLimit L] :
    IsDerivedLimit (derivedComplexInverseSystem L)
      ((DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj
        (termwiseInverseLimitComplex L)) := by
  sorry

end DualColimitStatements

/-! The dual of the compact-object statement from the preceding chapter is
recorded here even though the source gives no applications. -/

/-- The dual compactness condition: maps from a countable product are detected
by the corresponding compactness condition in the opposite category. -/
instance additiveCategory_opposite
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D] :
    AdditiveCategory Dᵒᵖ where
  toPreadditive := inferInstance
  toHasFiniteProducts := inferInstance

instance hasCountableCoproducts_opposite
    {D : Type u'} [Category.{v'} D] [HasCountableProducts D] :
    HasCountableCoproducts Dᵒᵖ where
  out _ := inferInstance

abbrev IsCountablyCocompact
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    [HasCountableProducts D] (K : D) : Prop :=
  IsCountablyCompact (D := Dᵒᵖ) (Opposite.op K)

/-- The direct system of Hom groups obtained by applying `Hom(-, K)` to an
inverse system. -/
abbrev homDirectSystemOut
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    (F : DerivedInverseSystem D) (K : D) : ℕ ⥤ AddCommGrpCat.{v'} :=
  (opOp ℕ) ⋙ F.op ⋙ preadditiveYoneda.obj K

/-- Dual to the compact-object comparison for a derived colimit: for a
cocompact target, maps out of a derived limit are computed by the colimit of
the stagewise Hom groups. -/
theorem cocompact_hom_derivedLimit_colimit_bijective
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [HasCountableProducts D]
    {F : DerivedInverseSystem D} {L K : D}
    (p : DerivedLimitPresentation F L)
    (hK : IsCountablyCocompact K) :
    ∃ φ : colimit (homDirectSystemOut F K) ⟶
          (preadditiveYoneda.obj K).obj (Opposite.op L),
      Function.Bijective φ ∧
        ∀ n : ℕ,
          colimit.ι (homDirectSystemOut F K) n ≫ φ =
            (preadditiveYoneda.obj K).map (derivedLimitProjection p n).op := by
  sorry

/-! ## Functoriality -/

section Functoriality

variable {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- A strict representative of a pro-morphism, using the canonical
`ProMorphismData` representation from the categories chapters. -/
abbrev StrictProMorphismData (F G : DerivedInverseSystem D) :=
  {a : ProMorphismData F G // StrictMono a.index}

/-- The block map used in the second product map of a pro-morphism. -/
noncomputable def ProMorphismData.blockMap
    {F G : DerivedInverseSystem D} (a : StrictProMorphismData F G)
    (P : ProductPresentation F) (n : ℕ) :
  P.product ⟶ F.obj (Opposite.op (a.1.index n)) :=
  P.projection (a.1.index n) +
    Finset.sum (Finset.Icc 1 (a.1.index (n + 1) - a.1.index n - 1)) (fun k =>
      P.projection (a.1.index n + k) ≫
        inverseSystemMap F (Nat.le_add_right (a.1.index n) k))

/-- The first map of products induced by a pro-morphism. -/
noncomputable def ProMorphismData.firstProductMap
    {F G : DerivedInverseSystem D} (a : StrictProMorphismData F G)
    (P : ProductPresentation F) (Q : ProductPresentation G) :
    P.product ⟶ Q.product :=
  Q.isLimit.lift
    (Fan.mk P.product (fun n =>
      P.projection (a.1.index n) ≫ a.1.app n))

/-- The second map of products induced by a pro-morphism. -/
noncomputable def ProMorphismData.secondProductMap
    {F G : DerivedInverseSystem D} (a : StrictProMorphismData F G)
    (P : ProductPresentation F) (Q : ProductPresentation G) :
    P.product ⟶ Q.product :=
  Q.isLimit.lift
    (Fan.mk P.product (fun n =>
      ProMorphismData.blockMap a P n ≫ a.1.app n))

/-- TR3 supplies the dotted map between derived-limit triangles.  The
existential deliberately makes no uniqueness claim, matching the source's
warning; the later pro-isomorphism implication is not needed in this chapter.
-/
theorem derivedLimit_functorial
    {F G : DerivedInverseSystem D} {K L : D}
    (p : DerivedLimitPresentation F K)
    (q : DerivedLimitPresentation G L)
    (a : StrictProMorphismData F G) :
    ∃ φ : K ⟶ L,
      φ ≫ q.inclusion = p.inclusion ≫ ProMorphismData.firstProductMap a p.product q.product ∧
      ProMorphismData.firstProductMap a p.product q.product ≫
          inverseSystemDifferenceMap G q.product =
        inverseSystemDifferenceMap F p.product ≫
          ProMorphismData.secondProductMap a p.product q.product ∧
      ProMorphismData.secondProductMap a p.product q.product ≫ q.connecting =
        p.connecting ≫ (shiftFunctor D (1 : ℤ)).map φ := by
  sorry

end Functoriality

/-! ## Truncation systems -/

section Truncations

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A]

/-- The inverse system of canonical truncations `τ ≥ -(n + 1) K`. -/
noncomputable def truncationInverseSystem
    (K : BookComplex A) [∀ i : ℤ, K.HasHomology i] :
    DerivedInverseSystem (BookComplex A) :=
  Functor.ofOpSequence
    (X := fun n : ℕ =>
      CochainComplex.canonicalTruncGE K (-((n : ℤ) + 1)))
    (fun n => by
      simpa [Nat.cast_add, add_assoc] using canonicalTruncGETransition K n)

/-- The induced inverse system in the derived category. -/
abbrev truncationDerivedInverseSystem
    (K : BookComplex A) [∀ i : ℤ, K.HasHomology i] :
    DerivedInverseSystem (DerivedCategory A) :=
  truncationInverseSystem K ⋙ (DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A)

/-- The canonical map from a complex to its lower canonical truncation. -/
noncomputable def truncationCanonicalMap
    (K : BookComplex A) [∀ i : ℤ, K.HasHomology i] (n : ℕ) :
    (DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj K ⟶
      (truncationDerivedInverseSystem K).obj (Opposite.op n) :=
  (DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).map
    (CochainComplex.canonicalTruncGEπ K (-((n : ℤ) + 1)))

theorem truncationCanonicalMap_compatible
    (K : BookComplex A) [∀ i : ℤ, K.HasHomology i] (n : ℕ) :
    truncationCanonicalMap K (n + 1) ≫
        inverseSystemTransition (truncationDerivedInverseSystem K) n =
      truncationCanonicalMap K n := by
  sorry

theorem exists_map_into_truncationDerivedLimit
    (K : BookComplex A) [∀ i : ℤ, K.HasHomology i]
    {R : DerivedCategory A}
    (p : DerivedLimitPresentation (truncationDerivedInverseSystem K) R) :
    ∃ c : (DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj K ⟶ R,
      ∀ n : ℕ,
        c ≫ derivedLimitProjection p n = truncationCanonicalMap K n := by
  sorry

theorem truncation_map_cohomology_identity
    (K : BookComplex A) [∀ i : ℤ, K.HasHomology i]
    {R : DerivedCategory A}
    (p : DerivedLimitPresentation (truncationDerivedInverseSystem K) R)
    (c : (DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj K ⟶ R)
    (hc : ∀ n : ℕ,
      c ≫ derivedLimitProjection p n = truncationCanonicalMap K n)
    (i : ℤ) (n : ℕ) :
    (DerivedCategory.homologyFunctor A i).map c ≫
        (DerivedCategory.homologyFunctor A i).map (derivedLimitProjection p n) =
      (DerivedCategory.homologyFunctor A i).map (truncationCanonicalMap K n) := by
  sorry

theorem truncationCanonicalMap_cohomology_isIso
    (K : BookComplex A) [∀ i : ℤ, K.HasHomology i]
    (i : ℤ) (n : ℕ) (h : -((n : ℤ) + 1) ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor A i).map (truncationCanonicalMap K n)) := by
  sorry

/-- The canonical identification of the cohomology of a truncation with the
cohomology of the original complex in the stable range. -/
noncomputable def truncationHomologyComparison
    (K : BookComplex A) [∀ i : ℤ, K.HasHomology i]
    (i : ℤ) (n : ℕ) (h : -((n : ℤ) + 1) ≤ i) :
    (DerivedCategory.homologyFunctor A i).obj
        ((truncationDerivedInverseSystem K).obj (Opposite.op n)) ⟶
      (DerivedCategory.homologyFunctor A i).obj
        ((DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj K) := by
  letI := truncationCanonicalMap_cohomology_isIso K i n h
  exact inv ((DerivedCategory.homologyFunctor A i).map (truncationCanonicalMap K n))

theorem truncation_cohomology_composite_eq_id
    (K : BookComplex A) [∀ i : ℤ, K.HasHomology i]
    {R : DerivedCategory A}
    (p : DerivedLimitPresentation (truncationDerivedInverseSystem K) R)
    (c : (DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj K ⟶ R)
    (hc : ∀ n : ℕ,
      c ≫ derivedLimitProjection p n = truncationCanonicalMap K n)
    (i : ℤ) (n : ℕ) (h : -((n : ℤ) + 1) ≤ i) :
    (DerivedCategory.homologyFunctor A i).map c ≫
        (DerivedCategory.homologyFunctor A i).map (derivedLimitProjection p n) ≫
          truncationHomologyComparison K i n h =
      𝟙 ((DerivedCategory.homologyFunctor A i).obj
        ((DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj K)) := by
  sorry

theorem truncation_cohomology_map_isIso_iff_projection_isIso
    (K : BookComplex A) [∀ i : ℤ, K.HasHomology i]
    {R : DerivedCategory A}
    (p : DerivedLimitPresentation (truncationDerivedInverseSystem K) R)
    (c : (DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj K ⟶ R)
    (hc : ∀ n : ℕ,
      c ≫ derivedLimitProjection p n = truncationCanonicalMap K n)
    (i : ℤ) (n : ℕ) (h : -((n : ℤ) + 1) ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor A i).map c) ↔
      IsIso ((DerivedCategory.homologyFunctor A i).map
        (derivedLimitProjection p n)) := by
  sorry

theorem truncation_map_isIso_independent
    (K : BookComplex A) [∀ i : ℤ, K.HasHomology i]
    {R R' : DerivedCategory A}
    (p : DerivedLimitPresentation (truncationDerivedInverseSystem K) R)
    (p' : DerivedLimitPresentation (truncationDerivedInverseSystem K) R')
    (c : (DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj K ⟶ R)
    (c' : (DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj K ⟶ R')
    (hc : ∀ n : ℕ,
      c ≫ derivedLimitProjection p n = truncationCanonicalMap K n)
    (hc' : ∀ n : ℕ,
      c' ≫ derivedLimitProjection p' n = truncationCanonicalMap K n) :
    IsIso c ↔ IsIso c' := by
  sorry

end Truncations

theorem truncationDerivedLimit_exists
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasCountableProducts A]
    [EnoughInjectives A]
    (K : BookComplex A) [∀ i : ℤ, K.HasHomology i] :
    ∃ R : DerivedCategory A,
      IsDerivedLimit (truncationDerivedInverseSystem K) R := by
  sorry

/-- The cohomology calculation used in the final K-injective argument: the
cohomology of the derived limit of the canonical truncations agrees with that
of the original complex. -/
theorem truncationDerivedLimit_cohomology_iso
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasCountableProducts A]
    [CountableAB4Star A]
    (K : BookComplex A) [∀ i : ℤ, K.HasHomology i]
    {R : DerivedCategory A}
    (p : DerivedLimitPresentation (truncationDerivedInverseSystem K) R)
    (i : ℤ) :
    Nonempty
      ((DerivedCategory.homologyFunctor A i).obj R ≅
        (DerivedCategory.homologyFunctor A i).obj
          ((DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj K)) := by
  sorry

/-! ## Bounded-below inverse systems and K-injectives -/

section SpecialInverseSystems

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The inverse-system functor underlying a `SpecialInverseSystem`. -/
abbrev specialInverseSystemFunctor
    {I : ObjectProperty A} {K : BookComplex A}
    (S : SpecialInverseSystem I K) :
  DerivedInverseSystem (BookComplex A) :=
  Functor.ofOpSequence S.transition

/-- Enough injectives supplies the special system of bounded-below injective
complexes used in the source lemma. -/
theorem exists_injectiveSpecialInverseSystem
    {K : BookComplex A} [EnoughInjectives A]
    [∀ i : ℤ, K.HasHomology i] :
    Nonempty (SpecialInverseSystem (isInjective A) K) := by
  sorry

/-- A chosen complex limit of a special inverse system. -/
noncomputable abbrev specialInverseSystemLimit
    {I : ObjectProperty A} {K : BookComplex A}
    (S : SpecialInverseSystem I K) [HasLimit (specialInverseSystemFunctor S)] :
  BookComplex A :=
  limit (specialInverseSystemFunctor S)

/-- The degreewise projection from the inverse-system limit to a stage. -/
noncomputable def specialDegreeProjection
    {I : ObjectProperty A} {K : BookComplex A}
    (S : SpecialInverseSystem I K)
    [HasLimit (specialInverseSystemFunctor S)] (p : ℤ) (n : ℕ) :
    (specialInverseSystemLimit S).X p ⟶ (S.stage n).X p :=
  (limit.π (specialInverseSystemFunctor S) (Opposite.op n)).f p

/-- The degreewise `1 - f` map on the product of the stages. -/
noncomputable def specialDegreeDifference
    {I : ObjectProperty A} {K : BookComplex A}
    (S : SpecialInverseSystem I K)
    (p : ℤ) [HasCountableProducts A] :
    (∏ᶜ fun n : ℕ => (S.stage n).X p) ⟶ ∏ᶜ fun n : ℕ => (S.stage n).X p :=
  Pi.lift (fun n =>
    Pi.π (fun n : ℕ => (S.stage n).X p) n -
      Pi.π (fun n : ℕ => (S.stage n).X p) (n + 1) ≫ (S.transition n).f p)

/-- The degreewise exact sequence used in the proof of the K-injective
difficulty lemma. -/
noncomputable def specialDegreeExactSequence
    {I : ObjectProperty A} {K : BookComplex A}
    (S : SpecialInverseSystem I K)
    [HasLimit (specialInverseSystemFunctor S)]
    (p : ℤ) [HasCountableProducts A] : ComposableArrows A 4 :=
  ComposableArrows.mk₄
    (0 : (0 : A) ⟶ (specialInverseSystemLimit S).X p)
    (Pi.lift (fun n => specialDegreeProjection S p n))
    (specialDegreeDifference S p)
    (0 : (∏ᶜ fun n : ℕ => (S.stage n).X p) ⟶ (0 : A))

/-- Countable products provide the limits needed by the special inverse system. -/
theorem specialInverseSystem_hasLimit
    {I : ObjectProperty A} {K : BookComplex A}
    (S : SpecialInverseSystem I K) [HasCountableProducts A] :
    HasLimit (specialInverseSystemFunctor S) := by
  sorry

/- The comparison maps in a special inverse system induce the map from the
original complex to its inverse-system limit. -/
theorem specialInverseSystem_limit_map_exists
    {I : ObjectProperty A} {K : BookComplex A}
    (S : SpecialInverseSystem I K)
    [HasLimit (specialInverseSystemFunctor S)] :
    ∃ γ : K ⟶ specialInverseSystemLimit S,
      ∀ n : ℕ,
        γ ≫ limit.π (specialInverseSystemFunctor S) (Opposite.op n) =
          CochainComplex.canonicalTruncGEπ K (-((n : ℤ) + 1)) ≫ S.comparison n := by
  sorry

theorem specialDegreeExactSequence_exact
    {I : ObjectProperty A} {K : BookComplex A}
    (S : SpecialInverseSystem I K)
    [HasLimit (specialInverseSystemFunctor S)]
    (p : ℤ) [HasCountableProducts A] :
    (specialDegreeExactSequence S p).Exact := by
  sorry

/-- The degreewise sequence is split exact in the sense used in the source
proof; the splitting is recorded with Mathlib's `ShortComplex.Splitting`. -/
theorem specialDegreeExactSequence_split
    {I : ObjectProperty A} {K : BookComplex A}
    (S : SpecialInverseSystem I K)
    [HasLimit (specialInverseSystemFunctor S)]
    (p : ℤ) [HasCountableProducts A] :
    ∃ h : (Pi.lift (fun n => specialDegreeProjection S p n)) ≫
          specialDegreeDifference S p = 0,
      Nonempty (ShortComplex.mk
        (Pi.lift (fun n => specialDegreeProjection S p n))
        (specialDegreeDifference S p) h).Splitting := by
  sorry

theorem specialInverseSystem_limit_isKInjective
    {K : BookComplex A}
    (S : SpecialInverseSystem (isInjective A) K)
    [HasLimit (specialInverseSystemFunctor S)] :
    (specialInverseSystemLimit S).IsKInjective := by
  sorry

/-- The special inverse system represents the derived limit of the canonical
truncation system. -/
theorem specialInverseSystem_limit_represents_truncations
    {K : BookComplex A} [HasDerivedCategory.{w} A]
    (S : SpecialInverseSystem (isInjective A) K)
    [HasLimit (specialInverseSystemFunctor S)] :
    IsDerivedLimit (truncationDerivedInverseSystem K)
      ((DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj
        (specialInverseSystemLimit S)) := by
  sorry

/- The comparison-map formulation of the difficulty lemma.  The first two
conjuncts record the complex-level limit and K-injectivity; the final
equivalence is the source's comparison with the map in the derived category. -/
theorem difficulty_K_injectives
    {K : BookComplex A} [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [EnoughInjectives A]
    (S : SpecialInverseSystem (isInjective A) K)
    [HasLimit (specialInverseSystemFunctor S)] :
    ∃ γ : K ⟶ specialInverseSystemLimit S,
      (∀ n : ℕ,
        γ ≫ limit.π (specialInverseSystemFunctor S) (Opposite.op n) =
          CochainComplex.canonicalTruncGEπ K (-((n : ℤ) + 1)) ≫ S.comparison n) ∧
      (specialInverseSystemLimit S).IsKInjective ∧
      IsDerivedLimit (truncationDerivedInverseSystem K)
        ((DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj
          (specialInverseSystemLimit S)) ∧
      ∀ {R : DerivedCategory A}
        (p : DerivedLimitPresentation (truncationDerivedInverseSystem K) R)
        (c : (DerivedCategory.Q : BookComplex A ⥤ DerivedCategory A).obj K ⟶ R),
        (∀ n : ℕ,
          c ≫ derivedLimitProjection p n = truncationCanonicalMap K n) →
        (QuasiIso γ ↔ IsIso c) := by
  sorry

end SpecialInverseSystems

/-! ## Enough K-injectives -/

theorem every_complex_has_kInjective_resolution
    {A : Type u} [Category.{v} A] [Abelian A]
    [EnoughInjectives A] [HasCountableProducts A] [CountableAB4Star A] :
    ∀ K : BookComplex A, HasKInjectiveResolution A K := by
  sorry

end Formalization.Books.Derived.Unit34
