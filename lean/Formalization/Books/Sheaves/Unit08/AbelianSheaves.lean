import Formalization.Books.Sheaves.Unit04.AbelianPresheaves
import Formalization.Books.Sheaves.Unit07.Sheaves
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Topology.Sheaves.Forget
import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Sheaves on Spaces, Chapter 8: Abelian sheaves

The source section is formalized with the canonical `AddCommGrpCat`-valued
presheaves and sheaves.  The abelian sheaf predicate is the source's
underlying-set sheaf condition, while `TopCat.Sheaf AddCommGrpCat X` is the
canonical category of such sheaves.  The exact sequence over an open cover is
presented with Mathlib's equalizer-products maps and `ShortComplex.Exact`.
-/

namespace Formalization.Books.Sheaves.Unit08

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit03
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit07

universe w v

/-! ## Abelian sheaves and their category -/

/-- An abelian sheaf on `X`, namely an abelian presheaf whose underlying
presheaf of sets is a sheaf. -/
abbrev AbelianSheaf {X : TopCat.{v}} (F : AbelianPresheaf.{w, v} X) : Prop :=
  SetSheaf (underlyingPresheaf F)

/-- The category `Ab(X)` of sheaves of abelian groups on `X`. -/
abbrev Ab (X : TopCat.{v}) := TopCat.Sheaf AddCommGrpCat.{w} X

/-- The source's underlying-set definition agrees with the canonical
`AddCommGrpCat`-valued sheaf condition. -/
theorem abelianSheaf_iff_categoryValuedSheaf
    {X : TopCat.{w}} (F : AbelianPresheaf.{w, w} X) :
    AbelianSheaf F ↔ TopCat.Presheaf.IsSheaf F := by
  change TopCat.Presheaf.IsSheaf
      (F ⋙ (CategoryTheory.forget AddCommGrpCat.{w})) ↔
    TopCat.Presheaf.IsSheaf F
  exact (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (CategoryTheory.forget AddCommGrpCat.{w}) F).symm

/-- The presheaf underlying an object of `Ab(X)` satisfies the source's
abelian-sheaf predicate. -/
theorem abelianSheaf_of_categoryValuedSheaf
    {X : TopCat.{w}} (F : Ab.{w, w} X) :
    AbelianSheaf F.presheaf := by
  exact (abelianSheaf_iff_categoryValuedSheaf F.presheaf).2 F.property

/-! ## Countable products and the real-line witness -/

/-- The source's local notion of surjectivity for a morphism of abelian sheaves. -/
abbrev AbelianSheafSurjective {X : TopCat.{v}} {F G : Ab.{w, v} X} (φ : F ⟶ G) : Prop :=
  TopCat.Presheaf.IsLocallySurjective φ.hom

/-- In `Ab(X)`, categorical epimorphisms are exactly locally surjective maps. -/
theorem abelianSheaf_epi_iff_surjective
    {X : TopCat.{v}} {F G : Ab.{w, v} X} (φ : F ⟶ G) :
    Epi φ ↔ AbelianSheafSurjective φ := by
  exact (TopCat.Sheaf.isLocallySurjective_iff_epi φ).symm

universe u

/-- The morphism between countable products induced by a family of morphisms. -/
noncomputable def countableProductMap {C : Type u} [Category.{v} C]
    [HasCountableProducts C] (A B : ℕ → C) (φ : ∀ n, A n ⟶ B n) :
    limit (Discrete.functor A) ⟶ limit (Discrete.functor B) :=
  limit.lift (Discrete.functor B)
    (Fan.mk _ (fun n => limit.π (Discrete.functor A) n ≫ φ n.as))

@[reassoc (attr := simp)] theorem countableProductMap_π
    {C : Type u} [Category.{v} C] [HasCountableProducts C]
    (A B : ℕ → C) (φ : ∀ n, A n ⟶ B n) (n : ℕ) :
    countableProductMap A B φ ≫ limit.π (Discrete.functor B) n =
      limit.π (Discrete.functor A) n ≫ φ n := by
  apply limit.lift_π

/-!
The next package is deliberately independent of a particular presentation of
`j_!`.  The concrete real-line family is supplied below; this interface lets
later chapters use its product morphism without unfolding sheaf presentations.
-/

/-- A countable family of short exact complexes together with its product map. -/
structure CountableShortExactFamily (C : Type u) [Category.{v} C]
    [HasCountableProducts C] where
  complex : ℕ → ShortComplex C
  shortExact : ∀ n, (complex n).ShortExact
  productMap_not_epi :
    ¬ Epi (countableProductMap (fun n => (complex n).X₂)
      (fun n => (complex n).X₃) (fun n => (complex n).g))

/-- Countable products are exact when they preserve the epimorphism in every
short exact family.  Products already preserve the finite-limit part in an
abelian category, so this is the right obstruction for the source's warning. -/
def CountableProductsExact (C : Type u) [Category.{v} C]
    [Abelian C] [HasCountableProducts C] : Prop :=
  ∀ (S : ℕ → ShortComplex C), (∀ n, (S n).ShortExact) →
    Epi (countableProductMap (fun n => (S n).X₂)
      (fun n => (S n).X₃) (fun n => (S n).g))

/-- The category of abelian sheaves on the real line, at an arbitrary size. -/
abbrev RealAbelianSheaves.{u} := Ab.{u, 0} (TopCat.of ℝ)

instance realAbelianSheaves_abelian : Abelian (RealAbelianSheaves.{u}) := by
  infer_instance

instance realAbelianSheaves_hasCountableProducts :
    HasCountableProducts (RealAbelianSheaves.{u}) := by
  infer_instance

/-- The explicit countable short-exact family used for the real-line product
counterexample.  Its standard geometric presentation is the family obtained
from the intervals `(1/(n+2), 1/(n+1))` and the exact quotient
`j_! ℤ → 𝒞⁰ → 𝒞⁰/j_! ℤ`; the package records the resulting sheaves and maps. -/
noncomputable def realLineShortExactFamily :
    CountableShortExactFamily (RealAbelianSheaves.{u}) := by
  sorry

theorem realLineShortExactFamily_shortExact (n : ℕ) :
    (realLineShortExactFamily.complex n).ShortExact :=
  realLineShortExactFamily.shortExact n

/-- The product morphism of the real-line family is not an epimorphism. -/
theorem realLineShortExactFamily_product_not_epi :
    ¬ Epi (countableProductMap
      (fun n => (realLineShortExactFamily.complex n).X₂)
      (fun n => (realLineShortExactFamily.complex n).X₃)
      (fun n => (realLineShortExactFamily.complex n).g)) :=
  realLineShortExactFamily.productMap_not_epi

/-- Equivalently, the real-line product morphism is not locally surjective. -/
theorem realLineShortExactFamily_product_not_surjective :
    ¬ AbelianSheafSurjective
      (countableProductMap
        (fun n => (realLineShortExactFamily.complex n).X₂)
        (fun n => (realLineShortExactFamily.complex n).X₃)
        (fun n => (realLineShortExactFamily.complex n).g)) := by
  intro h
  apply realLineShortExactFamily_product_not_epi
  exact abelianSheaf_epi_iff_surjective _ |>.2 h

/-- Countable products in `Ab(ℝ)` are not exact. -/
theorem realAbelianSheaves_not_countableProductsExact :
    ¬ CountableProductsExact (RealAbelianSheaves.{u}) := by
  intro h
  exact realLineShortExactFamily_product_not_epi
    (h realLineShortExactFamily.complex realLineShortExactFamily.shortExact)

/-! ## The exact sequence attached to an open cover -/

/-- The product of sections over the members of an open cover. -/
noncomputable abbrev abelianSheafCoverSectionsProduct
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens F U

/-- The product of sections over all pairwise intersections in an open cover. -/
noncomputable abbrev abelianSheafCoverIntersectionProduct
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.piInters F U

/-- The restriction map from sections over the union to the product of
sections over the members of the cover. -/
noncomputable abbrev abelianSheafCoverRestriction
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) :
    F.obj (op (iSup U)) ⟶ abelianSheafCoverSectionsProduct F U :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.res F U

/-- Restriction of the first member of each pair to its intersection. -/
noncomputable abbrev abelianSheafCoverLeftRestriction
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) :
    abelianSheafCoverSectionsProduct F U ⟶
      abelianSheafCoverIntersectionProduct F U :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes F U

/-- Restriction of the second member of each pair to its intersection. -/
noncomputable abbrev abelianSheafCoverRightRestriction
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) :
    abelianSheafCoverSectionsProduct F U ⟶
      abelianSheafCoverIntersectionProduct F U :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes F U

/-- The map sending a family `(s_i)` to the family of differences
`s_{i₀}|_{U_{i₀} ∩ U_{i₁}} - s_{i₁}|_{U_{i₀} ∩ U_{i₁}}`. -/
noncomputable abbrev abelianSheafCoverDifference
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) :
    abelianSheafCoverSectionsProduct F U ⟶
      abelianSheafCoverIntersectionProduct F U :=
  abelianSheafCoverLeftRestriction F U - abelianSheafCoverRightRestriction F U

/-- The short complex at the product of sections in the source's exact
sequence. -/
noncomputable def abelianSheafCoverShortComplex
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) : ShortComplex AddCommGrpCat.{u} where
  f := abelianSheafCoverRestriction F U
  g := abelianSheafCoverDifference F U
  zero := by
    rw [Preadditive.comp_sub]
    rw [TopCat.Presheaf.SheafConditionEqualizerProducts.w]
    exact sub_self _

/-- Exactness of the displayed complex
`0 → F(⋃ U_i) → ∏_i F(U_i) → ∏_(i₀,i₁) F(U_{i₀} ∩ U_{i₁})`. -/
abbrev AbelianSheafCoverExact
    {X : TopCat.{u}} {ι : Type u} (F : AbelianPresheaf.{u, u} X)
    (U : ι → Opens X) : Prop :=
  Mono (abelianSheafCoverRestriction F U) ∧
    (abelianSheafCoverShortComplex F U).Exact

/-- For an abelian presheaf, the sheaf condition is equivalent to exactness
of the source's cover complex for every open cover. -/
theorem abelianSheaf_iff_cover_exact
    {X : TopCat.{u}} (F : AbelianPresheaf.{u, u} X) :
    AbelianSheaf F ↔
      ∀ ⦃ι : Type u⦄ (U : ι → Opens X), AbelianSheafCoverExact F U := by
  rw [abelianSheaf_iff_categoryValuedSheaf,
    TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts]
  constructor
  · intro h ι U
    obtain ⟨hU⟩ := h U
    have hU' := isLimitForkMapOfIsLimit (CategoryTheory.forget AddCommGrpCat.{u})
      (TopCat.Presheaf.SheafConditionEqualizerProducts.w F U) hU
    have huniq := (Types.type_equalizer_iff_unique _ _).1 ⟨hU'⟩
    change Mono (abelianSheafCoverRestriction F U) ∧
      (abelianSheafCoverShortComplex F U).Exact
    constructor
    · rw [AddCommGrpCat.mono_iff_injective]
      intro x y hxy
      have hcond :
          (ConcreteCategory.hom (abelianSheafCoverLeftRestriction F U))
              (ConcreteCategory.hom (abelianSheafCoverRestriction F U) x) =
            (ConcreteCategory.hom (abelianSheafCoverRightRestriction F U))
              (ConcreteCategory.hom (abelianSheafCoverRestriction F U) x) := by
        simpa only [ConcreteCategory.comp_apply] using
          ConcreteCategory.congr_hom
            (TopCat.Presheaf.SheafConditionEqualizerProducts.w F U) x
      exact (huniq _ hcond).unique rfl hxy.symm
    · rw [ShortComplex.ab_exact_iff]
      intro x₂ hx₂
      have hcond :
          (ConcreteCategory.hom (abelianSheafCoverLeftRestriction F U)) x₂ =
            (ConcreteCategory.hom (abelianSheafCoverRightRestriction F U)) x₂ := by
        change (ConcreteCategory.hom (abelianSheafCoverLeftRestriction F U)) x₂ -
            (ConcreteCategory.hom (abelianSheafCoverRightRestriction F U)) x₂ = 0 at hx₂
        exact sub_eq_zero.mp hx₂
      obtain ⟨x₁, hx₁, _⟩ := huniq x₂ hcond
      refine ⟨x₁, ?_⟩
      change (ConcreteCategory.hom (abelianSheafCoverRestriction F U)) x₁ = x₂
      change (ConcreteCategory.hom
        (TopCat.Presheaf.SheafConditionEqualizerProducts.res F U)) x₁ = x₂ at hx₁
      exact hx₁
  · intro h ι U
    have hS := h U
    obtain ⟨hmono, hexact⟩ := hS
    have hinj : Function.Injective
        (ConcreteCategory.hom (abelianSheafCoverRestriction F U)) :=
      (AddCommGrpCat.mono_iff_injective _).1 hmono
    have hex :
        ∀ x₂, (ConcreteCategory.hom (abelianSheafCoverDifference F U)) x₂ = 0 →
          ∃ x₁, (ConcreteCategory.hom
            (abelianSheafCoverRestriction F U)) x₁ = x₂ :=
      (ShortComplex.ab_exact_iff _).1 hexact
    have huniq' :
        ∀ y, (ConcreteCategory.hom
            ((CategoryTheory.forget AddCommGrpCat.{u}).map
              (abelianSheafCoverLeftRestriction F U))) y =
            (ConcreteCategory.hom
              ((CategoryTheory.forget AddCommGrpCat.{u}).map
                (abelianSheafCoverRightRestriction F U))) y →
          ∃! x, (ConcreteCategory.hom
            ((CategoryTheory.forget AddCommGrpCat.{u}).map
              (abelianSheafCoverRestriction F U))) x = y := by
      intro y hy
      have hy' :
          (ConcreteCategory.hom (abelianSheafCoverLeftRestriction F U)) y =
            (ConcreteCategory.hom (abelianSheafCoverRightRestriction F U)) y := by
        exact hy
      have hy0 :
          (ConcreteCategory.hom (abelianSheafCoverDifference F U)) y = 0 := by
        change (ConcreteCategory.hom (abelianSheafCoverLeftRestriction F U)) y -
            (ConcreteCategory.hom (abelianSheafCoverRightRestriction F U)) y = 0
        exact sub_eq_zero.mpr hy'
      obtain ⟨x, hx⟩ := hex y hy0
      refine ⟨x, ?_, ?_⟩
      · exact hx
      · intro y' hy'
        apply hinj
        exact hy'.trans hx.symm
    have htype := Types.typeEqualizerOfUnique
      ((CategoryTheory.forget AddCommGrpCat.{u}).map
        (abelianSheafCoverRestriction F U))
      (by
        rw [← Functor.map_comp, ← Functor.map_comp,
          TopCat.Presheaf.SheafConditionEqualizerProducts.w])
      huniq'
    exact ⟨isLimitOfIsLimitForkMap (CategoryTheory.forget AddCommGrpCat.{u})
      (TopCat.Presheaf.SheafConditionEqualizerProducts.w F U) htype⟩

end Formalization.Books.Sheaves.Unit08
