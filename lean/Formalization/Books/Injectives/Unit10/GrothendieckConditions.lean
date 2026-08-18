import Formalization.Books.Categories.Unit14.LimitsAndColimits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Filtered

/-!
# Injectives, Chapter 10: Grothendieck's AB conditions

The source uses the traditional names AB3, AB4, and AB5 (and their duals).
We use Mathlib's canonical interfaces: `HasCoproducts` and `HasProducts` for
AB3 and AB3*, `AB4`, `AB5`, `AB4Star`, and `AB5Star` for the exactness
conditions, `IsSeparator`/`HasSeparator` for a generator, and
`IsGrothendieckAbelian` for a Grothendieck abelian category.

The source's generator condition is recorded explicitly below as an equivalent
subobject formulation of `IsSeparator`; no second generator predicate is
introduced.
-/

namespace Formalization.Books.Injectives.Unit10

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C]

/-! ### The generator condition -/

/--
The source's definition of a generator, expressed with the canonical
`Subobject` and `Factors` APIs.  In an abelian category this is equivalent to
Mathlib's `IsSeparator` condition.
-/
theorem isSeparator_iff_source_generator [Abelian C] (U : C) :
    IsSeparator U ↔
      ∀ (M : C) (N : Subobject M), N ≠ ⊤ →
        ∃ f : U ⟶ M, ¬ N.Factors f := by
  constructor
  · intro h M N hN
    by_contra h'
    have hfac : ∀ f : U ⟶ M, N.Factors f := by
      intro f
      by_contra hf
      exact h' ⟨f, hf⟩
    apply hN
    letI : Epi N.arrow := by
      constructor
      intro Z g k e
      apply h.def g k
      intro f
      calc
        f ≫ g = (N.factorThru f (hfac f) ≫ N.arrow) ≫ g := by
          rw [Subobject.factorThru_arrow]
        _ = N.factorThru f (hfac f) ≫ (N.arrow ≫ g) := by simp only [Category.assoc]
        _ = N.factorThru f (hfac f) ≫ (N.arrow ≫ k) := by rw [e]
        _ = (N.factorThru f (hfac f) ≫ N.arrow) ≫ k := by simp only [Category.assoc]
        _ = f ≫ k := by rw [Subobject.factorThru_arrow]
    letI : Mono N.arrow := inferInstance
    letI : IsIso N.arrow := isIso_of_mono_of_epi _
    exact Subobject.eq_top_of_isIso_arrow N
  · intro h
    apply (isSeparator_def U).2
    intro X Y f g hfg
    by_contra hne
    let K := kernelSubobject (f - g)
    have hK : K ≠ ⊤ := by
      intro hK
      letI : IsIso K.arrow := (Subobject.isIso_arrow_iff_eq_top K).2 hK
      letI : IsIso (kernelSubobjectIso (f - g)).hom :=
        (kernelSubobjectIso (f - g)).isIso_hom
      letI : IsIso ((kernelSubobjectIso (f - g)).hom ≫ kernel.ι (f - g)) := by
        rw [kernelSubobject_arrow]
        infer_instance
      letI : IsIso (kernel.ι (f - g)) :=
        IsIso.of_isIso_comp_left (kernelSubobjectIso (f - g)).hom (kernel.ι (f - g))
      apply hne
      apply sub_eq_zero.mp
      rw [← cancel_epi (kernel.ι (f - g))]
      simpa using (kernel.condition (f - g))
    obtain ⟨t, ht⟩ := h X K hK
    apply ht
    apply (kernelSubobject_factors_iff (f - g) t).2
    rw [Preadditive.comp_sub, hfg, sub_self]

/-! ### AB3 and AB3* imply all (co)limits -/

/-- AB3: coproducts together with the abelian coequalizers give all colimits. -/
theorem hasColimits_of_ab3 [Abelian C] [HasCoproducts.{v} C] :
    HasColimits C :=
  Formalization.Books.Categories.Unit14.has_colimits_of_coproducts_and_coequalizers

/-- AB3*: products together with the abelian equalizers give all limits. -/
theorem hasLimits_of_ab3Star [Abelian C] [HasProducts.{v} C] :
    HasLimits C :=
  Formalization.Books.Categories.Unit14.has_limits_of_products_and_equalizers

/-! ### The exactness assertions -/

/--
Under AB4, the coproduct (direct sum) of a family of short exact sequences is
short exact.  A short complex in `Discrete I ⥤ C` is precisely such a family.
-/
theorem ab4_directSum_shortExact [Abelian C] [HasCoproducts.{v} C] [AB4 C]
    {I : Type v} (S : ShortComplex (Discrete I ⥤ C)) (hS : S.ShortExact) :
    (S.map (colim : (Discrete I ⥤ C) ⥤ C)).ShortExact := by
  exact hS.map_of_exact _

/- The colimit functor is right exact whenever the relevant coproduct exists;
   this is the source's warning that AB4 is only needed for left exactness. -/
theorem directSum_rightExact [HasCoproducts.{v} C] {I : Type v} :
    PreservesFiniteColimits (colim : (Discrete I ⥤ C) ⥤ C) := by
  infer_instance

/- The filtered form is stated for a general filtered category, which includes
   the directed-poset systems used in the source. -/
/-- Under AB5, filtered colimits preserve short exact sequences. -/
theorem ab5_filteredColimit_shortExact [Abelian C] [HasFilteredColimits C]
    [AB5 C] {J : Type v} [Category.{v} J] [IsFiltered J]
    (S : ShortComplex (J ⥤ C)) (hS : S.ShortExact) :
    (S.map (colim : (J ⥤ C) ⥤ C)).ShortExact := by
  exact hS.map_of_exact _

/- Filtered colimits are right exact as soon as they exist, without AB5. -/
theorem filteredColimit_rightExact {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J C] :
    PreservesFiniteColimits (colim : (J ⥤ C) ⥤ C) := by
  infer_instance

/-- Under AB4*, the product of a family of short exact sequences is short exact. -/
theorem ab4Star_product_shortExact [Abelian C] [HasProducts.{v} C] [AB4Star C]
    {I : Type v} (S : ShortComplex (Discrete I ⥤ C)) (hS : S.ShortExact) :
    (S.map (lim : (Discrete I ⥤ C) ⥤ C)).ShortExact := by
  exact hS.map_of_exact _

/- Products are left exact as soon as they exist, without AB4*. -/
theorem product_leftExact [HasProducts.{v} C] {I : Type v} :
    PreservesFiniteLimits (lim : (Discrete I ⥤ C) ⥤ C) := by
  infer_instance

/-- Under AB5*, cofiltered limits preserve short exact sequences. -/
theorem ab5Star_cofilteredLimit_shortExact [Abelian C]
    [HasCofilteredLimits C] [AB5Star C] {J : Type v} [Category.{v} J]
    [IsCofiltered J] (S : ShortComplex (J ⥤ C)) (hS : S.ShortExact) :
    (S.map (lim : (J ⥤ C) ⥤ C)).ShortExact := by
  sorry

/- Cofiltered limits are left exact as soon as they exist, without AB5*. -/
theorem cofilteredLimit_leftExact {J : Type v} [Category.{v} J] [IsCofiltered J]
    [HasLimitsOfShape J C] :
    PreservesFiniteLimits (lim : (J ⥤ C) ⥤ C) := by
  infer_instance

/-! ### The Grothendieck condition -/

/-- A Grothendieck abelian category has the source's AB5 condition. -/
theorem isGrothendieckAbelian_has_ab5 [Abelian C] [IsGrothendieckAbelian C] :
    AB5 C := by
  infer_instance

/-- A Grothendieck abelian category has the source's generator. -/
theorem isGrothendieckAbelian_has_generator [Abelian C]
    [IsGrothendieckAbelian C] : ∃ U : C, IsSeparator U := by
  exact HasSeparator.hasSeparator

end Formalization.Books.Injectives.Unit10
