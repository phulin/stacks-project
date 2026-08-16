import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Examples, Chapter 11: The category of derived complete modules

This file contains the common interfaces and concrete module constructions used
by the chapter section.  The source defines derived completeness through the
derived inverse-limit construction `T(M, f)`.  For a module, the equivalent
criterion is the vanishing of maps from `A[1/f]` and of the corresponding
degree-one Ext group; that is the criterion used here because the earlier
derived-category development is not part of the Examples formalization.
-/

namespace Formalization.Books.Examples.Unit11

open CategoryTheory CategoryTheory.Limits

universe u v

variable {A : Type u} [CommRing A]

/-! ### Derived-complete modules and their inclusion -/

/-- The localization of an `A`-module at one element of `A`. -/
noncomputable def localizedModule (f : A) : ModuleCat.{u} A :=
  ModuleCat.of A (Localization.Away f)

/-- The module-level `Hom`/`Ext¹` vanishing criterion for `T(M, f) = 0`. -/
def HomAndExtOneVanish (f : A) (M : ModuleCat.{u} A) : Prop :=
  (∀ g : localizedModule f ⟶ M, g = 0) ∧
    (∀ e : CategoryTheory.Abelian.Ext (localizedModule f) M 1, e = 0)

/-- A module is derived complete along `I` when the `T(M, f)` criterion vanishes
for every `f ∈ I`. -/
def IsDerivedComplete (I : Ideal A) (M : ModuleCat.{u} A) : Prop :=
  ∀ f : A, f ∈ I → HomAndExtOneVanish f M

/-- The object property defining the category `C` in the source section. -/
def DerivedCompleteModuleProperty (I : Ideal A) :
    ObjectProperty (ModuleCat.{u} A) :=
  fun M => IsDerivedComplete I M

/-- The full category of derived complete `A`-modules. -/
abbrev DerivedCompleteModuleCategory (I : Ideal A) :=
  (DerivedCompleteModuleProperty I).FullSubcategory

/-- The inclusion `C ↪ Mod_A`. -/
def derivedCompleteModuleInclusion (I : Ideal A) :
    DerivedCompleteModuleCategory I ⥤ ModuleCat.{u} A :=
  (DerivedCompleteModuleProperty I).ι

/-! ### Derived completion and the direct-sum counterexample -/

/-- The derived-completion/H⁰ interface used by the source section.

The completion functor is the left adjoint to the inclusion of derived-complete
modules.  Its value on a module is the source's `H⁰(M^∧)`.  Mathlib supplies
the adjunction API, while the derived-category construction itself is deferred
to the proof stage. -/
structure DerivedCompletionData (I : Ideal A) where
  completion : ModuleCat.{u} A ⥤ DerivedCompleteModuleCategory I
  adjunction : completion ⊣ derivedCompleteModuleInclusion I

/-- The module underlying `H⁰(M^∧)` for a chosen derived-completion theory. -/
def derivedCompletionH0 {I : Ideal A} (D : DerivedCompletionData I)
    (M : ModuleCat.{u} A) :
    ModuleCat.{u} A :=
  (derivedCompleteModuleInclusion I).obj (D.completion.obj M)

/-- The derived-completion unit on modules. -/
def derivedCompletionUnit {I : Ideal A} (D : DerivedCompletionData I)
    (M : ModuleCat.{u} A) :
    M ⟶ derivedCompletionH0 D M :=
  D.adjunction.unit.app M

/-- The source formula for a colimit in `C`: apply module colimit and then
take the module underlying `H⁰` of derived completion. -/
noncomputable def derivedCompleteColimit {I : Ideal A} (D : DerivedCompletionData I)
    {J : Type v} [Category.{v} J]
    (F : J ⥤ DerivedCompleteModuleCategory I)
    [HasColimit (F ⋙ derivedCompleteModuleInclusion I)] :
    DerivedCompleteModuleCategory I :=
  D.completion.obj (colimit (F ⋙ derivedCompleteModuleInclusion I))

/-- The canonical cocone map into the completed colimit attached to a diagram in
the derived-complete category. -/
noncomputable def derivedCompleteColimitMap {I : Ideal A}
    (D : DerivedCompletionData I) {J : Type v} [Category.{v} J]
    (F : J ⥤ DerivedCompleteModuleCategory I)
    [HasColimit (F ⋙ derivedCompleteModuleInclusion I)] (j : J) :
    F.obj j ⟶ derivedCompleteColimit D F :=
  ObjectProperty.homMk <|
    colimit.ι (F ⋙ derivedCompleteModuleInclusion I) j ≫
      D.adjunction.unit.app (colimit (F ⋙ derivedCompleteModuleInclusion I))

/-- The ordinary module adic completion used in the direct-sum obstruction. -/
noncomputable def adicCompletionObject (I : Ideal A) (M : ModuleCat.{u} A) :
    ModuleCat.{u} A :=
  ModuleCat.of A (AdicCompletion I M)

/-- The canonical map from a module to its adic completion. -/
noncomputable def adicCompletionUnit (I : Ideal A) (M : ModuleCat.{u} A) :
    (M : Type u) →ₗ[A] (adicCompletionObject I M : Type u) :=
  AdicCompletion.of I M

/-- The direct sum `⊕ₙ A`, represented by finitely supported functions. -/
noncomputable def countableDirectSum (A : Type u) [CommRing A] : ModuleCat.{u} A :=
  ModuleCat.of A (ℕ →₀ A)

/-- The ideal `(p)` in the `p`-adic integers. -/
noncomputable def padicIdeal (p : ℕ) [Fact p.Prime] : Ideal ℤ_[p] :=
  Ideal.span {(p : ℤ_[p])}

/-- The module `ℤ_[p] / p^n ℤ_[p]`. -/
noncomputable def padicQuotient (p n : ℕ) [Fact p.Prime] : ModuleCat ℤ_[p] :=
  ModuleCat.of ℤ_[p] (ℤ_[p] ⧸ Ideal.span {((p : ℤ_[p]) ^ n)})

/-- Multiplication by `p^(n-m)` induces the map between the power quotients
`A/(p^m) → A/(p^n)` whenever `m ≤ n`. -/
noncomputable def padicPowerQuotientMap (p m n : ℕ) [Fact p.Prime] (hmn : m ≤ n) :
    padicQuotient p m ⟶ padicQuotient p n :=
  ModuleCat.ofHom <|
    (Ideal.span {((p : ℤ_[p]) ^ m)}).liftQ
      ((Ideal.span {((p : ℤ_[p]) ^ n)}).mkQ.comp
        (LinearMap.mulLeft ℤ_[p] ((p : ℤ_[p]) ^ (n - m)))) <| by
      refine (Ideal.span_le).2 ?_
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      change (Ideal.span {((p : ℤ_[p]) ^ n)}).mkQ
        (((p : ℤ_[p]) ^ (n - m)) * (p : ℤ_[p]) ^ m) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      apply Ideal.mem_span_singleton'.2
      refine ⟨1, ?_⟩
      rw [one_mul, ← pow_add, Nat.sub_add_cancel hmn]

/-- All existing filtered colimits in `C` are exact.  This is the
typeclass-free form of the `AB5` condition used to state its failure without
assuming the very colimit instances whose failure is being exhibited. -/
def FilteredColimitsExact (C : Type u) [Category.{v} C] : Prop :=
  ∀ (J : Type v) [Category.{v} J] [IsFiltered J] [HasColimitsOfShape J C],
    HasExactColimitsOfShape J C

end Formalization.Books.Examples.Unit11
