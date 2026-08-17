import Formalization.Books.Algebra.Unit09.Localization
import Formalization.Books.Algebra.Unit90.CoherentRings
import Formalization.Books.Homology.Unit10.SerreSubcategories
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Defs

/-!
# More on Algebra, Chapter 53: Abelian categories of modules

The category of modules is represented by Mathlib's `ModuleCat`.  Full
subcategories are specified by `ObjectProperty`, and the Serre conditions are
the canonical `IsSerreClass` and `IsWeakSerreClass` interfaces from the
homological-algebra formalization.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Formalization.Books.MoreAlgebra.Unit53

/-! ## The ambient category and coherent modules -/

/-- Mathlib's bundled category of `R`-modules. -/
abbrev moduleCategory (R : Type u) [CommRing R] := ModuleCat.{u} R

theorem moduleCategory_is_abelian (R : Type u) [CommRing R] :
    Nonempty (Abelian (moduleCategory R)) :=
  ⟨inferInstance⟩

/- The coherent-module property and category are the canonical declarations
   from More Algebra's earlier coherent-rings chapter. -/
abbrev coherentModuleProperty (R : Type u) [CommRing R] :
    ObjectProperty (moduleCategory R) :=
  Formalization.Books.Algebra.Unit90.coherentModuleProperty R

abbrev coherentModuleCategory (R : Type u) [CommRing R] :=
  (coherentModuleProperty R).FullSubcategory

instance coherentModuleProperty_isWeakSerreClass
    (R : Type u) [CommRing R] :
    (coherentModuleProperty R).IsWeakSerreClass := by
  sorry

theorem coherentModuleCategory_is_abelian
    (R : Type u) [CommRing R] :
    Nonempty (Abelian (coherentModuleCategory R)) :=
  ⟨inferInstance⟩

/-! ## Modules on which a multiplicative subset acts invertibly -/

/-- The property that every element of `S` acts bijectively on a module. -/
abbrev localizationModuleProperty (R : Type u) [CommRing R] (S : Submonoid R) :
    ObjectProperty (moduleCategory R) :=
  Formalization.Books.Algebra.Unit09.localizationModuleProperty S

/-- The full subcategory of modules on which `S` acts by isomorphisms. -/
abbrev localizationModuleCategory (R : Type u) [CommRing R] (S : Submonoid R) :=
  (localizationModuleProperty R S).FullSubcategory

instance localizationModuleProperty_isSerreClass
    (R : Type u) [CommRing R] (S : Submonoid R) :
    (localizationModuleProperty R S).IsSerreClass := by
  sorry

theorem localizationModuleCategory_is_abelian
    (R : Type u) [CommRing R] (S : Submonoid R) :
    Nonempty (Abelian (localizationModuleCategory R S)) := by
  exact (Formalization.Books.Homology.Unit10.serre_subcategory_is_abelian_and_inclusion_exact
    (localizationModuleProperty R S)).1

/-! ## Ideal-power torsion modules -/

/-- Every element of `M` is killed by a positive power of the ideal `I`. -/
def IsIPowerTorsion {R : Type u} [CommRing R]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  ∀ x : M, ∃ n : ℕ, 0 < n ∧ ∀ a : R, a ∈ I ^ n → a • x = 0

/-- The object property of `I`-power torsion modules. -/
def iPowerTorsionModuleProperty (R : Type u) [CommRing R] (I : Ideal R) :
    ObjectProperty (moduleCategory R) :=
  fun M => IsIPowerTorsion I (M : Type u)

/-- The full subcategory of `I`-power torsion modules. -/
abbrev iPowerTorsionModuleCategory (R : Type u) [CommRing R] (I : Ideal R) :=
  (iPowerTorsionModuleProperty R I).FullSubcategory

theorem iPowerTorsionModuleProperty_isSerreClass
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG) :
    (iPowerTorsionModuleProperty R I).IsSerreClass := by
  sorry

theorem iPowerTorsionModuleCategory_is_abelian
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG) :
    Nonempty (Abelian (iPowerTorsionModuleCategory R I)) := by
  let hSerre : (iPowerTorsionModuleProperty R I).IsSerreClass :=
    iPowerTorsionModuleProperty_isSerreClass R I hI
  exact (@Formalization.Books.Homology.Unit10.serre_subcategory_is_abelian_and_inclusion_exact
    (moduleCategory R) _ _ (iPowerTorsionModuleProperty R I) hSerre).1

/-! ## Torsion modules -/

/-- The property that every element is killed by a non-zero-divisor. -/
def torsionModuleProperty (R : Type u) [CommRing R] :
    ObjectProperty (moduleCategory R) :=
  fun M => Module.IsTorsion R (M : Type u)

/-- The full subcategory of torsion modules. -/
abbrev torsionModuleCategory (R : Type u) [CommRing R] :=
  (torsionModuleProperty R).FullSubcategory

instance torsionModuleProperty_isSerreClass
    (R : Type u) [CommRing R] :
    (torsionModuleProperty R).IsSerreClass := by
  sorry

theorem torsionModuleCategory_is_abelian
    (R : Type u) [CommRing R] :
    Nonempty (Abelian (torsionModuleCategory R)) := by
  exact (Formalization.Books.Homology.Unit10.serre_subcategory_is_abelian_and_inclusion_exact
    (torsionModuleProperty R)).1

/-! ## Finitely generated modules and the non-Noetherian obstruction -/

/-- The property defining finitely generated modules. -/
abbrev finitelyGeneratedModuleProperty (R : Type u) [CommRing R] :
    ObjectProperty (moduleCategory R) :=
  ModuleCat.isFG R

/-- The full subcategory of finitely generated modules. -/
abbrev finitelyGeneratedModuleCategory (R : Type u) [CommRing R] :=
  FGModuleCat.{u} R

/-- The map `R → R/I`, viewed as a morphism of finitely generated modules. -/
def idealQuotientMap (R : Type u) [CommRing R] (I : Ideal R) :
    FGModuleCat.of R R ⟶ FGModuleCat.of R (R ⧸ I) :=
  FGModuleCat.ofHom (Ideal.Quotient.mkₐ R I).toLinearMap

/-- A non-finitely generated ideal gives a quotient map with no kernel in the
finitely generated module category. -/
theorem idealQuotientMap_has_no_kernel
    (R : Type u) [CommRing R] (I : Ideal R) (hI : ¬ I.FG) :
    ¬ HasKernel (idealQuotientMap R I) := by
  sorry

theorem finitelyGeneratedModuleCategory_not_abelian_of_not_noetherian
    (R : Type u) [CommRing R] (hR : ¬ IsNoetherianRing R) :
    ¬ Nonempty (Abelian (finitelyGeneratedModuleCategory R)) := by
  sorry

/-! ## The Noetherian case -/

/-- Over a Noetherian ring, coherence agrees with finite generation. -/
theorem coherentModuleProperty_iff_finitelyGenerated
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : moduleCategory R) :
    coherentModuleProperty R M ↔ finitelyGeneratedModuleProperty R M := by
  sorry

theorem finitelyGeneratedModuleCategory_is_abelian
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Nonempty (Abelian (finitelyGeneratedModuleCategory R)) :=
  ⟨inferInstance⟩

instance finitelyGeneratedModuleProperty_isSerreClass
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    (finitelyGeneratedModuleProperty R).IsSerreClass := by
  sorry

end Formalization.Books.MoreAlgebra.Unit53
