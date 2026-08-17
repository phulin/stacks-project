import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.LinearAlgebra.Basis.Basic
import Formalization.Books.Algebra.Unit75.TorGroups
import Formalization.Books.Derived.Unit15.ClassicalDerivedFunctors
import Formalization.Books.MoreAlgebra.Unit56.DerivedCategoriesOfModules

/-!
# More on Algebra, Chapter 57: Computing Tor

The source's module categories, bounded-above derived categories, and
cohomology functors are Mathlib's canonical categorical constructions.  The
Tor groups themselves reuse the canonical resolution-based construction from
Commutative Algebra, Chapter 75.  The only new interface here is the
source-facing package for a total left derived functor on bounded-above
derived categories and its computation on bounded-above complexes.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit75
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit15
open Formalization.Books.MoreAlgebra.Unit53
open Formalization.Books.MoreAlgebra.Unit56

universe w u v u' v'

namespace Formalization.Books.MoreAlgebra.Unit57

/-! ## Modules, projectives, and bounded-above derived categories -/

/-- The module category used in the source's notation `Mod_R`. -/
abbrev Mod (R : Type u) [CommRing R] := moduleCategory R

/-- The source's assertion that `Mod_R` has enough projectives. -/
theorem mod_has_enough_projectives (R : Type u) [CommRing R] :
    EnoughProjectives (Mod R) := by
  infer_instance

/-- A module with a basis is projective in the categorical module category. -/
theorem projective_module_of_basis (R : Type u) [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M] {ι : Type u}
    (b : Module.Basis ι R M) : Projective (ModuleCat.of R M) := by
  exact ModuleCat.projective_of_free b

/-- The source's `D(R)`. -/
abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] :=
  Formalization.Books.MoreAlgebra.Unit56.D R

/-- The source's bounded-above derived category `D⁻(R)`. -/
abbrev DMinus (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] :=
  Formalization.Books.MoreAlgebra.Unit56.DMinus R

/-! ## Ordinary tensor functors and their total left derived functors -/

/-- Tensoring an `R`-module on the right by a fixed module `M`. -/
noncomputable abbrev tensorModuleFunctor (R : Type u) [CommRing R]
    (M : Mod R) : Mod R ⥤ Mod R :=
  MonoidalCategory.tensorRight M

/- The source's total left derived functor is represented by a functor on
`D⁻`.  The `represented` field records its defining computation on the
bounded-above homotopy category, using the canonical localization functor. -/
structure LeftDerivedMinusFunctorData
    {C : Type u} [Category.{v} C] [Abelian C]
    {E : Type u'} [Category.{v'} E] [Abelian E]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} E]
    (F : C ⥤ E) [F.Additive] where
  /-- The total left derived functor on bounded-above derived categories. -/
  functor : Formalization.Books.Derived.Unit11.DMinus C ⥤
    Formalization.Books.Derived.Unit11.DMinus E
  /-- The functor is computed by `F` on bounded-above complexes. -/
  represented : ∀ K : KMinus C,
    Nonempty (functor.obj ((minusDerivedLocalizationFunctor C).obj K) ≅
      (classicalHomotopyMinusToDerived F).obj K)

/-- Bounded-above projective resolutions give the source's total left derived
functor for an additive functor out of a category with enough projectives. -/
theorem leftDerivedMinusFunctorData_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {E : Type u'} [Category.{v'} E] [Abelian E]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} E]
    [EnoughProjectives C] (F : C ⥤ E) [F.Additive] :
    Nonempty (LeftDerivedMinusFunctorData F) := by
  sorry

/-- A chosen total left derived functor on bounded-above derived categories. -/
noncomputable def leftDerivedMinusFunctor
    {C : Type u} [Category.{v} C] [Abelian C]
    {E : Type u'} [Category.{v'} E] [Abelian E]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} E]
    [EnoughProjectives C] (F : C ⥤ E) [F.Additive] :
    Formalization.Books.Derived.Unit11.DMinus C ⥤
      Formalization.Books.Derived.Unit11.DMinus E :=
  (Classical.choice (leftDerivedMinusFunctorData_exists F)).functor

/-- The total left derived tensor functor `- ⊗ᴸ_R M : D⁻(R) ⥤ D⁻(R)`. -/
noncomputable abbrev derivedTensorModuleFunctor
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : Mod R) :
    DMinus R ⥤ DMinus R :=
  leftDerivedMinusFunctor (tensorModuleFunctor R M)

/-! ## Cohomology and the Tor satellites -/

/- The degree-zero stalk of a module, regarded as an object of `D⁻(R)`. -/
noncomputable def moduleInDMinus (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (N : Mod R) : DMinus R :=
  ⟨(DerivedCategory.singleFunctor (Mod R) 0).obj N, ⟨0, inferInstance⟩⟩

/- The canonical cohomology functor on the bounded-above derived category. -/
noncomputable abbrev dMinusCohomologyFunctor
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (n : ℤ) :
    Formalization.Books.Derived.Unit11.DMinus C ⥤ C :=
  DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor C n

/-- The derived tensor product of a module object with `M`, represented in
`D⁻(R)`. -/
noncomputable abbrev derivedTensorModule
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M N : Mod R) : DMinus R :=
  (derivedTensorModuleFunctor R M).obj (moduleInDMinus R N)

/-- The cohomology object which is the `p`-th Tor satellite. -/
noncomputable abbrev derivedTorModule
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M N : Mod R) (p : ℕ) : Mod R :=
  (dMinusCohomologyFunctor (C := Mod R) (-(p : ℤ))).obj
    (derivedTensorModule R M N)

/-- The satellite identity `H⁻ᵖ(N ⊗ᴸ M) ≅ Tor_p^R(N, M)`. -/
theorem derivedTensorModule_cohomology_iso_tor
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M N : Mod R) (p : ℕ) :
    Nonempty (derivedTorModule R M N p ≅ Tor N M p) := by
  sorry

/-! ## Tensoring with an algebra -/

/-- The ordinary extension-of-scalars functor `- ⊗_R A : Mod_R ⥤ Mod_A`. -/
noncomputable abbrev algebraTensorFunctor
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) :
    Mod R ⥤ ModuleCat A :=
  ModuleCat.extendScalars f

instance algebraTensorFunctor_additive
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) :
    (algebraTensorFunctor f).Additive := by
  exact (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive

/-- The total left derived base-change functor
`- ⊗ᴸ_R A : D⁻(R) ⥤ D⁻(A)`. -/
noncomputable abbrev derivedTensorAlgebraFunctor
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (ModuleCat A)]
    (f : R →+* A) : DMinus R ⥤
      Formalization.Books.Derived.Unit11.DMinus (ModuleCat A) :=
  leftDerivedMinusFunctor (algebraTensorFunctor f)

/-- The `R`-module underlying the algebra `A` along `f`. -/
abbrev algebraAsRModule {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : Mod R :=
  (ModuleCat.restrictScalars f).obj (ModuleCat.of A A)

/-- The derived tensor product with an algebra, represented in `D⁻(A)`. -/
noncomputable abbrev derivedTensorAlgebra
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (ModuleCat A)]
    (f : R →+* A) (N : Mod R) :
      Formalization.Books.Derived.Unit11.DMinus (ModuleCat A) :=
  (derivedTensorAlgebraFunctor f).obj (moduleInDMinus R N)

/-- The `A`-module carrying the cohomology of derived base change. -/
noncomputable abbrev derivedTorAlgebra
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (ModuleCat A)]
    (f : R →+* A) (N : Mod R) (p : ℕ) : ModuleCat A :=
  (dMinusCohomologyFunctor (C := ModuleCat A) (-(p : ℤ))).obj
    (derivedTensorAlgebra f N)

/-- The algebra-valued satellite identity, after restriction to `R`, is the
canonical Tor group `Tor_p^R(N, A)`.  The source's `A`-module structure is
retained by the left-hand side. -/
theorem derivedTensorAlgebra_cohomology_iso_tor
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (ModuleCat A)]
    (f : R →+* A) (N : Mod R) (p : ℕ) :
    Nonempty ((ModuleCat.restrictScalars f).obj (derivedTorAlgebra f N p) ≅
      Tor N (algebraAsRModule f) p) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit57
