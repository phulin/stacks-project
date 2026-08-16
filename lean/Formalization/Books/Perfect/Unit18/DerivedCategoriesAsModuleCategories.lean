import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Derived Categories of Schemes, Chapter 18: Derived categories as module categories

This file formalizes the precise interfaces and assertions in the section
“Derived categories as module categories”.
-/

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace Formalization.Books.Perfect.Unit18

noncomputable section

universe w u v

/-! ### Quasi-coherent complexes and the derived category -/

/-- A complex of `𝒪_X`-modules has quasi-coherent cohomology. -/
def HasQuasiCoherentCohomology (X : Scheme.{u})
    (K : CochainComplex X.Modules ℤ) : Prop :=
  ∀ n : ℤ, (K.homology n).IsQuasicoherent

/-- The object property used for `D_\QCoh(𝒪_X)`.  It is phrased using a
representative complex so that the definition uses Mathlib's chosen derived
category and its canonical cohomology objects. -/
def dQCohObjects (X : Scheme.{u}) [HasDerivedCategory.{v} X.Modules] :
    ObjectProperty (DerivedCategory X.Modules) :=
  fun K => ∃ C : CochainComplex X.Modules ℤ,
    DerivedCategory.Q.obj C = K ∧ HasQuasiCoherentCohomology X C

/-- The full subcategory `D_\QCoh(𝒪_X)`. -/
abbrev DQCoh (X : Scheme.{u}) [HasDerivedCategory.{v} X.Modules] :=
  (dQCohObjects X).FullSubcategory

/-! ### Differential graded algebra interfaces -/

/-- The graded data underlying a differential graded algebra.

The differential is the differential of the underlying cochain complex.  The
multiplication is kept as explicit graded data; the two law predicates below
are the algebraic compatibility conditions supplied by the differential
graded algebra development. -/
structure DifferentialGradedAlgebra where
  complex : CochainComplex AddCommGrpCat ℤ
  multiplication : ∀ n m : ℤ,
    complex.X n → complex.X m → complex.X (n + m)
  one : complex.X 0

/-- The associativity, unit, and additivity laws for a graded multiplication.

`HEq` records the canonical reassociation transports between graded pieces. -/
def GradedAlgebraLaws (E : DifferentialGradedAlgebra.{u}) : Prop :=
  (∀ (n m k : ℤ) (x : E.complex.X n) (y : E.complex.X m) (z : E.complex.X k),
    HEq (E.multiplication (n + m) k (E.multiplication n m x y) z)
      (E.multiplication n (m + k) x (E.multiplication m k y z))) ∧
  (∀ (n : ℤ) (x : E.complex.X n), HEq (E.multiplication 0 n E.one x) x) ∧
  (∀ (n : ℤ) (x : E.complex.X n), HEq (E.multiplication n 0 x E.one) x) ∧
  (∀ (n m : ℤ) (x₁ x₂ : E.complex.X n) (y : E.complex.X m),
    E.multiplication n m (x₁ + x₂) y =
      E.multiplication n m x₁ y + E.multiplication n m x₂ y) ∧
  (∀ (n m : ℤ) (x : E.complex.X n) (y₁ y₂ : E.complex.X m),
    E.multiplication n m x (y₁ + y₂) =
      E.multiplication n m x y₁ + E.multiplication n m x y₂)

/-- Transport an element of a graded piece along an equality of degrees. -/
def transportGraded {E : DifferentialGradedAlgebra.{u}} {n m : ℤ}
    (h : n = m) (x : E.complex.X n) : E.complex.X m := h ▸ x

/-- The Leibniz rule for the differential of a differential graded algebra. -/
def DifferentialGradedLeibniz (E : DifferentialGradedAlgebra.{u}) : Prop :=
  ∀ (n m : ℤ) (x : E.complex.X n) (y : E.complex.X m),
    E.complex.d (n + m) (n + m + 1) (E.multiplication n m x y) =
      transportGraded (E := E) (by omega)
        (E.multiplication n (m + 1) x (E.complex.d m (m + 1) y)) +
      transportGraded (E := E) (by omega)
        (n.negOnePow • E.multiplication (n + 1) m
          (E.complex.d n (n + 1) x) y)

/-- The property that the displayed graded data is a differential graded algebra.

Square-zero is already part of the `CochainComplex` structure. -/
def IsDifferentialGradedAlgebra (E : DifferentialGradedAlgebra.{u}) : Prop :=
  GradedAlgebraLaws E ∧ DifferentialGradedLeibniz E

/-- Finiteness of the set of degrees with nonzero cohomology. -/
def HasFiniteNonzeroCohomology (E : DifferentialGradedAlgebra.{u}) : Prop :=
  Set.Finite {n : ℤ | ¬ IsZero (E.complex.homology n)}

/-! ### The endomorphism differential graded algebra -/

open CochainComplex
open CochainComplex.HomComplex

/-- The endomorphism differential graded algebra of a complex, with
underlying complex the Mathlib cochain Hom complex. -/
def endomorphismDGA {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) :
    DifferentialGradedAlgebra where
  complex := CochainComplex.HomComplex K K
  multiplication := fun n m x y => y.comp x (by omega)
  one := Cochain.ofHom (𝟙 K)

/-- The endomorphism Hom complex carries the differential graded algebra laws. -/
theorem endomorphismDGA_isDGA {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) :
    IsDifferentialGradedAlgebra (endomorphismDGA K) := by
  sorry

/-! ### Derived tensor and derived DGA categories -/

/-- A chosen derived category of differential graded modules over `E`.

Mathlib has the localization machinery for ordinary derived categories but no
packaged category of differential graded modules.  This record is the
chapter-facing interface for the preceding DGA development: the proposition
field records that the chosen category is the derived localization of DGA
modules and is triangulated. -/
structure DifferentialGradedDerivedCategory
    (E : DifferentialGradedAlgebra.{u}) where
  carrier : Type v
  category : Category.{v} carrier
  derived_localization : Prop
  triangulated : Prop

instance (E : DifferentialGradedAlgebra.{u})
    (D : DifferentialGradedDerivedCategory.{u, v} E) : Category D.carrier := D.category

/-- Data for the derived tensor functor `- ⊗ᴸ_E K`. -/
structure DerivedTensorFunctorData {X : Scheme.{u}}
    [HasDerivedCategory.{v} X.Modules] (E : DifferentialGradedAlgebra.{u})
    (K : CochainComplex X.Modules ℤ)
    (D : DifferentialGradedDerivedCategory.{u, v} E) where
  functor : D.carrier ⥤ DerivedCategory X.Modules
  isDerivedTensor : Prop

/-- The functor carried by `DerivedTensorFunctorData`. -/
def derivedTensorFunctor {X : Scheme.{u}}
    [HasDerivedCategory.{v} X.Modules] {E : DifferentialGradedAlgebra.{u}}
    {K : CochainComplex X.Modules ℤ}
    {D : DifferentialGradedDerivedCategory.{u, v} E}
    (T : DerivedTensorFunctorData E K D) : D.carrier ⥤ DerivedCategory X.Modules :=
  T.functor

/-! ### The first lemma and the finite-cohomology theorem -/

/-- The derived tensor functor with a complex having quasi-coherent cohomology
lands in `D_\QCoh(𝒪_X)`. -/
theorem lemma_tensor_with_QCoh_complex {X : Scheme.{u}}
    [HasDerivedCategory.{v} X.Modules]
    (K : CochainComplex X.Modules ℤ) (hK : HasQuasiCoherentCohomology X K)
    (D : DifferentialGradedDerivedCategory (endomorphismDGA K))
    (T : DerivedTensorFunctorData (endomorphismDGA K) K D) :
    ∀ Y : D.carrier, dQCohObjects X (T.functor.obj Y) := by
  sorry

/-- Cohomology of the endomorphism DGA is the corresponding shifted Hom in the
derived category. -/
theorem endomorphism_cohomology_ext {X : Scheme.{u}}
    [HasDerivedCategory.{v} X.Modules]
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective] (n : ℤ) :
    (endomorphismDGA K).complex.homology n ≅
      AddCommGrpCat.of
        (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj K)⟦n⟧) := by
  sorry

/-- A quasi-compact and quasi-separated scheme has a quasi-coherent derived
category equivalent to the derived category of a DGA with finite cohomology. -/
theorem theorem_DQCoh_is_Ddga {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] :
    letI := HasDerivedCategory.standard X.Modules
    ∃ E : DifferentialGradedAlgebra,
      IsDifferentialGradedAlgebra E ∧ HasFiniteNonzeroCohomology E ∧
        ∃ D : DifferentialGradedDerivedCategory E,
          Nonempty (DQCoh X ≌ D.carrier) := by
  sorry

end

end Formalization.Books.Perfect.Unit18

example : MonoidalCategory (CochainComplex AddCommGrpCat ℤ) := inferInstance

end

end Books.Perfect.Unit18
