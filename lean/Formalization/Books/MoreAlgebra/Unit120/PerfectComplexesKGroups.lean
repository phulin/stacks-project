import Formalization.Books.Algebra.Unit55.KGroups
import Formalization.Books.Derived.Unit28.KGroups
import Formalization.Books.MoreAlgebra.Unit75.CharacterizingPerfectComplexes
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# More on Algebra, Chapter 120: Perfect complexes and K-groups

This file records the Euler-characteristic map from perfect derived objects to
the algebraic `K₀` of the ring, together with the exact-sequence and acyclic
complex interfaces used to make the construction independent of a chosen
finite projective representative.  The perfect derived category is the full
subcategory supplied by the object-property API.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Algebra.Unit55
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit28
open Formalization.Books.MoreAlgebra.Unit59
open Formalization.Books.MoreAlgebra.Unit75
open scoped BigOperators CategoryTheory.Pretriangulated

universe w u

namespace Formalization.Books.MoreAlgebra.Unit120

variable {R : Type u} [CommRing R]
variable [HasDerivedCategory.{w} (Formalization.Books.MoreAlgebra.Unit75.Mod R)]

/-! ## Perfect derived objects -/

/-- The perfect-object property in the derived category of `R`, reusing the
canonical object property from the earlier perfect-complex chapter. -/
abbrev perfectObjects (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Formalization.Books.MoreAlgebra.Unit75.Mod R)] :
    ObjectProperty (Formalization.Books.MoreAlgebra.Unit75.D R) :=
  Formalization.Books.MoreAlgebra.Unit75.PerfectObjects R

/-- Perfectness is invariant under isomorphism in the derived category. -/
instance perfectObjects_isClosedUnderIsomorphisms
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Formalization.Books.MoreAlgebra.Unit75.Mod R)] :
    (perfectObjects R).IsClosedUnderIsomorphisms := by
  sorry

/-- Perfect objects form a triangulated subcategory. -/
instance perfectObjects_isTriangulated
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Formalization.Books.MoreAlgebra.Unit75.Mod R)] :
    (perfectObjects R).IsTriangulated := by
  sorry

/-- The derived category of perfect objects, written `D_perf(R)` in the source. -/
abbrev PerfectDerivedCategory (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Formalization.Books.MoreAlgebra.Unit75.Mod R)] :=
  (perfectObjects R).FullSubcategory

/-- The triangulated `K₀` of the perfect derived category. -/
abbrev PerfectDerivedKZero (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Formalization.Books.MoreAlgebra.Unit75.Mod R)] :=
  Formalization.Books.Derived.Unit28.KZero (PerfectDerivedCategory R)

/-- Shift a perfect derived object, retaining its perfectness proof. -/
def perfectShift (K : PerfectDerivedCategory R) (n : ℤ) :
    PerfectDerivedCategory R :=
  ⟨(shiftFunctor (Formalization.Books.MoreAlgebra.Unit75.D R) n).obj K.obj,
    (perfectObjects R).le_shift n K.obj K.property⟩

/-! ## The alternating class of a finite projective complex -/

/-- A bounded complex whose terms are finite projective modules. -/
abbrev FiniteProjectiveComplex (R : Type u) [CommRing R] :=
  {E : Formalization.Books.MoreAlgebra.Unit75.Comp R //
    BoundedFiniteProjectiveComplex R E}

/-- The alternating `K₀(R)` class of a bounded finite-projective complex.

The sum is taken over the finite support of the complex, using the canonical
finite-support API for bounded complexes. -/
noncomputable def finiteProjectiveTermClass
    (E : Formalization.Books.MoreAlgebra.Unit75.Comp R)
    (hE : BoundedFiniteProjectiveComplex R E) (i : ℤ) :
    Formalization.Books.Algebra.Unit55.KZero R :=
  letI : Module.Projective R (E.X i : Type u) := (hE.2 i).1
  letI : Module.Finite R (E.X i : Type u) := (hE.2 i).2
  (i.negOnePow : ℤ) •
    Formalization.Books.Algebra.Unit55.kZeroClass
      (R := R) (M := (E.X i : Type u))

/-- The alternating `K₀(R)` class of a bounded finite-projective complex. -/
noncomputable def finiteProjectiveComplexClass
    (E : Formalization.Books.MoreAlgebra.Unit75.Comp R)
    (hE : BoundedFiniteProjectiveComplex R E) :
    Formalization.Books.Algebra.Unit55.KZero R :=
  ∑ i ∈
      (Formalization.Books.Derived.Unit28.boundedComplexTermSupport_finite
        (A := Formalization.Books.MoreAlgebra.Unit75.Mod R) E hE.1).toFinset,
    finiteProjectiveTermClass E hE i

/-- The class is additive across a short exact sequence of finite-projective
complexes.  This is the short-exact-sequence calculation in the proof of the
source's first lemma. -/
theorem finiteProjectiveComplexClass_shortExact
    {K L M : Formalization.Books.MoreAlgebra.Unit75.Comp R}
    (hK : BoundedFiniteProjectiveComplex R K)
    (hL : BoundedFiniteProjectiveComplex R L)
    (hM : BoundedFiniteProjectiveComplex R M)
    (f : K ⟶ L) (g : L ⟶ M) (hfg : f ≫ g = 0)
    (hS : ({ X₁ := K, X₂ := L, X₃ := M, f := f, g := g, zero := hfg } :
      ShortComplex (Formalization.Books.MoreAlgebra.Unit75.Comp R)).ShortExact) :
    finiteProjectiveComplexClass L hL =
      finiteProjectiveComplexClass K hK + finiteProjectiveComplexClass M hM := by
  sorry

/-- The kernel of a termwise surjection between bounded finite-projective
complexes is again bounded finite-projective. -/
theorem boundedFiniteProjectiveComplex_kernel_of_termwiseSurjective
    {K L : Formalization.Books.MoreAlgebra.Unit75.Comp R}
    (hK : BoundedFiniteProjectiveComplex R K)
    (hL : BoundedFiniteProjectiveComplex R L)
    (f : K ⟶ L) (hf : TermwiseSurjective f) :
    BoundedFiniteProjectiveComplex R (kernel f) := by
  sorry

/-- The kernel calculation for a termwise-surjective map of finite-projective
complexes. -/
theorem finiteProjectiveComplexClass_termwiseSurjective
    {K L : Formalization.Books.MoreAlgebra.Unit75.Comp R}
    (hK : BoundedFiniteProjectiveComplex R K)
    (hL : BoundedFiniteProjectiveComplex R L)
    (f : K ⟶ L) (hf : TermwiseSurjective f)
    (hker : BoundedFiniteProjectiveComplex R (kernel f)) :
    finiteProjectiveComplexClass K hK =
      finiteProjectiveComplexClass (kernel f) hker +
        finiteProjectiveComplexClass L hL := by
  sorry

/-- An acyclic bounded finite-projective complex has zero alternating class. -/
theorem finiteProjectiveComplexClass_eq_zero_of_acyclic
    (E : Formalization.Books.MoreAlgebra.Unit75.Comp R)
    (hE : BoundedFiniteProjectiveComplex R E)
    (hacyclic : IsAcyclic E) :
    finiteProjectiveComplexClass E hE = 0 := by
  sorry

/-- Quasi-isomorphic bounded finite-projective complexes have the same class. -/
theorem finiteProjectiveComplexClass_eq_of_quasiIso
    {K L : Formalization.Books.MoreAlgebra.Unit75.Comp R}
    (hK : BoundedFiniteProjectiveComplex R K)
    (hL : BoundedFiniteProjectiveComplex R L)
    (f : K ⟶ L) (hf : QuasiIsomorphism f) :
    finiteProjectiveComplexClass K hK =
      finiteProjectiveComplexClass L hL := by
  sorry

/-! ## The map `c` -/

/-- The map `c : perfect complexes over R → K₀(R)`. -/
noncomputable def perfectComplexClass
    (K : PerfectDerivedCategory R) :
    Formalization.Books.Algebra.Unit55.KZero R :=
  let hK : Perfect R K.obj := K.property
  let E := Classical.choose hK
  finiteProjectiveComplexClass E (Classical.choose_spec hK).1

/-- A distinguished triangle all of whose objects are perfect. -/
structure PerfectDistinguishedTriangle
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Formalization.Books.MoreAlgebra.Unit75.Mod R)] where
  triangle : Triangle (Formalization.Books.MoreAlgebra.Unit75.D R)
  distinguished : triangle ∈
    distTriang (Formalization.Books.MoreAlgebra.Unit75.D R)
  perfect₁ : perfectObjects R triangle.obj₁
  perfect₂ : perfectObjects R triangle.obj₂
  perfect₃ : perfectObjects R triangle.obj₃

/-- The alternating class is compatible with shifts. -/
theorem perfectComplexClass_shift
    (K : PerfectDerivedCategory R) (n : ℤ) :
    perfectComplexClass (perfectShift K n) =
      (n.negOnePow : ℤ) • perfectComplexClass K := by
  sorry

/-- The class computed from any bounded finite-projective representative is
the class of the represented perfect object. -/
theorem perfectComplexClass_eq_representation
    (K : PerfectDerivedCategory R)
    (E : Formalization.Books.MoreAlgebra.Unit75.Comp R)
    (hE : BoundedFiniteProjectiveComplex R E)
    (hIso : Nonempty ((derivedQuotient R).obj E ≅ K.obj)) :
    perfectComplexClass K = finiteProjectiveComplexClass E hE := by
  sorry

/-- The map `c` is additive on distinguished triangles of perfect objects. -/
theorem perfectComplexClass_distinguishedTriangle
    (T : PerfectDistinguishedTriangle R) :
    perfectComplexClass ⟨T.triangle.obj₂, T.perfect₂⟩ =
      perfectComplexClass ⟨T.triangle.obj₁, T.perfect₁⟩ +
        perfectComplexClass ⟨T.triangle.obj₃, T.perfect₃⟩ := by
  sorry

/-! ## Identification of the two zeroth K-groups -/

/-- The stalk of a finite projective module is a perfect derived object. -/
theorem perfectModule_of_finiteProjective
    (M : Formalization.Books.MoreAlgebra.Unit75.Mod R)
    [Module.Finite R (M : Type u)]
    [Module.Projective R (M : Type u)] :
    PerfectModule R M := by
  sorry

/-- The perfect derived object represented by a finite projective module in
degree zero. -/
noncomputable def perfectModuleObject
    (M : Formalization.Books.MoreAlgebra.Unit75.Mod R)
    [Module.Finite R (M : Type u)]
    [Module.Projective R (M : Type u)] : PerfectDerivedCategory R :=
  ⟨moduleInDerived R M, perfectModule_of_finiteProjective M⟩

/-- The stalk object attached to one term of a finite-projective complex. -/
noncomputable def perfectModuleTermObject
    (E : Formalization.Books.MoreAlgebra.Unit75.Comp R)
    (hE : BoundedFiniteProjectiveComplex R E) (i : ℤ) :
    PerfectDerivedCategory R :=
  letI : Module.Projective R (E.X i : Type u) := (hE.2 i).1
  letI : Module.Finite R (E.X i : Type u) := (hE.2 i).2
  perfectModuleObject (E.X i)

/-- In the perfect-derived K₀, a finite-projective complex is the alternating
sum of the classes of its stalk terms. -/
theorem perfectDerivedKZero_class_of_representation
    (E : Formalization.Books.MoreAlgebra.Unit75.Comp R)
    (hE : BoundedFiniteProjectiveComplex R E)
    (K : PerfectDerivedCategory R)
    (hIso : Nonempty ((derivedQuotient R).obj E ≅ K.obj)) :
    Formalization.Books.Derived.Unit28.KZero.classOf K =
      ∑ i ∈
        (Formalization.Books.Derived.Unit28.boundedComplexTermSupport_finite
          (A := Formalization.Books.MoreAlgebra.Unit75.Mod R) E hE.1).toFinset,
        (i.negOnePow : ℤ) •
          Formalization.Books.Derived.Unit28.KZero.classOf
            (perfectModuleTermObject E hE i) := by
  sorry

/-- The derived and algebraic zeroth K-groups are canonically isomorphic. -/
theorem perfectDerivedKZero_identification :
    ∃ e : PerfectDerivedKZero R ≃+
        Formalization.Books.Algebra.Unit55.KZero R,
      (∀ K : PerfectDerivedCategory R,
        e (Formalization.Books.Derived.Unit28.KZero.classOf K) =
          perfectComplexClass K) ∧
      (∀ (M : Formalization.Books.MoreAlgebra.Unit75.Mod R)
          [Module.Finite R (M : Type u)]
          [Module.Projective R (M : Type u)],
        e.symm (Formalization.Books.Algebra.Unit55.kZeroClass
          (R := R) (M := (M : Type u))) =
          Formalization.Books.Derived.Unit28.KZero.classOf
            (perfectModuleObject M)) := by
  sorry

/-- A chosen usable equivalence between `K₀(D_perf(R))` and `K₀(R)`. -/
noncomputable def perfectDerivedKZeroEquiv :
    PerfectDerivedKZero R ≃+
      Formalization.Books.Algebra.Unit55.KZero R :=
  Classical.choose (perfectDerivedKZero_identification (R := R))

/-- The chosen equivalence sends a perfect-object class to its alternating
class. -/
theorem perfectDerivedKZeroEquiv_class
    (K : PerfectDerivedCategory R) :
    perfectDerivedKZeroEquiv (R := R)
        (Formalization.Books.Derived.Unit28.KZero.classOf K) =
      perfectComplexClass K := by
  exact (Classical.choose_spec
    (perfectDerivedKZero_identification (R := R))).1 K

end Formalization.Books.MoreAlgebra.Unit120
