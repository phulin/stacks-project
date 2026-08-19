import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Polynomial.Basic
import Formalization.Books.MoreAlgebra.Unit59

/-!
# More on Algebra, Chapter 60: Derived change of rings

This file records the cross-ring derived tensor functors, their functoriality,
the tensor--restriction adjunction, and the associativity interfaces from the
chapter.  The underlying complexes and same-ring derived tensor product are
the canonical constructions exposed in the preceding chapters.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.MoreAlgebra.Unit56
open Formalization.Books.MoreAlgebra.Unit59
open Formalization.Books.MoreAlgebra.Unit58

universe w u v

namespace Formalization.Books.MoreAlgebra.Unit60

/-! ## Derived base change and tensoring with a complex -/

abbrev Comp (R : Type u) [CommRing R] := Unit59.Comp R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] := Unit59.D R

noncomputable abbrev derivedQuotient (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] : Comp R ⥤ D R :=
  Unit59.derivedComplexQuotient R

/- The degree-zero object used when the source writes a module as a complex.
   This is the same stalk construction used by the preceding Tor chapter. -/
noncomputable def moduleStalk (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (M : ModuleCat.{u} R) : D R :=
  (derivedQuotient R).obj
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)

noncomputable abbrev moduleComplex (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) : Comp R :=
  (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M

/- A derived tensor functor with a fixed object of the target derived
   category.  Its representation field is the K-flat computation from the
   source, while the exactness field records the fact that it is a derived
   functor of triangulated categories. -/
structure DerivedTensorObjectData
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (N : D A) where
  functor : D R ⥤ D A
  exact : Nonempty (ExactTriangulatedFunctorData functor)
  represented : ∀ (K : Comp R), IsKFlat K →
    Nonempty (functor.obj ((derivedQuotient R).obj K) ≅
      Unit59.derivedTensor
        ((derivedQuotient A).obj (Unit59.baseChangeComplex f K)) N)

theorem existsDerivedTensorObjectData
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (N : D A) : Nonempty (DerivedTensorObjectData f N) := by
  sorry

noncomputable def derivedTensorObjectData
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (N : D A) : DerivedTensorObjectData f N :=
  Classical.choice (existsDerivedTensorObjectData f N)

noncomputable abbrev derivedTensorObjectFunctor
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (N : D A) : D R ⥤ D A :=
  (derivedTensorObjectData f N).functor

theorem derivedTensorObject_exact
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (N : D A) : Nonempty (ExactTriangulatedFunctorData
      (derivedTensorObjectFunctor f N)) :=
  (derivedTensorObjectData f N).exact

theorem derivedTensorObject_of_kFlat
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (N : D A) (K : Comp R) (hK : IsKFlat K) :
    Nonempty ((derivedTensorObjectFunctor f N).obj
        ((derivedQuotient R).obj K) ≅
      Unit59.derivedTensor
        ((derivedQuotient A).obj (Unit59.baseChangeComplex f K)) N) :=
  (derivedTensorObjectData f N).represented K hK

/- The source's notation `- ⊗ᴸ_R N` for a complex `N` of `A`-modules. -/
noncomputable abbrev derivedTensorWithComplexFunctor
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (N : Comp A) : D R ⥤ D A :=
  derivedTensorObjectFunctor f ((derivedQuotient A).obj N)

/- Taking `N = A[0]` gives the derived base-change functor.  The stalk
   complex is the tensor unit supplied by Chapter 59. -/
noncomputable abbrev derivedBaseChangeFunctor
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) : D R ⥤ D A :=
  derivedTensorWithComplexFunctor f (tensorUnit A)

theorem derivedBaseChange_of_kFlat
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K : Comp R) (hK : IsKFlat K) :
    Nonempty ((derivedBaseChangeFunctor f).obj ((derivedQuotient R).obj K) ≅
      Unit59.derivedTensor
        ((derivedQuotient A).obj (Unit59.baseChangeComplex f K))
        ((derivedQuotient A).obj (tensorUnit A))) :=
  derivedTensorObject_of_kFlat f ((derivedQuotient A).obj (tensorUnit A))
    K hK

/- This is the functorial identification displayed in the first lemma of the
   source: derive over `R` and then tensor with `N`, or first derive base
   change to `A` and then tensor over `A`. -/
theorem derivedTensorObject_baseChange_associative
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (N : D A) (E : D R) :
    Nonempty ((derivedTensorObjectFunctor f N).obj E ≅
      (Unit59.derivedTensorFunctor N).obj
        ((derivedBaseChangeFunctor f).obj E)) := by
  sorry

/-! ## Restriction of scalars and functoriality -/

structure DerivedRestrictionData
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) where
  functor : D A ⥤ D R
  exact : Nonempty (ExactTriangulatedFunctorData functor)
  represented : ∀ (K : Comp A),
    Nonempty (functor.obj ((derivedQuotient A).obj K) ≅
      (derivedQuotient R).obj (restrictScalarsComplex f K))

theorem existsDerivedRestrictionData
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    Nonempty (DerivedRestrictionData f) := by
  sorry

noncomputable def derivedRestrictionData
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    DerivedRestrictionData f :=
  Classical.choice (existsDerivedRestrictionData f)

noncomputable abbrev derivedRestrictionFunctor
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) : D A ⥤ D R :=
  (derivedRestrictionData f).functor

theorem derivedRestriction_exact
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    Nonempty (ExactTriangulatedFunctorData (derivedRestrictionFunctor f)) :=
  (derivedRestrictionData f).exact

theorem derivedRestriction_on_complex
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K : Comp A) :
    Nonempty ((derivedRestrictionFunctor f).obj ((derivedQuotient A).obj K) ≅
      (derivedQuotient R).obj (restrictScalarsComplex f K)) :=
  (derivedRestrictionData f).represented K

/- A map of fixed target complexes induces the source's transformation of
   derived tensor functors.  The choice is made once and exposed as a real
   definition; the isomorphism assertion is recorded for quasi-isomorphisms. -/
theorem existsDerivedTensorTransformation
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    {L N : Comp A} (φ : L ⟶ N) :
    Nonempty (derivedTensorWithComplexFunctor f L ⟶
      derivedTensorWithComplexFunctor f N) := by
  sorry

noncomputable def derivedTensorTransformation
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    {L N : Comp A} (φ : L ⟶ N) :
    derivedTensorWithComplexFunctor f L ⟶
      derivedTensorWithComplexFunctor f N :=
  Classical.choice (existsDerivedTensorTransformation f φ)

theorem derivedTensorTransformation_isIso
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    {L N : Comp A} (φ : L ⟶ N) (hφ : QuasiIso φ) :
    IsIso (derivedTensorTransformation f φ) := by
  sorry

/- The source's warning compares two derived objects carrying different
   `A`-module structures.  Naming the two sides makes that distinction
   available to clients instead of hiding it in a proposition. -/
noncomputable def derivedTensorLeftSide
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (N N' : ModuleCat.{u} A) : D A :=
  (derivedTensorWithComplexFunctor f (moduleComplex A N')).obj
    ((derivedRestrictionFunctor f).obj (moduleStalk A N))

noncomputable def derivedTensorRightSide
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (N N' : ModuleCat.{u} A) : D A :=
  (derivedTensorWithComplexFunctor f (moduleComplex A N)).obj
    ((derivedRestrictionFunctor f).obj (moduleStalk A N'))

def DerivedTensorSideWarning
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (N N' : ModuleCat.{u} A) : Prop :=
  ¬ Nonempty (derivedTensorLeftSide f N N' ≅ derivedTensorRightSide f N N')

/- The polynomial example from the source.  The quotient `R/(x)` is made an
   `R/(xy)`-module through the evident quotient map, so this is a genuine
   instance of the preceding side-sensitive comparison. -/
abbrev polynomialExampleRing (k : Type u) [CommRing k] := Polynomial (Polynomial k)

noncomputable def polynomialExampleX (k : Type u) [CommRing k] :
    polynomialExampleRing k := Polynomial.C Polynomial.X

noncomputable def polynomialExampleY (k : Type u) [CommRing k] :
    polynomialExampleRing k := Polynomial.X

noncomputable def polynomialExampleXYIdeal (k : Type u) [CommRing k] :
    Ideal (polynomialExampleRing k) :=
  Ideal.span ({polynomialExampleX k * polynomialExampleY k} :
    Set (polynomialExampleRing k))

noncomputable def polynomialExampleXIdeal (k : Type u) [CommRing k] :
    Ideal (polynomialExampleRing k) :=
  Ideal.span ({polynomialExampleX k} : Set (polynomialExampleRing k))

abbrev polynomialExampleQuotient (k : Type u) [CommRing k] :=
  polynomialExampleRing k ⧸ polynomialExampleXYIdeal k

abbrev polynomialExampleModuleCarrier (k : Type u) [CommRing k] :=
  polynomialExampleRing k ⧸ polynomialExampleXIdeal k

theorem polynomialExampleXY_le_X (k : Type u) [CommRing k] :
    polynomialExampleXYIdeal k ≤ polynomialExampleXIdeal k := by
  apply Ideal.span_le.2
  intro z hz
  rcases Set.mem_singleton_iff.mp hz with rfl
  exact Ideal.mem_span_singleton'.2 ⟨polynomialExampleY k, by
    rw [mul_comm]⟩

noncomputable def polynomialExampleAction (k : Type u) [CommRing k] :
    polynomialExampleQuotient k →+* polynomialExampleModuleCarrier k :=
  Ideal.Quotient.factor (polynomialExampleXY_le_X k)

noncomputable def polynomialExampleMap (k : Type u) [CommRing k] :
    polynomialExampleRing k →+* polynomialExampleQuotient k :=
  Ideal.Quotient.mk _

noncomputable def polynomialExampleN (k : Type u) [CommRing k] :
    ModuleCat.{u} (polynomialExampleQuotient k) :=
  letI : Module (polynomialExampleQuotient k)
      (polynomialExampleModuleCarrier k) :=
    Module.compHom _ (polynomialExampleAction k)
  ModuleCat.of _ (polynomialExampleModuleCarrier k)

noncomputable def polynomialExampleN' (k : Type u) [CommRing k] :
    ModuleCat.{u} (polynomialExampleQuotient k) :=
  ModuleCat.of _ (polynomialExampleQuotient k)

theorem derivedTensorSideWarning_polynomial_example
    (k : Type u) [Field k]
    [HasDerivedCategory.{w} (ModuleCat.{u} (polynomialExampleRing k))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (polynomialExampleQuotient k))] :
    DerivedTensorSideWarning (R := polynomialExampleRing k)
      (A := polynomialExampleQuotient k) (polynomialExampleMap k)
      (polynomialExampleN k) (polynomialExampleN' k) := by
  sorry

/-! ## Tensor--restriction adjunction -/

theorem derivedBaseChange_leftAdjoint_restriction
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    Nonempty (derivedBaseChangeFunctor f ⊣ derivedRestrictionFunctor f) := by
  sorry

/-! ## Double base change -/

/- A target-derived object can serve as the fixed second factor in a
   cross-ring tensor functor.  This is the object-level form needed to state
   the source's associativity law without choosing additional resolutions. -/
noncomputable abbrev derivedTensorWithObjectFunctor
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (N : D A) : D R ⥤ D A :=
  derivedTensorObjectFunctor f N

theorem doubleBaseChange_functor_iso
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [HasDerivedCategory.{w} (ModuleCat.{u} C)]
    (f : A →+* B) (g : B →+* C) (N : Comp B) (K : Comp C) :
    Nonempty (
      (derivedTensorWithComplexFunctor f N ⋙
        derivedTensorWithComplexFunctor g K) ≅
      derivedTensorWithObjectFunctor (g.comp f)
        ((derivedTensorWithComplexFunctor g K).obj
        ((derivedQuotient B).obj N))) := by
  sorry

/- The second displayed comparison in the source is the signed interchange
   map: tensor first with `K`, then with `N` after base change to `C`. -/
theorem doubleBaseChange_signed_flip
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [HasDerivedCategory.{w} (ModuleCat.{u} C)]
    (f : A →+* B) (g : B →+* C) (N : Comp B) (K : Comp C)
    (E : D A) :
    Nonempty (
      ((derivedTensorWithComplexFunctor f N ⋙
          derivedTensorWithComplexFunctor g K).obj E) ≅
      (Unit59.derivedTensorFunctor
        ((derivedTensorWithComplexFunctor g (tensorUnit C)).obj
          ((derivedQuotient B).obj N))).obj
        ((derivedTensorWithComplexFunctor (g.comp f) K).obj E)) := by
  sorry

theorem doubleBaseChange_modules
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [HasDerivedCategory.{w} (ModuleCat.{u} C)]
    (f : A →+* B) (g : B →+* C)
    (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) (K : ModuleCat.{u} C) :
    Nonempty (
      ((derivedTensorWithComplexFunctor f (moduleComplex B N) ⋙
          derivedTensorWithComplexFunctor g (moduleComplex C K)).obj
        (moduleStalk A M)) ≅
      ((derivedTensorWithObjectFunctor (g.comp f)
          ((derivedTensorWithComplexFunctor g (moduleComplex C K)).obj
            ((derivedQuotient B).obj (moduleComplex B N)))).obj
        (moduleStalk A M))) := by
  sorry

/- The three-way module identity in the source is the objectwise form of the
   preceding functor isomorphism together with base change to `C`. -/
theorem doubleBaseChange_module_chain
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [HasDerivedCategory.{w} (ModuleCat.{u} C)]
    (f : A →+* B) (g : B →+* C)
    (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) (K : ModuleCat.{u} C) :
    let Ncomplex := moduleComplex B N
    let Kcomplex := moduleComplex C K
    let X :=
      (derivedTensorWithComplexFunctor g Kcomplex).obj
        ((derivedTensorWithComplexFunctor f Ncomplex).obj (moduleStalk A M))
    let Y :=
      (derivedTensorWithObjectFunctor (g.comp f)
        ((derivedTensorWithComplexFunctor g Kcomplex).obj
          ((derivedQuotient B).obj Ncomplex))).obj (moduleStalk A M)
    let Z :=
      (Unit59.derivedTensorFunctor
        ((derivedTensorWithComplexFunctor g Kcomplex).obj
          ((derivedQuotient B).obj Ncomplex))).obj
        ((derivedBaseChangeFunctor (g.comp f)).obj (moduleStalk A M))
    Nonempty (X ≅ Y) ∧ Nonempty (Y ≅ Z) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit60
