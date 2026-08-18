import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.Flat
import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit75.TorGroups
import Formalization.Books.MoreAlgebra.Unit60.DerivedBaseChange

/-!
# More on Algebra, Chapter 61: Tor independence

This file records the comparison-map, flat base-change, derived-cohomology,
and localization interfaces used in the source section.  The preceding
formalization provides the canonical resolution-based `Tor` construction and
the same-ring and cross-ring derived tensor functors.  The comparison
transformation and the canonical `A ⊗ R B`-action on `Tor` are kept as explicit
interfaces because the preceding APIs do not package those two constructions
in the source's form.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit75
open Formalization.Books.MoreAlgebra.Unit56
open Formalization.Books.MoreAlgebra.Unit60
open scoped TensorProduct

universe u w

namespace Formalization.Books.MoreAlgebra.Unit61

abbrev Derived (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :=
  Formalization.Books.MoreAlgebra.Unit56.D R

/-! ## Ring squares and the comparison map -/

/-- A commutative square of commutative rings.

The two maps from `R` to `A'` are recorded explicitly because the source
uses a square, rather than silently identifying one of them with an
`algebraMap`. -/
structure RingSquare (R A R' A' : Type u)
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] where
  rToA : R →+* A
  rToR' : R →+* R'
  aToA' : A →+* A'
  r'ToA' : R' →+* A'
  commutes : aToA'.comp rToA = r'ToA'.comp rToR'

/-- The canonical ring maps in the base-change square
`R → A`, `R → R'`, `A → A ⊗[R] R'`, `R' → A ⊗[R] R'`. -/
noncomputable def baseChangeRingSquare
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R →+* A) (g : R →+* R') :
    letI : Algebra R A := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    RingSquare R A R' (A ⊗[R] R') := by
  letI : Algebra R A := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  exact
    { rToA := f
      rToR' := g
      aToA' := Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g
      r'ToA' := Formalization.Books.Algebra.Unit14.baseChangeRingMap f g
      commutes := by
        ext x
        rw [← RingHom.algebraMap_toAlgebra f, ← RingHom.algebraMap_toAlgebra g]
        exact Algebra.TensorProduct.tmul_one_eq_one_tmul x }

/-- The tensor product ring in the base-change square, with the algebra
structures induced by the two displayed ring maps. -/
noncomputable abbrev baseChangeTensor
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R →+* A) (g : R →+* R') : Type u :=
  letI : Algebra R A := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  A ⊗[R] R'

/- The two ordinary base-change functors in the source's assertion that
   `- ⊗_R R'` and `- ⊗_A (A ⊗_R R')` agree as functors.  The `R`-based
   functor restricts an `A`-module to `R`, extends scalars to `R'`, and then
   uses the canonical `R'`-algebra structure on the tensor-product ring. -/
noncomputable abbrev ordinaryTensorOverA
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R →+* A) (g : R →+* R') :
    ModuleCat.{u} A ⥤ ModuleCat.{u} (baseChangeTensor f g) :=
  ModuleCat.extendScalars (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g)

noncomputable abbrev ordinaryTensorOverR
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R →+* A) (g : R →+* R') :
    ModuleCat.{u} A ⥤ ModuleCat.{u} (baseChangeTensor f g) :=
  ModuleCat.restrictScalars f ⋙ ModuleCat.extendScalars g ⋙
    ModuleCat.extendScalars (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)

/-- The derived base-change data attached to a ring square.

The natural transformation is the source's functorial comparison map
`K ⊗ᴸ_R R' ⟶ K ⊗ᴸ_A A'`, with both sides regarded as objects of `D(R')`.
The cross-ring derived scalar-change functors are the canonical functors from
Chapter 60; the comparison transformation is the remaining source-facing
interface. -/
structure DerivedRingSquare
    {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} A')] (S : RingSquare R A R' A') where
  comparison :
    (derivedRestrictionFunctor S.rToA ⋙ derivedBaseChangeFunctor S.rToR') ⟶
      (derivedBaseChangeFunctor S.aToA' ⋙ derivedRestrictionFunctor S.r'ToA')

/-- The functorial comparison transformation exists for every ring square. -/
theorem existsDerivedRingSquare
    {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    (S : RingSquare R A R' A') : Nonempty (DerivedRingSquare S) := by
  sorry

/-- A chosen source-facing comparison transformation for a ring square. -/
noncomputable def derivedRingSquare
    {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    (S : RingSquare R A R' A') : DerivedRingSquare S :=
  Classical.choice (existsDerivedRingSquare S)

/-- The comparison morphism at a derived object. -/
noncomputable def comparisonMap
    {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    {S : RingSquare R A R' A'} (D : DerivedRingSquare S) (K : Derived A) :
    ((derivedRestrictionFunctor S.rToA ⋙ derivedBaseChangeFunctor S.rToR').obj K ⟶
      (derivedBaseChangeFunctor S.aToA' ⋙ derivedRestrictionFunctor S.r'ToA').obj K) :=
  D.comparison.app K

/-- In the base-change case, ordinary tensoring over `R` and over `A` are
the same extension-of-scalars functor, up to the canonical isomorphism. -/
theorem ordinaryTensor_baseChange
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R →+* A) (g : R →+* R') (M : ModuleCat A) :
    letI : Algebra R A := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    Nonempty
      (((ModuleCat.extendScalars
          (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g)).obj M) ≅
        (ModuleCat.extendScalars
          (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)).obj
            ((ModuleCat.extendScalars g).obj
            ((ModuleCat.restrictScalars f).obj M))) := by
  sorry

/-- The pointwise base-change identifications assemble to the functor-level
isomorphism asserted in the source. -/
theorem ordinaryTensor_baseChange_functor_iso
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R →+* A) (g : R →+* R') :
    letI : Algebra R A := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    Nonempty (ordinaryTensorOverA f g ≅ ordinaryTensorOverR f g) := by
  sorry

/-! ## Tor independence -/

/-- `A` and `B` are Tor independent over the `R`-algebra structures. -/
def TorIndependent (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] : Prop :=
  ∀ p : ℕ, 0 < p → IsZero (Tor (ModuleCat.of R A) (ModuleCat.of R B) p)

/-- Tor independence with the two structure maps supplied explicitly. -/
def TorIndependentVia {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) : Prop :=
  letI : Algebra R A := f.toAlgebra
  letI : Algebra R B := g.toAlgebra
  TorIndependent R A B

/-- The vanishing condition in the definition, exposed for clients that
want to work directly with the canonical resolution-based Tor objects. -/
theorem torIndependent_iff
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    TorIndependent R A B ↔
      ∀ p : ℕ, 0 < p → IsZero (Tor (ModuleCat.of R A) (ModuleCat.of R B) p) := by
  rfl

/-- The polynomial quotient example from the source. -/
noncomputable abbrev polynomialAtZero (k : Type u) [Field k] : Type u :=
  Polynomial k ⧸ Ideal.span ({Polynomial.X} : Set (Polynomial k))

/-- The quotient map `k[x] → k[x]/(x)`. -/
noncomputable def polynomialAtZeroMap (k : Type u) [Field k] :
    Polynomial k →+* polynomialAtZero k :=
  Ideal.Quotient.mk _

/-- The source's example has nonzero positive Tor, so its comparison map is
not an isomorphism in general. -/
theorem polynomialAtZero_not_torIndependent
    (k : Type u) [Field k] :
    letI : Algebra (Polynomial k) (polynomialAtZero k) :=
      (polynomialAtZeroMap k).toAlgebra
    ¬ TorIndependent (Polynomial k) (polynomialAtZero k) (polynomialAtZero k) := by
  sorry

/-- If the base-change comparison is an isomorphism for every derived object,
then the Tor groups in the base-change square vanish in positive degrees. -/
theorem torIndependent_of_comparisonMap_isIso
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R →+* A) (g : R →+* R')
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} (baseChangeTensor f g))]
    (hComparison : ∀ K : Derived A,
      IsIso (comparisonMap (derivedRingSquare (baseChangeRingSquare f g)) K)) :
    TorIndependentVia f g := by
  sorry

/-- Under the base-change identification `A' = A ⊗[R] R'`, Tor independence
of `A` and `R'` makes the derived comparison map an isomorphism. -/
theorem comparisonMap_isIso_of_torIndependent
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R →+* A) (g : R →+* R')
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} (baseChangeTensor f g))]
    (hTor : TorIndependentVia f g)
    (K : Derived A) :
    IsIso (comparisonMap (derivedRingSquare (baseChangeRingSquare f g)) K) := by
  sorry

/-- The square used in the polynomial-quotient counterexample. -/
noncomputable def polynomialComparisonSquare (k : Type u) [Field k] :
    RingSquare (Polynomial k) (polynomialAtZero k)
      (polynomialAtZero k) (polynomialAtZero k) :=
  { rToA := polynomialAtZeroMap k
    rToR' := polynomialAtZeroMap k
    aToA' := RingHom.id _
    r'ToA' := RingHom.id _
    commutes := by
      ext x
      simp }

/-- The comparison map in the polynomial example is not an isomorphism. -/
theorem polynomialComparisonMap_not_isIso
    (k : Type u) [Field k]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Polynomial k))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (polynomialAtZero k))] :
    ¬ IsIso (comparisonMap (derivedRingSquare (polynomialComparisonSquare k))
      (moduleStalk (polynomialAtZero k)
        (ModuleCat.of (polynomialAtZero k) (polynomialAtZero k)))) := by
  sorry

/-! ## Flat base change for Tor -/

/-- The canonical map from the base ring to the tensor product of two
algebras. -/
def tensorBaseMap (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] : R →+* (A ⊗[R] B) :=
  (Algebra.TensorProduct.includeLeftRingHom : A →+* (A ⊗[R] B)).comp
    (algebraMap R A)

/-- A source-facing model for the canonical `A ⊗[R] B`-module structure on
`Tor_i^R(A, B)`.  The resolution-based Tor object from Chapter 75 supplies
the underlying `R`-module; the tensor-product action is the only missing
piece of that API. -/
structure TorTensorModule
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] where
  object : ℕ → ModuleCat (A ⊗[R] B)
  underlyingTor : ∀ i,
    Nonempty ((ModuleCat.restrictScalars (tensorBaseMap R A B)).obj (object i) ≅
      Tor (ModuleCat.of R A) (ModuleCat.of R B) i)

/-- Existence of the canonical tensor-product action on the Tor groups. -/
theorem existsTorTensorModule
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    Nonempty (TorTensorModule R A B) := by
  sorry

/-- A chosen model of all Tor groups carrying their canonical
`A ⊗[R] B`-module structures. -/
noncomputable def torTensorModule
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] : TorTensorModule R A B :=
  Classical.choice (existsTorTensorModule R A B)

/-- The source's flat-base-change diagram, with its tensor-product maps. -/
structure FlatBaseChangeSquare
    {R A B R' A' B' : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing R'] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R R']
    [Algebra R' A'] [Algebra R' B'] where
  aToA' : A →+* A'
  r'ToA' : R' →+* A'
  bToB' : B →+* B'
  r'ToB' : R' →+* B'
  aBase : A ⊗[R] R' →+* A'
  bBase : R' ⊗[R] B →+* B'
  baseMap : (A ⊗[R] B) →+* (A' ⊗[R'] B')
  commutesA : aToA'.comp (algebraMap R A) = r'ToA'.comp (algebraMap R R')
  commutesB : bToB'.comp (algebraMap R B) = r'ToB'.comp (algebraMap R R')
  aBase_left : aBase.comp
      (Algebra.TensorProduct.includeLeftRingHom : A →+* (A ⊗[R] R')) = aToA'
  aBase_right : aBase.comp
      (Algebra.TensorProduct.includeRight.toRingHom : R' →+* (A ⊗[R] R')) = r'ToA'
  bBase_left : bBase.comp
      (Algebra.TensorProduct.includeLeftRingHom : R' →+* (R' ⊗[R] B)) = r'ToB'
  bBase_right : bBase.comp
      (Algebra.TensorProduct.includeRight.toRingHom : B →+* (R' ⊗[R] B)) = bToB'
  baseMap_left : baseMap.comp
      (Algebra.TensorProduct.includeLeftRingHom : A →+* (A ⊗[R] B)) =
    (Algebra.TensorProduct.includeLeftRingHom : A' →+* (A' ⊗[R'] B')).comp aToA'
  baseMap_right : baseMap.comp
      (Algebra.TensorProduct.includeRight.toRingHom : B →+* (A ⊗[R] B)) =
    (Algebra.TensorProduct.includeRight.toRingHom : B' →+* (A' ⊗[R'] B')).comp bToB'

/-- The flat-base-change formula for the canonical tensor-module models of
the two Tor systems, over the compatible diagram `S`. -/
theorem tor_flat_baseChange
    {R A B R' A' B' : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing R'] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R R']
    [Algebra R' A'] [Algebra R' B']
    (S : FlatBaseChangeSquare (R := R) (A := A) (B := B)
      (R' := R') (A' := A') (B' := B'))
    (hR : RingHom.Flat (algebraMap R R'))
    (hA : RingHom.Flat S.aBase) (hB : RingHom.Flat S.bBase) (i : ℕ) :
    Nonempty ((ModuleCat.extendScalars S.baseMap).obj
      ((torTensorModule R A B).object i) ≅
      (torTensorModule R' A' B').object i) := by
  sorry

/-- Flat base change preserves Tor independence. -/
theorem torIndependent_flat_baseChange
    {R A B R' : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing R']
    (f : R →+* A) (h : R →+* B) (g : R →+* R')
    (hflat : RingHom.Flat g)
    (hTor : TorIndependentVia f h) :
    TorIndependentVia
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap h g) := by
  sorry

/-! ## Derived cohomology after flat base change -/

/-- The cohomology functor on the unbounded derived category of modules. -/
noncomputable abbrev derivedCohomologyFunctor
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (i : ℤ) :
    Derived R ⥤ ModuleCat.{u} R :=
  DerivedCategory.homologyFunctor (ModuleCat.{u} R) i

/-- The left derived tensor object in the source's flat-base-change formula. -/
noncomputable abbrev derivedCohomologyLeftObject
    {R A B R' A' B' : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing R'] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R R']
    [Algebra R' A'] [Algebra R' B']
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    [HasDerivedCategory.{w} (ModuleCat.{u} B')]
    (S : FlatBaseChangeSquare (R := R) (A := A) (B := B)
      (R' := R') (A' := A') (B' := B'))
    (M : Derived A) : Derived B' :=
  (derivedBaseChangeFunctor S.r'ToB').obj
    ((derivedRestrictionFunctor S.r'ToA').obj
      ((derivedBaseChangeFunctor S.aToA').obj M))

/-- The un-base-changed derived tensor object in the source's formula. -/
noncomputable abbrev derivedCohomologySourceObject
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)] (M : Derived A) : Derived B :=
  (derivedBaseChangeFunctor (algebraMap R B)).obj
    ((derivedRestrictionFunctor (algebraMap R A)).obj M)

/-- Models for the two cohomology modules in the source's comparison
identity.  The fields identify the models with the actual derived-category
cohomology objects and record that the right-hand model is scalar extension
of the original `A ⊗[R] B`-module. -/
structure DerivedCohomologyBaseChange
    {R A B R' A' B' : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing R'] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R R']
    [Algebra R' A'] [Algebra R' B']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    [HasDerivedCategory.{w} (ModuleCat.{u} B')]
    (S : FlatBaseChangeSquare (R := R) (A := A) (B := B)
      (R' := R') (A' := A') (B' := B')) where
  left : ℤ → Derived A ⥤ ModuleCat.{u} (A' ⊗[R'] B')
  source : ℤ → Derived A ⥤ ModuleCat.{u} (A ⊗[R] B)
  right : ℤ → Derived A ⥤ ModuleCat.{u} (A' ⊗[R'] B')
  left_underlying : ∀ (i : ℤ) (M : Derived A),
    Nonempty ((ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight.toRingHom : B' →+* (A' ⊗[R'] B'))).obj
      ((left i).obj M) ≅
      (derivedCohomologyFunctor i).obj (derivedCohomologyLeftObject S M))
  source_underlying : ∀ (i : ℤ) (M : Derived A),
    Nonempty ((ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight.toRingHom : B →+* (A ⊗[R] B))).obj
      ((source i).obj M) ≅
      (derivedCohomologyFunctor i).obj (derivedCohomologySourceObject M))
  right_baseChange : ∀ (i : ℤ) (M : Derived A),
    Nonempty ((ModuleCat.extendScalars S.baseMap).obj ((source i).obj M) ≅
      (right i).obj M)

/-- The source's cohomology isomorphism after flat base change. -/
theorem derivedCohomology_flat_baseChange
    {R A B R' A' B' : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing R'] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R R']
    [Algebra R' A'] [Algebra R' B']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    [HasDerivedCategory.{w} (ModuleCat.{u} B')]
    (S : FlatBaseChangeSquare (R := R) (A := A) (B := B)
      (R' := R') (A' := A') (B' := B'))
    (hR : RingHom.Flat (algebraMap R R'))
    (hA : RingHom.Flat S.aBase) (hB : RingHom.Flat S.bBase)
    (C : DerivedCohomologyBaseChange S) (i : ℤ) (M : Derived A) :
    Nonempty ((C.left i).obj M ≅ (C.right i).obj M) := by
  sorry

/-! ## Localization criterion -/

/-- A pair of primes of `A` and `B` lying over the same prime of `R`, with
the induced maps between the corresponding local rings made explicit. -/
structure LocalPrimePair
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] where
  p : PrimeSpectrum A
  q : PrimeSpectrum B
  r : PrimeSpectrum R
  pOver : PrimeSpectrum.comap (algebraMap R A) p = r
  qOver : PrimeSpectrum.comap (algebraMap R B) q = r

namespace LocalPrimePair

/-- The canonical local-ring map induced by `R → A` at a pair of primes over one another. -/
noncomputable def rToAp
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (P : LocalPrimePair R A B) :
    Localization.AtPrime P.r.asIdeal →+* Localization.AtPrime P.p.asIdeal :=
  let h : P.r.asIdeal = P.p.asIdeal.comap (algebraMap R A) := by
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal P.pOver).symm
  Localization.localRingHom P.r.asIdeal P.p.asIdeal (algebraMap R A) h

/-- The canonical local-ring map induced by `R → B` at a pair of primes over one another. -/
noncomputable def rToBq
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (P : LocalPrimePair R A B) :
    Localization.AtPrime P.r.asIdeal →+* Localization.AtPrime P.q.asIdeal :=
  let h : P.r.asIdeal = P.q.asIdeal.comap (algebraMap R B) := by
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal P.qOver).symm
  Localization.localRingHom P.r.asIdeal P.q.asIdeal (algebraMap R B) h

end LocalPrimePair

/-- The localized Tor-independence predicate for a local prime pair. -/
def LocalPrimePair.TorIndependent
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (P : LocalPrimePair R A B) : Prop :=
  TorIndependentVia P.rToAp P.rToBq

/-- A prime of `A ⊗[R] B`, together with its contractions and the local-ring
maps from `R_𝔯` to `A_𝔭` and `B_𝔮`. -/
structure TensorPrimePair
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] extends LocalPrimePair R A B where
  s : PrimeSpectrum (A ⊗[R] B)
  rContraction :
    PrimeSpectrum.comap (tensorBaseMap R A B) s =
      toLocalPrimePair.r
  pContraction :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeLeftRingHom : A →+* (A ⊗[R] B)) s =
      toLocalPrimePair.p
  qContraction :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight.toRingHom : B →+* (A ⊗[R] B)) s =
      toLocalPrimePair.q

namespace TensorPrimePair

noncomputable abbrev aToTensor
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (S : TensorPrimePair R A B) :
    A →+* (A ⊗[R] B) :=
  Algebra.TensorProduct.includeLeftRingHom

noncomputable abbrev bToTensor
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (S : TensorPrimePair R A B) :
    B →+* (A ⊗[R] B) :=
  Algebra.TensorProduct.includeRight.toRingHom

/-- The localization map from `A_𝔭` to the localization at `s`. -/
noncomputable def pToS
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (S : TensorPrimePair R A B) :
    Localization.AtPrime S.p.asIdeal →+* Localization.AtPrime S.s.asIdeal :=
  let h : S.p.asIdeal = S.s.asIdeal.comap S.aToTensor := by
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal S.pContraction).symm
  Localization.localRingHom S.p.asIdeal S.s.asIdeal S.aToTensor h

/-- The localization map from `B_𝔮` to the localization at `s`. -/
noncomputable def qToS
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (S : TensorPrimePair R A B) :
    Localization.AtPrime S.q.asIdeal →+* Localization.AtPrime S.s.asIdeal :=
  let h : S.q.asIdeal = S.s.asIdeal.comap S.bToTensor := by
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal S.qContraction).symm
  Localization.localRingHom S.q.asIdeal S.s.asIdeal S.bToTensor h

end TensorPrimePair

/-- A chosen tensor-module model for the local Tor groups.  It reuses the
same canonical action interface after specializing the rings to the local
maps `R_𝔯 → A_𝔭` and `R_𝔯 → B_𝔮`. -/
noncomputable def localTorTensorModule
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (S : TensorPrimePair R A B) :
    letI : Algebra (Localization.AtPrime S.r.asIdeal)
        (Localization.AtPrime S.p.asIdeal) := S.toLocalPrimePair.rToAp.toAlgebra
    letI : Algebra (Localization.AtPrime S.r.asIdeal)
        (Localization.AtPrime S.q.asIdeal) := S.toLocalPrimePair.rToBq.toAlgebra
    TorTensorModule (Localization.AtPrime S.r.asIdeal)
      (Localization.AtPrime S.p.asIdeal) (Localization.AtPrime S.q.asIdeal) := by
  letI : Algebra (Localization.AtPrime S.r.asIdeal)
      (Localization.AtPrime S.p.asIdeal) := S.toLocalPrimePair.rToAp.toAlgebra
  letI : Algebra (Localization.AtPrime S.r.asIdeal)
      (Localization.AtPrime S.q.asIdeal) := S.toLocalPrimePair.rToBq.toAlgebra
  exact torTensorModule _ _ _

/-- The global Tor group localized at the prime `s` of `A ⊗[R] B`. -/
noncomputable def localizedGlobalTor
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (T : TorTensorModule R A B)
    (S : TensorPrimePair R A B) (i : ℕ) :
    ModuleCat (Localization.AtPrime S.s.asIdeal) :=
  (ModuleCat.extendScalars
      (algebraMap (A ⊗[R] B) (Localization.AtPrime S.s.asIdeal))).obj
    (T.object i)

/-- A chosen map from the tensor product of the localized rings to the
localization at `s`.  The existence and compatibility of this map are part
of the source-facing localization interface. -/
structure LocalTensorMap
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (S : TensorPrimePair R A B) where
  map :
    letI : Algebra (Localization.AtPrime S.r.asIdeal)
        (Localization.AtPrime S.p.asIdeal) := S.toLocalPrimePair.rToAp.toAlgebra
    letI : Algebra (Localization.AtPrime S.r.asIdeal)
        (Localization.AtPrime S.q.asIdeal) := S.toLocalPrimePair.rToBq.toAlgebra
    (Localization.AtPrime S.p.asIdeal ⊗[Localization.AtPrime S.r.asIdeal]
      Localization.AtPrime S.q.asIdeal) →+* Localization.AtPrime S.s.asIdeal
  map_left :
    letI : Algebra (Localization.AtPrime S.r.asIdeal)
        (Localization.AtPrime S.p.asIdeal) := S.toLocalPrimePair.rToAp.toAlgebra
    letI : Algebra (Localization.AtPrime S.r.asIdeal)
        (Localization.AtPrime S.q.asIdeal) := S.toLocalPrimePair.rToBq.toAlgebra
    map.comp (Algebra.TensorProduct.includeLeftRingHom :
      Localization.AtPrime S.p.asIdeal →+*
        (Localization.AtPrime S.p.asIdeal ⊗[Localization.AtPrime S.r.asIdeal]
          Localization.AtPrime S.q.asIdeal)) = S.pToS
  map_right :
    letI : Algebra (Localization.AtPrime S.r.asIdeal)
        (Localization.AtPrime S.p.asIdeal) := S.toLocalPrimePair.rToAp.toAlgebra
    letI : Algebra (Localization.AtPrime S.r.asIdeal)
        (Localization.AtPrime S.q.asIdeal) := S.toLocalPrimePair.rToBq.toAlgebra
    map.comp (Algebra.TensorProduct.includeRight.toRingHom :
      Localization.AtPrime S.q.asIdeal →+*
        (Localization.AtPrime S.p.asIdeal ⊗[Localization.AtPrime S.r.asIdeal]
          Localization.AtPrime S.q.asIdeal)) = S.qToS

/-- The localized Tor group over `R_𝔯`, then localized at `s`. -/
noncomputable def localizedLocalTor
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (S : TensorPrimePair R A B)
    (L : LocalTensorMap S) (i : ℕ) :
    ModuleCat (Localization.AtPrime S.s.asIdeal) := by
  letI : Algebra (Localization.AtPrime S.r.asIdeal)
      (Localization.AtPrime S.p.asIdeal) := S.toLocalPrimePair.rToAp.toAlgebra
  letI : Algebra (Localization.AtPrime S.r.asIdeal)
      (Localization.AtPrime S.q.asIdeal) := S.toLocalPrimePair.rToBq.toAlgebra
  exact (ModuleCat.extendScalars L.map).obj ((localTorTensorModule S).object i)

/-- The localized comparison identity from the source.  Both sides are now
the actual localized Tor constructions; only the canonical map between the
two localization rings remains an explicit interface. -/
structure LocalizedTorIdentity
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (S : TensorPrimePair R A B) where
  localTensor : LocalTensorMap S
  comparison : ∀ i, Nonempty (localizedGlobalTor (torTensorModule R A B) S i ≅
    localizedLocalTor S localTensor i)

/-- Tor independence is equivalent to Tor independence after localization at
corresponding primes. -/
theorem torIndependent_iff_localPrimePairs
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    TorIndependent R A B ↔
      ∀ P : LocalPrimePair R A B, P.TorIndependent := by
  sorry

/-- The prime-localized Tor identity used in the third formulation of the
source lemma. -/
theorem tor_localization_identity
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (S : TensorPrimePair R A B) :
    Nonempty (LocalizedTorIdentity S) := by
  sorry

/-- The localized comparison isomorphism supplied by the prime-localization
identity. -/
theorem localizedTor_comparison
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (S : TensorPrimePair R A B)
    (D : LocalizedTorIdentity S) (i : ℕ) :
    Nonempty (localizedGlobalTor (torTensorModule R A B) S i ≅
      localizedLocalTor S D.localTensor i) := by
  exact D.comparison i

/-- Vanishing is invariant under the localized comparison isomorphism. -/
theorem localizedTor_isZero_iff
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (S : TensorPrimePair R A B)
    (D : LocalizedTorIdentity S) (i : ℕ) :
    IsZero (localizedGlobalTor (torTensorModule R A B) S i) ↔
      IsZero (localizedLocalTor S D.localTensor i) := by
  sorry

/-- A chosen localized Tor object supplied by the localization identity. -/
noncomputable def localizedTor
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (S : TensorPrimePair R A B) (i : ℕ) :
    ModuleCat (Localization.AtPrime S.s.asIdeal) :=
  localizedGlobalTor (torTensorModule R A B) S i

/-- Vanishing of all positive-degree prime-localized Tor modules is equivalent
to Tor independence. -/
theorem torIndependent_iff_localizedTor_vanishing
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    TorIndependent R A B ↔
      ∀ S : TensorPrimePair R A B, ∀ i : ℕ,
        0 < i → IsZero (localizedTor S i) := by
  sorry

/-- The second and third localization formulations in the source are
equivalent; the comparison identity is supplied by
`tor_localization_identity`. -/
theorem localPrimePairs_iff_localizedTor_vanishing
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    (∀ P : LocalPrimePair R A B, P.TorIndependent) ↔
      ∀ S : TensorPrimePair R A B, ∀ i : ℕ,
        0 < i → IsZero (localizedTor S i) := by
  constructor
  · intro h
    exact torIndependent_iff_localizedTor_vanishing.mp
      (torIndependent_iff_localPrimePairs.mpr h)
  · intro h
    exact torIndependent_iff_localPrimePairs.mp
      (torIndependent_iff_localizedTor_vanishing.mpr h)

end Formalization.Books.MoreAlgebra.Unit61
