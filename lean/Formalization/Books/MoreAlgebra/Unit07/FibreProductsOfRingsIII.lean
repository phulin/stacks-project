import Formalization.Books.MoreAlgebra.Unit06.FibreProductsOfRingsII
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# More on Algebra, Chapter 7: Fibre products of rings, III

This file records the relative base-change situation from the source.  The
ring squares and module functors use the canonical tensor-product and module
gluing constructions from the preceding fibre-product chapters.
-/

namespace Formalization.Books.MoreAlgebra.Unit07

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.MoreAlgebra.Unit05
open Formalization.Books.MoreAlgebra.Unit06
open scoped TensorProduct

universe u

noncomputable section

/-! ## The relative fibre-product situation -/

/-- A map out of the fibre-product ring in the preceding situation. -/
structure RelativeFibreProductSituation
    (A A' B D' : Type u)
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D'] where
  /-- The base fibre-product situation `B → A ← A'`. -/
  base : FibreProductSituation A A' B
  /-- The map `B' → D'`. -/
  toD' : fibreProductRing base →+* D'

/-- The base ring `B'` in a relative fibre-product situation. -/
abbrev relativeFibreProductRing
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') : Type u :=
  fibreProductRing S.base

/-- The map `B' → A` obtained from the lower-left projection. -/
def relativeBaseToA
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    relativeFibreProductRing S →+* A :=
  S.base.toA.comp (fibreProductToB S.base)

/-- The two descriptions of the map `B' → A` agree. -/
theorem relativeBaseToA_eq_via_A'
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    relativeBaseToA S = S.base.fromA'.comp (fibreProductToA' S.base) := by
  ext x
  exact RingSquare.comm_apply (fibreProductRingSquare S.base) x

/-- The ring `D = D' ⊗_{B'} B`. -/
abbrev relativeD
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') : Type u :=
  letI : Algebra (relativeFibreProductRing S) D' := S.toD'.toAlgebra
  letI : Algebra (relativeFibreProductRing S) B :=
    (fibreProductToB S.base).toAlgebra
  D' ⊗[relativeFibreProductRing S] B

/-- The ring `C' = D' ⊗_{B'} A'`. -/
abbrev relativeC'
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') : Type u :=
  letI : Algebra (relativeFibreProductRing S) D' := S.toD'.toAlgebra
  letI : Algebra (relativeFibreProductRing S) A' :=
    (fibreProductToA' S.base).toAlgebra
  D' ⊗[relativeFibreProductRing S] A'

/-- The ring `C = D' ⊗_{B'} A`. -/
abbrev relativeC
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') : Type u :=
  letI : Algebra (relativeFibreProductRing S) D' := S.toD'.toAlgebra
  letI : Algebra (relativeFibreProductRing S) A :=
    (relativeBaseToA S).toAlgebra
  D' ⊗[relativeFibreProductRing S] A

/-- The canonical map `D' → D`. -/
def relativeD'ToD
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    D' →+* relativeD S := by
  letI : Algebra (relativeFibreProductRing S) D' := S.toD'.toAlgebra
  letI : Algebra (relativeFibreProductRing S) B :=
    (fibreProductToB S.base).toAlgebra
  exact Algebra.TensorProduct.includeLeftRingHom

/-- The canonical map `B → D`. -/
def relativeBToD
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    B →+* relativeD S := by
  letI : Algebra (relativeFibreProductRing S) D' := S.toD'.toAlgebra
  letI : Algebra (relativeFibreProductRing S) B :=
    (fibreProductToB S.base).toAlgebra
  exact Algebra.TensorProduct.includeRight.toRingHom

/-- The canonical map `D' → C'`. -/
def relativeD'ToC'
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    D' →+* relativeC' S := by
  letI : Algebra (relativeFibreProductRing S) D' := S.toD'.toAlgebra
  letI : Algebra (relativeFibreProductRing S) A' :=
    (fibreProductToA' S.base).toAlgebra
  exact Algebra.TensorProduct.includeLeftRingHom

/-- The canonical map `A' → C'`. -/
def relativeA'ToC'
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    A' →+* relativeC' S := by
  letI : Algebra (relativeFibreProductRing S) D' := S.toD'.toAlgebra
  letI : Algebra (relativeFibreProductRing S) A' :=
    (fibreProductToA' S.base).toAlgebra
  exact Algebra.TensorProduct.includeRight.toRingHom

/-- The canonical map `D' → C`. -/
def relativeD'ToC
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    D' →+* relativeC S := by
  letI : Algebra (relativeFibreProductRing S) D' := S.toD'.toAlgebra
  letI : Algebra (relativeFibreProductRing S) A :=
    (relativeBaseToA S).toAlgebra
  exact Algebra.TensorProduct.includeLeftRingHom

/-- The canonical map `D → C`. -/
def relativeDToC
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    relativeD S →+* relativeC S := by
  letI : Algebra (relativeFibreProductRing S) D' := S.toD'.toAlgebra
  letI : Algebra (relativeFibreProductRing S) B :=
    (fibreProductToB S.base).toAlgebra
  letI : Algebra (relativeFibreProductRing S) A :=
    (relativeBaseToA S).toAlgebra
  exact Algebra.TensorProduct.mapRingHom
    (RingHom.id (relativeFibreProductRing S)) (RingHom.id D') S.base.toA
    (by ext; simp)
    (by
      ext x
      change S.base.toA (fibreProductToB S.base x) = relativeBaseToA S x
      rfl)

/-- The canonical map `A → C`. -/
def relativeAToC
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    A →+* relativeC S := by
  letI : Algebra (relativeFibreProductRing S) D' := S.toD'.toAlgebra
  letI : Algebra (relativeFibreProductRing S) A :=
    (relativeBaseToA S).toAlgebra
  exact Algebra.TensorProduct.includeRight.toRingHom

/-- The base-change map `C' → C`. -/
def relativeC'ToC
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    relativeC' S →+* relativeC S := by
  letI : Algebra (relativeFibreProductRing S) D' := S.toD'.toAlgebra
  letI : Algebra (relativeFibreProductRing S) A' :=
    (fibreProductToA' S.base).toAlgebra
  letI : Algebra (relativeFibreProductRing S) A :=
    (relativeBaseToA S).toAlgebra
  exact Algebra.TensorProduct.mapRingHom
    (RingHom.id (relativeFibreProductRing S)) (RingHom.id D') S.base.fromA'
    (by ext; simp)
    (by
      ext x
      change S.base.fromA' (fibreProductToA' S.base x) = relativeBaseToA S x
      exact (RingSquare.comm_apply (fibreProductRingSquare S.base) x).symm)

/-- The relative commutative square of rings. -/
def relativeRingSquare
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    RingSquare (relativeC S) (relativeC' S) (relativeD S) D' where
  t := relativeC'ToC S
  s := relativeDToC S
  u := relativeD'ToD S
  v := relativeD'ToC' S
  comm := by
    have hD :
        (relativeDToC S).comp (relativeD'ToD S) = relativeD'ToC S := by
      ext x
      simp [relativeDToC, relativeD'ToD, relativeD'ToC]
    have hC' :
        (relativeC'ToC S).comp (relativeD'ToC' S) = relativeD'ToC S := by
      ext x
      simp [relativeC'ToC, relativeD'ToC', relativeD'ToC]
    exact hD.trans hC'.symm

/- The displayed large diagram has four nontrivial squares.  The central
  square is already packaged by `relativeRingSquare`; this theorem records
  the remaining diagram identities at the level of ring homomorphisms. -/
theorem relative_big_diagram_commutes
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    ((relativeD'ToD S).comp S.toD' =
        (relativeBToD S).comp (fibreProductToB S.base)) ∧
      ((relativeD'ToC' S).comp S.toD' =
        (relativeA'ToC' S).comp (fibreProductToA' S.base)) ∧
      ((relativeC'ToC S).comp (relativeA'ToC' S) =
        (relativeAToC S).comp S.base.fromA') ∧
      (relativeBaseToA S =
        S.base.fromA'.comp (fibreProductToA' S.base)) := by
  sorry

/-- The canonical map from `D'` to the pullback of its two base changes. -/
def relativeD'ToBaseChangePullback
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
  D' →+* RingHom.pullback (relativeDToC S) (relativeC'ToC S) :=
  { toFun := fun x =>
      ⟨(relativeD'ToD S x, relativeD'ToC' S x),
        RingSquare.comm_apply (relativeRingSquare S) x⟩
    map_one' := by ext <;> simp
    map_mul' := by intro x y; ext <;> simp
    map_zero' := by ext <;> simp
    map_add' := by intro x y; ext <;> simp }

/-- The map in the source's footnote is surjective, although it is not assumed
to be an isomorphism. -/
theorem relativeD'ToBaseChangePullback_surjective
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    Function.Surjective (relativeD'ToBaseChangePullback S) := by
  sorry

/-- The relative module gluing category attached to the new ring square. -/
abbrev relativeModuleGluingCategory
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :=
  ModuleGluingCategory (relativeRingSquare S)

/-- The source's relative functor
`Mod(D') → Mod(D) ×_{Mod(C)} Mod(C')`. -/
noncomputable def relativeModuleFunctor
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    ModuleCat.{u} D' ⥤ relativeModuleGluingCategory S :=
  moduleBaseChangeFunctor (relativeRingSquare S)

/-- The `D`-module component of the source's relative base-change functor. -/
abbrev relativeModuleLeftBaseChange
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (L' : ModuleCat.{u} D') : ModuleCat.{u} (relativeD S) :=
  moduleGluingLeftObj (D := relativeRingSquare S)
    (X := (relativeModuleFunctor S).obj L')

/-- The `C'`-module component of the source's relative base-change functor. -/
abbrev relativeModuleRightBaseChange
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (L' : ModuleCat.{u} D') : ModuleCat.{u} (relativeC' S) :=
  moduleGluingRightObj (D := relativeRingSquare S)
    (X := (relativeModuleFunctor S).obj L')

/-- The comparison isomorphism in the source's object notation
`(N, M', φ)`. -/
abbrev relativeModuleComparison
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (L' : ModuleCat.{u} D') :
    (ModuleCat.extendScalars (relativeDToC S)).obj
        (relativeModuleLeftBaseChange S L') ⟶
      (ModuleCat.extendScalars (relativeC'ToC S)).obj
        (relativeModuleRightBaseChange S L') :=
  moduleGluingComparison (D := relativeRingSquare S)
    ((relativeModuleFunctor S).obj L')

/-- The compatible-pair presentation of the object produced by the relative
base-change functor. -/
abbrev relativeModuleCompatiblePairs
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (L' : ModuleCat.{u} D') :=
  moduleFiberCompatiblePairs (relativeRingSquare S)
    ((relativeModuleFunctor S).obj L')

/-- The compatible-pair fibre product `N ×_{M'/IM'} M'` in the source's
right-adjoint description. -/
noncomputable abbrev relativeModuleFiberProduct
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (X : relativeModuleGluingCategory S) : ModuleCat.{u} D' :=
  moduleFiberProduct (relativeRingSquare S) X

/-- The compatible-pair right adjoint for the relative module functor. -/
noncomputable abbrev relativeModuleRightAdjoint
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    relativeModuleGluingCategory S ⥤ ModuleCat.{u} D' :=
  moduleFiberProductRightAdjointCanonical (relativeRingSquare S)

/-- The right-adjoint structure of the relative module functor. -/
noncomputable def relativeModuleAdjunction
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    relativeModuleFunctor S ⊣ relativeModuleRightAdjoint S :=
  (moduleFiberProductAdjunctionData (relativeRingSquare S)).adjunction

/-- The source's identification of a relative compatible-pair module with
the two modules recovered by base change. -/
theorem relativeModule_composition_isIdentity
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    Nonempty
      (relativeModuleRightAdjoint S ⋙ relativeModuleFunctor S ≅
        𝟭 (relativeModuleGluingCategory S)) := by
  sorry

/-- A chosen natural isomorphism for the relative module recovery statement. -/
noncomputable def relativeModule_composition_iso
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    relativeModuleRightAdjoint S ⋙ relativeModuleFunctor S ≅
      𝟭 (relativeModuleGluingCategory S) :=
  Classical.choice (relativeModule_composition_isIdentity S)

/-- The two componentwise base-change isomorphisms in the relative module
lemma. -/
theorem relativeModule_recovery_exists
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (X : relativeModuleGluingCategory S) :
    Nonempty
      (((ModuleCat.extendScalars (relativeD'ToD S)).obj
          ((relativeModuleRightAdjoint S).obj X) ≅
        moduleGluingLeftObj (D := relativeRingSquare S) (X := X)) ×
        ((ModuleCat.extendScalars (relativeD'ToC' S)).obj
          ((relativeModuleRightAdjoint S).obj X) ≅
        moduleGluingRightObj (D := relativeRingSquare S) (X := X))) := by
  sorry

/-- A chosen pair of componentwise recovery isomorphisms. -/
noncomputable def relativeModule_recovery
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (X : relativeModuleGluingCategory S) :
    (((ModuleCat.extendScalars (relativeD'ToD S)).obj
        ((relativeModuleRightAdjoint S).obj X) ≅
      moduleGluingLeftObj (D := relativeRingSquare S) (X := X)) ×
      ((ModuleCat.extendScalars (relativeD'ToC' S)).obj
        ((relativeModuleRightAdjoint S).obj X) ≅
      moduleGluingRightObj (D := relativeRingSquare S) (X := X))) :=
  Classical.choice (relativeModule_recovery_exists S X)

/-! ## Relative module properties -/

/-- The ideal `J = ker(B' → B)` in the relative situation. -/
abbrev relativeIdealJ
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    Ideal (relativeFibreProductRing S) :=
  RingHom.ker (fibreProductToB S.base)

/-- The extension `JD'` of `J` to `D'`. -/
abbrev relativeIdealJD'
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') : Ideal D' :=
  Ideal.map S.toD' (relativeIdealJ S)

/-- The extension `IC'` of the kernel ideal `I` to `C'`. -/
abbrev relativeIdealIC'
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') : Ideal (relativeC' S) :=
  Ideal.map (relativeA'ToC' S) (fibreProductIdeal S.base)

/-- The reduction `M'/IC'M'` used in the source's alternative description of
the gluing map. -/
abbrev relativeModuleReduction
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    {M' : Type u} [AddCommGroup M'] [Module (relativeC' S) M'] : Type u :=
  M' ⧸ (relativeIdealIC' S • (⊤ : Submodule (relativeC' S) M'))

/-- The map `JD' → IC'` is surjective, expressed as equality of image ideals. -/
theorem relative_surjection_ideals
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    Ideal.map (relativeD'ToC' S) (relativeIdealJD' S) =
      relativeIdealIC' S := by
  sorry

/-- The `B`-module obtained from the left component of a relative triple. -/
abbrev relativeLeftModuleOverB
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (X : relativeModuleGluingCategory S) : ModuleCat.{u} B :=
  (ModuleCat.restrictScalars (relativeBToD S)).obj
    (moduleGluingLeftObj (D := relativeRingSquare S) (X := X))

/-- The `A'`-module obtained from the right component of a relative triple. -/
abbrev relativeRightModuleOverA'
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (X : relativeModuleGluingCategory S) : ModuleCat.{u} A' :=
  (ModuleCat.restrictScalars (relativeA'ToC' S)).obj
    (moduleGluingRightObj (D := relativeRingSquare S) (X := X))

/-- Finite compatible-pair modules in the relative situation are finite over
`D'`. -/
theorem relative_finite_module
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (X : relativeModuleGluingCategory S)
    [Module.Finite (relativeD S)
      (moduleGluingLeftObj (D := relativeRingSquare S) (X := X) : Type u)]
    [Module.Finite (relativeC' S)
      (moduleGluingRightObj (D := relativeRingSquare S) (X := X) : Type u)] :
    Module.Finite D' ((relativeModuleRightAdjoint S).obj X : Type u) := by
  sorry

/-- The property of a relative triple whose two displayed components are flat
over `B` and `A'`, respectively. -/
def relativeFlatGluingProperty
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    ObjectProperty (relativeModuleGluingCategory S) :=
  fun X =>
    Module.Flat B (relativeLeftModuleOverB S X : Type u) ∧
      Module.Flat A' (relativeRightModuleOverA' S X : Type u)

/-- The full subcategory of flat relative module triples. -/
abbrev relativeFlatGluingCategory
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :=
  ObjectProperty.FullSubcategory (relativeFlatGluingProperty S)

/-- The property of a `D'`-module that is flat over `B'`. -/
def relativeFlatModuleProperty
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    ObjectProperty (ModuleCat.{u} D') :=
  fun L' =>
    Module.Flat (relativeFibreProductRing S)
      ((ModuleCat.restrictScalars S.toD').obj L' : Type u)

/-- The category of relative `D'`-modules flat over `B'`. -/
abbrev relativeFlatModuleCategory
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :=
  ObjectProperty.FullSubcategory (relativeFlatModuleProperty S)

/-- A flat relative compatible-pair module is flat over `B'`. -/
theorem relative_flat_module
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (X : relativeModuleGluingCategory S)
    (hX : relativeFlatGluingProperty S X) :
    Module.Flat (relativeFibreProductRing S)
      ((ModuleCat.restrictScalars S.toD').obj
        ((relativeModuleRightAdjoint S).obj X) : Type u) := by
  sorry

/-- The adjunction unit is an isomorphism for a `D'`-module flat over `B'`. -/
theorem relative_flat_module_recovery
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (L' : ModuleCat.{u} D')
    (hL' : relativeFlatModuleProperty S L') :
    IsIso ((relativeModuleAdjunction S).unit.app L') := by
  sorry

/-- A chosen isomorphism expressing recovery of a flat relative module. -/
noncomputable def relative_flat_module_recoveryIso
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (L' : ModuleCat.{u} D')
    (hL' : relativeFlatModuleProperty S L') :
    L' ≅ (relativeModuleRightAdjoint S).obj ((relativeModuleFunctor S).obj L') := by
  letI := relative_flat_module_recovery S L' hL'
  exact asIso ((relativeModuleAdjunction S).unit.app L')

/-- Flat `D'`-modules over `B'` are equivalent to flat relative triples. -/
theorem relative_flat_module_equivalence_exists
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    Nonempty (relativeFlatModuleCategory S ≌ relativeFlatGluingCategory S) := by
  sorry

/-- A chosen equivalence between the two flat relative module categories. -/
noncomputable def relative_flat_module_equivalence
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D') :
    relativeFlatModuleCategory S ≌ relativeFlatGluingCategory S :=
  Classical.choice (relative_flat_module_equivalence_exists S)

/-! ## Relative finite presentation -/

/-- The finitely-presented relative module assertion. -/
theorem relative_finitelyPresented_module
    {A A' B D' D'' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D'] [CommRing D'']
    (S : RelativeFibreProductSituation A A' B D')
    (X : relativeModuleGluingCategory S)
    (toD'' : relativeFibreProductRing S →+* D'')
    (fromD'' : D'' →+* D')
    (hfactor : fromD''.comp toD'' = S.toD')
    (hflat : RingHom.Flat toD'')
    (hfp : RingHom.FinitePresentation fromD'')
    (hNfp : Module.FinitePresentation (relativeD S)
      (moduleGluingLeftObj (D := relativeRingSquare S) (X := X) : Type u))
    (hNflat : Module.Flat B (relativeLeftModuleOverB S X : Type u))
    (hMfp : Module.FinitePresentation (relativeC' S)
      (moduleGluingRightObj (D := relativeRingSquare S) (X := X) : Type u))
    (hMflat : Module.Flat A' (relativeRightModuleOverA' S X : Type u)) :
    Module.FinitePresentation D' ((relativeModuleRightAdjoint S).obj X : Type u) := by
  sorry

/-! ## Properties of algebras over the fibre product -/

/-- The quotient `C'/IC'` appearing in a system of algebras. -/
abbrev relativeAlgebraSystemQuotient
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    (base : FibreProductSituation A A' B)
    (C' : CommAlgCat.{u} A') : Type u :=
  (C' : Type u) ⧸ Ideal.map (algebraMap A' C') (fibreProductIdeal base)

/-- The tensor product `D ⊗_B A` in a system of algebras. -/
abbrev relativeAlgebraSystemTensor
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    (base : FibreProductSituation A A' B)
    (D : CommAlgCat.{u} B) : Type u :=
  letI : Algebra B A := base.toA.toAlgebra
  D ⊗[B] A

/-- The data `φ : D ⊗_B A ≅ C'/IC'` in a system of algebras. -/
structure RelativeAlgebraSystemData
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    (base : FibreProductSituation A A' B)
    (D : CommAlgCat.{u} B) (C' : CommAlgCat.{u} A') where
  /-- The displayed tensor-product isomorphism. -/
  phi : relativeAlgebraSystemTensor base D ≃+* relativeAlgebraSystemQuotient base C'
  /-- Compatibility of the isomorphism with the two maps into `C'/IC'`. -/
  compatible :
    letI : Algebra B A := base.toA.toAlgebra
    ∀ b : B, ∀ a' : A',
      base.toA b = base.fromA' a' →
      phi (Algebra.TensorProduct.includeLeftRingHom (algebraMap B D b)) =
        Ideal.Quotient.mk (Ideal.map (algebraMap A' C') (fibreProductIdeal base))
          (algebraMap A' C' a')

/-- A system `(D, C', φ)` from the algebra-properties lemma. -/
structure RelativeAlgebraSystem
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    (base : FibreProductSituation A A' B) where
  /-- The `B`-algebra `D`. -/
  D : CommAlgCat.{u} B
  /-- The `A'`-algebra `C'`. -/
  C' : CommAlgCat.{u} A'
  /-- The tensor-product and quotient identification. -/
  data : RelativeAlgebraSystemData base D C'

/-- The map `C' → C'/IC'`. -/
def relativeAlgebraSystemC'ToC
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    {base : FibreProductSituation A A' B}
    (X : RelativeAlgebraSystem base) :
    (X.C' : Type u) →+* relativeAlgebraSystemQuotient base X.C' :=
  Ideal.Quotient.mk (Ideal.map (algebraMap A' X.C') (fibreProductIdeal base))

/-- The map `D → C` obtained from `φ` and `D → D ⊗_B A`. -/
def relativeAlgebraSystemDToC
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    {base : FibreProductSituation A A' B}
    (X : RelativeAlgebraSystem base) :
    (X.D : Type u) →+* relativeAlgebraSystemQuotient base X.C' := by
  letI : Algebra B A := base.toA.toAlgebra
  exact X.data.phi.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom

/-- The pullback ring `D' = D ×_C C'` of a system of algebras. -/
abbrev relativeAlgebraSystemDPrime
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    {base : FibreProductSituation A A' B}
    (X : RelativeAlgebraSystem base) : Type u :=
  RingHom.pullback (relativeAlgebraSystemDToC X) (relativeAlgebraSystemC'ToC X)

/-- The map `B' → D'` attached to a system of algebras. -/
def relativeAlgebraSystemToDPrime
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    {base : FibreProductSituation A A' B}
    (X : RelativeAlgebraSystem base) :
    fibreProductRing base →+* relativeAlgebraSystemDPrime X :=
  { toFun := fun x =>
      ⟨(algebraMap B X.D (fibreProductToB base x),
        algebraMap A' X.C' (fibreProductToA' base x)),
        X.data.compatible _ _ (RingSquare.comm_apply (fibreProductRingSquare base) x)⟩
    map_one' := by ext <;> simp
    map_mul' := by intro x y; ext <;> simp
    map_zero' := by ext <;> simp
    map_add' := by intro x y; ext <;> simp }

/-- Finite type, flatness, finite presentation, smoothness, and étaleness are
preserved and detected by the relative fibre-product algebra construction. -/
theorem relative_properties_algebras_over_fibre_product
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    (base : FibreProductSituation A A' B)
    (X : RelativeAlgebraSystem base) :
    (RingHom.FiniteType (relativeAlgebraSystemToDPrime X) ↔
        RingHom.FiniteType (algebraMap B X.D) ∧
          RingHom.FiniteType (algebraMap A' X.C')) ∧
      (RingHom.Flat (relativeAlgebraSystemToDPrime X) ↔
        RingHom.Flat (algebraMap B X.D) ∧
          RingHom.Flat (algebraMap A' X.C')) ∧
      ((RingHom.Flat (relativeAlgebraSystemToDPrime X) ∧
          RingHom.FinitePresentation (relativeAlgebraSystemToDPrime X)) ↔
        (RingHom.Flat (algebraMap B X.D) ∧
          RingHom.FinitePresentation (algebraMap B X.D)) ∧
          (RingHom.Flat (algebraMap A' X.C') ∧
            RingHom.FinitePresentation (algebraMap A' X.C'))) ∧
      (RingHom.Smooth (relativeAlgebraSystemToDPrime X) ↔
        RingHom.Smooth (algebraMap B X.D) ∧
          RingHom.Smooth (algebraMap A' X.C')) ∧
      (RingHom.Etale (relativeAlgebraSystemToDPrime X) ↔
        RingHom.Etale (algebraMap B X.D) ∧
          RingHom.Etale (algebraMap A' X.C')) := by
  sorry

/-- The relative-situation package obtained from a system by viewing its
pullback ring as the new `D'`. -/
def relativeAlgebraSystemSituation
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    (base : FibreProductSituation A A' B)
    (X : RelativeAlgebraSystem base) :
    RelativeFibreProductSituation A A' B (relativeAlgebraSystemDPrime X) where
  base := base
  toD' := relativeAlgebraSystemToDPrime X

/-- If `D'` is flat over `B'`, it is recovered from its two base changes. -/
theorem relative_flat_algebra_base_change_isPullback
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    (base : FibreProductSituation A A' B)
    (X : RelativeAlgebraSystem base)
    (hflat : RingHom.Flat (relativeAlgebraSystemToDPrime X)) :
    Nonempty
      {e : relativeAlgebraSystemDPrime X ≃+*
          RingHom.pullback
            (relativeDToC (relativeAlgebraSystemSituation base X))
            (relativeC'ToC (relativeAlgebraSystemSituation base X)) //
        e.toRingHom =
          relativeD'ToBaseChangePullback (relativeAlgebraSystemSituation base X)} := by
  sorry

/-- The category of flat `B'`-algebras, represented as a full subcategory of
the under-category of commutative rings. -/
def relativeFlatAlgebraProperty
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    (base : FibreProductSituation A A' B) :
    ObjectProperty (Under (CommRingCat.of (fibreProductRing base))) :=
  fun X => RingHom.Flat X.hom.hom

/-- The source's category of flat `B'`-algebras. -/
abbrev relativeFlatAlgebraCategory
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    (base : FibreProductSituation A A' B) :=
  ObjectProperty.FullSubcategory (relativeFlatAlgebraProperty base)

/-- Morphisms of systems of algebras, expressed by their maps on `D`, `C'`,
and `C'/IC'`. -/
structure RelativeAlgebraSystemHom
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    {base : FibreProductSituation A A' B}
    (X Y : RelativeAlgebraSystem base) where
  d : X.D ⟶ Y.D
  cPrime : X.C' ⟶ Y.C'
  c : relativeAlgebraSystemQuotient base X.C' →+*
    relativeAlgebraSystemQuotient base Y.C'
  c_comm :
    c.comp (relativeAlgebraSystemC'ToC X) =
      (relativeAlgebraSystemC'ToC Y).comp cPrime.hom.toRingHom
  d_comm :
    c.comp (relativeAlgebraSystemDToC X) =
      (relativeAlgebraSystemDToC Y).comp d.hom.toRingHom

@[ext]
theorem RelativeAlgebraSystemHom.ext
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    {base : FibreProductSituation A A' B}
    {X Y : RelativeAlgebraSystem base}
    {f g : RelativeAlgebraSystemHom X Y}
    (hd : f.d = g.d) (hcPrime : f.cPrime = g.cPrime)
    (hc : f.c = g.c) : f = g := by
  cases f
  cases g
  cases hd
  cases hcPrime
  cases hc
  rfl

instance relativeAlgebraSystemCategory
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    (base : FibreProductSituation A A' B) :
    Category (RelativeAlgebraSystem base) where
  Hom X Y := RelativeAlgebraSystemHom X Y
  id X :=
    { d := 𝟙 X.D
      cPrime := 𝟙 X.C'
      c := RingHom.id _
      c_comm := by simp
      d_comm := by simp }
  comp f g :=
    { d := f.d ≫ g.d
      cPrime := f.cPrime ≫ g.cPrime
      c := g.c.comp f.c
      c_comm := by
        change (g.c.comp f.c).comp (relativeAlgebraSystemC'ToC _) =
          (relativeAlgebraSystemC'ToC _).comp
            (g.cPrime.hom.toRingHom.comp f.cPrime.hom.toRingHom)
        rw [RingHom.comp_assoc, f.c_comm, ← RingHom.comp_assoc, g.c_comm]
        change
          (relativeAlgebraSystemC'ToC _).comp
              (g.cPrime.hom.toRingHom.comp f.cPrime.hom.toRingHom) =
            (relativeAlgebraSystemC'ToC _).comp
              (g.cPrime.hom.toRingHom.comp f.cPrime.hom.toRingHom)
        rfl
      d_comm := by
        change (g.c.comp f.c).comp (relativeAlgebraSystemDToC _) =
          (relativeAlgebraSystemDToC _).comp
            (g.d.hom.toRingHom.comp f.d.hom.toRingHom)
        rw [RingHom.comp_assoc, f.d_comm, ← RingHom.comp_assoc, g.d_comm]
        change
          (relativeAlgebraSystemDToC _).comp
              (g.d.hom.toRingHom.comp f.d.hom.toRingHom) =
            (relativeAlgebraSystemDToC _).comp
              (g.d.hom.toRingHom.comp f.d.hom.toRingHom)
        rfl }
  id_comp f := by
    apply RelativeAlgebraSystemHom.ext <;> simp
  comp_id f := by
    apply RelativeAlgebraSystemHom.ext <;> simp
  assoc f g h := by
    apply RelativeAlgebraSystemHom.ext
    · simp
    · simp
    · change h.c.comp (g.c.comp f.c) = (h.c.comp g.c).comp f.c
      rw [RingHom.comp_assoc]

/-- The systems whose two displayed algebra maps are flat. -/
def relativeFlatAlgebraSystemProperty
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    (base : FibreProductSituation A A' B) :
    ObjectProperty (RelativeAlgebraSystem base) :=
  fun X =>
    RingHom.Flat (algebraMap B X.D) ∧
      RingHom.Flat (algebraMap A' X.C')

/-- The full subcategory of flat algebra systems. -/
abbrev relativeFlatAlgebraSystemCategory
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    (base : FibreProductSituation A A' B) :=
  ObjectProperty.FullSubcategory (relativeFlatAlgebraSystemProperty base)

/-- Flat `B'`-algebras are equivalent to flat systems `(D, C', φ)`. -/
theorem relative_flat_algebra_equivalence_exists
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    (base : FibreProductSituation A A' B) :
    Nonempty
      (relativeFlatAlgebraCategory base ≌ relativeFlatAlgebraSystemCategory base) := by
  sorry

/-- A chosen equivalence between flat algebras and flat systems. -/
noncomputable def relative_flat_algebra_equivalence
    {A A' B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    (base : FibreProductSituation A A' B) :
    relativeFlatAlgebraCategory base ≌ relativeFlatAlgebraSystemCategory base :=
  Classical.choice (relative_flat_algebra_equivalence_exists base)

/-! ## Quotients of modules -/

/-- A quotient presentation of a module, retaining the source's explicit
surjectivity condition. -/
structure RelativeModuleQuotientMap
    {R : Type u} [Ring R] (L : ModuleCat.{u} R) where
  Q : ModuleCat.{u} R
  map : L ⟶ Q
  surjective : Function.Surjective (fun x => map x)

/-- A source-side quotient of a relative `D'`-module. -/
structure RelativeModuleQuotientSource
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (L' : ModuleCat.{u} D') where
  quotient : RelativeModuleQuotientMap L'
  finitePresentation :
    Module.FinitePresentation D' (quotient.Q : Type u)
  flat :
    Module.Flat (relativeFibreProductRing S)
      ((ModuleCat.restrictScalars S.toD').obj quotient.Q : Type u)

/-- The pair of base-changed quotient presentations in the source's remark.
The two isomorphisms to `Q₁₂` make the phrase “the same quotient” precise. -/
structure RelativeModuleQuotientPair
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (L' : ModuleCat.{u} D') where
  left : RelativeModuleQuotientMap (relativeModuleLeftBaseChange S L')
  left_finitePresentation :
    Module.FinitePresentation (relativeD S) (left.Q : Type u)
  left_flat : Module.Flat B (relativeLeftModuleOverB S
    ((relativeModuleFunctor S).obj L') : Type u)
  right : RelativeModuleQuotientMap (relativeModuleRightBaseChange S L')
  right_finitePresentation :
    Module.FinitePresentation (relativeC' S) (right.Q : Type u)
  right_flat : Module.Flat A' (relativeRightModuleOverA' S
    ((relativeModuleFunctor S).obj L') : Type u)
  common : ModuleCat.{u} (relativeC S)
  left_common :
    (ModuleCat.extendScalars (relativeDToC S)).obj left.Q ⟶ common
  right_common :
    (ModuleCat.extendScalars (relativeC'ToC S)).obj right.Q ⟶ common
  left_common_isIso : IsIso left_common
  right_common_isIso : IsIso right_common
  common_compatibility :
    (ModuleCat.extendScalars (relativeDToC S)).map left.map ≫ left_common =
      relativeModuleComparison S L' ≫
        (ModuleCat.extendScalars (relativeC'ToC S)).map right.map ≫ right_common

/-- The source's bijective correspondence between flat finitely-presented
quotients and compatible pairs of such quotients. -/
theorem relative_module_quotient_correspondence
    {A A' B D' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D']
    (S : RelativeFibreProductSituation A A' B D')
    (hfp : RingHom.FinitePresentation S.toD')
    (L' : ModuleCat.{u} D') :
    Nonempty
      (RelativeModuleQuotientSource S L' ≃
        RelativeModuleQuotientPair S L') := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit07
