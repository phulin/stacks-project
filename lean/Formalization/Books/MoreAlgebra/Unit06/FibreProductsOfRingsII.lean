import Formalization.Books.MoreAlgebra.Unit05.FibreProductsOfRingsI
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# More on Algebra, Chapter 6: Fibre products of rings, II

The source fixes a pullback of commutative rings
`B → A ← A'` with `A' → A` surjective.  The ring pullback and its
projections are Mathlib's canonical `RingHom.pullback` construction.  For
modules, the category of triples and the compatible-pair pullback are the
canonical `ModuleGluingCategory` and `moduleFiberProduct` constructions from
the preceding chapter.
-/

namespace Formalization.Books.MoreAlgebra.Unit06

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Formalization.Books.MoreAlgebra.Unit05

universe u

noncomputable section

/-! ## The fibre-product situation -/

/-- The ring maps and surjectivity hypothesis in the source's situation. -/
structure FibreProductSituation (A A' B : Type u)
    [CommRing A] [CommRing A'] [CommRing B] where
  /-- The map `B → A`. -/
  toA : B →+* A
  /-- The surjective map `A' → A`. -/
  fromA' : A' →+* A
  /-- Surjectivity of `A' → A`. -/
  fromA'_surjective : Function.Surjective fromA'

/-- The kernel `I = ker(A' → A)` in the source's situation. -/
abbrev fibreProductIdeal
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) : Ideal A' :=
  RingHom.ker D.fromA'

/-- The ring `B' = B ×_A A'`, using Mathlib's canonical pullback subring. -/
abbrev fibreProductRing
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) : Type u :=
  RingHom.pullback D.toA D.fromA'

/-- The projection `B' → B`. -/
abbrev fibreProductToB
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) : fibreProductRing D →+* B :=
  RingHom.pullbackFst D.toA D.fromA'

/-- The projection `B' → A'`. -/
abbrev fibreProductToA'
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) : fibreProductRing D →+* A' :=
  RingHom.pullbackSnd D.toA D.fromA'

/-- The commutative square of rings attached to the source's situation. -/
def fibreProductRingSquare
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    RingSquare A A' B (fibreProductRing D) where
  t := D.fromA'
  s := D.toA
  u := fibreProductToB D
  v := fibreProductToA' D
  comm := RingHom.pullback_comm_sq D.toA D.fromA'

/-- The square defining `B'` is cartesian in `CommRingCat`. -/
theorem fibreProduct_isPullback
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    IsPullback
      (CommRingCat.ofHom (fibreProductToB D))
      (CommRingCat.ofHom (fibreProductToA' D))
      (CommRingCat.ofHom D.toA)
      (CommRingCat.ofHom D.fromA') := by
  sorry

/-- The projection `B' → B` is surjective because `A' → A` is surjective. -/
theorem fibreProduct_toB_surjective
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Function.Surjective (fibreProductToB D) := by
  exact RingHom.surjective_pullbackFst_of_surjective D.toA D.fromA'
    D.fromA'_surjective

/-- The kernel of `B' → B` maps onto the kernel `I` of `A' → A`. -/
theorem fibreProduct_kernel_map
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Ideal.map (fibreProductToA' D) (RingHom.ker (fibreProductToB D)) =
      fibreProductIdeal D := by
  simpa [fibreProductIdeal] using
    (RingHom.map_pullbackSnd_ker_pullbackFst_eq D.toA D.fromA')

/-- The map on kernel elements induced by the projection `B' → A'`. -/
def fibreProduct_kernel_to_ideal
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    (RingHom.ker (fibreProductToB D) : Type u) →
      (fibreProductIdeal D : Type u) :=
  fun x => ⟨fibreProductToA' D x, by
    change D.fromA' (fibreProductToA' D x) = 0
    have hx : fibreProductToB D x = 0 := by
      simpa only [RingHom.mem_ker] using x.property
    have hcomm : D.toA (fibreProductToB D (x : fibreProductRing D)) =
        D.fromA' (fibreProductToA' D (x : fibreProductRing D)) :=
      DFunLike.congr_fun (RingHom.pullback_comm_sq D.toA D.fromA')
        (x : fibreProductRing D)
    rw [← hcomm]
    simp [hx]
  ⟩

/-- The source's assertion that the induced kernel map is bijective. -/
theorem fibreProduct_kernel_equiv_exists
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Nonempty
      {e : (RingHom.ker (fibreProductToB D) : Type u) ≃
          (fibreProductIdeal D : Type u) //
        ∀ x, e x = fibreProduct_kernel_to_ideal D x} := by
  sorry

/-- A chosen equivalence for the induced map on kernel elements. -/
noncomputable def fibreProduct_kernel_equiv
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    (RingHom.ker (fibreProductToB D) : Type u) ≃
      (fibreProductIdeal D : Type u) :=
  (Classical.choice (fibreProduct_kernel_equiv_exists D)).1

theorem fibreProduct_kernel_equiv_apply
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) (x : RingHom.ker (fibreProductToB D)) :
    fibreProduct_kernel_equiv D x = fibreProduct_kernel_to_ideal D x :=
  (Classical.choice (fibreProduct_kernel_equiv_exists D)).2 x

/-- On spectra, the ring pullback square is a pushout square of topological
spaces.  `Spec.topMap` is Mathlib's canonical contravariant spectrum map. -/
theorem fibreProduct_spectrum_isPushout
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    IsPushout
      (Spec.topMap (CommRingCat.ofHom D.toA))
      (Spec.topMap (CommRingCat.ofHom D.fromA'))
      (Spec.topMap (CommRingCat.ofHom (fibreProductToB D)))
      (Spec.topMap (CommRingCat.ofHom (fibreProductToA' D))) := by
  sorry

/-- Integrality descends across the surjective leg of the pullback square. -/
theorem fibreProduct_integral
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (h_integral : D.toA.IsIntegral) :
    (fibreProductToA' D).IsIntegral := by
  sorry

/-! ## Modules over the pullback -/

/-- The quotient `M'/IM'` used by the source to describe a gluing map. -/
abbrev fibreProductModuleReduction
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    {M' : Type u} [AddCommGroup M'] [Module A' M'] : Type u :=
  M' ⧸ (fibreProductIdeal D • (⊤ : Submodule A' M'))

/-- The category of module triples `(N, M', φ)` in the source, implemented by
the canonical full subcategory from Unit05. -/
abbrev fibreProductModuleGluingCategory
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :=
  ModuleGluingCategory (fibreProductRingSquare D)

/-- The source's functor `Mod(B') → Mod(B) ×_{Mod(A)} Mod(A')`. -/
noncomputable def fibreProductModuleFunctor
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    ModuleCat.{u} (fibreProductRing D) ⥤ fibreProductModuleGluingCategory D :=
  moduleBaseChangeFunctor (fibreProductRingSquare D)

/-- The compatible-pair module pullback attached to a module triple. -/
noncomputable abbrev fibreProductModule
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory D) :
    ModuleCat.{u} (fibreProductRing D) :=
  moduleFiberProduct (fibreProductRingSquare D) X

/-- The compatible-pair condition underlying `fibreProductModule`. -/
abbrev fibreProductModuleCompatiblePairs
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory D) :=
  moduleFiberCompatiblePairs (fibreProductRingSquare D) X

/-- The categorical module pullback and the source's compatible-pair
presentation have the same underlying elements. -/
noncomputable def fibreProductModuleCompatiblePairEquiv
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory D) :
    (fibreProductModule D X : Type u) ≃
      {p : (moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X) : Type u) ×
        (moduleGluingRightObj (D := fibreProductRingSquare D) (X := X) : Type u) //
        p ∈ fibreProductModuleCompatiblePairs D X} :=
  moduleFiberProduct_compatiblePairEquiv (fibreProductRingSquare D) X

/-- The projection from the compatible-pair module to its `B`-module
component. -/
def fibreProductModule_leftProjection
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (situation : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory situation) :
    fibreProductModule situation X →
      moduleGluingLeftObj (fibreProductRingSquare situation) X :=
  fun (x : fibreProductModule situation X) =>
    (moduleFiberProductPair (fibreProductRingSquare situation) X x).1

/-- In the source's module lemma, the compatible-pair projection to `N` is
surjective. -/
theorem fibreProductModule_leftProjection_surjective
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (situation : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory situation) :
    Function.Surjective (fibreProductModule_leftProjection situation X) := by
  sorry

/-- The right adjoint given by the compatible-pair module pullback. -/
noncomputable abbrev fibreProductModuleRightAdjoint
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    fibreProductModuleGluingCategory D ⥤ ModuleCat.{u} (fibreProductRing D) :=
  moduleFiberProductRightAdjointCanonical (fibreProductRingSquare D)

/-- The module functor has the source's compatible-pair right adjoint. -/
noncomputable def fibreProductModule_rightAdjoint
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    fibreProductModuleFunctor D ⊣ fibreProductModuleRightAdjoint D := by
  exact (moduleFiberProductAdjunctionData (fibreProductRingSquare D)).adjunction

/-- The source's assertion that applying the gluing functor to the right
adjoint recovers a module triple, expressed by a natural isomorphism. -/
theorem fibreProductModule_composition_isIdentity
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Nonempty
      (fibreProductModuleRightAdjoint D ⋙ fibreProductModuleFunctor D ≅
        𝟭 (fibreProductModuleGluingCategory D)) := by
  sorry

/-- A chosen natural isomorphism expressing the recovery of a module triple. -/
noncomputable def fibreProductModule_composition_iso
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    fibreProductModuleRightAdjoint D ⋙ fibreProductModuleFunctor D ≅
      𝟭 (fibreProductModuleGluingCategory D) :=
  Classical.choice (fibreProductModule_composition_isIdentity D)

/-- The componentwise base-change isomorphisms asserted in the source. -/
theorem fibreProductModule_recovery_exists
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory D) :
    Nonempty
      (((ModuleCat.extendScalars (fibreProductToB D)).obj
          ((fibreProductModuleRightAdjoint D).obj X) ≅
        moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X)) ×
        ((ModuleCat.extendScalars (fibreProductToA' D)).obj
          ((fibreProductModuleRightAdjoint D).obj X) ≅
        moduleGluingRightObj (D := fibreProductRingSquare D) (X := X))) := by
  sorry

/-- A chosen pair of the source's componentwise recovery isomorphisms. -/
noncomputable def fibreProductModule_recovery
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory D) :
    (((ModuleCat.extendScalars (fibreProductToB D)).obj
        ((fibreProductModuleRightAdjoint D).obj X) ≅
      moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X)) ×
      ((ModuleCat.extendScalars (fibreProductToA' D)).obj
        ((fibreProductModuleRightAdjoint D).obj X) ≅
      moduleGluingRightObj (D := fibreProductRingSquare D) (X := X))) :=
  Classical.choice (fibreProductModule_recovery_exists D X)

/-- The unit of the module adjunction, i.e. the source's adjunction map. -/
noncomputable def fibreProductModuleAdjunctionMap
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) (L' : ModuleCat.{u} (fibreProductRing D)) :
    L' ⟶ (fibreProductModuleRightAdjoint D).obj ((fibreProductModuleFunctor D).obj L') :=
  (fibreProductModule_rightAdjoint D).unit.app L'

/-- The adjunction map is surjective. -/
theorem fibreProductModuleAdjunctionMap_surjective
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) (L' : ModuleCat.{u} (fibreProductRing D)) :
    Function.Surjective (fun x => fibreProductModuleAdjunctionMap D L' x) := by
  sorry

/-- The displayed adjunction map is not injective for arbitrary pullback
diagrams.  The source's concrete witness is
`B' = k[x, y]/(xy)`, `A' = B'/(x)`, `B = B'/(y)`,
`A = B'/(x, y)`, and `L' = B'/(x - y)`. -/
theorem fibreProductModuleAdjunctionMap_not_injective_in_general :
    ¬ (∀ {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
        (D : FibreProductSituation A A' B)
        (L' : ModuleCat.{u} (fibreProductRing D)),
        Function.Injective (fun x => fibreProductModuleAdjunctionMap D L' x)) := by
  sorry

/-! ## The concrete non-injectivity example -/

/-- The polynomial ring `k[x,y]` used in the source's example. -/
abbrev fibreProductExamplePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

/-- The ideal `(xy)` in `k[x,y]`. -/
def fibreProductExampleXYIdeal (k : Type u) [Field k] :
    Ideal (fibreProductExamplePolynomialRing k) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)} :
      Set (fibreProductExamplePolynomialRing k))

/-- The ring `B' = k[x,y]/(xy)` in the source's example. -/
abbrev fibreProductExampleBPrime (k : Type u) [Field k] :=
  fibreProductExamplePolynomialRing k ⧸ fibreProductExampleXYIdeal k

/-- The ideal `(x)` in `B'`. -/
def fibreProductExampleXIdeal (k : Type u) [Field k] :
    Ideal (fibreProductExampleBPrime k) :=
  Ideal.span
    ({Ideal.Quotient.mk (fibreProductExampleXYIdeal k)
        (MvPolynomial.X (0 : Fin 2))} : Set (fibreProductExampleBPrime k))

/-- The ideal `(y)` in `B'`. -/
def fibreProductExampleYIdeal (k : Type u) [Field k] :
    Ideal (fibreProductExampleBPrime k) :=
  Ideal.span
    ({Ideal.Quotient.mk (fibreProductExampleXYIdeal k)
        (MvPolynomial.X (1 : Fin 2))} : Set (fibreProductExampleBPrime k))

/-- The ideal `(x - y)` in `B'`. -/
def fibreProductExampleXYDifferenceIdeal (k : Type u) [Field k] :
    Ideal (fibreProductExampleBPrime k) :=
  Ideal.span
    ({Ideal.Quotient.mk (fibreProductExampleXYIdeal k)
        (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2))} :
      Set (fibreProductExampleBPrime k))

/-- The four quotient rings in the source's concrete example. -/
abbrev fibreProductExampleA' (k : Type u) [Field k] :=
  fibreProductExampleBPrime k ⧸ fibreProductExampleXIdeal k

abbrev fibreProductExampleB (k : Type u) [Field k] :=
  fibreProductExampleBPrime k ⧸ fibreProductExampleYIdeal k

abbrev fibreProductExampleA (k : Type u) [Field k] :=
  fibreProductExampleBPrime k ⧸
    (fibreProductExampleXIdeal k ⊔ fibreProductExampleYIdeal k)

/-- The quotient maps from `B'` in the source's example. -/
def fibreProductExampleBPrimeToB (k : Type u) [Field k] :
    fibreProductExampleBPrime k →+* fibreProductExampleB k :=
  Ideal.Quotient.mk (fibreProductExampleYIdeal k)

def fibreProductExampleBPrimeToA' (k : Type u) [Field k] :
    fibreProductExampleBPrime k →+* fibreProductExampleA' k :=
  Ideal.Quotient.mk (fibreProductExampleXIdeal k)

/-- The induced maps from `B` and `A'` to `A`. -/
def fibreProductExampleBToA (k : Type u) [Field k] :
    fibreProductExampleB k →+* fibreProductExampleA k :=
  Ideal.Quotient.factor le_sup_right

def fibreProductExampleA'ToA (k : Type u) [Field k] :
    fibreProductExampleA' k →+* fibreProductExampleA k :=
  Ideal.Quotient.factor le_sup_left

/-- The commutative square of quotient rings in the source's example. -/
def fibreProductExampleRingSquare (k : Type u) [Field k] :
    RingSquare (fibreProductExampleA k) (fibreProductExampleA' k)
      (fibreProductExampleB k) (fibreProductExampleBPrime k) where
  t := fibreProductExampleA'ToA k
  s := fibreProductExampleBToA k
  u := fibreProductExampleBPrimeToB k
  v := fibreProductExampleBPrimeToA' k
  comm := by
    simp [fibreProductExampleBToA, fibreProductExampleA'ToA,
      fibreProductExampleBPrimeToB, fibreProductExampleBPrimeToA']

/-- The module `L' = B'/(x-y)` in the source's example. -/
abbrev fibreProductExampleLPrime (k : Type u) [Field k] :=
  fibreProductExampleBPrime k ⧸ fibreProductExampleXYDifferenceIdeal k

noncomputable abbrev fibreProductExampleModule (k : Type u) [Field k] :
    ModuleCat.{u} (fibreProductExampleBPrime k) :=
  ModuleCat.of (fibreProductExampleBPrime k) (fibreProductExampleLPrime k)

/-- The class of `x` in `L'`. -/
def fibreProductExampleXClass (k : Type u) [Field k] :
    fibreProductExampleLPrime k :=
  Ideal.Quotient.mk (fibreProductExampleXYDifferenceIdeal k)
    (Ideal.Quotient.mk (fibreProductExampleXYIdeal k)
      (MvPolynomial.X (0 : Fin 2)))

/-- The source's concrete example has a nonzero class of `x` mapping to zero. -/
theorem fibreProductExample_x_nonzero_maps_zero (k : Type u) [Field k] :
    fibreProductExampleXClass k ≠ 0 ∧
      (moduleFiberProductAdjunctionData (fibreProductExampleRingSquare k)).adjunction.unit.app
          (fibreProductExampleModule k)
          (fibreProductExampleXClass k) = 0 := by
  sorry

/-- The compatible-pair pullback is functorial for morphisms of triples. -/
theorem fibreProductModule_map_surjective
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    {X Y : fibreProductModuleGluingCategory D} (f : X ⟶ Y)
    (hN : Function.Surjective f.hom.left)
    (hM' : Function.Surjective f.hom.right) :
    Function.Surjective (fun x => (fibreProductModuleRightAdjoint D).map f x) := by
  sorry

/-- Finite modules on the two upper corners give a finite compatible-pair
module over the pullback ring. -/
theorem fibreProduct_finite_module
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory D)
    [Module.Finite B
      (moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X) : Type u)]
    [Module.Finite A'
      (moduleGluingRightObj (D := fibreProductRingSquare D) (X := X) : Type u)] :
    Module.Finite (fibreProductRing D)
      ((fibreProductModuleRightAdjoint D).obj X : Type u) := by
  sorry

/-! ## The exact sequence and flat modules -/

/-- The first map in the source's exact sequence
`0 → B' → B ⊕ A' → A → 0`. -/
def fibreProductExactLeft
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) : fibreProductRing D → B × A' :=
  fun x => (fibreProductToB D x, fibreProductToA' D x)

/-- The second map in the source's exact sequence
`0 → B' → B ⊕ A' → A → 0`. -/
def fibreProductExactRight
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) : B × A' → A :=
  fun x => D.toA x.1 - D.fromA' x.2

/-- Exactness, injectivity on the left, and surjectivity on the right of the
source's short exact sequence. -/
theorem fibreProduct_exact_sequence
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Function.Injective (fibreProductExactLeft D) ∧
      Function.Exact (fibreProductExactLeft D) (fibreProductExactRight D) ∧
      Function.Surjective (fibreProductExactRight D) := by
  sorry

/-- The full subcategory of module triples whose two displayed components are
flat. -/
def fibreProductFlatGluingProperty
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    ObjectProperty (fibreProductModuleGluingCategory D) :=
  fun X =>
    Module.Flat B
        (moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X) : Type u) ∧
      Module.Flat A'
        (moduleGluingRightObj (D := fibreProductRingSquare D) (X := X) : Type u)

abbrev fibreProductFlatGluingCategory
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :=
  ObjectProperty.FullSubcategory (fibreProductFlatGluingProperty D)

/-- The category of flat modules over the pullback ring. -/
def fibreProductFlatModuleProperty
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    ObjectProperty (ModuleCat.{u} (fibreProductRing D)) :=
  fun L' => Module.Flat (fibreProductRing D) (L' : Type u)

abbrev fibreProductFlatModuleCategory
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :=
  ObjectProperty.FullSubcategory (fibreProductFlatModuleProperty D)

/-- If both components of a triple are flat, its compatible-pair module is
flat over the pullback ring. -/
theorem fibreProduct_flat_module
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (X : fibreProductModuleGluingCategory D)
    [Module.Flat B
      (moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X) : Type u)]
    [Module.Flat A'
      (moduleGluingRightObj (D := fibreProductRingSquare D) (X := X) : Type u)] :
    Module.Flat (fibreProductRing D)
      ((fibreProductModuleRightAdjoint D).obj X : Type u) := by
  sorry

/-- For a flat pullback module, the adjunction map back to the compatible-pair
module is an isomorphism. -/
theorem fibreProduct_flat_module_recovery
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (L' : ModuleCat.{u} (fibreProductRing D))
    [Module.Flat (fibreProductRing D) (L' : Type u)] :
    IsIso (fibreProductModuleAdjunctionMap D L') := by
  sorry

/-- A chosen isomorphism expressing the source's recovery statement for flat
modules. -/
noncomputable def fibreProduct_flat_module_recoveryIso
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B)
    (L' : ModuleCat.{u} (fibreProductRing D))
    [Module.Flat (fibreProductRing D) (L' : Type u)] :
    L' ≅ (fibreProductModuleRightAdjoint D).obj ((fibreProductModuleFunctor D).obj L') := by
  letI := fibreProduct_flat_module_recovery D L'
  exact asIso (fibreProductModuleAdjunctionMap D L')

/-- Flat modules over the pullback ring are equivalent to flat module triples. -/
theorem fibreProduct_flat_module_equivalence_exists
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Nonempty (fibreProductFlatModuleCategory D ≌ fibreProductFlatGluingCategory D) := by
  sorry

noncomputable def fibreProduct_flat_module_equivalence
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    fibreProductFlatModuleCategory D ≌ fibreProductFlatGluingCategory D :=
  Classical.choice (fibreProduct_flat_module_equivalence_exists D)

/-! ## Finite projective modules -/

/-- The full subcategory of finite projective modules over a ring. -/
def fibreProductFiniteProjectiveProperty
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    ObjectProperty (ModuleCat.{u} (fibreProductRing D)) :=
  fun L' =>
    Module.Finite (fibreProductRing D) (L' : Type u) ∧
      Module.Projective (fibreProductRing D) (L' : Type u)

abbrev fibreProductFiniteProjectiveModuleCategory
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :=
  ObjectProperty.FullSubcategory (fibreProductFiniteProjectiveProperty D)

/-- The full subcategory of triples with finite projective components. -/
def fibreProductFiniteProjectiveGluingProperty
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    ObjectProperty (fibreProductModuleGluingCategory D) :=
  fun X =>
    (Module.Finite B
        (moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X) : Type u) ∧
      Module.Projective B
        (moduleGluingLeftObj (D := fibreProductRingSquare D) (X := X) : Type u)) ∧
    (Module.Finite A'
        (moduleGluingRightObj (D := fibreProductRingSquare D) (X := X) : Type u) ∧
      Module.Projective A'
        (moduleGluingRightObj (D := fibreProductRingSquare D) (X := X) : Type u))

abbrev fibreProductFiniteProjectiveGluingCategory
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :=
  ObjectProperty.FullSubcategory (fibreProductFiniteProjectiveGluingProperty D)

/-- Finite projective modules over the pullback ring are equivalent to triples
with finite projective components. -/
theorem fibreProduct_finite_projective_equivalence_exists
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    Nonempty
      (fibreProductFiniteProjectiveModuleCategory D ≌
        fibreProductFiniteProjectiveGluingCategory D) := by
  sorry

noncomputable def fibreProduct_finite_projective_equivalence
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (D : FibreProductSituation A A' B) :
    fibreProductFiniteProjectiveModuleCategory D ≌
      fibreProductFiniteProjectiveGluingCategory D :=
  Classical.choice (fibreProduct_finite_projective_equivalence_exists D)

end

end Formalization.Books.MoreAlgebra.Unit06
