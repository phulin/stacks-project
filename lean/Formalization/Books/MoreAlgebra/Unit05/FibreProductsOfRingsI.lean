import Formalization.Books.Categories.Unit31.TwoFibreProducts
import Formalization.Books.Algebra.Unit09.Localization
import Formalization.Books.Algebra.Unit51.MoreNoetherianRings
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Exact.Basic
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# More on Algebra, Chapter 5: Fibre products of rings, I

This file uses Mathlib's canonical pullback subrings and subalgebras.  The
category of triples of modules is the canonical full subcategory of a comma
category used by the earlier chapter's `IsoComma` construction, and the
module fibre product is the categorical pullback in `ModuleCat`; the source's
compatible-pair description is recorded alongside that construction.
-/

namespace Formalization.Books.MoreAlgebra.Unit05

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit31
open scoped ChangeOfRings

universe u

noncomputable section

/-! ## Finite type and finite-index fibre products -/

/-- The exact sequence underlying the first displayed fibre-product diagram.

The source uses this exactness in its proof; the canonical equalizer
presentation of `AlgHom.pullback` is used for the object itself. -/
theorem algebraPullback_exact
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) :
    Function.Exact
      (fun x : AlgHom.pullback f g => (x : A × C))
      (fun x : A × C => f x.1 - g x.2) := by
  sorry

/- The proof's two exact rows use the kernel `I = ker(A → B)` and the
canonical projections of the algebra pullback. -/

/-- The ideal `I` used in the exact-row diagram in the proof of
`finiteType_algHom_pullback`. -/
abbrev algebraPullbackKernel
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) : Ideal A :=
  RingHom.ker f.toRingHom

/-- The inclusion of the proof's kernel `I` into `A`. -/
def algebraPullbackKernelToA
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    algebraPullbackKernel f → A :=
  fun x => x

/-- The inclusion of `I` into the algebra pullback `A ×_B C`. -/
def algebraPullbackKernelToPullback
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) :
    algebraPullbackKernel f → AlgHom.pullback f g :=
  fun x => ⟨((x : A), 0), by
    change f (x : A) = g 0
    rw [show f (x : A) = 0 by simpa [algebraPullbackKernel] using x.property]
    simp⟩

/-- The map from the fibre product to the product used in the Artin--Tate
argument. -/
def algebraPullbackToProduct
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) :
    AlgHom.pullback f g →+* A × C :=
  (AlgHom.pullbackFst f g).toRingHom.prod (AlgHom.pullbackSnd f g).toRingHom

/-- The map from the fibre product to the product is injective. -/
theorem algebraPullback_to_product_injective
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) :
    Function.Injective (algebraPullbackToProduct f g) := by
  intro x y hxy
  exact Subtype.ext hxy

/-- The product ring is finite as a module over the fibre product, as used
in the Artin--Tate argument. -/
theorem algebraPullback_product_finite
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B)
    (hf : Function.Surjective f)
    (hg : RingHom.Finite g.toRingHom) :
    (algebraPullbackToProduct f g).Finite := by
  sorry

/-- The exact rows in the proof of the finite-type fibre-product lemma,
with `I` represented by the canonical kernel ideal. -/
theorem algebraPullback_exact_rows
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) (hf : Function.Surjective f) :
    Function.Exact (algebraPullbackKernelToA f) f ∧
      Function.Surjective f ∧
      Function.Exact (algebraPullbackKernelToPullback f g)
        (AlgHom.pullbackSnd f g) ∧
      Function.Surjective (AlgHom.pullbackSnd f g) := by
  sorry

/-! The source-facing finite-type lemma follows the proof-support interfaces
above, which makes the Artin--Tate route available when its body is filled. -/

/-- A finite-type fibre product of algebras in the hypotheses of the source
lemma.  `AlgHom.pullback` is Mathlib's canonical fibre-product algebra, and
`RingHom.Finite` is the established finite-module condition for `C → B`. -/
theorem finiteType_algHom_pullback
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B)
    (hR : IsNoetherianRing R)
    (hA : Algebra.FiniteType R A)
    (hB : Algebra.FiniteType R B)
    (hC : Algebra.FiniteType R C)
    (hf : Function.Surjective f)
    (hg : RingHom.Finite g.toRingHom) :
    Algebra.FiniteType R (AlgHom.pullback f g) := by
  sorry

/-- The product of a family of algebra maps with varying codomains.  Mathlib
provides `AlgHom.pi` for a common domain; this small componentwise map is the
corresponding canonical construction needed for the finite-index diagram. -/
def piAlgHomMap
    {R I : Type*} {A B : I → Type*}
    [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)]
    (f : ∀ i, A i →ₐ[R] B i) :
    (∀ i, A i) →ₐ[R] (∀ i, B i) :=
  { toRingHom :=
      { toFun := fun x i => f i (x i)
        map_one' := by
          funext i
          simp
        map_mul' := by
          intro x y
          funext i
          simp
        map_zero' := by
          funext i
          simp
        map_add' := by
          intro x y
          funext i
          simp }
    commutes' := by
      intro r
      funext i
      simp }

/-- The finite-index cartesian-product consequence of the first lemma. -/
theorem finiteType_of_finite_cartesian_product
    {R P Q I : Type u} {A B : I → Type u}
    [CommRing R] [CommRing P] [CommRing Q]
    [Algebra R P] [Algebra R Q]
    [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
    [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)]
    [Finite I]
    (φ : ∀ i, A i →ₐ[R] B i)
    (ψ : ∀ i, Q →ₐ[R] B i)
    (pA : P →ₐ[R] (∀ i, A i))
    (pQ : P →ₐ[R] Q)
    (hcart :
      IsPullback
        (CommRingCat.ofHom pA.toRingHom)
        (CommRingCat.ofHom pQ.toRingHom)
        (CommRingCat.ofHom (piAlgHomMap φ).toRingHom)
        (CommRingCat.ofHom (AlgHom.pi ψ).toRingHom))
    (hR : IsNoetherianRing R)
    (hQ : Algebra.FiniteType R Q)
    (hA : ∀ i, Algebra.FiniteType R (A i))
    (hB : ∀ i, Algebra.FiniteType R (B i))
    (hφ : ∀ i, Function.Surjective (φ i))
    (hψ : ∀ i, Function.Surjective (ψ i)) :
    Algebra.FiniteType R P := by
  sorry

/-! ## Localization -/

/-- The element of a ring pullback corresponding to compatible elements on
the two lower-right corners of the source diagram. -/
def ringPullbackElement
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (g : B) (f : R')
    (h : s g = t f) : RingHom.pullback s t :=
  ⟨(g, f), h⟩

/-- The localized first projection from the canonical ring pullback. -/
noncomputable def localizedPullbackFst
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (g : B) (f : R')
    (h : s g = t f) :
    Localization.Away (ringPullbackElement s t g f h) →+*
      Localization.Away
        ((RingHom.pullbackFst s t) (ringPullbackElement s t g f h)) :=
  Localization.awayMap (RingHom.pullbackFst s t)
    (ringPullbackElement s t g f h)

/-- The localized second projection from the canonical ring pullback. -/
noncomputable def localizedPullbackSnd
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (g : B) (f : R')
    (h : s g = t f) :
    Localization.Away (ringPullbackElement s t g f h) →+*
      Localization.Away
        ((RingHom.pullbackSnd s t) (ringPullbackElement s t g f h)) :=
  Localization.awayMap (RingHom.pullbackSnd s t)
    (ringPullbackElement s t g f h)

/-- The localized map from `B_g` to the common localization of `R`. -/
noncomputable def localizedPullbackBaseLeft
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (g : B) (f : R')
    (_h : s g = t f) :
    Localization.Away g →+* Localization.Away (s g) :=
  Localization.awayMap s g

/-- The localized map from `R'_f` to the same chosen common localization. -/
noncomputable def localizedPullbackBaseRight
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (g : B) (f : R')
    (h : s g = t f) :
    Localization.Away f →+* Localization.Away (s g) := by
  rw [h]
  exact Localization.awayMap t f

/-- Localization preserves the ring pullback diagram from the source. -/
theorem localized_ring_pullback_isPullback
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (g : B) (f : R')
    (h : s g = t f) :
    IsPullback
      (CommRingCat.ofHom (localizedPullbackFst s t g f h))
      (CommRingCat.ofHom (localizedPullbackSnd s t g f h))
      (CommRingCat.ofHom (localizedPullbackBaseLeft s t g f h))
      (CommRingCat.ofHom (localizedPullbackBaseRight s t g f h)) := by
  sorry

/-- The exact sequence displayed in the localization proof, before
localization: it is the equalizer sequence for the canonical pullback. -/
theorem ringPullback_exact
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) :
    Function.Exact
      (fun x : RingHom.pullback s t => (x : B × R'))
      (fun x : B × R' => s x.1 - t x.2) := by
  sorry

/-- The two component maps in the localized exact sequence, stated directly
for an arbitrary element of the canonical pullback subring. -/
noncomputable def localizedPullbackFstCanonical
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (h : RingHom.pullback s t) :
    Localization.Away h →+*
      Localization.Away ((RingHom.pullbackFst s t) h) :=
  Localization.awayMap (RingHom.pullbackFst s t) h

noncomputable def localizedPullbackSndCanonical
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (h : RingHom.pullback s t) :
    Localization.Away h →+*
      Localization.Away ((RingHom.pullbackSnd s t) h) :=
  Localization.awayMap (RingHom.pullbackSnd s t) h

noncomputable def localizedPullbackBaseRightCanonical
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (h : RingHom.pullback s t) :
      Localization.Away ((RingHom.pullbackSnd s t) h) →+*
      Localization.Away (s ((RingHom.pullbackFst s t) h)) := by
  have hst : s ((RingHom.pullbackFst s t) h) =
      t ((RingHom.pullbackSnd s t) h) := by
    exact h.property
  rw [hst]
  exact Localization.awayMap t ((RingHom.pullbackSnd s t) h)

/-- The localized exact sequence used in the proof of the localization
lemma. -/
theorem localized_ringPullback_exact
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    (s : B →+* R) (t : R' →+* R) (h : RingHom.pullback s t) :
    Function.Exact
      (fun x : Localization.Away h =>
        (localizedPullbackFstCanonical s t h x,
          localizedPullbackSndCanonical s t h x))
      (fun p : Localization.Away ((RingHom.pullbackFst s t) h) ×
          Localization.Away ((RingHom.pullbackSnd s t) h) =>
        Localization.awayMap s ((RingHom.pullbackFst s t) h) p.1 -
          localizedPullbackBaseRightCanonical s t h p.2) := by
  sorry

/-! ## Modules over a commutative square -/

/-- A commutative square of rings.

The module functor in the source only assumes commutativity of the square;
cartesianness is needed for the preceding localization statement, but not for
this construction. -/
structure RingSquare (R R' B B' : Type u)
    [CommRing R] [CommRing R'] [CommRing B] [CommRing B'] where
  /-- The upper horizontal map `R' → R`. -/
  t : R' →+* R
  /-- The left vertical map `B → R`. -/
  s : B →+* R
  /-- The lower horizontal map `B' → B`. -/
  u : B' →+* B
  /-- The right vertical map `B' → R'`. -/
  v : B' →+* R'
  /-- Commutativity of the square. -/
  comm : s.comp u = t.comp v

@[simp]
theorem RingSquare.comm_apply
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (x : B') :
    D.s (D.u x) = D.t (D.v x) :=
  DFunLike.congr_fun D.comm x

/-- The category of module triples `(N, M', φ)` over a commutative square.
This is the canonical full subcategory of the comma category on isomorphisms,
the underlying implementation of the earlier Categories construction. -/
abbrev ModuleGluingCategory
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') :=
  IsoComma (ModuleCat.extendScalars D.s) (ModuleCat.extendScalars D.t)

/-- The two module components of an object of `ModuleGluingCategory`.  These
abbreviations keep projections out of binder positions, where Lean parses a
dotted projection as a binder name. -/
abbrev moduleGluingLeftObj
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) : ModuleCat.{u} B :=
  (isoCommaLeft (ModuleCat.extendScalars D.s) (ModuleCat.extendScalars D.t)).obj X

abbrev moduleGluingRightObj
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) : ModuleCat.{u} R' :=
  (isoCommaRight (ModuleCat.extendScalars D.s) (ModuleCat.extendScalars D.t)).obj X

abbrev moduleGluingComparison
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    (ModuleCat.extendScalars D.s).obj
        (moduleGluingLeftObj (D := D) (X := X)) ⟶
      (ModuleCat.extendScalars D.t).obj
        (moduleGluingRightObj (D := D) (X := X)) :=
  (isoCommaComparison (ModuleCat.extendScalars D.s) (ModuleCat.extendScalars D.t)).app X

theorem moduleGluingComparison_isIso
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    IsIso (moduleGluingComparison D X) := by
  exact isoComma_isIso_hom X

/-- The canonical comparison between the two iterated extensions of scalars
along a commutative square. -/
noncomputable def moduleBaseChangeComparison
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') :
    (ModuleCat.extendScalars D.u ⋙ ModuleCat.extendScalars D.s) ≅
      (ModuleCat.extendScalars D.v ⋙ ModuleCat.extendScalars D.t) := by
  let ecomm : ModuleCat.extendScalars (D.s.comp D.u) ≅
      ModuleCat.extendScalars (D.t.comp D.v) :=
    eqToIso (congrArg (fun f => ModuleCat.extendScalars f) D.comm)
  exact (ModuleCat.extendScalarsComp D.u D.s).symm ≪≫ ecomm ≪≫
    ModuleCat.extendScalarsComp D.v D.t

/-- The source's functor from modules over the lower-right ring to triples of
modules.  Its two components are extension of scalars, and its comparison is
the canonical iterated-extension isomorphism. -/
noncomputable def moduleBaseChangeFunctor
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') :
    ModuleCat.{u} B' ⥤ ModuleGluingCategory D where
  obj L :=
    { obj :=
        { left := (ModuleCat.extendScalars D.u).obj L
          right := (ModuleCat.extendScalars D.v).obj L
          hom := (moduleBaseChangeComparison D).hom.app L }
      property := by
        change IsIso ((moduleBaseChangeComparison D).hom.app L)
        infer_instance }
  map f :=
    ObjectProperty.homMk
      { left := (ModuleCat.extendScalars D.u).map f
        right := (ModuleCat.extendScalars D.v).map f
        w := (moduleBaseChangeComparison D).hom.naturality f }
  map_id := by
    intro L
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp
  map_comp := by
    intro L M N f g
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp

noncomputable abbrev moduleBaseChange
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') :
    ModuleCat.{u} B' ⥤ ModuleGluingCategory D :=
  moduleBaseChangeFunctor D

/-- The common target used to compare the two canonical maps defining the
module pullback. -/
abbrev moduleFiberCommonTarget
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) : ModuleCat.{u} B' :=
  (ModuleCat.restrictScalars (D.s.comp D.u)).obj
    ((ModuleCat.extendScalars D.t).obj X.obj.right)

/-- The map from the `B`-module component to the common target. -/
noncomputable def moduleFiberLeftMap
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    (ModuleCat.restrictScalars D.u).obj X.obj.left ⟶
      moduleFiberCommonTarget D X := by
  let K : ModuleCat.{u} R := (ModuleCat.extendScalars D.t).obj X.obj.right
  let e := ModuleCat.restrictScalarsComp'App D.u D.s (D.s.comp D.u) rfl K
  exact
    (ModuleCat.restrictScalars D.u).map
        ((ModuleCat.extendRestrictScalarsAdj D.s).unit.app X.obj.left ≫
          (ModuleCat.restrictScalars D.s).map X.obj.hom) ≫
      e.inv

/-- The map from the `R'`-module component to the common target. -/
noncomputable def moduleFiberRightMap
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    (ModuleCat.restrictScalars D.v).obj X.obj.right ⟶
      moduleFiberCommonTarget D X := by
  let K : ModuleCat.{u} R := (ModuleCat.extendScalars D.t).obj X.obj.right
  let e := ModuleCat.restrictScalarsComp'App D.v D.t (D.t.comp D.v) rfl K
  exact
    (ModuleCat.restrictScalars D.v).map
        ((ModuleCat.extendRestrictScalarsAdj D.t).unit.app X.obj.right) ≫
      e.inv ≫
      (ModuleCat.restrictScalarsCongr D.comm).inv.app K

/-- The map on the common target induced by a morphism of module triples. -/
def moduleFiberCommonMap
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') {X Y : ModuleGluingCategory D}
    (f : X ⟶ Y) :
    moduleFiberCommonTarget D X ⟶ moduleFiberCommonTarget D Y :=
  (ModuleCat.restrictScalars (D.s.comp D.u)).map
    ((ModuleCat.extendScalars D.t).map f.hom.right)

/-- Naturality of the first map in the categorical module pullback. -/
theorem moduleFiberLeftMap_naturality
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') {X Y : ModuleGluingCategory D}
    (f : X ⟶ Y) :
    (ModuleCat.restrictScalars D.u).map f.hom.left ≫ moduleFiberLeftMap D Y =
      moduleFiberLeftMap D X ≫ moduleFiberCommonMap D f := by
  sorry

/-- Naturality of the second map in the categorical module pullback. -/
theorem moduleFiberRightMap_naturality
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') {X Y : ModuleGluingCategory D}
    (f : X ⟶ Y) :
    (ModuleCat.restrictScalars D.v).map f.hom.right ≫ moduleFiberRightMap D Y =
      moduleFiberRightMap D X ≫ moduleFiberCommonMap D f := by
  sorry

/-- The source's compatible-pair set, written in terms of the canonical
tensor base-change elements. -/
def moduleFiberCompatiblePairs
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    Set ((moduleGluingLeftObj (D := D) (X := X) : Type u) ×
      (moduleGluingRightObj (D := D) (X := X) : Type u)) :=
  {p |
    X.obj.hom ((1 : R) ⊗ₜ[B, D.s] p.1) =
      (1 : R) ⊗ₜ[R', D.t] p.2}

/-- The module fibre product is the categorical pullback of the two maps
whose elementwise condition is `moduleFiberCompatiblePairs`. -/
noncomputable abbrev moduleFiberProduct
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) : ModuleCat.{u} B' :=
  limit (cospan (moduleFiberLeftMap D X) (moduleFiberRightMap D X))

/-- The two coordinate maps of the categorical module fibre product. -/
def moduleFiberProductPair
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D)
    (x : moduleFiberProduct D X) :
    (moduleGluingLeftObj (D := D) (X := X) : Type u) ×
      (moduleGluingRightObj (D := D) (X := X) : Type u) :=
  (limit.π (cospan (moduleFiberLeftMap D X) (moduleFiberRightMap D X))
      WalkingCospan.left x,
    limit.π (cospan (moduleFiberLeftMap D X) (moduleFiberRightMap D X))
      WalkingCospan.right x)

/-- The map between the two categorical module pullbacks induced by a morphism
of triples. -/
noncomputable def moduleFiberProductMap
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') {X Y : ModuleGluingCategory D}
    (f : X ⟶ Y) : moduleFiberProduct D X ⟶ moduleFiberProduct D Y :=
  pullback.lift
    (pullback.fst (moduleFiberLeftMap D X) (moduleFiberRightMap D X) ≫
      (ModuleCat.restrictScalars D.u).map f.hom.left)
    (pullback.snd (moduleFiberLeftMap D X) (moduleFiberRightMap D X) ≫
      (ModuleCat.restrictScalars D.v).map f.hom.right) (by
        simp only [Category.assoc]
        rw [moduleFiberLeftMap_naturality D f, moduleFiberRightMap_naturality D f]
        exact congrArg (fun k => k ≫ moduleFiberCommonMap D f)
          (PullbackCone.condition (limit.cone
            (cospan (moduleFiberLeftMap D X) (moduleFiberRightMap D X)))) )

/-- The compatible-pair pullback is functorial in the module triple. -/
noncomputable def moduleFiberProductRightAdjointCanonical
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') :
    ModuleGluingCategory D ⥤ ModuleCat.{u} B' where
  obj X := moduleFiberProduct D X
  map f := moduleFiberProductMap D f
  map_id := by
    intro X
    apply pullback.hom_ext
    · simp [moduleFiberProductMap]
    · simp [moduleFiberProductMap]
  map_comp := by
    intro X Y Z f g
    apply pullback.hom_ext
    · simp only [moduleFiberProductMap, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.assoc]
      simp
    · simp only [moduleFiberProductMap, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.assoc]
      simp

/-- The categorical pullback and the source's compatible-pair presentation
have the same underlying elements. -/
theorem moduleFiberProduct_pair_is_compatible
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D)
    (x : moduleFiberProduct D X) :
    moduleFiberProductPair D X x ∈ moduleFiberCompatiblePairs D X := by
  sorry

/-- The compatible-pair presentation is equivalent to the underlying set of
the categorical module pullback. -/
theorem moduleFiberProduct_compatiblePairEquiv_exists
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    Nonempty
      ((moduleFiberProduct D X : Type u) ≃
        {p : (moduleGluingLeftObj (D := D) (X := X) : Type u) ×
          (moduleGluingRightObj (D := D) (X := X) : Type u) //
          p ∈ moduleFiberCompatiblePairs D X}) := by
  sorry

/-- Source-facing chosen equivalence between the categorical pullback and its
compatible-pair presentation. -/
noncomputable def moduleFiberProduct_compatiblePairEquiv
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    (moduleFiberProduct D X : Type u) ≃
      {p : (moduleGluingLeftObj (D := D) (X := X) : Type u) ×
        (moduleGluingRightObj (D := D) (X := X) : Type u) //
        p ∈ moduleFiberCompatiblePairs D X} :=
  Classical.choice (moduleFiberProduct_compatiblePairEquiv_exists D X)

/-! ## Base change and the right adjoint -/

/-- The adjunction data asserting that the compatible-pair fibre product is a
right adjoint of the source's module functor. -/
structure ModuleFiberProductAdjunctionData
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') where
  adjunction : moduleBaseChangeFunctor D ⊣ moduleFiberProductRightAdjointCanonical D

/-- The source's module functor has the compatible-pair fibre product as a
right adjoint. -/
theorem moduleFiberProduct_rightAdjoint_exists
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') :
    Nonempty (ModuleFiberProductAdjunctionData D) := by
  sorry

noncomputable def moduleFiberProductAdjunctionData
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') : ModuleFiberProductAdjunctionData D :=
  Classical.choice (moduleFiberProduct_rightAdjoint_exists D)

noncomputable abbrev moduleFiberProductRightAdjoint
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') : ModuleGluingCategory D ⥤ ModuleCat.{u} B' :=
  moduleFiberProductRightAdjointCanonical D

/-- The source-facing adjunction Hom equivalence. -/
noncomputable def moduleFiberProductHomEquiv
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    ((moduleBaseChange D).obj L ⟶ X) ≃
      (L ⟶ (moduleFiberProductRightAdjoint D).obj X) :=
  (moduleFiberProductAdjunctionData D).adjunction.homEquiv L X

/-- The compatible pairs of component maps appearing on the right-hand side
of the source's displayed Hom identity. -/
def moduleCompatibleHomPairs
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    Set (((ModuleCat.extendScalars D.u).obj L ⟶
          moduleGluingLeftObj (D := D) (X := X)) ×
      ((ModuleCat.extendScalars D.v).obj L ⟶
        moduleGluingRightObj (D := D) (X := X))) :=
  {p |
    (moduleBaseChangeComparison D).hom.app L ≫
          (ModuleCat.extendScalars D.t).map p.2 =
    (ModuleCat.extendScalars D.s).map p.1 ≫
        moduleGluingComparison (D := D) (X := X)}

/- The second displayed Hom fibre product in the source, after applying the
tensor--restriction adjunctions, is the ordinary pullback Hom description
for the categorical module pullback. -/
def moduleCompatibleHomPairsAdjoint
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    Set (((L ⟶ (ModuleCat.restrictScalars D.u).obj
          (moduleGluingLeftObj (D := D) (X := X))) ×
      (L ⟶ (ModuleCat.restrictScalars D.v).obj
        (moduleGluingRightObj (D := D) (X := X))))) :=
  {p |
    p.1 ≫ moduleFiberLeftMap D X =
      p.2 ≫ moduleFiberRightMap D X}

/-- The displayed Hom fibre product is equivalent to the adjunction Hom set.
The subtype is the ordinary Lean realization of the fibre product of the two
component Hom sets over the common `R`-Hom set. -/
theorem moduleFiberProductHomPairEquiv_exists
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    Nonempty
      ((L ⟶ moduleFiberProduct D X) ≃
        {p : ((ModuleCat.extendScalars D.u).obj L ⟶
              moduleGluingLeftObj (D := D) (X := X)) ×
          ((ModuleCat.extendScalars D.v).obj L ⟶
            moduleGluingRightObj (D := D) (X := X)) //
          p ∈ moduleCompatibleHomPairs D L X}) := by
  sorry

/-- The second displayed Hom fibre product is equivalent to maps into the
categorical module pullback. -/
theorem moduleFiberProductHomAdjointPairEquiv_exists
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    Nonempty
      ((L ⟶ moduleFiberProduct D X) ≃
        {p : ((L ⟶ (ModuleCat.restrictScalars D.u).obj
                (moduleGluingLeftObj (D := D) (X := X))) ×
            (L ⟶ (ModuleCat.restrictScalars D.v).obj
              (moduleGluingRightObj (D := D) (X := X)))) //
          p ∈ moduleCompatibleHomPairsAdjoint D L X}) := by
  sorry

noncomputable def moduleFiberProductHomAdjointPairEquiv
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    (L ⟶ moduleFiberProduct D X) ≃
      {p : ((L ⟶ (ModuleCat.restrictScalars D.u).obj
              (moduleGluingLeftObj (D := D) (X := X))) ×
          (L ⟶ (ModuleCat.restrictScalars D.v).obj
            (moduleGluingRightObj (D := D) (X := X)))) //
        p ∈ moduleCompatibleHomPairsAdjoint D L X} :=
  Classical.choice (moduleFiberProductHomAdjointPairEquiv_exists D L X)

/-- A chosen source-facing equivalence for the Hom identity. -/
noncomputable def moduleFiberProductHomPairEquiv
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    (L ⟶ moduleFiberProduct D X) ≃
      {p : ((ModuleCat.extendScalars D.u).obj L ⟶
            moduleGluingLeftObj (D := D) (X := X)) ×
        ((ModuleCat.extendScalars D.v).obj L ⟶
          moduleGluingRightObj (D := D) (X := X)) //
        p ∈ moduleCompatibleHomPairs D L X} :=
  Classical.choice (moduleFiberProductHomPairEquiv_exists D L X)

end

end Formalization.Books.MoreAlgebra.Unit05
