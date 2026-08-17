import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Exact.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.Localization.Away.Basic
import Formalization.Books.Categories.Unit31.TwoFibreProducts

/-!
# More on Algebra, Chapter 5: Fibre products of rings, I

This file uses Mathlib's canonical pullback subrings and subalgebras.  The
category of triples of modules is the earlier chapter's `IsoComma`
construction, and the module fibre product is the categorical pullback in
`ModuleCat`; the source's compatible-pair description is recorded alongside
that construction.
-/

namespace Formalization.Books.MoreAlgebra.Unit05

open CategoryTheory
open CategoryTheory.Limits
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

/-! ## Modules over a cartesian square -/

/-- A commutative square of rings together with its cartesian property. -/
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
  /-- The square is cartesian in commutative rings. -/
  cartesian :
    IsPullback
      (CommRingCat.ofHom u)
      (CommRingCat.ofHom v)
      (CommRingCat.ofHom s)
      (CommRingCat.ofHom t)

@[simp]
theorem RingSquare.comm_apply
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (x : B') :
    D.s (D.u x) = D.t (D.v x) :=
  DFunLike.congr_fun D.comm x

/-- The category of module triples `(N, M', φ)` over a cartesian square.
The earlier Categories chapter supplies the iso-comma implementation. -/
abbrev ModuleGluingCategory
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') :=
  Formalization.Books.Categories.Unit31.TwoFibreProductCategory
    (ModuleCat.extendScalars D.s) (ModuleCat.extendScalars D.t)

/-- The two module components of an object of `ModuleGluingCategory`.  These
abbreviations keep projections out of binder positions, where Lean parses a
dotted projection as a binder name. -/
abbrev moduleGluingLeftObj
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) : ModuleCat.{u} B :=
  X.obj.left

abbrev moduleGluingRightObj
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) : ModuleCat.{u} R' :=
  X.obj.right

abbrev moduleGluingComparison
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    (ModuleCat.extendScalars D.s).obj
        (moduleGluingLeftObj (D := D) (X := X)) ⟶
      (ModuleCat.extendScalars D.t).obj
        (moduleGluingRightObj (D := D) (X := X)) :=
  X.obj.hom

theorem moduleGluingComparison_isIso
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (X : ModuleGluingCategory D) :
    IsIso (moduleGluingComparison D X) := by
  infer_instance

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
noncomputable def moduleFiberProduct
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

/-- Data specifying the source's base-change functor, including its canonical
objectwise identifications with the two extension-of-scalars components. -/
structure ModuleBaseChangeData
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') where
  functor : ModuleCat.{u} B' ⥤ ModuleGluingCategory D
  left_iso : ∀ L : ModuleCat.{u} B',
      moduleGluingLeftObj (D := D) (X := functor.obj L) ≅
        (ModuleCat.extendScalars D.u).obj L
  right_iso : ∀ L : ModuleCat.{u} B',
      moduleGluingRightObj (D := D) (X := functor.obj L) ≅
        (ModuleCat.extendScalars D.v).obj L
  comparison : ∀ L : ModuleCat.{u} B',
    (ModuleCat.extendScalars D.s).obj ((ModuleCat.extendScalars D.u).obj L) ≅
      (ModuleCat.extendScalars D.t).obj ((ModuleCat.extendScalars D.v).obj L)

/-- The canonical base-change functor and its objectwise comparison data. -/
theorem moduleBaseChange_exists
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') : Nonempty (ModuleBaseChangeData D) := by
  sorry

noncomputable def moduleBaseChangeData
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') : ModuleBaseChangeData D :=
  Classical.choice (moduleBaseChange_exists D)

noncomputable abbrev moduleBaseChange
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') : ModuleCat.{u} B' ⥤ ModuleGluingCategory D :=
  (moduleBaseChangeData D).functor

/-- The right-adjoint data in the source lemma.  The objectwise comparison
to `moduleFiberProduct` makes the compatible-pair functor explicit while the
adjunction is retained in Mathlib's categorical form. -/
structure ModuleFiberProductAdjunctionData
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') where
  rightAdjoint : ModuleGluingCategory D ⥤ ModuleCat.{u} B'
  rightAdjoint_iso : ∀ X : ModuleGluingCategory D,
    rightAdjoint.obj X ≅ moduleFiberProduct D X
  adjunction : (moduleBaseChangeData D).functor ⊣ rightAdjoint

/-- The module functor of the source has `moduleFiberProduct` as a right
adjoint. -/
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
  (moduleFiberProductAdjunctionData D).rightAdjoint

/-- The source-facing adjunction Hom equivalence. -/
noncomputable def moduleFiberProductHomEquiv
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : RingSquare R R' B B') (L : ModuleCat.{u} B')
    (X : ModuleGluingCategory D) :
    ((moduleBaseChange D).obj L ⟶ X) ≃
      (L ⟶ (moduleFiberProductAdjunctionData D).rightAdjoint.obj X) :=
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
    ((moduleBaseChangeData D).comparison L).hom ≫
          (ModuleCat.extendScalars D.t).map p.2 =
      (ModuleCat.extendScalars D.s).map p.1 ≫
        moduleGluingComparison (D := D) (X := X)}

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
