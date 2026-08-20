import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Cohomology.Unit03.DerivedFunctors
import Formalization.Books.Derived.Unit08
import Formalization.Books.Derived.Unit10.DistinguishedTriangles
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Sheaves.Unit25.RingedSpaces
import Formalization.Books.Sheaves.Unit31.Infrastructure
import Mathlib.Order.Interval.Set.Basic

/-!
# Cohomology of Sheaves, Chapter 40: Tor dimension

This file formalizes the Tor-amplitude statements for derived categories of
modules on a ringed space.  The derived tensor product and flat-complex
interfaces are those of Cohomology Chapter 19.  The three derived functors
which the source uses (restriction to an open, pullback, and taking a stalk)
are exposed through the usual derived-functor data records; their
construction from the corresponding exact functors is left for the proof
stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Opposite
open Set
open TopologicalSpace
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11

universe v

namespace Formalization.Books.Cohomology.Unit40

abbrev RingedSpace := Formalization.Books.Sheaves.Unit25.RingedSpace

abbrev RingedSpaceHom := Formalization.Books.Sheaves.Unit25.RingedSpaceHom

/-! ## Ringed-space derived categories -/

abbrev Mod (X : RingedSpace.{v}) :=
  Formalization.Books.Sheaves.Unit10.Mod X.structureSheaf

noncomputable instance ringedSpaceModule_hasDerivedCategory
    (X : RingedSpace.{v}) : HasDerivedCategory (Mod X) :=
  HasDerivedCategory.standard _

abbrev Comp (X : RingedSpace.{v}) :=
  CochainComplex (Mod X) ℤ

abbrev D (X : RingedSpace.{v}) :=
  DerivedCategory (Mod X)

noncomputable abbrev derivedQuotient (X : RingedSpace.{v}) :
    CochainComplex (Mod X) ℤ ⥤ DerivedCategory (Mod X) :=
  DerivedCategory.Q (C := Mod X)

noncomputable abbrev derivedCohomology (X : RingedSpace.{v}) (i : ℤ) :
    D X ⥤ Mod X :=
  DerivedCategory.homologyFunctor (Mod X) i

noncomputable abbrev moduleObject {X : RingedSpace.{v}}
    (F : Mod X) : D X :=
  (DerivedCategory.singleFunctor (Mod X) 0).obj F

/- A derived tensor product is the functor supplied by the canonical
   construction on sheaves of modules.  Its interface is kept local because
   the existing Chapter 19 implementation is specialized to commutative
   sheaves of rings, whereas a ringed space here uses the Chapter 10
   `RingSheaf` model. -/
structure DerivedTensorData (X : RingedSpace.{v}) where
  functor : (D X × D X) ⥤ D X

theorem existsDerivedTensorData (X : RingedSpace.{v}) :
    Nonempty (DerivedTensorData X) := by
  sorry

noncomputable def derivedTensorData (X : RingedSpace.{v}) :
    DerivedTensorData X :=
  Classical.choice (existsDerivedTensorData X)

noncomputable abbrev derivedTensorObject {X : RingedSpace.{v}}
    (E F : D X) : D X :=
  (derivedTensorData X).functor.obj (E, F)

/- The ordinary tensor product used in the flatness predicate is the
   corresponding module-level canonical construction. -/
structure ModuleTensorData (X : RingedSpace.{v}) where
  functor : (Mod X × Mod X) ⥤ Mod X

theorem existsModuleTensorData (X : RingedSpace.{v}) :
    Nonempty (ModuleTensorData X) := by
  sorry

noncomputable def moduleTensorData (X : RingedSpace.{v}) :
    ModuleTensorData X :=
  Classical.choice (existsModuleTensorData X)

def tensorSlice {C D : Type*} [Category C] [Category D]
    (F : (C × C) ⥤ D) (M : C) : C ⥤ D where
  obj A := F.obj (A, M)
  map f := F.map (f, 𝟙 M)
  map_id A := by rw [← F.map_id]; rfl
  map_comp f g := by
    rw [← F.map_comp]
    congr 1
    simp

noncomputable abbrev tensorRightFunctor (X : RingedSpace.{v})
    (F : Mod X) : Mod X ⥤ Mod X :=
  tensorSlice (moduleTensorData X).functor F

def IsFlatModule (X : RingedSpace.{v}) (F : Mod X) : Prop :=
  IsExact (tensorRightFunctor X F)

/-! ## Restriction, pullback, and stalk derived functors -/

/- The source uses the derived functor induced by restriction to an open.
   `openModuleRestrictionFunctor` is the canonical module-level functor; the
   record below is the derived-category interface it induces. -/
structure OpenRestrictionData (X : RingedSpace.{v}) (U : Opens X.carrier) where
  functor : D X ⥤ D (Formalization.Books.Sheaves.Unit22.ringedOpenSubspace X U)
  exact : Nonempty (ExactTriangulatedFunctorData functor)

theorem existsOpenRestrictionData (X : RingedSpace.{v})
    (U : Opens X.carrier) : Nonempty (OpenRestrictionData X U) := by
  sorry

noncomputable def openRestrictionData (X : RingedSpace.{v})
    (U : Opens X.carrier) : OpenRestrictionData X U :=
  Classical.choice (existsOpenRestrictionData X U)

noncomputable abbrev derivedOpenRestriction (X : RingedSpace.{v})
    (U : Opens X.carrier) : D X ⥤
      D (Formalization.Books.Sheaves.Unit22.ringedOpenSubspace X U) :=
  (openRestrictionData X U).functor

/- The same derived-functor interface records `Lf^*` for an arbitrary
   morphism of ringed spaces. -/
structure DerivedPullbackData {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) where
  functor : D Y ⥤ D X
  exact : Nonempty (ExactTriangulatedFunctorData functor)

theorem existsDerivedPullbackData {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) : Nonempty (DerivedPullbackData f) := by
  sorry

noncomputable def derivedPullbackData {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) : DerivedPullbackData f :=
  Classical.choice (existsDerivedPullbackData f)

noncomputable abbrev derivedPullback {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) : D Y ⥤ D X :=
  (derivedPullbackData f).functor

/- Stalks are the pullbacks along the one-point morphisms.  We keep the
   stalk functor explicit so the object in the stalkwise criterion has a
   canonical type. -/
abbrev StalkRing (X : RingedSpace.{v}) (x : X.carrier) :=
  TopCat.Presheaf.stalk (C := RingCat) X.structureSheaf.obj x

abbrev StalkMod (X : RingedSpace.{v}) (x : X.carrier) :=
  ModuleCat (StalkRing X x)

abbrev StalkD (X : RingedSpace.{v}) (x : X.carrier) :=
  DerivedCategory (StalkMod X x)

noncomputable instance stalkModule_hasDerivedCategory
    (X : RingedSpace.{v}) (x : X.carrier) :
    HasDerivedCategory (StalkMod X x) :=
  HasDerivedCategory.standard _

structure StalkData (X : RingedSpace.{v}) (x : X.carrier) where
  functor : D X ⥤ StalkD X x
  exact : Nonempty (ExactTriangulatedFunctorData functor)

theorem existsStalkData (X : RingedSpace.{v}) (x : X.carrier) :
    Nonempty (StalkData X x) := by
  sorry

noncomputable def stalkData (X : RingedSpace.{v}) (x : X.carrier) :
    StalkData X x :=
  Classical.choice (existsStalkData X x)

noncomputable abbrev derivedStalk (X : RingedSpace.{v}) (x : X.carrier) :
    D X ⥤ StalkD X x :=
  (stalkData X x).functor

structure StalkDerivedTensorData (X : RingedSpace.{v}) (x : X.carrier) where
  functor : (StalkD X x × StalkD X x) ⥤ StalkD X x

theorem existsStalkDerivedTensorData (X : RingedSpace.{v}) (x : X.carrier) :
    Nonempty (StalkDerivedTensorData X x) := by
  sorry

noncomputable def stalkDerivedTensorData (X : RingedSpace.{v})
    (x : X.carrier) : StalkDerivedTensorData X x :=
  Classical.choice (existsStalkDerivedTensorData X x)

noncomputable abbrev stalkDerivedTensor (X : RingedSpace.{v})
    (x : X.carrier) : StalkD X x → StalkD X x → StalkD X x :=
  fun E F => (stalkDerivedTensorData X x).functor.obj (E, F)

/-! ## Tor amplitude and tor dimension -/

/-- `E` has tor-amplitude in `[a, b]` when its derived tensor with every
module has no cohomology outside that interval. -/
def TorAmplitude (X : RingedSpace.{v}) (E : D X) (a b : ℤ) : Prop :=
  ∀ (F : Mod X) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((derivedCohomology X i).obj
      (derivedTensorObject E (moduleObject F)))

def StalkTorAmplitude (X : RingedSpace.{v}) (x : X.carrier)
    (E : StalkD X x) (a b : ℤ) : Prop :=
  ∀ (F : StalkMod X x) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((DerivedCategory.homologyFunctor (StalkMod X x) i).obj
      (stalkDerivedTensor X x E
        ((DerivedCategory.singleFunctor (StalkMod X x) 0).obj F)))

/-- An object has finite tor dimension when it has finite tor-amplitude. -/
def HasFiniteTorDimension (X : RingedSpace.{v}) (E : D X) : Prop :=
  ∃ a b : ℤ, a ≤ b ∧ TorAmplitude X E a b

/-- An open family witnesses locally finite tor dimension. -/
def LocallyHasFiniteTorDimension (X : RingedSpace.{v}) (E : D X) : Prop :=
    ∃ (ι : Type v) (U : ι → Opens X.carrier),
    (∀ x : X.carrier, ∃ i : ι, x ∈ U i) ∧
      ∀ i : ι,
        HasFiniteTorDimension
          (Formalization.Books.Sheaves.Unit22.ringedOpenSubspace X (U i))
          ((derivedOpenRestriction X (U i)).obj E)

/-- A module has tor dimension at most `d` when its degree-zero object has
tor-amplitude in `[-d, 0]`. -/
def ModuleTorDimensionLE {X : RingedSpace.{v}} (F : Mod X) (d : ℤ) : Prop :=
  TorAmplitude X (moduleObject F) (-d) 0

/-- The source's observation that finite tor dimension implies bounded
cohomology. -/
theorem hasFiniteTorDimension_derivedBounded
    (X : RingedSpace.{v}) (E : D X)
    (hE : HasFiniteTorDimension X E) :
    derivedBoundedProperty (Mod X) E := by
  sorry

/-! ## Flat representatives -/

/-- A complex is supported in `[a, b]`. -/
def IsSupportedIn {X : RingedSpace.{v}} (K : Comp X) (a b : ℤ) : Prop :=
  ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)

def TermwiseFlat {X : RingedSpace.{v}} (K : Comp X) : Prop :=
  ∀ i : ℤ, IsFlatModule X (K.X i)

/-- The cokernel of the differential out of degree `i`. -/
noncomputable def cokerDifferential {X : RingedSpace.{v}}
    (K : Comp X) (i : ℤ) : Mod X :=
  cokernel (K.d i (i + 1))

/-- The last-flat-term lemma for a bounded-above flat complex. -/
theorem cokerDifferential_flat_of_torAmplitude
    (X : RingedSpace.{v}) (K : Comp X) (a b : ℤ)
    (hK : IsBoundedAbove K) (hflat : TermwiseFlat K)
    (hamp : TorAmplitude X ((derivedQuotient X).obj K) a b) :
    IsFlatModule X (cokerDifferential K (a - 1)) := by
  sorry

/-- Tor-amplitude is equivalent to having a flat representative supported in
the same interval. -/
theorem torAmplitude_iff_bounded_flat_complex
    (X : RingedSpace.{v}) (E : D X) (a b : ℤ) :
    TorAmplitude X E a b ↔
      ∃ K : Comp X, TermwiseFlat K ∧ IsSupportedIn K a b ∧
        Nonempty ((derivedQuotient X).obj K ≅ E) := by
  sorry

/-! ## Pullback and stalk criteria -/

theorem torAmplitude_pullback
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (E : D Y) (a b : ℤ)
    (hE : TorAmplitude Y E a b) :
    TorAmplitude X ((derivedPullback f).obj E) a b := by
  sorry

theorem torAmplitude_iff_stalkwise
    (X : RingedSpace.{v}) (E : D X) (a b : ℤ) :
    TorAmplitude X E a b ↔
      ∀ x : X.carrier,
        StalkTorAmplitude X x ((derivedStalk X x).obj E) a b := by
  sorry

/-! ## Triangles, tensor products, and summands -/

theorem torAmplitude_of_distinguishedTriangle₁₂
    (X : RingedSpace.{v}) (T : Triangle (D X))
    (hT : T ∈ distTriang (D X)) (a b : ℤ)
    (h₁ : TorAmplitude X T.obj₁ (a + 1) (b + 1))
    (h₂ : TorAmplitude X T.obj₂ a b) :
    TorAmplitude X T.obj₃ a b := by
  sorry

theorem torAmplitude_of_distinguishedTriangle₁₃
    (X : RingedSpace.{v}) (T : Triangle (D X))
    (hT : T ∈ distTriang (D X)) (a b : ℤ)
    (h₁ : TorAmplitude X T.obj₁ a b)
    (h₃ : TorAmplitude X T.obj₃ a b) :
    TorAmplitude X T.obj₂ a b := by
  sorry

theorem torAmplitude_of_distinguishedTriangle₂₃
    (X : RingedSpace.{v}) (T : Triangle (D X))
    (hT : T ∈ distTriang (D X)) (a b : ℤ)
    (h₂ : TorAmplitude X T.obj₂ (a + 1) (b + 1))
    (h₃ : TorAmplitude X T.obj₃ a b) :
    TorAmplitude X T.obj₁ (a + 1) (b + 1) := by
  sorry

theorem torAmplitude_tensor
    (X : RingedSpace.{v}) (K L : D X) (a b c d : ℤ)
    (hK : TorAmplitude X K a b) (hL : TorAmplitude X L c d) :
    TorAmplitude X (derivedTensorObject K L) (a + c) (b + d) := by
  sorry

theorem torAmplitude_of_biprod
    (X : RingedSpace.{v}) (K L : D X) (a b : ℤ)
    (hKL : TorAmplitude X (K ⊞ L) a b) :
    TorAmplitude X K a b ∧ TorAmplitude X L a b := by
  sorry

end Formalization.Books.Cohomology.Unit40
