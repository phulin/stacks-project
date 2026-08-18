import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Data.Set.Lattice

/-!
# Duality for Schemes, Chapter 1: shared interfaces

Mathlib supplies schemes, their morphism properties, and the categorical
machinery used below.  It does not supply the derived category of
quasi-coherent sheaves on an arbitrary scheme.  This file therefore records
the smallest source-facing interface for those derived categories.  The
operations are genuine data (rather than propositions asserting their
existence), so the declarations in the section files can state the
book's maps and isomorphisms without replacing them by `True`.
-/

namespace Formalization.Books.Duality.Unit01

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v w

noncomputable section

abbrev Scheme := AlgebraicGeometry.Scheme

abbrev SchemeMorphism {X Y : Scheme.{u}} := X ⟶ Y

/-! ## Derived categories attached to schemes -/

class SchemeDerivedContext (S : Type u) where
  Obj : S → Type v
  category : ∀ X : S, Category.{v} (Obj X)
  zero : ∀ X : S, HasZeroMorphisms (Obj X)
  structureSheaf : ∀ X : S, Obj X
  tensor : ∀ X : S, Obj X → Obj X → Obj X
  directSum : ∀ X : S, (ℕ → Obj X) → Obj X
  internalHom : ∀ X : S, Obj X → Obj X → Obj X
  affineInternalHom : ∀ X : S, Obj X → Obj X → Obj X
  evaluationMap : ∀ X : S, (K L M : Obj X) →
    tensor X (internalHom X L M) K ⟶ internalHom X (internalHom X K L) M
  shift : ∀ X : S, ℤ → Obj X → Obj X
  isQuasiCoherent : ∀ X : S, Obj X → Prop
  isCoherent : ∀ X : S, Obj X → Prop
  isPerfect : ∀ X : S, Obj X → Prop
  isInvertible : ∀ X : S, Obj X → Prop
  isBoundedAbove : ∀ X : S, Obj X → Prop
  isBoundedBelow : ∀ X : S, Obj X → Prop
  isBounded : ∀ X : S, Obj X → Prop
  isFiniteTorDimension : ∀ X : S, Obj X → Prop
  isFiniteInjectiveDimension : ∀ X : S, Obj X → Prop
  isPseudoCoherent : ∀ X : S, Obj X → Prop
  supportLabel : S → Type u
  isSupportedOn : ∀ {X : S}, supportLabel X → Obj X → Prop
  isLocallyDualizing : ∀ X : S, Obj X → Prop
  isUniversallyCatenary : ∀ _X : S, Prop
  isDimensionFunction : ∀ X : S, (supportLabel X → ℤ) → Prop
  sheafExt : ∀ X : S, ℤ → Obj X → Obj X → Obj X
  supportDimension : ∀ X : S, Obj X → supportLabel X → ℕ
  depth : ∀ X : S, Obj X → supportLabel X → ℕ
  isInSupport : ∀ X : S, Obj X → supportLabel X → Prop

abbrev DerivedObject (X : S) [SchemeDerivedContext S] :=
  SchemeDerivedContext.Obj X

instance derivedObjectCategory (X : S) [SchemeDerivedContext S] :
    Category.{v} (DerivedObject X) :=
  SchemeDerivedContext.category X

instance derivedObjectZero (X : S) [SchemeDerivedContext S] :
    HasZeroMorphisms (DerivedObject X) :=
  SchemeDerivedContext.zero X

def StructureSheaf {S : Type u} [SchemeDerivedContext S] (X : S) : DerivedObject X :=
  SchemeDerivedContext.structureSheaf X

def Tensor {S : Type u} [SchemeDerivedContext S] {X : S}
    (K L : DerivedObject X) : DerivedObject X :=
  SchemeDerivedContext.tensor X K L

def DirectSum {S : Type u} [SchemeDerivedContext S] {X : S}
    (K : ℕ → DerivedObject X) : DerivedObject X :=
  SchemeDerivedContext.directSum X K

def InternalHom {S : Type u} [SchemeDerivedContext S] {X : S}
    (K L : DerivedObject X) : DerivedObject X :=
  SchemeDerivedContext.internalHom X K L

def AffineInternalHom {S : Type u} [SchemeDerivedContext S] {X : S}
    (K L : DerivedObject X) : DerivedObject X :=
  SchemeDerivedContext.affineInternalHom X K L

def EvaluationMap {S : Type u} [SchemeDerivedContext S] {X : S}
    (K L M : DerivedObject X) :
    Tensor (InternalHom L M) K ⟶ InternalHom (InternalHom K L) M :=
  SchemeDerivedContext.evaluationMap X K L M

def Shift {S : Type u} [SchemeDerivedContext S] {X : S}
    (K : DerivedObject X) (n : ℤ) : DerivedObject X :=
  SchemeDerivedContext.shift X n K

def IsQuasiCoherent {S : Type u} [SchemeDerivedContext S]
    {X : S} (K : DerivedObject X) : Prop :=
  SchemeDerivedContext.isQuasiCoherent X K

def IsCoherent {S : Type u} [SchemeDerivedContext S]
    {X : S} (K : DerivedObject X) : Prop :=
  SchemeDerivedContext.isCoherent X K

def IsPerfectObject {S : Type u} [SchemeDerivedContext S]
    {X : S} (K : DerivedObject X) : Prop :=
  SchemeDerivedContext.isPerfect X K

def IsInvertibleObject {S : Type u} [SchemeDerivedContext S]
    {X : S} (K : DerivedObject X) : Prop :=
  SchemeDerivedContext.isInvertible X K

def IsBoundedAbove {S : Type u} [SchemeDerivedContext S]
    {X : S} (K : DerivedObject X) : Prop :=
  SchemeDerivedContext.isBoundedAbove X K

def IsBoundedBelow {S : Type u} [SchemeDerivedContext S]
    {X : S} (K : DerivedObject X) : Prop :=
  SchemeDerivedContext.isBoundedBelow X K

def IsBounded {S : Type u} [SchemeDerivedContext S]
    {X : S} (K : DerivedObject X) : Prop :=
  SchemeDerivedContext.isBounded X K

def HasFiniteTorDimension {S : Type u} [SchemeDerivedContext S]
    {X : S} (K : DerivedObject X) : Prop :=
  SchemeDerivedContext.isFiniteTorDimension X K

def HasFiniteInjectiveDimension {S : Type u} [SchemeDerivedContext S]
    {X : S} (K : DerivedObject X) : Prop :=
  SchemeDerivedContext.isFiniteInjectiveDimension X K

def IsPseudoCoherent {S : Type u} [SchemeDerivedContext S]
    {X : S} (K : DerivedObject X) : Prop :=
  SchemeDerivedContext.isPseudoCoherent X K

def IsSupportedOn {S : Type u} [SchemeDerivedContext S]
    {X : S} (T : SchemeDerivedContext.supportLabel X) (K : DerivedObject X) : Prop :=
  SchemeDerivedContext.isSupportedOn T K

def IsDualizingComplexOn {S : Type u} [SchemeDerivedContext S]
    {X : S} (K : DerivedObject X) : Prop :=
  SchemeDerivedContext.isLocallyDualizing X K

def IsUniversallyCatenary {S : Type u} [SchemeDerivedContext S] (X : S) : Prop :=
  SchemeDerivedContext.isUniversallyCatenary X

def IsDimensionFunction {S : Type u} [SchemeDerivedContext S]
    {X : S} (δ : SchemeDerivedContext.supportLabel X → ℤ) : Prop :=
  SchemeDerivedContext.isDimensionFunction X δ

def SheafExt {S : Type u} [SchemeDerivedContext S] {X : S}
    (i : ℤ) (F K : DerivedObject X) : DerivedObject X :=
  SchemeDerivedContext.sheafExt X i F K

def SupportDimension {S : Type u} [SchemeDerivedContext S] {X : S}
    (K : DerivedObject X) (x : SchemeDerivedContext.supportLabel X) : ℕ :=
  SchemeDerivedContext.supportDimension X K x

def Depth {S : Type u} [SchemeDerivedContext S] {X : S}
    (K : DerivedObject X) (x : SchemeDerivedContext.supportLabel X) : ℕ :=
  SchemeDerivedContext.depth X K x

def InSupport {S : Type u} [SchemeDerivedContext S] {X : S}
    (K : DerivedObject X) (x : SchemeDerivedContext.supportLabel X) : Prop :=
  SchemeDerivedContext.isInSupport X K x

def Isomorphic {S : Type u} [SchemeDerivedContext S]
    {X : S} (K L : DerivedObject X) : Prop :=
  Nonempty (K ≅ L)

/-! ## Derived pushforward, pullback, and adjoints -/

class SchemeDerivedOperations (S : Type u) [Category.{w, u} S]
    [SchemeDerivedContext S] where
  pushforward : ∀ {X Y : S}, (X ⟶ Y) → DerivedObject X ⥤ DerivedObject Y
  pullback : ∀ {X Y : S}, (X ⟶ Y) → DerivedObject Y ⥤ DerivedObject X
  torIndependent : ∀ {X Y Z : S}, (X ⟶ Z) → (Y ⟶ Z) → Prop

def RPushforward {S : Type u} [Category.{w, u} S] [SchemeDerivedContext S]
    [SchemeDerivedOperations S] {X Y : S} (f : X ⟶ Y) :
    DerivedObject X ⥤ DerivedObject Y :=
  SchemeDerivedOperations.pushforward f

def LPullback {S : Type u} [Category.{w, u} S] [SchemeDerivedContext S]
    [SchemeDerivedOperations S] {X Y : S} (f : X ⟶ Y) :
    DerivedObject Y ⥤ DerivedObject X :=
  SchemeDerivedOperations.pullback f

structure RightAdjointData {S : Type u} [Category.{w, u} S]
    [SchemeDerivedContext S] [SchemeDerivedOperations S]
    {X Y : S} (f : X ⟶ Y) where
  rightAdjoint : DerivedObject Y ⥤ DerivedObject X
  adjunction : Nonempty (Adjunction (RPushforward f) rightAdjoint)
  sheafyTrace : ∀ (L : DerivedObject X) (K : DerivedObject Y),
    (RPushforward f).obj (InternalHom L (rightAdjoint.obj K)) ⟶
      InternalHom ((RPushforward f).obj L) K

noncomputable def Trace {S : Type u} [Category.{w, u} S]
    [SchemeDerivedContext S] [SchemeDerivedOperations S]
    {X Y : S} {f : X ⟶ Y} (a : RightAdjointData f)
    (K : DerivedObject Y) :
    (RPushforward f).obj (a.rightAdjoint.obj K) ⟶ K :=
  (Classical.choice a.adjunction).counit.app K

/-! ## Cartesian squares and their objectwise base-change maps -/

structure CartesianSquare (S : Type u) [Category.{w, u} S]
    [HasPullbacks S] where
  X' : S
  X : S
  Y' : S
  Y : S
  g' : X' ⟶ X
  f' : X' ⟶ Y'
  g : Y' ⟶ Y
  f : X ⟶ Y
  comm : g' ≫ f = f' ≫ g
  isPullback : IsPullback g' f' f g

structure BaseChangeData {S : Type u} [Category.{w, u} S]
    [HasPullbacks S] [SchemeDerivedContext S] [SchemeDerivedOperations S]
    (square : CartesianSquare S)
    (a : RightAdjointData square.f)
    (a' : RightAdjointData square.f') where
  map : ∀ K : DerivedObject square.Y,
    (LPullback square.g').obj (a.rightAdjoint.obj K) ⟶
      a'.rightAdjoint.obj ((LPullback square.g).obj K)

def BaseChangeMap {S : Type u} [Category.{w, u} S]
    [HasPullbacks S] [SchemeDerivedContext S] [SchemeDerivedOperations S]
    {square : CartesianSquare S} {a : RightAdjointData square.f}
    {a' : RightAdjointData square.f'} (b : BaseChangeData square a a')
    (K : DerivedObject square.Y) :
    (LPullback square.g').obj (a.rightAdjoint.obj K) ⟶
      a'.rightAdjoint.obj ((LPullback square.g).obj K) :=
  b.map K

def IsIsoBaseChange {S : Type u} [Category.{w, u} S]
    [HasPullbacks S] [SchemeDerivedContext S] [SchemeDerivedOperations S]
    {square : CartesianSquare S} {a : RightAdjointData square.f}
    {a' : RightAdjointData square.f'} (b : BaseChangeData square a a') : Prop :=
  ∀ K : DerivedObject square.Y, IsIso (BaseChangeMap b K)

/-! ## Source-facing geometric predicates -/

def IsNoetherianScheme (X : Scheme.{u}) : Prop :=
  AlgebraicGeometry.IsNoetherian X

def IsQuasiCompactMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.QuasiCompact f

def IsQuasiSeparatedMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.QuasiSeparated f

def IsFlatMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.Flat f

def IsLocallyOfFiniteTypeMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.LocallyOfFiniteType f

def IsLocallyQuasiFiniteMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.LocallyQuasiFinite f

def IsFinitePresentationMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.QuasiCompact f ∧ AlgebraicGeometry.LocallyOfFinitePresentation f

def IsSeparatedMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.IsSeparated f

def IsAffineMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.IsAffineHom f

def IsEtaleMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.Etale f

def IsSmoothMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.Smooth f

def IsSmoothOfRelativeDimensionMorphism {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : ℕ) : Prop :=
  AlgebraicGeometry.SmoothOfRelativeDimension d f

def IsProperMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.IsProper f

def IsFiniteMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.IsFinite f

def IsClosedImmersionMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.IsClosedImmersion f

def IsOpenImmersionMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.IsOpenImmersion f

def IsTorIndependent {X Y Z : Scheme.{u}} [SchemeDerivedContext Scheme]
    [SchemeDerivedOperations Scheme] (f : X ⟶ Z) (g : Y ⟶ Z) : Prop :=
  SchemeDerivedOperations.torIndependent f g

end

end Formalization.Books.Duality.Unit01
