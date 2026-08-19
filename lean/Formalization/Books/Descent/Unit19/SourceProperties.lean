import Formalization.Books.Descent.Unit19.TargetAndApplication
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.PrimeField
import Mathlib.RingTheory.Algebraic.Defs

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Formalization.Books.Descent.Unit19

/-! ## Properties local on the source -/

def Precompose (P : SchemeMorphismProperty) : Prop :=
  ∀ {X X' Y : Scheme.{u}} (a : X' ⟶ X) (f : X ⟶ Y), P f → P (a ≫ f)

def IsZariskiLocalOnSource (P : SchemeMorphismProperty) : Prop :=
  IsLocalOnSource .zariski P

def IsFppfLocalOnSource (P : SchemeMorphismProperty) : Prop :=
  IsLocalOnSource .fppf P

def IsFpqcLocalOnSource (P : SchemeMorphismProperty) : Prop :=
  IsLocalOnSource .fpqc P

def IsEtaleLocalOnSource (P : SchemeMorphismProperty) : Prop :=
  IsLocalOnSource .etale P

def IsSmoothLocalOnSource (P : SchemeMorphismProperty) : Prop :=
  IsLocalOnSource .smooth P

def IsSyntomicLocalOnSource (P : SchemeMorphismProperty) : Prop :=
  IsLocalOnSource .syntomic P

theorem precompose_property_local_on_source
    (τ : Topology) (P : SchemeMorphismProperty)
    (hP : IsLocalOnSource τ P) {X X' Y : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (ha : coveringMorphismProperty τ a)
    (hf : P f) : P (a ≫ f) := by sorry

noncomputable def largestOpenOfSource
    (τ : Topology) (P : SchemeMorphismProperty)
    (_hP : IsLocalOnSource τ P) {X Y : Scheme.{u}} (f : X ⟶ Y) : X.Opens :=
  sSup {W : X.Opens | P (W.ι ≫ f)}

theorem largestOpenOfSource_is_largest
    (τ : Topology) (P : SchemeMorphismProperty)
    (hP : IsLocalOnSource τ P) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P ((largestOpenOfSource τ P hP f).ι ≫ f) ∧
      ∀ W : X.Opens, P (W.ι ≫ f) → W ≤ largestOpenOfSource τ P hP f := by sorry

theorem largestOpenOfSource_preimage
    (τ : Topology) (P : SchemeMorphismProperty)
    (hP : IsLocalOnSource τ P) {X X' Y : Scheme.{u}} (f : X ⟶ Y)
    (a : X' ⟶ X) (ha : coveringMorphismProperty τ a) :
    largestOpenOfSource τ P hP (a ≫ f) =
      a ⁻¹ᵁ largestOpenOfSource τ P hP f := by sorry

def AffineSourceDescent (P : SchemeMorphismProperty) (τ : Topology) : Prop :=
  ∀ {X' X Y : Scheme.{u}} (a : X' ⟶ X) (f : X ⟶ Y),
    IsAffine X' → IsAffine X → Surjective a →
    coveringMorphismProperty τ a → P (a ≫ f) → P f

def StandardSourceCoveringMorphism (τ : Topology) : SchemeMorphismProperty :=
  coveringMorphismProperty τ

theorem affine_source_descent_standard_cover
    (P : SchemeMorphismProperty) (τ : Topology) :
    AffineSourceDescent P τ ↔
      ∀ {X' X Y : Scheme.{u}} (a : X' ⟶ X) (f : X ⟶ Y),
        IsAffine X' → IsAffine X → Surjective a →
        StandardSourceCoveringMorphism τ a → P (a ≫ f) → P f := by sorry

theorem local_on_source_of_affine_criterion
    (τ : Topology) (P : SchemeMorphismProperty)
    (hpre : Precompose P)
    (hsource : IsZariskiLocalOnSource P)
    (htarget : IsZariskiLocalOnTarget P)
    (haffine : AffineSourceDescent P τ) : IsLocalOnSource τ P := by sorry

/-! ## The source-local examples -/

def InjectiveOnStalks {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ x : X, Function.Injective (f.stalkMap x).hom

theorem flat_isFpqcLocalOnSource : IsFpqcLocalOnSource (@Flat) := by sorry

theorem injectiveOnStalks_isFpqcLocalOnSource :
    IsFpqcLocalOnSource (fun _ _ f => InjectiveOnStalks f) := by sorry

theorem locallyOfFinitePresentation_isFppfLocalOnSource :
    IsFppfLocalOnSource (@LocallyOfFinitePresentation) := by sorry

theorem locallyOfFiniteType_isFppfLocalOnSource :
    IsFppfLocalOnSource (@LocallyOfFiniteType) := by sorry

theorem open_isFppfLocalOnSource :
    IsFppfLocalOnSource (topologically IsOpenMap) := by sorry

theorem universallyOpen_isFppfLocalOnSource :
    IsFppfLocalOnSource (@UniversallyOpen) := by sorry

theorem syntomic_isSyntomicLocalOnSource :
    IsSyntomicLocalOnSource (@IsSyntomic) := by sorry

theorem smooth_isSmoothLocalOnSource :
    IsSmoothLocalOnSource (@Smooth) := by sorry

theorem etale_isEtaleLocalOnSource :
    IsEtaleLocalOnSource (@Etale) := by sorry

theorem locallyQuasiFinite_isEtaleLocalOnSource :
    IsEtaleLocalOnSource (@LocallyQuasiFinite) := by sorry

theorem unramified_isEtaleLocalOnSource :
    IsEtaleLocalOnSource (@IsUnramified) := by sorry

theorem gUnramified_isEtaleLocalOnSource :
    IsEtaleLocalOnSource (@IsGUnramified) := by sorry

/-! ## Étale-locality on source-and-target -/

/-! The two counterexamples motivating the definition.  We record the
properties by their pointwise scheme-theoretic formulations; this keeps the
examples independent of a separate global Noetherian-scheme API. -/

def LocallyNoetherianTarget : SchemeMorphismProperty :=
  fun _ Y _ => IsLocallyNoetherian Y

def NoetherianAlongSpecializations : SchemeMorphismProperty :=
  fun X Y f =>
    ∀ (x : X), ∀ (y : Y), y ∈ closure ({f x} : Set Y) →
      IsNoetherianRing (Y.presheaf.stalk y : Type u)

structure SillyExampleTwoCounterexample
    (X Y U V : Scheme.{u}) where
  f : X ⟶ Y
  a : U ⟶ X
  b : V ⟶ Y
  h : U ⟶ V
  comm : a ≫ f = h ≫ b
  surjective_a : Surjective a
  surjective_b : Surjective b
  etale_a : Etale a
  etale_b : Etale b
  property_h : NoetherianAlongSpecializations h
  not_property_f : ¬ NoetherianAlongSpecializations f

def StableUnderEtalePostcomposition (P : SchemeMorphismProperty) : Prop :=
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    P f → Etale g → P (f ≫ g)

theorem silly_example_one :
    IsEtaleLocalOnSource LocallyNoetherianTarget ∧
      IsEtaleLocalOnTarget LocallyNoetherianTarget ∧
      ¬ StableUnderEtalePostcomposition LocallyNoetherianTarget := by sorry

theorem silly_example_two :
    IsEtaleLocalOnSource NoetherianAlongSpecializations ∧
      IsEtaleLocalOnTarget NoetherianAlongSpecializations ∧
      ∃ X Y U V : Scheme.{u}, Nonempty (SillyExampleTwoCounterexample X Y U V) := by sorry

def StableUnderEtalePrecomposition (P : SchemeMorphismProperty) : Prop :=
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), Etale f → P g → P (f ≫ g)

def StableUnderEtaleBaseChange (P : SchemeMorphismProperty) : Prop :=
  PreservedByBaseChange (@Etale) P

def EtaleLocalDiagramHasProperty (P : SchemeMorphismProperty)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ {U V : Scheme.{u}} (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V),
    Etale a → Etale b → a ≫ f = h ≫ b → P h

def EtaleLocalAtSourceAndTarget (P : SchemeMorphismProperty) : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    P f ↔ ∀ x : X, ∃ (U V : Scheme.{u}) (a : U ⟶ X) (b : V ⟶ Y)
      (h : U ⟶ V) (u : U), Etale a ∧ Etale b ∧
        a ≫ f = h ≫ b ∧ a u = x ∧ P h

def IsEtaleLocalOnSourceAndTarget (P : SchemeMorphismProperty) : Prop :=
  StableUnderEtalePrecomposition P ∧ StableUnderEtaleBaseChange P ∧
    EtaleLocalAtSourceAndTarget P

def EtaleLocalOnSourceAndTargetSeparately (P : SchemeMorphismProperty) : Prop :=
  IsEtaleLocalOnSource P ∧ IsEtaleLocalOnTarget P

def DeligneMumfordEtaleLocal (P : SchemeMorphismProperty) : Prop :=
  ∀ {X X' Y Y' : Scheme.{u}} (a : X' ⟶ X) (b : Y' ⟶ Y)
    (h' : X' ⟶ Y') (h : X ⟶ Y),
    a ≫ h = h' ≫ b → Surjective a → Surjective b →
    Etale a → Etale b → (P h ↔ P h')

def EtaleTargetCoverProperty (P : SchemeMorphismProperty)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ (𝒰 : Cover .etale Y),
    ∀ i, P (baseChangeTo f (𝒰.f i))

def EtaleSourceCoverProperty (P : SchemeMorphismProperty)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ (𝒰 : Cover .etale X),
    ∀ i, P (𝒰.f i ≫ f)

def NestedEtaleCoverProperty (P : SchemeMorphismProperty)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ (𝒰 : Cover .etale Y),
    ∀ i, ∃ (𝒱 : Cover .etale (baseChange f (𝒰.f i))),
      ∀ j, P (𝒱.f j ≫ baseChangeTo f (𝒰.f i))

def EtaleLocalPointwiseDiagramProperty (P : SchemeMorphismProperty)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ x : X, ∃ (U V : Scheme.{u}) (a : U ⟶ X) (b : V ⟶ Y)
    (h : U ⟶ V) (u : U), Etale a ∧ Etale b ∧
      a ≫ f = h ≫ b ∧ a u = x ∧ P h

theorem etaleLocalOnSourceAndTarget_implies
    (P : SchemeMorphismProperty) (hP : IsEtaleLocalOnSourceAndTarget P) :
    IsEtaleLocalOnSource P ∧ IsEtaleLocalOnTarget P ∧
      (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
        P f → Etale g → P (f ≫ g)) ∧
      (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
        Etale g → P (f ≫ g) → P f) := by sorry

theorem etaleLocalOnSourceAndTarget_implies_DM_and_separate
    (P : SchemeMorphismProperty) (hP : IsEtaleLocalOnSourceAndTarget P) :
    DeligneMumfordEtaleLocal P ∧ EtaleLocalOnSourceAndTargetSeparately P := by sorry

theorem deligneMumfordEtaleLocal_implies_separate
    (P : SchemeMorphismProperty) (hP : DeligneMumfordEtaleLocal P) :
    EtaleLocalOnSourceAndTargetSeparately P := by sorry

def EtaleLocalCharacterization (P : SchemeMorphismProperty)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  P f ∧
  EtaleLocalPointwiseDiagramProperty P f ∧
  EtaleLocalDiagramHasProperty P f ∧
  (∃ (U V : Scheme.{u}) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V),
    Surjective a ∧ Etale a ∧ Etale b ∧ a ≫ f = h ≫ b ∧ P h)
  ∧ EtaleTargetCoverProperty P f
  ∧ EtaleSourceCoverProperty P f
  ∧ NestedEtaleCoverProperty P f

theorem etaleLocalOnSourceAndTarget_characterize
    (P : SchemeMorphismProperty) (hP : IsEtaleLocalOnSourceAndTarget P)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    EtaleLocalCharacterization P f ↔ P f := by sorry

theorem etaleLocalOnSourceAndTarget_of_source_target_local
    (P : SchemeMorphismProperty)
    (hsource : IsEtaleLocalOnSource P)
    (htarget : IsEtaleLocalOnTarget P)
    (hopen : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      P f → IsOpenImmersion g → P (f ≫ g)) :
    IsEtaleLocalOnSourceAndTarget P := by sorry

theorem standard_etale_local_source_target_list :
    IsEtaleLocalOnSourceAndTarget (@Flat) ∧
      IsEtaleLocalOnSourceAndTarget (@LocallyOfFinitePresentation) ∧
      IsEtaleLocalOnSourceAndTarget (@LocallyOfFiniteType) ∧
      IsEtaleLocalOnSourceAndTarget (@UniversallyOpen) ∧
      IsEtaleLocalOnSourceAndTarget (@IsSyntomic) ∧
      IsEtaleLocalOnSourceAndTarget (@Smooth) ∧
      IsEtaleLocalOnSourceAndTarget (@Etale) ∧
      IsEtaleLocalOnSourceAndTarget (@LocallyQuasiFinite) ∧
      IsEtaleLocalOnSourceAndTarget (@IsUnramified) ∧
      IsEtaleLocalOnSourceAndTarget (@IsGUnramified) := by sorry

def IsEtaleAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f)

def IsSmoothAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)

theorem etaleLocalOnSourceAndTarget_pointwise
    (P : SchemeMorphismProperty) (hP : IsEtaleLocalOnSourceAndTarget P)
    {X X' Y Y' : Scheme.{u}} (a : X' ⟶ X) (b : Y' ⟶ Y)
    (f' : X' ⟶ Y') (f : X ⟶ Y) (comm : a ≫ f = f' ≫ b)
    (x' : X') (x : X) (y' : Y') (y : Y) (hx : a x' = x) (hy : b y' = y)
    (hfx : f x = y) (hfx' : f' x' = y')
    (ha : IsEtaleAt a x') (hb : IsEtaleAt b y') :
    x ∈ largestOpenOfSource .etale P
      (by sorry) f ↔
      x' ∈ largestOpenOfSource .etale P
        (by sorry) f' := by sorry

theorem etaleSource_smoothTarget_pointwise
    (P : SchemeMorphismProperty)
    (hsource : IsEtaleLocalOnSource P)
    (htarget : IsSmoothLocalOnTarget P)
    (hopen : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      P f → IsOpenImmersion g → P (f ≫ g))
    {X X' Y Y' : Scheme.{u}} (a : X' ⟶ X) (b : Y' ⟶ Y)
    (f' : X' ⟶ Y') (f : X ⟶ Y) (comm : a ≫ f = f' ≫ b)
    (x' : X') (x : X) (y' : Y') (y : Y) (hx : a x' = x) (hy : b y' = y)
    (hfx : f x = y) (hfx' : f' x' = y')
    (hcart : IsEtaleAt (pullback.lift a f' comm) x')
    (hb : IsSmoothAt b y') :
    x ∈ largestOpenOfSource .etale P hsource f ↔
      x' ∈ largestOpenOfSource .etale P hsource f' := by sorry

/-! The orbit lemma used in the smooth-target argument. -/

def triangularTranslation {k : Type u} [Field k] {n : ℕ}
    (i j : Fin n) (d : ℕ) (_hij : i ≠ j) (x : Fin n → k) : Fin n → k :=
  Function.update x i (x i + x j ^ d)

structure TranslationInvariantOpen (k : Type u) [Field k] (n : ℕ) where
  carrier : Set (Fin n → k)
  nonempty : carrier.Nonempty
  invariant : ∀ (i j : Fin n) (d : ℕ) (hij : i ≠ j),
    Set.image (fun x => triangularTranslation i j d hij x) carrier = carrier

def AlgebraicOverPrimeField {k : Type u} [Field k] (x : k) : Prop :=
  IsAlgebraic (⊥ : Subfield k) x

structure TranslationInvariantConclusion {k : Type u} [Field k] {n : ℕ}
    (W : TranslationInvariantOpen k n) : Prop where
  full_or_finite : W.carrier = Set.univ ∨
    (W.carrierᶜ).Finite ∧
      ∃ p : ℕ, Nat.Prime p ∧ CharP k p ∧
      ∀ z ∈ W.carrierᶜ, ∀ i : Fin n, AlgebraicOverPrimeField (z i)

theorem translationInvariantOpen_orbit
    {k : Type u} [Field k] {n : ℕ} (hn : 2 ≤ n)
    (W : TranslationInvariantOpen k n) :
    TranslationInvariantConclusion W := by sorry

/-! Smooth-target étale-locality and the pointwise Frobenius obstruction. -/

theorem etaleLocalOnSourceAndTarget_of_etaleSource_smoothTarget
    (P : SchemeMorphismProperty)
    (hsource : IsEtaleLocalOnSource P)
    (htarget : IsSmoothLocalOnTarget P)
    (hopen : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      P f → IsOpenImmersion g → P (f ≫ g))
    : IsEtaleLocalOnSourceAndTarget P := by sorry

end Formalization.Books.Descent.Unit19
