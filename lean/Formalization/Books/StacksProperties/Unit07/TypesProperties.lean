import Formalization.Books.StacksProperties.Unit06.QuasiCompact

/-!
# Properties of Algebraic Stacks, Chapter 1, Section 7

This file records the source's two locality interfaces: properties of
schemes which are local for smooth covers, and properties of pointed scheme
germs which are local for smooth covers.  A scheme over the fixed base is
represented by the underlying scheme of an object of `Over S`, as in the
convention layer.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace Formalization.Books.StacksProperties.Unit01

structure SmoothLocalSchemeProperty (S : Scheme.{u}) where
  schemeProperty : Scheme.{u} → Prop
  spaceProperty : AlgebraicSpace S → Prop
  comparison : ∀ W : AlgebraicSpace S,
    schemeProperty W.left ↔ spaceProperty W
  smoothLocal : Prop

def IsSmoothCover {S : Scheme.{u}} {X : AlgebraicStack S}
    (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X) : Prop :=
  Function.Surjective w.map ∧ w.smooth

def SomeSchemeSmoothProperty {S : Scheme.{u}}
    (P : SmoothLocalSchemeProperty S) (X : AlgebraicStack S) : Prop :=
  ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X),
    IsSmoothCover W w ∧ P.schemeProperty W.left

def EverySchemeSmoothProperty {S : Scheme.{u}}
    (P : SmoothLocalSchemeProperty S) (X : AlgebraicStack S) : Prop :=
  ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X),
    w.smooth → P.schemeProperty W.left

def SomeSpaceSmoothProperty {S : Scheme.{u}}
    (P : SmoothLocalSchemeProperty S) (X : AlgebraicStack S) : Prop :=
  ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X),
    IsSmoothCover W w ∧ P.spaceProperty W

def EverySpaceSmoothProperty {S : Scheme.{u}}
    (P : SmoothLocalSchemeProperty S) (X : AlgebraicStack S) : Prop :=
  ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X),
    w.smooth → P.spaceProperty W

theorem type_property_characterization {S : Scheme.{u}}
    (P : SmoothLocalSchemeProperty S) (X : AlgebraicStack S)
    (hlocal : ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X),
      IsSmoothCover W w → P.schemeProperty W.left →
      ∀ (W' : AlgebraicSpace S) (w' : SpaceToStackMorphism W' X),
        w'.smooth → P.schemeProperty W'.left) :
    SomeSchemeSmoothProperty P X ↔
      EverySchemeSmoothProperty P X ∧
        SomeSpaceSmoothProperty P X ∧ EverySpaceSmoothProperty P X := by
  unfold SomeSchemeSmoothProperty EverySchemeSmoothProperty
    SomeSpaceSmoothProperty EverySpaceSmoothProperty
  constructor
  · rintro ⟨W, w, hcover, hproperty⟩
    refine ⟨?_, ⟨W, w, hcover, (P.comparison W).mp hproperty⟩, ?_⟩
    · intro W' w' hsmooth
      exact hlocal W w hcover hproperty W' w' hsmooth
    · intro W' w' hsmooth
      exact (P.comparison W').mp
        (hlocal W w hcover hproperty W' w' hsmooth)
  · rintro ⟨_, ⟨W, w, hcover, hproperty⟩, _⟩
    exact ⟨W, w, hcover, (P.comparison W).mpr hproperty⟩

def HasTypeProperty {S : Scheme.{u}}
    (P : SmoothLocalSchemeProperty S) (X : AlgebraicStack S) : Prop :=
  SomeSchemeSmoothProperty P X

theorem type_property_of_representable_scheme {S : Scheme.{u}}
    (P : SmoothLocalSchemeProperty S) (X : AlgebraicStack S)
    (_hX : IsRepresentableByScheme X)
    (hcover : ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X),
      IsSmoothCover W w)
    (hlocal : ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X),
      IsSmoothCover W w → P.schemeProperty W.left →
      ∀ (W' : AlgebraicSpace S) (w' : SpaceToStackMorphism W' X),
        w'.smooth → P.schemeProperty W'.left) :
    HasTypeProperty P X ↔ EverySchemeSmoothProperty P X := by
  unfold HasTypeProperty SomeSchemeSmoothProperty EverySchemeSmoothProperty
  constructor
  · rintro ⟨W, w, hcover, hproperty⟩ W' w' hsmooth
    exact hlocal W w hcover hproperty W' w' hsmooth
  · intro hproperty
    rcases hcover with ⟨W, w, hW⟩
    exact ⟨W, w, hW, hproperty W w hW.2⟩

theorem type_property_of_representable_space {S : Scheme.{u}}
    (P : SmoothLocalSchemeProperty S) (X : AlgebraicStack S)
    (_hX : IsRepresentableByAlgebraicSpace X)
    (hcover : ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X),
      IsSmoothCover W w)
    (hlocal : ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X),
      IsSmoothCover W w → P.spaceProperty W →
      ∀ (W' : AlgebraicSpace S) (w' : SpaceToStackMorphism W' X),
        w'.smooth → P.spaceProperty W') :
    HasTypeProperty P X ↔ EverySpaceSmoothProperty P X := by
  unfold HasTypeProperty SomeSchemeSmoothProperty EverySpaceSmoothProperty
  constructor
  · rintro ⟨W, w, hcover, hproperty⟩ W' w' hsmooth
    exact hlocal W w hcover ((P.comparison W).mp hproperty) W' w' hsmooth
  · intro hproperty
    rcases hcover with ⟨W, w, hW⟩
    refine ⟨W, w, hW, ?_⟩
    exact (P.comparison W).mpr (hproperty W w hW.2)

inductive SmoothLocalPropertyName
  | locallyNoetherian
  | jacobson
  | locallyNoetherianAndSk
  | cohenMacaulay
  | reduced
  | normal
  | locallyNoetherianAndRk
  | regular
  | nagata
  deriving DecidableEq, Repr

def smoothLocalPropertyNames : List SmoothLocalPropertyName :=
  [.locallyNoetherian, .jacobson, .locallyNoetherianAndSk,
   .cohenMacaulay, .reduced, .normal, .locallyNoetherianAndRk,
   .regular, .nagata]

structure SmoothLocalGermProperty (S : Scheme.{u}) where
  schemeProperty : LocalPropertyOfGerms.{u}
  spaceProperty : ∀ (W : AlgebraicSpace S), W.left → Prop
  comparison : ∀ (W : AlgebraicSpace S) (u : W.left),
    schemeProperty.property W.left u ↔ spaceProperty W u
  smoothLocal : schemeProperty.smoothLocal

def SomeSchemeGermPropertyAt {S : Scheme.{u}}
    (P : SmoothLocalGermProperty S) {X : AlgebraicStack S}
    (x : StackPoint X) : Prop :=
  ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X) (u : W.left),
    w.smooth ∧ w.map u = x ∧ P.schemeProperty.property W.left u

def EverySchemeGermPropertyAt {S : Scheme.{u}}
    (P : SmoothLocalGermProperty S) {X : AlgebraicStack S}
    (x : StackPoint X) : Prop :=
  ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X) (u : W.left),
    w.smooth → w.map u = x → P.schemeProperty.property W.left u

def SomeSpaceGermPropertyAt {S : Scheme.{u}}
    (P : SmoothLocalGermProperty S) {X : AlgebraicStack S}
    (x : StackPoint X) : Prop :=
  ∃ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X) (u : W.left),
    w.smooth ∧ w.map u = x ∧ P.spaceProperty W u

def EverySpaceGermPropertyAt {S : Scheme.{u}}
    (P : SmoothLocalGermProperty S) {X : AlgebraicStack S}
    (x : StackPoint X) : Prop :=
  ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X) (u : W.left),
    w.smooth → w.map u = x → P.spaceProperty W u

theorem local_source_target_at_point {S : Scheme.{u}}
    (P : SmoothLocalGermProperty S) {X : AlgebraicStack S}
    (x : StackPoint X)
    (hlocal : ∀ (W : AlgebraicSpace S) (w : SpaceToStackMorphism W X)
      (u : W.left),
      w.smooth → w.map u = x → P.schemeProperty.property W.left u →
      ∀ (W' : AlgebraicSpace S) (w' : SpaceToStackMorphism W' X)
        (u' : W'.left),
        w'.smooth → w'.map u' = x →
          P.schemeProperty.property W'.left u') :
    SomeSchemeGermPropertyAt P x ↔
      EverySchemeGermPropertyAt P x ∧
        SomeSpaceGermPropertyAt P x ∧ EverySpaceGermPropertyAt P x := by
  unfold SomeSchemeGermPropertyAt EverySchemeGermPropertyAt
    SomeSpaceGermPropertyAt EverySpaceGermPropertyAt
  constructor
  · rintro ⟨W, w, u, hsmooth, hmap, hproperty⟩
    refine ⟨?_, ⟨W, w, u, hsmooth, hmap,
      (P.comparison W u).mp hproperty⟩, ?_⟩
    · intro W' w' u' hsmooth' hmap'
      exact hlocal W w u hsmooth hmap hproperty W' w' u' hsmooth' hmap'
    · intro W' w' u' hsmooth' hmap'
      exact (P.comparison W' u').mp
        (hlocal W w u hsmooth hmap hproperty W' w' u' hsmooth' hmap')
  · rintro ⟨_, ⟨W, w, u, hsmooth, hmap, hproperty⟩, _⟩
    exact ⟨W, w, u, hsmooth, hmap, (P.comparison W u).mpr hproperty⟩

def HasGermPropertyAt {S : Scheme.{u}}
    (P : SmoothLocalGermProperty S) {X : AlgebraicStack S}
    (x : StackPoint X) : Prop :=
  SomeSchemeGermPropertyAt P x

end Formalization.Books.StacksProperties.Unit01
