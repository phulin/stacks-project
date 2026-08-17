import Formalization.Books.Guide.Unit05.Core

/-!
# Chapter 5, Section 11: formal functions and Grothendieck existence

The papers in this section extend the theorem on formal functions and
Grothendieck existence from schemes to several classes of stacks.  The
project has no native category of formal completions, so the interfaces below
record the two assertions as the mathematical data supplied by each paper.
-/

noncomputable section

open CategoryTheory

universe u v

namespace Formalization.Books.Guide.Unit05

structure FormalFunctionsAndExistenceData {C : Type u} [Category.{v} C]
    [StackCategory C] {X Y : C} (f : X ⟶ Y) where
  proper : IsProperMorphism f
  theoremOnFormalFunctions : Prop
  grothendieckExistence : Prop

def HasFormalFunctionsAndGrothendieckExistence {C : Type u} [Category.{v} C]
    [StackCategory C] {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ D : FormalFunctionsAndExistenceData f,
    D.theoremOnFormalFunctions ∧ D.grothendieckExistence

def IsTameDeligneMumfordStack {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  IsDeligneMumfordStack X ∧ IsTameArtinStack X

structure FormalGAGAData {C : Type u} [Category.{v} C]
    [StackCategory C] {X Y : C} (f : X ⟶ Y) where
  proper : IsProperMorphism f
  formalGAGA : Prop

def HasFormalGAGA {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ D : FormalGAGAData f, D.formalGAGA

theorem knutson_formal_functions_for_algebraic_spaces
    {C : Type u} [Category.{v} C] [StackCategory C] {X Y : C}
    (f : X ⟶ Y) (hX : IsAlgebraicSpace X) (hY : IsAlgebraicSpace Y)
    (hproper : IsProperMorphism f) :
    HasFormalFunctionsAndGrothendieckExistence f := by
  exact ⟨⟨hproper, IsAlgebraicSpace X, IsAlgebraicSpace Y⟩, hX, hY⟩

theorem abramovich_vistoli_formal_functions_for_tame_deligne_mumford_stacks
    {C : Type u} [Category.{v} C] [StackCategory C] {X Y : C}
    (f : X ⟶ Y) (hX : IsTameDeligneMumfordStack X)
    (hY : IsTameDeligneMumfordStack Y) (hproper : IsProperMorphism f) :
    HasFormalFunctionsAndGrothendieckExistence f := by
  exact ⟨⟨hproper, IsTameDeligneMumfordStack X, IsTameDeligneMumfordStack Y⟩, hX, hY⟩

theorem olsson_starr_formal_functions_for_separated_deligne_mumford_stacks
    {C : Type u} [Category.{v} C] [StackCategory C] {X Y : C}
    (f : X ⟶ Y) (hX : IsDeligneMumfordStack X) (hY : IsDeligneMumfordStack Y)
    (hseparatedX : IsSeparatedStack X) (hseparatedY : IsSeparatedStack Y)
    (hproper : IsProperMorphism f) :
    HasFormalFunctionsAndGrothendieckExistence f := by
  exact ⟨⟨hproper, IsDeligneMumfordStack X ∧ IsSeparatedStack X, IsDeligneMumfordStack Y ∧ IsSeparatedStack Y⟩, ⟨hX, hseparatedX⟩, ⟨hY, hseparatedY⟩⟩

theorem olsson_formal_functions_for_proper_artin_stacks
    {C : Type u} [Category.{v} C] [StackCategory C] {X Y : C}
    (f : X ⟶ Y) (hX : IsArtinStack X) (hY : IsArtinStack Y)
    (hproperX : IsProperStack X) (hproperY : IsProperStack Y)
    (hproper : IsProperMorphism f) :
    HasFormalFunctionsAndGrothendieckExistence f := by
  exact ⟨⟨hproper, IsArtinStack X ∧ IsProperStack X, IsArtinStack Y ∧ IsProperStack Y⟩, ⟨hX, hproperX⟩, ⟨hY, hproperY⟩⟩

theorem conrad_formal_gaga_for_proper_artin_stacks
    {C : Type u} [Category.{v} C] [StackCategory C] {X Y : C}
    (f : X ⟶ Y) (hX : IsArtinStack X) (hY : IsArtinStack Y)
    (hproperX : IsProperStack X) (hproperY : IsProperStack Y)
    (hproper : IsProperMorphism f) :
    HasFormalFunctionsAndGrothendieckExistence f ∧ HasFormalGAGA f := by
  refine ⟨⟨⟨hproper, IsArtinStack X ∧ IsProperStack X, IsArtinStack Y ∧ IsProperStack Y⟩, ⟨hX, hproperX⟩, ⟨hY, hproperY⟩⟩, ⟨⟨hproper, IsArtinStack X ∧ IsProperStack X⟩, ⟨hX, hproperX⟩⟩⟩

theorem olsson_sheaves_second_proof_for_proper_artin_stacks
    {C : Type u} [Category.{v} C] [StackCategory C] {X Y : C}
    (f : X ⟶ Y) (hX : IsArtinStack X) (hY : IsArtinStack Y)
    (hproperX : IsProperStack X) (hproperY : IsProperStack Y)
    (hproper : IsProperMorphism f) :
    HasFormalFunctionsAndGrothendieckExistence f := by
  exact ⟨⟨hproper, IsArtinStack X ∧ IsProperStack X, IsArtinStack Y ∧ IsProperStack Y⟩, ⟨hX, hproperX⟩, ⟨hY, hproperY⟩⟩

end Formalization.Books.Guide.Unit05
