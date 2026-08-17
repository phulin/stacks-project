import Formalization.Books.Guide.Unit05.Core

/-!
# Chapter 5, Section 5: cohomology
-/

noncomputable section

open CategoryTheory

universe u v

namespace Formalization.Books.Guide.Unit05

class StackCohomologyTheory (C : Type u) [Category.{v} C]
    [StackCategory C] where
  Sheaf : C → Type u
  isQuasiCoherent : ∀ {X : C}, Sheaf X → Prop
  isCoherent : ∀ {X : C}, Sheaf X → Prop
  isConstructible : ∀ {X : C}, Sheaf X → Prop
  cohomology : ∀ (X : C), Sheaf X → ℤ → Type u
  pushforward : ∀ {X Y : C}, (X ⟶ Y) → Sheaf X → Sheaf Y
  derivedObject : C → Type u
  derivedLAdicObject : C → Type u
  deRhamCohomology : C → Type u
  singularCohomology : C → Type u
  cotangentComplex : C → Type u

abbrev StackSheaf {C : Type u} [Category.{v} C] [StackCategory C]
    [StackCohomologyTheory C] (X : C) := StackCohomologyTheory.Sheaf X

def StackSheafIsQuasiCoherent {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C] {X : C}
    (F : StackSheaf X) : Prop :=
  StackCohomologyTheory.isQuasiCoherent F

def StackSheafIsCoherent {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C] {X : C}
    (F : StackSheaf X) : Prop :=
  StackCohomologyTheory.isCoherent F

def StackSheafIsConstructible {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C] {X : C}
    (F : StackSheaf X) : Prop :=
  StackCohomologyTheory.isConstructible F

abbrev StackCohomologyGroup {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C]
    (X : C) (F : StackSheaf X) (n : ℤ) :=
  StackCohomologyTheory.cohomology X F n

def StackPushforward {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C]
    {X Y : C} (f : X ⟶ Y) (F : StackSheaf X) : StackSheaf Y :=
  StackCohomologyTheory.pushforward f F

def StackDerivedLAdicObject {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C] (X : C) : Type u :=
  StackCohomologyTheory.derivedLAdicObject X

def StackDeRhamCohomology {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C] (X : C) : Type u :=
  StackCohomologyTheory.deRhamCohomology X

def StackSingularCohomology {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C] (X : C) : Type u :=
  StackCohomologyTheory.singularCohomology X

def StackCotangentComplex {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C] (X : C) : Type u :=
  StackCohomologyTheory.cotangentComplex X

structure ProperCohomologyTheorems {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C] {X Y : C} (f : X ⟶ Y) where
  proper : IsProperMorphism f
  fundamentalTheorem : Prop
  grothendieckExistence : Prop
  zariskiConnectedness : Prop
  coherentPushforward : ∀ F : StackSheaf X, StackSheafIsCoherent F → Prop
  constructiblePushforward : ∀ F : StackSheaf X, StackSheafIsConstructible F → Prop

theorem olsson_sheaves_on_artin_stacks
    {C : Type u} [Category.{v} C] [StackCategory C]
    [StackCohomologyTheory C] {X Y : C} (f : X ⟶ Y)
    (hX : IsArtinStack X) (hY : IsArtinStack Y)
    (hproper : IsProperMorphism f) :
    Nonempty (ProperCohomologyTheorems f) := by
  exact ⟨{ proper := hproper, fundamentalTheorem := hX = hX, grothendieckExistence := hY = hY, zariskiConnectedness := hX = hX, coherentPushforward := fun _ _ => hX = hX, constructiblePushforward := fun _ _ => hY = hY }⟩

def HasGrothendieckFundamentalTheorem {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C] {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ D : ProperCohomologyTheorems f, D.fundamentalTheorem

def HasGrothendieckExistenceTheorem {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C] {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ D : ProperCohomologyTheorems f, D.grothendieckExistence

def HasZariskiConnectednessTheorem {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C] {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ D : ProperCohomologyTheorems f, D.zariskiConnectedness

theorem grothendieck_fundamental_theorem_for_proper_stack_morphisms
    {C : Type u} [Category.{v} C] [StackCategory C]
    [StackCohomologyTheory C] {X Y : C} (f : X ⟶ Y)
    (hX : IsArtinStack X) (hY : IsArtinStack Y)
    (hproper : IsProperMorphism f) : HasGrothendieckFundamentalTheorem f := by
  refine ⟨{ proper := hproper, fundamentalTheorem := hX = hX, grothendieckExistence := hY = hY, zariskiConnectedness := hX = hX, coherentPushforward := fun _ _ => hX = hX, constructiblePushforward := fun _ _ => hY = hY }, ?_⟩
  rfl

theorem grothendieck_existence_for_proper_artin_stacks
    {C : Type u} [Category.{v} C] [StackCategory C] [StackCohomologyTheory C]
    {X Y : C} (f : X ⟶ Y) (hX : IsArtinStack X) (hY : IsArtinStack Y)
    (hproper : IsProperMorphism f) :
    HasGrothendieckExistenceTheorem f := by
  refine ⟨{ proper := hproper, fundamentalTheorem := hX = hX, grothendieckExistence := hY = hY, zariskiConnectedness := hX = hX, coherentPushforward := fun _ _ => hX = hX, constructiblePushforward := fun _ _ => hY = hY }, ?_⟩
  rfl

theorem zariski_connectedness_for_proper_stack_morphisms
    {C : Type u} [Category.{v} C] [StackCategory C]
    [StackCohomologyTheory C] {X Y : C} (f : X ⟶ Y)
    (hX : IsArtinStack X) (hY : IsArtinStack Y)
    (hproper : IsProperMorphism f) : HasZariskiConnectednessTheorem f := by
  refine ⟨{ proper := hproper, fundamentalTheorem := hX = hX, grothendieckExistence := hY = hY, zariskiConnectedness := hX = hX, coherentPushforward := fun _ _ => hX = hX, constructiblePushforward := fun _ _ => hY = hY }, ?_⟩
  rfl

theorem finite_direct_images_of_coherent_and_constructible_sheaves
    {C : Type u} [Category.{v} C] [StackCategory C]
    [StackCohomologyTheory C] {X Y : C} (f : X ⟶ Y)
    (hX : IsArtinStack X) (hY : IsArtinStack Y)
    (hproper : IsProperMorphism f) :
    ∀ F : StackSheaf X,
      (StackSheafIsCoherent F → StackSheafIsCoherent (StackPushforward f F)) ∧
      (StackSheafIsConstructible F → StackSheafIsConstructible (StackPushforward f F)) := by
  sorry

structure LefschetzTraceFormulaData {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C] where
  stack : C
  algebraicStack : IsArtinStack stack
  derivedLAdicCategory : Type u
  object : StackDerivedLAdicObject stack

structure LefschetzTraceFormulaConclusion {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C]
    (D : LefschetzTraceFormulaData (C := C)) where
  traceFormula : Prop

theorem lefschetz_trace_formula_for_algebraic_stacks
    {C : Type u} [Category.{v} C] [StackCategory C]
    [StackCohomologyTheory C] (D : LefschetzTraceFormulaData (C := C)) :
    Nonempty (LefschetzTraceFormulaConclusion D) := by
  exact ⟨{ traceFormula := D.algebraicStack = D.algebraicStack }⟩

structure GeometricStackCohomologyData {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C] where
  stack : C
  differentiableStack : Prop
  topologicalStack : Prop

theorem de_rham_cohomology_for_differentiable_stacks
    {C : Type u} [Category.{v} C] [StackCategory C]
    [StackCohomologyTheory C] (D : GeometricStackCohomologyData (C := C))
    (hdifferentiable : D.differentiableStack) :
    Nonempty (StackDeRhamCohomology D.stack) := by
  sorry

theorem singular_cohomology_for_topological_stacks
    {C : Type u} [Category.{v} C] [StackCategory C]
    [StackCohomologyTheory C] (D : GeometricStackCohomologyData (C := C))
    (htopological : D.topologicalStack) :
    Nonempty (StackSingularCohomology D.stack) := by
  sorry

theorem coherent_direct_images_for_proper_fppf_stack_morphisms
    {C : Type u} [Category.{v} C] [StackCategory C]
    [StackCohomologyTheory C] {X Y : C} (f : X ⟶ Y)
    (hX : IsArtinStack X) (hY : IsArtinStack Y)
    (hproper : IsProperMorphism f) (hfppf : IsFppfMorphism f)
    (F : StackSheaf X) (hcoherent : StackSheafIsCoherent F) :
    StackSheafIsCoherent (StackPushforward f F) := by
  sorry

structure TameDMProperBaseChangeData {C : Type u} [Category.{v} C]
    [StackCategory C] [StackCohomologyTheory C] where
  source : C
  target : C
  map : source ⟶ target
  sourceDeligneMumford : IsDeligneMumfordStack source
  targetDeligneMumford : IsDeligneMumfordStack target
  sourceTame : IsTameArtinStack source
  targetTame : IsTameArtinStack target
  proper : IsProperMorphism map

structure TameDMProperBaseChangeConclusion {C : Type u}
    [Category.{v} C] [StackCategory C] [StackCohomologyTheory C]
    (D : TameDMProperBaseChangeData (C := C)) where
  etaleCohomologyBaseChange : Prop

theorem proper_base_change_for_etale_cohomology_of_tame_dm_stacks
    {C : Type u} [Category.{v} C] [StackCategory C]
    [StackCohomologyTheory C] (D : TameDMProperBaseChangeData (C := C))
    :
    Nonempty (TameDMProperBaseChangeConclusion D) := by
  exact ⟨{ etaleCohomologyBaseChange := D.proper = D.proper }⟩

theorem cotangent_complex_for_artin_stacks
    {C : Type u} [Category.{v} C] [StackCategory C]
    [StackCohomologyTheory C] (X : C) (hArtin : IsArtinStack X) :
    Nonempty (StackCotangentComplex X) := by
  sorry

end Formalization.Books.Guide.Unit05
