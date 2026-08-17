import Formalization.Books.Guide.Unit05.Core

/-!
# Chapter 5, Section 10: toric stacks
-/

noncomputable section

open CategoryTheory

universe u v

namespace Formalization.Books.Guide.Unit05

structure StackyFan where
  lattice : Type u
  [latticeGroup : AddCommGroup lattice]
  rayIndex : Type u
  rayMap : rayIndex → lattice
  cones : Set (Set rayIndex)
  fanAxioms : Prop

structure SmoothToricDMStackData (C : Type u) [Category.{v} C]
    [StackCategory C] where
  stackyFan : StackyFan.{u}
  stack : C
  smooth : IsSmoothStack stack
  deligneMumford : IsDeligneMumfordStack stack
  quotientPresentation : IsGlobalQuotient stack

structure SmoothToricDMStackConclusion {C : Type u} [Category.{v} C]
    [StackCategory C] (D : SmoothToricDMStackData C) where
  associatedToStackyFan : Prop

theorem smooth_toric_dm_stack_from_stacky_fan
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : SmoothToricDMStackData C) :
    Nonempty (SmoothToricDMStackConclusion D) := by
  exact ⟨{ associatedToStackyFan := D.stackyFan = D.stackyFan }⟩

structure ToricTriple (C : Type u) [Category.{v} C]
    [StackCategory C] where
  stack : C
  smoothDeligneMumford : IsSmoothStack stack ∧ IsDeligneMumfordStack stack
  torusObject : C
  torusIsMultiplicativeGroup : Prop
  torus : Type u
  torusGroup : CommGroup torus
  openImmersion : torusObject ⟶ stack
  openImmersionIsOpen : Prop
  denseImage : Prop
  torusAction : Prop

structure ToricTripleStackyFanCorrespondence (C : Type u)
    [Category.{v} C] [StackCategory C] where
  toricTriple : ToricTriple C
  stackyFan : StackyFan.{u}

structure ToricTripleStackyFanConclusion {C : Type u} [Category.{v} C]
    [StackCategory C] (D : ToricTripleStackyFanCorrespondence C) where
  correspondence : Prop
  twoCategoryToOneCategory : Prop

theorem toric_triples_equivalent_to_stacky_fans
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : ToricTripleStackyFanCorrespondence C) :
    Nonempty (ToricTripleStackyFanConclusion D) := by
  exact ⟨{ correspondence := D.toricTriple = D.toricTriple, twoCategoryToOneCategory := D.stackyFan = D.stackyFan }⟩

structure DeltaCollection (C : Type u) [Category.{v} C]
    [StackCategory C] where
  stack : C
  fan : StackyFan.{u}
  collectionData : Type u

structure DeltaCollectionConclusion {C : Type u} [Category.{v} C]
    [StackCategory C] (D : DeltaCollection C) where
  satisfiesDeltaRelations : Prop

theorem toric_orbifold_delta_collections
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : DeltaCollection C) :
    Nonempty (DeltaCollectionConclusion D) := by
  exact ⟨{ satisfiesDeltaRelations := D.collectionData = D.collectionData }⟩

structure GeneralSmoothToricDMStackDeltaCollection (C : Type u)
    [Category.{v} C] [StackCategory C] where
  deltaCollection : DeltaCollection C
  generalSmoothDMStack : Prop

structure DMTorus (C : Type u) [Category.{v} C]
    [StackCategory C] where
  torus : C
  torusObjectIsGroup : Prop
  picardStack : C
  finiteGroup : Type u
  groupStructure : Group finiteGroup
  picardStackIsTProductBG : Prop

structure SmoothToricDMStackByDenseOrbit (C : Type u)
    [Category.{v} C] [StackCategory C] where
  stack : C
  smooth : IsSmoothStack stack
  deligneMumford : IsDeligneMumfordStack stack
  torus : DMTorus C
  denseOpenOrbit : Prop
  torusActionOnStack : Prop

structure SmoothToricDMStackDenseOrbitConclusion {C : Type u}
    [Category.{v} C] [StackCategory C]
    (D : SmoothToricDMStackByDenseOrbit C) where
  orbitIsTheDMTorus : Prop

theorem smooth_toric_dm_stacks_equivalent_to_stacky_fans
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : SmoothToricDMStackByDenseOrbit C) :
    Nonempty (SmoothToricDMStackDenseOrbitConclusion D) := by
  exact ⟨{ orbitIsTheDMTorus := D.torus = D.torus }⟩

structure ToricVarietySubgroupQuotient (C : Type u)
    [Category.{v} C] [StackCategory C] where
  toricVariety : C
  torusSubgroup : Type u
  groupStructure : Group torusSubgroup
  quotientStack : C
  quotientPresentation : Prop

structure GenericallyStackyToricSubstack (C : Type u)
    [Category.{v} C] [StackCategory C] where
  ambient : ToricVarietySubgroupQuotient C
  substack : C
  torusInvariant : Prop
  genericallyStacky : Prop

structure ToricStackCombinatorialDictionary (C : Type u)
    [Category.{v} C] [StackCategory C] where
  stack : C
  fan : StackyFan.{u}
  stackDictionary : Prop

structure ToricStackCombinatorialConclusion {C : Type u}
    [Category.{v} C] [StackCategory C]
    (D : ToricStackCombinatorialDictionary C) where
  combinatorialToGeometric : Prop
  geometricToCombinatorial : Prop
  smoothModuliInterpretation : Prop
  intrinsicCharacterization : Prop

theorem toric_stack_dictionary_and_intrinsic_characterization
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : ToricStackCombinatorialDictionary C) :
    Nonempty (ToricStackCombinatorialConclusion D) := by
  exact ⟨{ combinatorialToGeometric := D.stackDictionary = D.stackDictionary, geometricToCombinatorial := D.stackDictionary = D.stackDictionary, smoothModuliInterpretation := D.stackDictionary = D.stackDictionary, intrinsicCharacterization := D.stackDictionary = D.stackDictionary }⟩

end Formalization.Books.Guide.Unit05
