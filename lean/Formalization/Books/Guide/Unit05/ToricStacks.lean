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
  coneIndex : Type u
  rays : coneIndex → Type u
  rayMap : ∀ i, rays i → lattice
  fanAxioms : Prop

structure SmoothToricDMStackData (C : Type u) [Category.{v} C]
    [StackCategory C] where
  stackyFan : StackyFan.{u}
  stack : C
  smooth : IsSmoothStack stack
  deligneMumford : IsDeligneMumfordStack stack
  quotientPresentation : IsGlobalQuotient stack

structure SmoothToricDMStackConclusion where
  associatedToStackyFan : Prop

theorem smooth_toric_dm_stack_from_stacky_fan
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : SmoothToricDMStackData C) :
    Nonempty SmoothToricDMStackConclusion := by
  sorry

structure ToricTriple (C : Type u) [Category.{v} C]
    [StackCategory C] where
  stack : C
  smoothDeligneMumford : IsSmoothStack stack ∧ IsDeligneMumfordStack stack
  torusObject : C
  torusIsMultiplicativeGroup : Prop
  torus : Type u
  torusGroup : Group torus
  openImmersion : torusObject ⟶ stack
  openImmersionIsOpen : Prop
  denseImage : Prop
  torusAction : Prop

structure ToricTripleStackyFanCorrespondence (C : Type u)
    [Category.{v} C] [StackCategory C] where
  toricTriple : ToricTriple C
  stackyFan : StackyFan.{u}

structure ToricTripleStackyFanConclusion where
  correspondence : Prop
  twoCategoryToOneCategory : Prop

theorem toric_triples_equivalent_to_stacky_fans
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : ToricTripleStackyFanCorrespondence C) :
    Nonempty ToricTripleStackyFanConclusion := by
  sorry

structure DeltaCollection (C : Type u) [Category.{v} C]
    [StackCategory C] where
  stack : C
  fan : StackyFan.{u}
  collectionData : Type u

structure DeltaCollectionConclusion where
  satisfiesDeltaRelations : Prop

theorem toric_orbifold_delta_collections
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : DeltaCollection C) :
    Nonempty DeltaCollectionConclusion := by
  sorry

structure GeneralSmoothToricDMStackDeltaCollection (C : Type u)
    [Category.{v} C] [StackCategory C] where
  deltaCollection : DeltaCollection C
  generalSmoothDMStack : Prop

structure DMTorus (C : Type u) [Category.{v} C]
    [StackCategory C] where
  torus : C
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

structure SmoothToricDMStackDenseOrbitConclusion where
  orbitIsTheDMTorus : Prop

theorem smooth_toric_dm_stacks_equivalent_to_stacky_fans
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : SmoothToricDMStackByDenseOrbit C) :
    Nonempty SmoothToricDMStackDenseOrbitConclusion := by
  sorry

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

structure ToricStackCombinatorialConclusion where
  combinatorialToGeometric : Prop
  geometricToCombinatorial : Prop
  smoothModuliInterpretation : Prop
  intrinsicCharacterization : Prop

theorem toric_stack_dictionary_and_intrinsic_characterization
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : ToricStackCombinatorialDictionary C) :
    Nonempty ToricStackCombinatorialConclusion := by
  sorry

end Formalization.Books.Guide.Unit05
