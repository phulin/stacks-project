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
  associatedToStackyFan : Prop

theorem smooth_toric_dm_stack_from_stacky_fan
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : SmoothToricDMStackData C) :
    D.associatedToStackyFan := by
  sorry

structure ToricTriple (C : Type u) [Category.{v} C]
    [StackCategory C] where
  stack : C
  smoothDeligneMumford : IsSmoothStack stack ∧ IsDeligneMumfordStack stack
  torus : Type u
  torusGroup : Group torus
  openImmersion : torus → Point stack
  openImmersionInjective : Function.Injective openImmersion
  denseImage : Prop
  torusAction : torus → Point stack → Point stack
  actionAxioms : Prop

structure ToricTripleStackyFanCorrespondence (C : Type u)
    [Category.{v} C] [StackCategory C] where
  toricTriple : ToricTriple C
  stackyFan : StackyFan.{u}
  correspondence : Prop
  twoCategoryToOneCategory : Prop

theorem toric_triples_equivalent_to_stacky_fans
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : ToricTripleStackyFanCorrespondence C) :
    D.correspondence ∧ D.twoCategoryToOneCategory := by
  sorry

structure DeltaCollection (C : Type u) [Category.{v} C]
    [StackCategory C] where
  stack : C
  fan : StackyFan.{u}
  collectionData : Type u
  satisfiesDeltaRelations : Prop

theorem toric_orbifold_delta_collections
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : DeltaCollection C) :
    D.satisfiesDeltaRelations := by
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
  orbitIsTheDMTorus : Prop

theorem smooth_toric_dm_stacks_equivalent_to_stacky_fans
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : SmoothToricDMStackByDenseOrbit C) :
    D.orbitIsTheDMTorus := by
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
  combinatorialToGeometric : Prop
  geometricToCombinatorial : Prop
  smoothModuliInterpretation : Prop
  intrinsicCharacterization : Prop

theorem toric_stack_dictionary_and_intrinsic_characterization
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : ToricStackCombinatorialDictionary C) :
    D.combinatorialToGeometric ∧ D.geometricToCombinatorial ∧
      D.smoothModuliInterpretation ∧ D.intrinsicCharacterization := by
  sorry

end Formalization.Books.Guide.Unit05
