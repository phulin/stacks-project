import Formalization.Books.Cohomology.Unit02.CohomologyOfSheaves
import Formalization.Books.Homology.Unit06.Extensions
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# Cohomology of Sheaves, Chapter 5: first cohomology and extensions

The source identifies extensions of the structure sheaf by a sheaf of
modules with first cohomology.  Ext is Mathlib's derived-category Ext group;
the class of a short exact sequence is `ShortExact.extClass`.  The
injective-resolution construction is recorded using the earlier chapters'
delta-functor, injective-presentation, cokernel, and pullback APIs.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Derived.Unit20
open Formalization.Books.Homology.Unit06
open Formalization.Books.Homology.Unit12
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

namespace Formalization.Books.Cohomology.Unit05

/-! ## The Ext and cohomology objects in the statement -/

/- Mathlib deliberately does not make `hasExt_of_enoughInjectives` an
  instance, because several universe-small Ext structures can coexist.  The
  sheaf category here is locally `v`-small, so this is the source-facing
  choice needed for the chapter's `Ext¹`. -/
noncomputable instance ringedSpaceModule_hasExt (X : RingedSpace.{v}) :
    HasExt.{v} (Mod X.structureSheaf) := by
  exact CategoryTheory.hasExt_of_enoughInjectives.{v} (Mod X.structureSheaf)

/-- The structure sheaf regarded as a module over itself. -/
abbrev ringedSpaceStructureSheafModule (X : RingedSpace.{v}) :
    Mod X.structureSheaf :=
  SheafOfModules.unit X.structureSheaf

/-- The first cohomology group of a sheaf of modules on a ringed space. -/
abbrev ringedSpaceModuleFirstCohomology (X : RingedSpace.{v})
    (F : Mod X.structureSheaf) : Type v :=
  (ringedSpaceModuleCohomologyObject X F 1 : Type v)

/-- The `Ext¹` group of the structure sheaf by `F`. -/
abbrev ringedSpaceModuleExtensionClass (X : RingedSpace.{v})
    (F : Mod X.structureSheaf) : Type v :=
  CategoryTheory.Abelian.Ext (ringedSpaceStructureSheafModule X) F 1

/-! ## The class attached to an extension -/

/-- The short exact sequence underlying an extension in the module category. -/
abbrev ringedSpaceModuleExtensionSequence (X : RingedSpace.{v})
    (F : Mod X.structureSheaf)
    (E : Extension (Mod X.structureSheaf)
      F (ringedSpaceStructureSheafModule X)) : ShortComplex (Mod X.structureSheaf) :=
  E.toShortComplex

/-- The derived-category `Ext¹` class of a short exact module extension. -/
noncomputable def ringedSpaceModuleExtensionClassOfExtension
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (E : Extension (Mod X.structureSheaf)
      F (ringedSpaceStructureSheafModule X)) :
    ringedSpaceModuleExtensionClass X F :=
  E.toShortComplex_shortExact.extClass

/-! ## The image of the unit section -/

/-- The objectwise identification of the chosen delta-functor with the
cohomology functors from Chapter 2. -/
noncomputable def ringedSpaceModuleCohomologyFunctorIso
    (X : RingedSpace.{v}) (n : ℕ) :
    (ringedSpaceModuleCohomologyDeltaFunctor X).functor n ≅
      ringedSpaceModuleCohomology X (n : ℤ) :=
  eqToIso (ringedSpaceModuleCohomologyDeltaFunctor_functor X n)

/-- The degree-zero comparison from the chosen delta-functor to global
sections. -/
noncomputable def ringedSpaceModuleGlobalSectionsIso (X : RingedSpace.{v}) :
    (ringedSpaceModuleCohomologyDeltaFunctor X).functor 0 ≅
      ringedSpaceModuleGlobalSections X := by
  exact ringedSpaceModuleCohomologyFunctorIso X 0 ≪≫
    Classical.choice (higherRightDerivedFunctor_zero_iso
      (ringedSpaceModuleGlobalSections X)
      (ringedSpaceModuleGlobalSections_isLeftExact X))

/-- The unit section in the degree-zero module of global sections. -/
noncomputable def ringedSpaceModuleGlobalUnitSection (X : RingedSpace.{v}) :
    ((ringedSpaceModuleGlobalSections X).obj
      (ringedSpaceStructureSheafModule X) : Type v) :=
  (1 : X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier)))

/-- The image in `H¹(X,F)` of `1 ∈ Γ(X,O_X)` under the connecting map of an
extension.  The two comparison isomorphisms normalize the chosen universal
delta-functor to the Chapter 2 cohomology objects. -/
noncomputable def ringedSpaceModuleExtensionImageOfOne
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (E : Extension (Mod X.structureSheaf)
      F (ringedSpaceStructureSheafModule X)) :
    ringedSpaceModuleFirstCohomology X F :=
  ((ringedSpaceModuleCohomologyFunctorIso X 1).hom.app F).hom
    (((ringedSpaceModuleCohomologyDeltaFunctor X).delta
      E.toShortComplex E.toShortComplex_shortExact 0).hom
      (((ringedSpaceModuleGlobalSectionsIso X).inv.app
        (ringedSpaceStructureSheafModule X)).hom
        (ringedSpaceModuleGlobalUnitSection X)))

/-! ## The injective quotient and the inverse pullback construction -/

/-- A chosen injective presentation of `F`, supplied by enough injectives in
the category of sheaves of modules. -/
noncomputable def ringedSpaceModuleInjectivePresentation
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :
    InjectivePresentation F :=
  Classical.choice (EnoughInjectives.presentation F)

/-- The injective object chosen for `F`. -/
noncomputable abbrev ringedSpaceModuleInjectiveObject
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) : Mod X.structureSheaf :=
  (ringedSpaceModuleInjectivePresentation X F).J

/-- The monomorphism from `F` into the chosen injective object. -/
noncomputable abbrev ringedSpaceModuleInjectiveEmbedding
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :
    F ⟶ ringedSpaceModuleInjectiveObject X F :=
  (ringedSpaceModuleInjectivePresentation X F).f

theorem ringedSpaceModuleInjectiveEmbedding_mono
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :
    Mono (ringedSpaceModuleInjectiveEmbedding X F) :=
  (ringedSpaceModuleInjectivePresentation X F).mono

theorem ringedSpaceModuleInjectiveObject_injective
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :
    Injective (ringedSpaceModuleInjectiveObject X F) :=
  (ringedSpaceModuleInjectivePresentation X F).injective

/-- The quotient `Q = I/F` in the injective-resolution construction. -/
noncomputable abbrev ringedSpaceModuleInjectiveQuotient
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) : Mod X.structureSheaf :=
  cokernel (ringedSpaceModuleInjectiveEmbedding X F)

/-- The quotient projection `I ⟶ Q`. -/
noncomputable abbrev ringedSpaceModuleInjectiveQuotientProjection
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :
    ringedSpaceModuleInjectiveObject X F ⟶
      ringedSpaceModuleInjectiveQuotient X F :=
  cokernel.π (ringedSpaceModuleInjectiveEmbedding X F)

/-- The short exact sequence `0 → F → I → I/F → 0` used in the proof. -/
noncomputable def ringedSpaceModuleInjectiveQuotientExtension
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :
    Extension (Mod X.structureSheaf) F
      (ringedSpaceModuleInjectiveQuotient X F) where
  middle := ringedSpaceModuleInjectiveObject X F
  inclusion := ringedSpaceModuleInjectiveEmbedding X F
  projection := ringedSpaceModuleInjectiveQuotientProjection X F
  zero := cokernel.condition (ringedSpaceModuleInjectiveEmbedding X F)
  shortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_cokernel (ringedSpaceModuleInjectiveEmbedding X F))
    (ringedSpaceModuleInjectiveEmbedding_mono X F)
    (by infer_instance)

/-- Sections of `Q` are equivalently maps from the structure sheaf to `Q`. -/
noncomputable def ringedSpaceModuleQuotientSectionEquiv
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :
    (ringedSpaceStructureSheafModule X ⟶ ringedSpaceModuleInjectiveQuotient X F) ≃
      (ringedSpaceModuleInjectiveQuotient X F).sections := by
  exact SheafOfModules.unitHomEquiv (ringedSpaceModuleInjectiveQuotient X F)

/-- The value at the top open of the section associated to a map
`O_X ⟶ Q`.  Chapter 2 models `Γ(X, Q)` by evaluation at the top open. -/
noncomputable def ringedSpaceModuleQuotientSectionValue
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (t : ringedSpaceStructureSheafModule X ⟶
      ringedSpaceModuleInjectiveQuotient X F) :
    ((ringedSpaceModuleGlobalSections X).obj
      (ringedSpaceModuleInjectiveQuotient X F) : Type v) :=
  ((ringedSpaceModuleGlobalSections X).map t).hom
    (ringedSpaceModuleGlobalUnitSection X)

/-- The connecting class of a section `O_X ⟶ Q`. -/
noncomputable def ringedSpaceModuleQuotientSectionConnectingClass
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (t : ringedSpaceStructureSheafModule X ⟶
      ringedSpaceModuleInjectiveQuotient X F) :
    ringedSpaceModuleFirstCohomology X F :=
  ((ringedSpaceModuleCohomologyFunctorIso X 1).hom.app F).hom
    (((ringedSpaceModuleCohomologyDeltaFunctor X).delta
      (ringedSpaceModuleInjectiveQuotientExtension X F).toShortComplex
      (ringedSpaceModuleInjectiveQuotientExtension X F).toShortComplex_shortExact 0).hom
      (((ringedSpaceModuleGlobalSectionsIso X).inv.app
        (ringedSpaceModuleInjectiveQuotient X F)).hom
        (ringedSpaceModuleQuotientSectionValue X F t)))

/- The long exact sequence makes every first cohomology class come from a
  section of `Q`; the proposition is left for the prove stage. -/
theorem exists_ringedSpaceModule_quotient_section
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (ξ : ringedSpaceModuleFirstCohomology X F) :
    ∃ t : ringedSpaceStructureSheafModule X ⟶
      ringedSpaceModuleInjectiveQuotient X F,
      ringedSpaceModuleQuotientSectionConnectingClass X F t = ξ := by
  sorry

/-- The pullback extension obtained from a section `t : O_X ⟶ Q`. -/
noncomputable def ringedSpaceModulePullbackExtension
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (t : ringedSpaceStructureSheafModule X ⟶
      ringedSpaceModuleInjectiveQuotient X F) :
    Extension (Mod X.structureSheaf) F
      (ringedSpaceStructureSheafModule X) :=
  pullbackExtension (ringedSpaceModuleInjectiveQuotientExtension X F) t

/-- The canonical morphism from the pullback extension to `0 → F → I → Q → 0`.
It is the vertical part of the source's displayed pullback diagram. -/
noncomputable def ringedSpaceModulePullbackExtensionMorphism
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (t : ringedSpaceStructureSheafModule X ⟶
      ringedSpaceModuleInjectiveQuotient X F) :
    ExtensionMorphism (ringedSpaceModulePullbackExtension X F t)
      (ringedSpaceModuleInjectiveQuotientExtension X F) :=
  pullbackExtensionMorphism (ringedSpaceModuleInjectiveQuotientExtension X F) t

/-! ## The canonical bijection -/

/- The source's `Ext¹` is the extension class represented by a short exact
  sequence.  The theorem records both the bijection and its specified value
  on every extension; the chosen equivalence below gives a reusable map. -/
theorem exists_ringedSpaceModule_ext_h1_equiv
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :
    ∃ e : ringedSpaceModuleExtensionClass X F ≃
        ringedSpaceModuleFirstCohomology X F,
      ∀ E : Extension (Mod X.structureSheaf)
        F (ringedSpaceStructureSheafModule X),
        e (ringedSpaceModuleExtensionClassOfExtension X F E) =
          ringedSpaceModuleExtensionImageOfOne X F E := by
  sorry

/-- The canonical bijection `Ext¹(O_X,F) ≃ H¹(X,F)`. -/
noncomputable def ringedSpaceModuleExtH1Equiv
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :
    ringedSpaceModuleExtensionClass X F ≃
      ringedSpaceModuleFirstCohomology X F :=
  Classical.choose (exists_ringedSpaceModule_ext_h1_equiv X F)

/-- The source-facing map sending an extension class to the image of `1`. -/
noncomputable abbrev ringedSpaceModuleExtToH1
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :
    ringedSpaceModuleExtensionClass X F →
      ringedSpaceModuleFirstCohomology X F :=
  ringedSpaceModuleExtH1Equiv X F

/-- The inverse of the canonical `Ext¹`–`H¹` bijection. -/
noncomputable abbrev ringedSpaceModuleH1ToExt
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :
    ringedSpaceModuleFirstCohomology X F →
      ringedSpaceModuleExtensionClass X F :=
  (ringedSpaceModuleExtH1Equiv X F).symm

theorem ringedSpaceModuleExtToH1_extension
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (E : Extension (Mod X.structureSheaf)
      F (ringedSpaceStructureSheafModule X)) :
    ringedSpaceModuleExtToH1 X F
        (ringedSpaceModuleExtensionClassOfExtension X F E) =
      ringedSpaceModuleExtensionImageOfOne X F E :=
  (Classical.choose_spec (exists_ringedSpaceModule_ext_h1_equiv X F)) E

/- The pullback construction is the source's explicit inverse on a section.
  Its compatibility with the canonical bijection is the main proposition-level
  statement to prove later. -/
theorem ringedSpaceModulePullbackExtension_maps_to_section_class
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (t : ringedSpaceStructureSheafModule X ⟶
      ringedSpaceModuleInjectiveQuotient X F) :
    ringedSpaceModuleExtToH1 X F
        (ringedSpaceModuleExtensionClassOfExtension X F
          (ringedSpaceModulePullbackExtension X F t)) =
      ringedSpaceModuleQuotientSectionConnectingClass X F t := by
  sorry

end Formalization.Books.Cohomology.Unit05
