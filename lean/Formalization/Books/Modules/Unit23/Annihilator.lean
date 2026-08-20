import Formalization.Books.Modules.Unit22.InternalHom
import Mathlib.RingTheory.Ideal.Maps

/-!
# Sheaves of Modules, Chapter 23: The annihilator of a sheaf of modules

This file formalizes the source section `The annihilator of a sheaf of
modules`.  The commutative sheaf-of-rings model from the preceding chapters
represents a ringed space by `CommRingSheaf` and its modules by
`CommRingSheafModule`.
-/

namespace Formalization.Books.Modules.Unit23

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit09
open Formalization.Books.Modules.Unit12
open Formalization.Books.Modules.Unit16
open Formalization.Books.Modules.Unit18
open Formalization.Books.Modules.Unit22
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit17
open Formalization.Books.Sheaves.Unit22

universe v

noncomputable section

/-! ## The scalar endomorphism map and its kernel -/

/- The Chapter 18 map represented the identity endomorphism of `F`; it is the
   canonical sheaf map sending a local scalar to multiplication by that
   scalar. -/
noncomputable abbrev scalarEndomorphismMap {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    sheafModuleUnit O ⟶ internalHom O F F :=
  finiteDualIdentityMap O F

/- The source's annihilator is the kernel in the sheaf-of-modules category. -/
noncomputable abbrev annihilator {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    CommRingSheafModule O :=
  sheafModuleKernel (commRingSheafToRingSheaf O) (scalarEndomorphismMap O F)

noncomputable abbrev annihilatorι {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    annihilator O F ⟶ sheafModuleUnit O :=
  kernel.ι (scalarEndomorphismMap O F)

/-! ## Stalk annihilators -/

/- Mathlib's canonical ideal of scalars annihilating a module. -/
abbrev stalkModuleAnnihilator {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (x : X) :
    Ideal (↑(TopCat.Presheaf.stalk (C := RingCat.{v})
      (commRingSheafToRingSheaf O).obj x)) :=
  Module.annihilator (↑(TopCat.Presheaf.stalk (C := RingCat.{v})
      (commRingSheafToRingSheaf O).obj x))
    (↑((sheafModuleStalkFunctor (commRingSheafToRingSheaf O) x).obj F))

/- The stalk of the kernel maps canonically into the stalk of the structure
   sheaf.  Its range is the ideal represented by the sheaf annihilator at the
   point. -/
/- The module stalk functor remembers the additive stalk of the unit module,
   while the target ideal is written in the ring stalk.  The canonical
   stalk-level identification is isolated here so the range below is an
   actual ideal of the stalk ring. -/
theorem exists_unitStalkLinearEquiv {X : TopCat.{v}}
    (O : CommRingSheaf X) (x : X) :
    Nonempty ((↑((sheafModuleStalkFunctor (commRingSheafToRingSheaf O) x).obj
      (sheafModuleUnit O))) ≃ₗ[
        ↑(TopCat.Presheaf.stalk (C := RingCat.{v})
          (commRingSheafToRingSheaf O).obj x)]
      (↑(TopCat.Presheaf.stalk (C := RingCat.{v})
        (commRingSheafToRingSheaf O).obj x))) := by
  sorry

noncomputable def unitStalkLinearEquiv {X : TopCat.{v}}
    (O : CommRingSheaf X) (x : X) :
    (↑((sheafModuleStalkFunctor (commRingSheafToRingSheaf O) x).obj
      (sheafModuleUnit O))) ≃ₗ[
        ↑(TopCat.Presheaf.stalk (C := RingCat.{v})
          (commRingSheafToRingSheaf O).obj x)]
      (↑(TopCat.Presheaf.stalk (C := RingCat.{v})
        (commRingSheafToRingSheaf O).obj x)) :=
  Classical.choice (exists_unitStalkLinearEquiv O x)

noncomputable def annihilatorStalkIdeal {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (x : X) :
    Ideal (↑(TopCat.Presheaf.stalk (C := RingCat.{v})
      (commRingSheafToRingSheaf O).obj x)) := by
  exact Submodule.map
    ((unitStalkLinearEquiv O x).toLinearMap.comp
      ((sheafModuleStalkFunctor (commRingSheafToRingSheaf O) x).map
        (annihilatorι O F)).hom) ⊤

/- The stalk comparison starts with the canonical inclusion of ideals. -/
theorem annihilator_stalk_inclusion {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (x : X) :
    annihilatorStalkIdeal O F x ≤ stalkModuleAnnihilator O F x := by
  sorry

theorem annihilator_stalk_eq_of_isFiniteType {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O)
    (hF : IsFiniteType F) (x : X) :
    annihilatorStalkIdeal O F x = stalkModuleAnnihilator O F x := by
  sorry

/-! ## Quotients by ideal sheaves -/

/- A submodule of the structure sheaf is the project model for an ideal
   sheaf.  The explicit monomorphism makes the containment hypotheses and
   quotient maps available to later declarations. -/
structure IdealSheaf {X : TopCat.{v}} (O : CommRingSheaf X) where
  carrier : CommRingSheafModule O
  inclusion : carrier ⟶ sheafModuleUnit O
  inclusion_mono : Mono inclusion

instance idealSheaf_inclusion_mono {X : TopCat.{v}} (O : CommRingSheaf X)
    (I : IdealSheaf O) : Mono I.inclusion :=
  I.inclusion_mono

abbrev idealSheafQuotient {X : TopCat.{v}} {O : CommRingSheaf X}
    (I : IdealSheaf O) : CommRingSheafModule O :=
  sheafModuleCokernel (commRingSheafToRingSheaf O) I.inclusion

abbrev idealSheafQuotientMap {X : TopCat.{v}} {O : CommRingSheaf X}
    (I : IdealSheaf O) : sheafModuleUnit O ⟶ idealSheafQuotient I :=
  cokernel.π I.inclusion

/- The source's notation `I ⊆ Ann(O_X)(F)` is represented by the canonical
   vanishing composite through the kernel.  By the kernel universal property,
   this is equivalent to a factorization of `I` through `annihilator O F`. -/
def IdealSheaf.IsContainedInAnnihilator {X : TopCat.{v}}
    {O : CommRingSheaf X} (I : IdealSheaf O) (F : CommRingSheafModule O) : Prop :=
  I.inclusion ≫ scalarEndomorphismMap O F = 0

theorem idealSheaf_factors_through_annihilator {X : TopCat.{v}}
    {O : CommRingSheaf X} (I : IdealSheaf O) (F : CommRingSheafModule O)
    (hI : I.IsContainedInAnnihilator F) :
    ∃ q : I.carrier ⟶ annihilator O F, q ≫ annihilatorι O F = I.inclusion := by
  exact ⟨kernel.lift (scalarEndomorphismMap O F) I.inclusion hI,
    kernel.lift_ι (scalarEndomorphismMap O F) I.inclusion hI⟩

/- The quotient action is packaged as an O/I action on F.  The compatibility
   equation is the categorical form of the usual scalar action, and the
   stalk field records the standard commutative-algebra quotient at every
   point using the canonical stalk-cokernel comparison. -/
structure QuotientModuleStructure {X : TopCat.{v}} {O : CommRingSheaf X}
    (I : IdealSheaf O) (F : CommRingSheafModule O)
    (hI : I.IsContainedInAnnihilator F) where
  action : tensorProductSheaf O (idealSheafQuotient I) F ⟶ F
  action_compatibility :
    tensorProductMap (idealSheafQuotientMap I) (𝟙 F) ≫ action =
      (sheafModuleLeftUnitor O F).hom
  stalk_quotient : ∀ x : X, Nonempty (
    (sheafModuleStalkFunctor (commRingSheafToRingSheaf O) x).obj
        (idealSheafQuotient I) ≅
      cokernel ((sheafModuleStalkFunctor (commRingSheafToRingSheaf O) x).map
        I.inclusion))

theorem quotientModuleStructure_exists {X : TopCat.{v}}
    {O : CommRingSheaf X} (I : IdealSheaf O) (F : CommRingSheafModule O)
    (hI : I.IsContainedInAnnihilator F) :
    Nonempty (QuotientModuleStructure I F hI) := by
  sorry

noncomputable def quotientModuleStructure {X : TopCat.{v}}
    {O : CommRingSheaf X} (I : IdealSheaf O) (F : CommRingSheafModule O)
    (hI : I.IsContainedInAnnihilator F) : QuotientModuleStructure I F hI :=
  Classical.choice (quotientModuleStructure_exists I F hI)

/-! ## Coherence -/

theorem annihilator_isCoherent_of_isCoherent {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O)
    (hO : IsCoherent (sheafModuleUnit O)) (hF : IsCoherent F) :
    IsCoherent (annihilator O F) := by
  sorry

end

end Formalization.Books.Modules.Unit23
