import Formalization.Books.Cohomology.Unit09
import Formalization.Books.Cohomology.Unit15
import Formalization.Books.Modules.Unit06.ClosedImmersions
import Formalization.Books.Modules.Unit07.CanonicalExactSequence
import Formalization.Books.Sheaves.Unit31.Infrastructure
import Formalization.Books.Topology.Unit09.NoetherianSpaces
import Formalization.Books.Topology.Unit10.KrullDimension
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Cohomology of Sheaves, Chapter 16: vanishing on Noetherian topological spaces

This file formalizes the precise interfaces in the source section
`Vanishing on Noetherian topological spaces`.  Cohomology, closed and open
sheaf operations, filtered colimits, irreducible components, and Krull
dimension use the canonical constructions from earlier chapters and Mathlib.
The proposition-valued source results are theorem interfaces; their proofs are
deferred to the prove stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite
open Set
open TopologicalSpace
open _root_.Topology
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Cohomology.Unit09
open Formalization.Books.Cohomology.Unit15
open Formalization.Books.Categories.Unit23
open Formalization.Books.Modules.Unit06
open Formalization.Books.Modules.Unit07
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Topology.Unit09

universe v

namespace Formalization.Books.Cohomology.Unit16

/-! ## Closed immersions -/

/- A topological closed immersion is a TopCat morphism whose underlying map is
   a closed embedding.  The map itself is retained so that the canonical
   sheaf pushforward can be used without introducing another pushforward. -/
structure ClosedImmersionOfTopologicalSpaces {Z X : TopCat.{v}} where
  map : Z ⟶ X
  isClosedEmbedding : IsClosedEmbedding (ConcreteCategory.hom map)

/- The direct image itself is exact; the higher-direct-image vanishing below
   is the derived-functor form used by the source proof. -/
theorem closedImmersion_directImage_isExact
    {Z X : TopCat.{v}} (i : ClosedImmersionOfTopologicalSpaces (Z := Z) (X := X)) :
    Formalization.Books.Categories.Unit23.IsExact
      (Formalization.Books.Cohomology.Unit02.abelianSheafPushforward i.map) := by
  sorry

/- The higher direct image vanishes for a closed immersion. -/
theorem closedImmersion_higherDirectImage_isZero
    {Z X : TopCat.{v}} (i : ClosedImmersionOfTopologicalSpaces (Z := Z) (X := X))
    (F : Ab Z) (p : ℕ) (hp : 0 < p) :
    IsZero (abelianSheafHigherDirectImageObject i.map F (p : ℤ)) := by
  sorry

/- Cohomology is unchanged by pushing an abelian sheaf through a closed
   immersion.  The source writes this as an equality of groups; the canonical
   categorical form is an isomorphism of additive-group objects. -/
theorem cohomology_of_closed_immersion
    {Z X : TopCat.{v}} (i : ClosedImmersionOfTopologicalSpaces (Z := Z) (X := X))
    (F : Ab Z) (p : ℕ) :
    Nonempty
      (abelianSheafCohomologyObject Z F (p : ℤ) ≅
        abelianSheafCohomologyObject X
          ((Formalization.Books.Cohomology.Unit02.abelianSheafPushforward
            i.map).obj F) (p : ℤ)) := by
  sorry

/-! ## Constant sheaves on irreducible spaces -/

/- This is the site-theoretic constant sheaf in the additive category, which
   is the canonical sheaf-valued version of the source's `underline A`. -/
noncomputable def constantAbelianSheaf (X : TopCat.{v}) (A : AddCommGrpCat.{v}) :
    Ab X :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{v}).obj A

noncomputable abbrev constantIntegerAbelianSheaf (X : TopCat.{v}) : Ab X :=
  constantAbelianSheaf X (AddCommGrpCat.of (ULift.{v} ℤ))

/- The proof in the source first observes that this constant sheaf is
   flasque. -/
theorem irreducible_constantAbelianSheaf_isFlasque
    {X : TopCat.{v}} [IrreducibleSpace X] (A : AddCommGrpCat.{v}) :
    FlasqueAbelianSheaf X (constantAbelianSheaf X A) := by
  sorry

theorem irreducible_constant_cohomology_isZero
    {X : TopCat.{v}} [IrreducibleSpace X] (A : AddCommGrpCat.{v})
    (p : ℕ) (hp : 0 < p) :
    IsZero
      (abelianSheafCohomologyObject X (constantAbelianSheaf X A) (p : ℤ)) := by
  sorry

/-! ## Finitely generated subsheaves of a constant sheaf -/

/- A local section is indexed by its open domain.  This is the abelian-sheaf
   analogue of the local-section data used in Modules 4. -/
abbrev AbelianLocalSection {X : TopCat.{v}} (F : Ab X) :=
  Σ U : Opens X, F.presheaf.obj (op U)

def AbelianSubsheafContainsLocalSection
    {X : TopCat.{v}} {F : Ab X} (P : Subobject F)
    (t : AbelianLocalSection F) : Prop :=
  abelianSubsheafContainsSection P t.1 t.2

def IsGeneratedByLocalSections {X : TopCat.{v}} (F : Ab X)
    (S : Set (AbelianLocalSection F)) : Prop :=
  (∀ t ∈ S, AbelianSubsheafContainsLocalSection (⊤ : Subobject F) t) ∧
    ∀ P : Subobject F,
      (∀ t ∈ S, AbelianSubsheafContainsLocalSection P t) → ⊤ ≤ P

def IsGeneratedByFinitelyManyQuasiCompactSections {X : TopCat.{v}}
    (F : Ab X) : Prop :=
  ∃ S : Set (AbelianLocalSection F), S.Finite ∧
    (∀ t ∈ S, IsCompact (t.1 : Set X)) ∧
      IsGeneratedByLocalSections F S

def IsGeneratedByAtMostOneQuasiCompactSection {X : TopCat.{v}}
    (F : Ab X) : Prop :=
  ∃ S : Set (AbelianLocalSection F), S.Finite ∧ S.ncard ≤ 1 ∧
    (∀ t ∈ S, IsCompact (t.1 : Set X)) ∧
      IsGeneratedByLocalSections F S

/- The source's `j_! underline Z_U` is the canonical extension by zero of
   the constant additive sheaf with value `ULift Z`. -/
noncomputable def openConstantIntegerExtension
    {X : TopCat.{v}} (U : Opens X) : Ab X :=
  (openAbelianSheafExtensionFunctor U).obj
    (constantIntegerAbelianSheaf (openSubspace U))

def OpenExtensionByZeroShortExact {X : TopCat.{v}} (Q : Ab X) : Prop :=
  ∃ (U V : Opens X), IsCompact (U : Set X) ∧ IsCompact (V : Set X) ∧
    ∃ (f : openConstantIntegerExtension V ⟶ openConstantIntegerExtension U)
      (g : openConstantIntegerExtension U ⟶ Q) (hfg : f ≫ g = 0),
      (ShortComplex.mk f g hfg).ShortExact

noncomputable def subobjectQuotient {X : TopCat.{v}}
    {F : Ab X} (P Q : Subobject F) (hQ : Q ≤ P) : Ab X :=
  cokernel (Subobject.ofLE Q P hQ)

/- The filtration and each of its displayed quotient sequences. -/
structure ConstantSheafSubobjectFiniteFiltration
    {X : TopCat.{v}} (P : Subobject (constantIntegerAbelianSheaf X)) where
  length : ℕ
  step : Fin (length + 1) → Subobject (constantIntegerAbelianSheaf X)
  step_le : ∀ i, step i ≤ P
  step_mono : ∀ {i j}, i.1 ≤ j.1 → step i ≤ step j
  zero : step ⟨0, Nat.succ_pos _⟩ = ⊥
  last : step ⟨length, Nat.lt_succ_self _⟩ = P
  generated : IsGeneratedByFinitelyManyQuasiCompactSections (P : Ab X)
  successive : ∀ i : Fin length,
    OpenExtensionByZeroShortExact
      (subobjectQuotient
        (step ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
        (step ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self _ )⟩)
        (step_mono (Nat.le_succ i.1)))

theorem subsheaf_of_constant_has_finite_filtration
    {X : TopCat.{v}} (P : Subobject (constantIntegerAbelianSheaf X))
    (hP : IsGeneratedByFinitelyManyQuasiCompactSections (P : Ab X)) :
    Nonempty (ConstantSheafSubobjectFiniteFiltration P) := by
  sorry

/- The one-generator reduction used in the proof of the next lemma. -/
theorem atMostOneGenerated_is_quotient_of_openConstantIntegerExtension
    {X : TopCat.{v}} (F : Ab X)
    (hF : IsGeneratedByAtMostOneQuasiCompactSection F) :
    ∃ U : Opens X, IsCompact (U : Set X) ∧
      ∃ q : openConstantIntegerExtension U ⟶ F, Epi q := by
  sorry

/- The extension-by-zero term in the canonical open/closed sequence is
   supported on the closure of the open. -/
theorem openExtension_supported_on_closure
    {X : TopCat.{v}} (U : Opens X) (F : Ab X) :
    ∃ G : Ab (Formalization.Books.Modules.Unit06.closedSubspace
        (closure (U : Set X))),
      Nonempty
        ((Formalization.Books.Modules.Unit06.closedSheafDirectImage AddCommGrpCat
            (closure (U : Set X))
            (isClosed_closure : IsClosed (closure (U : Set X)))).obj G ≅
          (openAbelianSheafExtensionFunctor U).obj
            ((openSheafRestriction AddCommGrpCat U).obj F)) := by
  sorry

/-! ## Vanishing from quasi-compact open generators -/

theorem vanishing_for_quasiCompact_open_extensions
    {X : TopCat.{v}} (d : ℕ)
    (hXcompact : IsCompact (Set.univ : Set X))
    (hBasis : HasQuasiCompactOpenBasis (TopCat.of X))
    (hIntersections : ∀ U V : Opens X,
      IsCompact (U : Set X) → IsCompact (V : Set X) →
        IsCompact ((U : Set X) ∩ (V : Set X)))
    (hExtensionVanishing : ∀ (U : Opens X), IsCompact (U : Set X) →
      ∀ p : ℕ, d < p →
        IsZero (abelianSheafCohomologyObject X
          (openConstantIntegerExtension U) (p : ℤ))) :
    ∀ (F : Ab X) (p : ℕ), d < p →
      IsZero (abelianSheafCohomologyObject X F (p : ℤ)) := by
  sorry

/-! ## The non-quasi-compact initial-segment example -/

abbrev DattaSpace : TopCat := TopCat.of InitialSegmentSpace

noncomputable def dattaOpen (n : ℕ+) : Opens DattaSpace := by
  let e : DattaSpace ≃ ℕ+ :=
    WithTopology.equiv ℕ+ initialSegmentTopology
  exact ⟨e ⁻¹' Set.Iic n,
    initialSegmentSpace_isOpen_iff.mpr (Or.inr (Or.inr ⟨n, rfl⟩))⟩

theorem datta_open_iff {U : Set DattaSpace} :
    IsOpen U ↔ U = ∅ ∨ U = Set.univ ∨ ∃ n : ℕ+, U = dattaOpen n := by
  sorry

/- The source identifies a sheaf on this space with the inverse system of
   sections on the initial segments, and global sections with its limit. -/
structure DattaSheafInverseSystemData
    (F : TopCat.Sheaf AddCommGrpCat.{0} DattaSpace) where
  diagram : ℕ+ᵒᵖ ⥤ AddCommGrpCat.{0}
  section_iso : ∀ n : ℕ+,
    Nonempty (diagram.obj (op n) ≅ F.presheaf.obj (op (dattaOpen n)))
  global_sections_iso : Nonempty
    ((abelianSheafGlobalSections DattaSpace).obj F ≅ limit diagram)

theorem datta_sheaf_is_inverse_system
    (F : TopCat.Sheaf AddCommGrpCat.{0} DattaSpace) :
    Nonempty (DattaSheafInverseSystemData F) := by
  sorry

/- The failure of exactness of inverse limits is recorded directly at the
   categorical level, while the nonzero H¹ consequence is recorded below. -/
theorem datta_inverse_limit_functor_not_exact :
    ¬ Formalization.Books.Categories.Unit23.IsExact
      (lim : (ℕ+ᵒᵖ ⥤ AddCommGrpCat.{0}) ⥤ AddCommGrpCat.{0}) := by
  sorry

theorem datta_exists_nonzero_first_cohomology :
    ∃ F : TopCat.Sheaf AddCommGrpCat.{0} DattaSpace,
      ¬ IsZero (abelianSheafCohomologyObject DattaSpace F (1 : ℤ)) := by
  sorry

theorem datta_open_extension_cohomology_isZero (n : ℕ+) (p : ℕ)
    (hp : 0 < p) :
    IsZero (abelianSheafCohomologyObject DattaSpace
      (openConstantIntegerExtension (dattaOpen n)) (p : ℤ)) := by
  sorry

/- The three positive hypotheses of the preceding vanishing lemma hold for
   the initial-segment space; compactness of the whole space is intentionally
   not asserted. -/
theorem datta_has_quasiCompact_open_basis :
    HasQuasiCompactOpenBasis (TopCat.of DattaSpace) := by
  sorry

theorem datta_quasiCompact_open_intersections
    {U V : Opens DattaSpace} (hU : IsCompact (U : Set DattaSpace))
    (hV : IsCompact (V : Set DattaSpace)) :
    IsCompact ((U : Set DattaSpace) ∩ (V : Set DattaSpace)) := by
  sorry

/-! ## Subsheaves of a constant sheaf on an irreducible space -/

noncomputable def constantMultipleIntegerAbelianSheaf
    (X : TopCat.{v}) (d : ℤ) : Ab X :=
  constantAbelianSheaf X
    (AddCommGrpCat.of (ULift.{v} (AddSubgroup.zmultiples d)))

structure SubsheafOfConstantIntegerLocalForm
    {X : TopCat.{v}}
    (P : Subobject (constantIntegerAbelianSheaf X)) where
  U : Opens X
  nonempty : (U : Set X).Nonempty
  d : ℤ
  restriction_iso : Nonempty
    ((openSheafRestriction AddCommGrpCat U).obj (P : Ab X) ≅
      constantMultipleIntegerAbelianSheaf (openSubspace U) d)

theorem subsheaf_of_constant_on_irreducible_has_local_form
    {X : TopCat.{v}} [IrreducibleSpace X]
    (P : Subobject (constantIntegerAbelianSheaf X)) :
    Nonempty (SubsheafOfConstantIntegerLocalForm P) := by
  sorry

/- In the d = 0 branch of the proof, the dimension hypothesis is implicit in
   the source's induction context and is made explicit here. -/
theorem irreducible_zero_dimensional_nonempty_open_eq_univ
    {X : TopCat.{v}} [NoetherianSpace X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ (0 : WithBot ℕ∞))
    {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) :
    U = Set.univ := by
  sorry

theorem irreducible_zero_dimensional_sheaf_is_constant
    {X : TopCat.{v}} [NoetherianSpace X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ (0 : WithBot ℕ∞)) (F : Ab X) :
    ∃ A : AddCommGrpCat.{v},
      Nonempty (F ≅ constantAbelianSheaf X A) := by
  sorry

/-! ## Grothendieck's vanishing theorem -/

/- The displayed `0 → j_!j^*F → F → i_*i^*F → 0` is already the
   source-faithful `canonicalExactSequence` from Modules 7, whose
   `canonicalExactSequence_shortExact` theorem is imported above. -/

theorem grothendieck_vanishing
    {X : TopCat.{v}} [NoetherianSpace X] (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Ab X) (p : ℕ) (hp : d < p) :
    IsZero (abelianSheafCohomologyObject X F (p : ℤ)) := by
  sorry

end Formalization.Books.Cohomology.Unit16
