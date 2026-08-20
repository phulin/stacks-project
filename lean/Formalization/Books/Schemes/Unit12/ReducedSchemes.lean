import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.LocallyClosed

/-!
# Schemes, Chapter 12: Reduced schemes

The canonical reduced-scheme predicate and ideal-sheaf constructions are Mathlib's
`AlgebraicGeometry.IsReduced`, `Scheme.IdealSheafData.vanishingIdeal`, and
`Scheme.IdealSheafData.subscheme`.  This file records the source-facing interfaces for
local rings, reduced induced structures, reductions, locally closed subsets, and
factorization through a closed subscheme.
-/

namespace Formalization.Books.Schemes.Unit12

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry
open scoped Set.Notation

universe u

noncomputable section

/-! ## Reduced schemes -/

/- The name is chapter-local, while the predicate itself is Mathlib's canonical one. -/
abbrev IsReducedScheme (X : Scheme.{u}) : Prop := AlgebraicGeometry.IsReduced X

/-- A scheme is reduced exactly when all of its local rings are reduced. -/
theorem isReducedScheme_iff_localRings (X : Scheme.{u}) :
    IsReducedScheme X ↔ ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
  constructor
  · intro h x
    let _ : IsReducedScheme X := h
    infer_instance
  · intro h
    let _ : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := h
    exact AlgebraicGeometry.isReduced_of_isReduced_stalk X

/-- The sectionwise characterization of reduced schemes. -/
theorem isReducedScheme_iff_sections (X : Scheme.{u}) :
    IsReducedScheme X ↔ ∀ U : X.Opens, _root_.IsReduced Γ(X, U) := by
  constructor
  · intro h U
    exact h.component_reduced U
  · intro h
    exact ⟨h⟩

/-- The affine characterization of reducedness. -/
theorem affine_isReduced_iff (R : CommRingCat.{u}) :
    IsReducedScheme (Spec R) ↔ _root_.IsReduced R :=
  AlgebraicGeometry.affine_isReduced_iff R

/-! ## Closed subschemes and reduced induced structures -/

/- A closed subscheme is represented by Mathlib's ideal-sheaf datum.  Its support is
   the underlying closed subset, and `subscheme`/`subschemeι` are the associated scheme
   and closed immersion. -/
structure SchemeStructure (X : Scheme.{u}) (T : Closeds X) where
  ideal : X.IdealSheafData
  support_eq : ideal.support = T

abbrev SchemeStructure.scheme {X : Scheme.{u}} {T : Closeds X}
    (Z : SchemeStructure X T) : Scheme.{u} :=
  Z.ideal.subscheme

abbrev SchemeStructure.inclusion {X : Scheme.{u}} {T : Closeds X}
    (Z : SchemeStructure X T) : Z.scheme ⟶ X :=
  Z.ideal.subschemeι

/-- The reduced induced scheme structure on a closed subset. -/
noncomputable def reducedInducedSchemeStructure
    (X : Scheme.{u}) (T : Closeds X) : SchemeStructure X T :=
  { ideal := Scheme.IdealSheafData.vanishingIdeal T
    support_eq := by
      ext x
      simp }

/-- The reduced induced subscheme is reduced. -/
theorem reducedInducedSchemeStructure_isReduced
    (X : Scheme.{u}) (T : Closeds X) :
    IsReducedScheme (reducedInducedSchemeStructure X T).scheme := by
  sorry

/-- The reduced induced subscheme has exactly the prescribed underlying closed subset. -/
theorem reducedInducedSchemeStructure_range
    (X : Scheme.{u}) (T : Closeds X) :
    Set.range (reducedInducedSchemeStructure X T).inclusion = (T : Set X) := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact congrArg (fun S : Closeds X => (S : Set X))
    (reducedInducedSchemeStructure X T).support_eq

/-- There is a unique reduced closed subscheme with a prescribed closed underlying set. -/
theorem exists_unique_reduced_closed_subscheme
    (X : Scheme.{u}) (T : Closeds X) :
    ∃! Z : SchemeStructure X T, IsReducedScheme Z.scheme := by
  sorry

/-- The reduction of `X`, represented as its reduced induced scheme structure. -/
noncomputable def reductionStructure (X : Scheme.{u}) : SchemeStructure X (⊤ : Closeds X) :=
  reducedInducedSchemeStructure X ⊤

/-- The reduced scheme `X_red`. -/
abbrev reduction (X : Scheme.{u}) : Scheme.{u} :=
  (reductionStructure X).scheme

/-- The canonical closed immersion `X_red ⟶ X`. -/
abbrev reductionι (X : Scheme.{u}) : reduction X ⟶ X :=
  (reductionStructure X).inclusion

/-- The reduction is reduced. -/
theorem reduction_isReduced (X : Scheme.{u}) : IsReducedScheme (reduction X) := by
  exact reducedInducedSchemeStructure_isReduced X ⊤

/-! ## Locally closed reduced induced structures -/

/-- The boundary of a subset, as used for a locally closed reduced induced structure. -/
def boundary (X : Scheme.{u}) (T : Set X) : Set X := closure T \ T

/-- The boundary of a locally closed subset is closed. -/
theorem isClosed_boundary (X : Scheme.{u}) {T : Set X} (hT : IsLocallyClosed T) :
    IsClosed (boundary X T) := by
  simpa [boundary, coborder] using hT.isOpen_coborder

/-- The open complement of the boundary of a locally closed subset. -/
noncomputable def locallyClosedOpen (X : Scheme.{u}) (T : Set X) (hT : IsLocallyClosed T) : X.Opens :=
  ⟨(boundary X T)ᶜ, (isClosed_boundary X hT).isOpen_compl⟩

/-- The locally closed subset, viewed as a closed subset of the open complement of its boundary. -/
noncomputable def locallyClosedClosedSubset (X : Scheme.{u}) (T : Set X) (hT : IsLocallyClosed T) :
    Closeds (locallyClosedOpen X T hT) := by
  refine ⟨{x : locallyClosedOpen X T hT | (x : X) ∈ T}, ?_⟩
  change IsClosed (coborder T ↓∩ T)
  exact isClosed_preimage_val_coborder

/-- The reduced induced scheme structure on a locally closed subset. -/
noncomputable def locallyClosedReducedInducedSchemeStructure
    (X : Scheme.{u}) (T : Set X) (hT : IsLocallyClosed T) :
    SchemeStructure (locallyClosedOpen X T hT)
      (locallyClosedClosedSubset X T hT) :=
  reducedInducedSchemeStructure (locallyClosedOpen X T hT)
    (locallyClosedClosedSubset X T hT)

/-! ## Factorization through reductions -/

/-- A morphism factors through a closed subscheme when it factors through its inclusion. -/
def FactorsThrough {Y X : Scheme.{u}} (f : Y ⟶ X)
    {T : Closeds X} (Z : SchemeStructure X T) : Prop :=
  ∃ g : Y ⟶ Z.scheme, g ≫ Z.inclusion = f

/-- A map from a reduced scheme factors through a closed subscheme exactly when its image is
contained in the underlying closed subset. -/
theorem factorsThrough_iff_range_subset
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsReducedScheme Y]
    {T : Closeds X} (Z : SchemeStructure X T) :
    FactorsThrough f Z ↔ Set.range f ⊆ (T : Set X) := by
  sorry

/-- Every morphism from a reduced scheme factors through the reduction of its target. -/
theorem exists_factor_through_reduction
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsReducedScheme Y] :
    ∃ g : Y ⟶ reduction X, g ≫ reductionι X = f := by
  sorry

end

end Formalization.Books.Schemes.Unit12
