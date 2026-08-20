import Formalization.Books.Schemes.Unit09.Schemes
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.Topology.Sober

/-!
# Schemes, Chapter 11: Zariski topology of schemes

This file records the topological statements in the chapter.  Scheme-specific affine opens,
basic opens, and the affine Zariski site are Mathlib's canonical constructions; the source-facing
interfaces below keep the chapter's statements available in its own namespace.
-/

namespace Formalization.Books.Schemes.Unit11

open CategoryTheory
open AlgebraicGeometry
open Opposite
open TopologicalSpace

universe u v

noncomputable section

/-! ## Generic points and affine-open topology -/

/-- Every irreducible closed subset of a scheme has a unique generic point. -/
theorem scheme_is_sober (X : Scheme.{u}) :
    ∀ {Z : Set X}, IsIrreducible Z → IsClosed Z →
      ∃! x : X, IsGenericPoint x Z := by
  sorry

/-- The affine opens form the topological basis asserted in the chapter. -/
theorem affine_opens_form_basis (X : Scheme.{u}) :
    Opens.IsBasis X.affineOpens :=
  X.isBasis_affineOpens

/-- There are schemes with two affine opens whose intersection is not affine. -/
theorem exists_nonaffine_intersection_of_affine_opens :
    ∃ (X : Scheme.{u}) (U V : X.Opens),
      IsAffineOpen U ∧ IsAffineOpen V ∧ ¬ IsAffineOpen (U ⊓ V) := by
  sorry

/-- The underlying space of a scheme is locally quasi-compact. -/
theorem scheme_is_locally_quasi_compact (X : Scheme.{u}) :
    LocallyCompactSpace X := by
  sorry

/-! ## Basic opens on overlapping affine charts -/

/-- A point in the intersection of two affine opens has an affine basic-open neighborhood which
is basic in both charts. -/
theorem exists_affine_basicOpen_neighborhood
    {X : Scheme.{u}} {U V : X.affineOpens} {x : X}
    (hx : x ∈ (U : X.Opens) ⊓ (V : X.Opens)) :
    ∃ (W : X.affineOpens)
      (f : Γ(X, (U : X.Opens))) (g : Γ(X, (V : X.Opens))),
      x ∈ (W : X.Opens) ∧
        (W : X.Opens) = X.basicOpen f ∧
        (W : X.Opens) = X.basicOpen g := by
  sorry

/-- A finite affine-basic-open refinement of an affine open inside an affine-open cover. -/
theorem exists_finite_affineBasicOpen_cover
    {X : Scheme.{u}} {ι : Type v} (U : ι → X.affineOpens)
    (hU : (⨆ i, (U i : X.Opens)) = ⊤) (V : X.affineOpens) :
    ∃ n : ℕ, ∃ W : Fin n → X.affineOpens,
      (⨆ j, (W j : X.Opens)) = (V : X.Opens) ∧
        ∀ j, ∃ i : ι, ∃ f : Γ(X, (U i : X.Opens)),
          (W j : X.Opens) = X.basicOpen f := by
  sorry

/-! ## Sheaves on the affine basis -/

/-- A presheaf on the small affine Zariski site of `X`. -/
abbrev AffineOpenPresheaf (X : Scheme.{u}) :=
  (Scheme.AffineZariskiSite X)ᵒᵖ ⥤ Type u

/-- The presheaf on affine opens obtained by restricting a sheaf on the underlying space. -/
noncomputable def affineOpenPresheafOfSchemeSheaf
    (X : Scheme.{u}) (F : TopCat.Sheaf (Type u) X) : AffineOpenPresheaf X :=
  ((Scheme.AffineZariskiSite.sheafEquiv (X := X) (A := Type u)).inverse.obj F).val

/-- A presheaf on affine opens is the restriction of a sheaf on `X`. -/
def IsRestrictionOfSchemeSheaf
    {X : Scheme.{u}} (F : AffineOpenPresheaf X) : Prop :=
  ∃ G : TopCat.Sheaf (Type u) X,
    Nonempty (F ≅ affineOpenPresheafOfSchemeSheaf X G)

/-- The sheaf condition for a presheaf on the small affine Zariski site. -/
def IsAffineSiteSheaf {X : Scheme.{u}} (F : AffineOpenPresheaf X) : Prop :=
  CategoryTheory.Presheaf.IsSheaf
    (Scheme.AffineZariskiSite.grothendieckTopology X) F

/-- The affine-basis two-open gluing condition from the source.

The site order records precisely that an affine open is a basic open in a larger affine open.
The auxiliary object `T` is the affine basic-open representative of the intersection, so the
compatibility equation and the restriction maps are expressed using the canonical site arrows.
-/
noncomputable def affineEmpty (X : Scheme.{u}) : Scheme.AffineZariskiSite X :=
  ⟨⊥, isAffineOpen_bot X⟩

def HasBinaryStandardOpenGluing
    {X : Scheme.{u}} (F : AffineOpenPresheaf X) : Prop :=
  (Nonempty (F.obj (op (affineEmpty X))) ∧
      Subsingleton (F.obj (op (affineEmpty X)))) ∧
    ∀ (U V W : Scheme.AffineZariskiSite X)
      (hVU : V ≤ U) (hWU : W ≤ U)
      (hcover : U.toOpens = V.toOpens ⊔ W.toOpens),
      ∃ (T : Scheme.AffineZariskiSite X) (hTV : T ≤ V) (hTW : T ≤ W),
        T.toOpens = V.toOpens ⊓ W.toOpens ∧
        Function.Injective (fun s : F.obj (op U) =>
          (F.map (homOfLE hVU).op s, F.map (homOfLE hWU).op s)) ∧
        ∀ (sV : F.obj (op V)) (sW : F.obj (op W)),
          (F.map (homOfLE hTV).op sV = F.map (homOfLE hTW).op sW ↔
            ∃ sU : F.obj (op U),
              F.map (homOfLE hVU).op sU = sV ∧
                F.map (homOfLE hWU).op sU = sW)

/-- A presheaf on affine opens extends to a sheaf exactly when it is a sheaf on that basis, and
exactly when the empty-open and binary standard-open gluing tests hold. -/
theorem affine_open_presheaf_sheaf_criterion
    {X : Scheme.{u}} (F : AffineOpenPresheaf X) :
    (IsRestrictionOfSchemeSheaf F ↔ IsAffineSiteSheaf F) ∧
      (IsAffineSiteSheaf F ↔ HasBinaryStandardOpenGluing F) := by
  sorry

/-! ## Finite discrete schemes and closed points -/

/-- The underlying space is finite and discrete. -/
def IsFiniteDiscreteScheme (X : Scheme.{u}) : Prop :=
  Finite X ∧ DiscreteTopology X

/-- A scheme with finite discrete underlying space is affine. -/
theorem finite_discrete_scheme_is_affine
    (X : Scheme.{u}) (hX : IsFiniteDiscreteScheme X) : IsAffine X := by
  sorry

/-- A scheme has a closed point when one of its points is a closed singleton. -/
def HasClosedPoint (X : Scheme.{u}) : Prop :=
  ∃ x : X, IsClosed ({x} : Set X)

/-- There exists a scheme without closed points. -/
theorem exists_scheme_without_closed_points :
    ∃ X : Scheme.{u}, ¬ HasClosedPoint X := by
  sorry

end

end Formalization.Books.Schemes.Unit11
