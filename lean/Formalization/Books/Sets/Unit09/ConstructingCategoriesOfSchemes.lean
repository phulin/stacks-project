import Formalization.Books.Sets.Unit08
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Localization.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Set Theory, Chapter 9: Constructing categories of schemes

This file formalizes the size bounds and closure statements in the source
section.  Mathlib has a fully developed category of schemes, but it does not
identify that type with the ambient ZFC universe used in the textbook.  The
small `SchemeCoding` interface below records that missing bridge explicitly:
it codes each Lean scheme by a `ZFSet`, and `Sch c α` is the full subcategory
of schemes whose codes lie in `V_α`.

All theorem proofs are intentionally deferred to the prove stage.  Definitions
which are direct translations of the source are given actual bodies.
-/

universe u v

namespace Formalization.Books.Sets.Unit09

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

/-! ### Size and the bound function -/

/-- The cardinality of the affine opens of a scheme. -/
def affineOpenCardinal (X : Scheme.{u}) : Cardinal.{u} :=
  Cardinal.mk X.affineOpens

/-- The supremum of the cardinalities of sections on affine opens. -/
def affineSectionCardinal (X : Scheme.{u}) : Cardinal.{u} :=
  ⨆ U : X.affineOpens, Cardinal.mk (Γ(X, U.1))

/-- The size of a scheme used in this chapter. -/
def schemeSize (X : Scheme.{u}) : Cardinal.{u} :=
  max Cardinal.aleph0 (max (affineOpenCardinal X) (affineSectionCardinal X))

/-- The cardinal bound used when closing a collection of schemes. -/
def Bound (κ : Cardinal.{u}) : Cardinal.{u} :=
  max (κ ^ Cardinal.aleph0) (Order.succ κ)

/-- The alternative faster-growing bound mentioned in the source remark. -/
def alternativeBound (κ : Cardinal.{u}) : Cardinal.{u} := κ ^ κ

/-- The affine coordinate ring of an affine scheme. -/
abbrev schemeRing (X : Scheme.{u}) := Γ(X, ⊤)

/-! ### The set-theoretic coding bridge and the full subcategories `Sch α` -/

/-- A coding of Lean schemes by the ambient `ZFSet` universe.

The source treats schemes as objects of the ambient set universe.  This
interface keeps that ambient coding visible instead of silently identifying
the Lean type `Scheme` with `ZFSet`.
-/
structure SchemeCoding where
  code : Scheme.{u} → ZFSet.{u}
  injective : Function.Injective code

/-- The predicate that a coded scheme belongs to the von Neumann level `V_α`. -/
def SchemeInLevel (c : SchemeCoding.{u}) (α : Ordinal.{u}) (X : Scheme.{u}) : Prop :=
  c.code X ∈ ZFSet.vonNeumann α

/-- The full subcategory of coded schemes whose codes belong to `V_α`. -/
abbrev Sch (c : SchemeCoding.{u}) (α : Ordinal.{u}) : Type _ :=
  (ObjectProperty.FullSubcategory (SchemeInLevel c α))

/-- The inclusion of `Sch α` into the category of schemes. -/
abbrev schInclusion (c : SchemeCoding.{u}) (α : Ordinal.{u}) :
    Sch c α ⥤ Scheme :=
  ObjectProperty.ι (SchemeInLevel c α)

/-- A scheme is represented at level `α` when an object of `Sch α` is isomorphic to it. -/
def IsRepresentedAt (c : SchemeCoding.{u}) (α : Ordinal.{u}) (X : Scheme.{u}) : Prop :=
  ∃ Y : Sch c α, Nonempty (Y.obj ≅ X)

/-! ### Countable diagrams and the closure predicates -/

/- The source's countability hypothesis is Mathlib's canonical
`CategoryTheory.CountableCategory`, whose fields record countable objects and
countable hom types. -/

/-- Existence of a limit cone, without choosing a global `HasLimit` instance. -/
def HasLimitCone {C : Type u} [Category C] {I : Type v} [Category I]
    (F : I ⥤ C) : Prop :=
  Nonempty (LimitCone F)

/-- Existence of a colimit cocone, without choosing a global `HasColimit` instance. -/
def HasColimitCocone {C : Type u} [Category C] {I : Type v} [Category I]
    (F : I ⥤ C) : Prop :=
  Nonempty (ColimitCocone F)

/-- The source's phrase “isomorphic to the ambient limit” for a chosen subcategory cone. -/
def LimitConeAgreesWithAmbient {c : SchemeCoding.{u}} {α : Ordinal.{u}}
    {I : Type v} [Category I] (F : I ⥤ Sch c α) : Prop :=
  ∀ (t : LimitCone F) (s : LimitCone (F ⋙ schInclusion c α)),
    Nonempty ((schInclusion c α).obj t.cone.pt ≅ s.cone.pt)

/-- The source's phrase “isomorphic to the ambient colimit” for a chosen subcategory cocone. -/
def ColimitCoconeAgreesWithAmbient {c : SchemeCoding.{u}} {α : Ordinal.{u}}
    {I : Type v} [Category I] (F : I ⥤ Sch c α) : Prop :=
  ∀ (t : ColimitCocone F) (s : ColimitCocone (F ⋙ schInclusion c α)),
    Nonempty ((schInclusion c α).obj t.cocone.pt ≅ s.cocone.pt)

/-! ### The bounded-size and category-construction lemmas -/

/-- There is a set of scheme representatives for every fixed size bound. -/
theorem exists_bounded_scheme_representatives (κ : Cardinal.{u}) :
    ∃ A : Set Scheme.{u},
      ∀ X : Scheme.{u}, schemeSize X ≤ κ →
        ∃ Y ∈ A, Nonempty (Y ≅ X) := by
  sorry

/-- The stage condition used in the transfinite construction of the small category. -/
def StageAdmissible (c : SchemeCoding.{u}) (α β : Ordinal.{u})
    (fα : Ordinal.{u}) : Prop :=
  α + 1 ≤ β ∧ fα ≤ β ∧
    (∀ S : Sch c fα, ∀ T : Scheme.{u},
      schemeSize T ≤ Bound (schemeSize S.obj) → IsRepresentedAt c β T) ∧
    (∀ {I : Type u} [Category.{u} I] [CountableCategory I]
      (F : I ⥤ Sch c fα),
      (HasLimitCone (F ⋙ schInclusion c fα) ∨
        HasColimitCocone (F ⋙ schInclusion c fα)) →
      ∃ T : Scheme.{u}, IsRepresentedAt c β T)

/-- The transfinite-recursion interface for the function `f` in the source proof. -/
def IsSchemeClosureFunction (c : SchemeCoding.{u}) (f : Ordinal.{u} → Ordinal.{u}) : Prop :=
  f 0 = 0 ∧
    (∀ α, IsLeast {β | StageAdmissible c α β (f α)} (f (α + 1))) ∧
    (∀ α, Order.IsSuccLimit α → f α = ⨆ β : Set.Iio α, f β.1)

/-- The transfinite stage function described in the proof of the construction lemma exists. -/
theorem exists_scheme_closure_function (c : SchemeCoding.{u}) :
    ∃ f : Ordinal.{u} → Ordinal.{u}, IsSchemeClosureFunction c f := by
  sorry

/-- A limit level containing the initial set and closed under the source's operations. -/
theorem lemma_construct_category (c : SchemeCoding.{u}) (S₀ : Set Scheme.{u}) :
    ∃ α : Ordinal.{u}, Order.IsSuccLimit α ∧
      S₀ ⊆ {X | SchemeInLevel c α X} ∧
      (∀ S : Sch c α, ∀ T : Scheme.{u},
        schemeSize T ≤ Bound (schemeSize S.obj) → IsRepresentedAt c α T) ∧
      (∀ {I : Type u} [Category.{u} I] [CountableCategory I]
        (F : I ⥤ Sch c α),
        HasLimitCone (F ⋙ schInclusion c α) ↔ HasLimitCone F) ∧
      (∀ {I : Type u} [Category.{u} I] [CountableCategory I]
        (F : I ⥤ Sch c α), LimitConeAgreesWithAmbient F) ∧
      (∀ {I : Type u} [Category.{u} I] [CountableCategory I]
        (F : I ⥤ Sch c α),
        HasColimitCocone (F ⋙ schInclusion c α) ↔ HasColimitCocone F) ∧
      (∀ {I : Type u} [Category.{u} I] [CountableCategory I]
        (F : I ⥤ Sch c α), ColimitCoconeAgreesWithAmbient F) := by
  sorry

/-!
The reflection remark is recorded at the level of a witness relation.  The
two clauses correspond to reflecting the binary relation and its existential
projection together; this is exactly the combination needed to keep a chosen
witness inside the reflected level.
-/

/-- External and relativized witness predicates agree on a level. -/
def ReflectsWitnessRelation (M : ZFSet.{u})
    (P PRel : ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  (∀ X Y, X ∈ M → Y ∈ M → (P X Y ↔ PRel X Y)) ∧
    (∀ X, X ∈ M → ((∃ Y, P X Y) ↔ ∃ Y ∈ M, PRel X Y))

/-- Reflecting both a witness relation and its existential projection keeps witnesses in the level. -/
theorem reflected_witness_mem {M X : ZFSet.{u}}
    {P PRel : ZFSet.{u} → ZFSet.{u} → Prop}
    (hM : ReflectsWitnessRelation M P PRel) (hX : X ∈ M)
    (hP : ∃ Y, P X Y) :
    ∃ Y ∈ M, P X Y := by
  sorry

/-! ### Basic size bounds -/

/-- For an affine scheme, the size is the maximum of `ℵ₀` and its coordinate ring. -/
theorem schemeSize_affine (X : Scheme.{u}) [IsAffine X] :
    schemeSize X = max Cardinal.aleph0 (Cardinal.mk (schemeRing X)) := by
  sorry

/-- The size bound for an open cover by schemes. -/
theorem schemeSize_le_of_openCover (X : Scheme.{u}) (𝒰 : X.OpenCover) :
    schemeSize X ≤
      max (Cardinal.mk 𝒰.I₀) (⨆ i : 𝒰.I₀, schemeSize (𝒰.X i)) := by
  sorry

/-- The size bound for a fibre product of schemes. -/
theorem schemeSize_pullback_le {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    schemeSize (pullback f g) ≤ max (schemeSize X) (schemeSize Y) := by
  sorry

/-- A quasi-compact, locally finite-type morphism does not increase scheme size. -/
theorem schemeSize_le_of_quasiCompact_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [LocallyOfFiniteType f] :
    schemeSize X ≤ schemeSize S := by
  sorry

/-- The two size-bounded cases of the monomorphism lemma. -/
theorem schemeSize_le_of_monomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f]
    (h : QuasiCompact f ∨ LocallyOfFinitePresentation f) :
    schemeSize X ≤ schemeSize Y := by
  sorry

/-- The source's warning that locally finite type alone does not give the same bound. -/
theorem exists_locallyOfFiniteType_monomorphism_not_size_bounded :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y),
      Mono f ∧ LocallyOfFiniteType f ∧ ¬ schemeSize X ≤ schemeSize Y := by
  sorry

/-! ### What belongs to the constructed category -/

/-- A finite-type scheme morphism in the sense used by this chapter. -/
def IsFiniteTypeSchemeMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  QuasiCompact f ∧ LocallyOfFiniteType f

/-- An affine-open cover with a prescribed cardinality bound. -/
def HasAffineOpenCoverOfCardinalAtMost (X : Scheme.{u}) (κ : Cardinal.{u}) : Prop :=
  ∃ 𝒰 : X.OpenCover, Cardinal.mk 𝒰.I₀ ≤ κ ∧ ∀ i, IsAffine (𝒰.X i)

/-- Pullbacks of objects of `Sch α` remain in `Sch α` and are ambient pullbacks. -/
theorem scheme_category_has_pullbacks {c : SchemeCoding.{u}} {α : Ordinal.{u}}
    (hα : ∀ {I : Type u} [Category.{u} I] [CountableCategory I]
      (F : I ⥤ Sch c α), HasLimitCone (F ⋙ schInclusion c α) ↔ HasLimitCone F)
    (hαIso : ∀ {I : Type u} [Category.{u} I] [CountableCategory I]
      (F : I ⥤ Sch c α), LimitConeAgreesWithAmbient F)
    {X Y S : Sch c α} (f : X.obj ⟶ S.obj) (g : Y.obj ⟶ S.obj) :
    ∃ P : Sch c α, Nonempty (P.obj ≅ pullback f g) := by
  sorry

/-- Countable coproducts of objects of `Sch α` remain in `Sch α`. -/
theorem scheme_category_has_countable_coproducts {c : SchemeCoding.{u}} {α : Ordinal.{u}}
    (hα : ∀ {I : Type u} [Category.{u} I] [CountableCategory I]
      (F : I ⥤ Sch c α), HasColimitCocone (F ⋙ schInclusion c α) ↔ HasColimitCocone F)
    (hαIso : ∀ {I : Type u} [Category.{u} I] [CountableCategory I]
      (F : I ⥤ Sch c α), ColimitCoconeAgreesWithAmbient F)
    {I : Type u} [Countable I] (S : I → Sch c α) :
    ∃ P : Sch c α, ∃ t : ColimitCocone (Discrete.functor S),
      Nonempty (P.obj ≅ t.cocone.pt.obj) := by
  sorry

/-- Open subschemes of objects of `Sch α` have representatives in `Sch α`. -/
theorem openImmersion_represented {c : SchemeCoding.{u}} {α : Ordinal.{u}}
    {S U : Scheme.{u}} (hS : SchemeInLevel c α S) (f : U ⟶ S) [IsOpenImmersion f] :
    IsRepresentedAt c α U := by
  sorry

/-- Closed subschemes of objects of `Sch α` have representatives in `Sch α`. -/
theorem closedImmersion_represented {c : SchemeCoding.{u}} {α : Ordinal.{u}}
    {S T : Scheme.{u}} (hS : SchemeInLevel c α S) (f : T ⟶ S)
    (hf : IsClosedImmersion f) :
    IsRepresentedAt c α T := by
  sorry

/-- Finite-type schemes over objects of `Sch α` have representatives in `Sch α`. -/
theorem finiteType_represented {c : SchemeCoding.{u}} {α : Ordinal.{u}}
    {S T : Scheme.{u}} (hS : SchemeInLevel c α S) (f : T ⟶ S)
    (hf : IsFiniteTypeSchemeMorphism f) :
    IsRepresentedAt c α T := by
  sorry

/-- A scheme glued from a bounded open cover has a representative in `Sch α`. -/
theorem openCover_represented {c : SchemeCoding.{u}} {α : Ordinal.{u}}
    {S T : Scheme.{u}} (hT : SchemeInLevel c α T) (𝒰 : S.OpenCover)
    (h₁ : ∀ i, schemeSize (𝒰.X i) ≤ (schemeSize T) ^ Cardinal.aleph0)
    (h₂ : Cardinal.mk 𝒰.I₀ ≤ (schemeSize T) ^ Cardinal.aleph0) :
    IsRepresentedAt c α S := by
  sorry

/-- Locally finite-type schemes with a sufficiently small affine cover have representatives. -/
theorem locallyOfFiniteType_represented {c : SchemeCoding.{u}} {α : Ordinal.{u}}
    {S T : Scheme.{u}} (hS : SchemeInLevel c α S) (f : T ⟶ S)
    [LocallyOfFiniteType f]
    (𝒰 : T.OpenCover) (h𝒰 : ∀ i, IsAffine (𝒰.X i))
    (hcard : Cardinal.mk 𝒰.I₀ ≤ (schemeSize S) ^ Cardinal.aleph0) :
    IsRepresentedAt c α T := by
  sorry

/-- The continuum-sized affine-cover example from the source. -/
theorem locallyOfFiniteType_represented_of_continuum_affineCover
    {c : SchemeCoding.{u}} {α : Ordinal.{u}} {S T : Scheme.{u}}
    (hS : SchemeInLevel c α S) (f : T ⟶ S) [LocallyOfFiniteType f]
    (𝒰 : T.OpenCover) (h𝒰 : ∀ i, IsAffine (𝒰.X i))
    (hcard : Cardinal.mk 𝒰.I₀ ≤ Cardinal.aleph0 ^ Cardinal.aleph0) :
    IsRepresentedAt c α T := by
  sorry

/-- Monomorphisms of the two bounded kinds have representatives in `Sch α`. -/
theorem monomorphism_represented {c : SchemeCoding.{u}} {α : Ordinal.{u}}
    {S T : Scheme.{u}} (hS : SchemeInLevel c α S) (f : T ⟶ S) [Mono f]
    (hf : QuasiCompact f ∨ LocallyOfFinitePresentation f) :
    IsRepresentedAt c α T := by
  sorry

/-! ### Explicit affine constructions -/

/- Mathlib's `AdicCompletion I R` is the canonical compatible-family model of
the inverse limit of the quotients by the powers of `I`. -/

/- The canonical algebraic closure is Mathlib's `AlgebraicClosure`; the base
field here is the residue field of the corresponding point of `Spec R`. -/
abbrev residueFieldAlgebraicClosure (R : CommRingCat.{u})
    (p : PrimeSpectrum R) : Type u :=
  AlgebraicClosure p.asIdeal.ResidueField

/-- A scheme is represented in `Sch α` whenever its affine coordinate ring has a bounded
cardinality construction of one of the kinds listed in the source. -/
theorem affine_construction_adic_completion
    {c : SchemeCoding.{u}} {α : Ordinal.{u}} {T : Scheme.{u}}
    (hT : SchemeInLevel c α T) [IsAffine T] (I : Ideal (schemeRing T))
    : IsRepresentedAt c α
      (Spec (CommRingCat.of (AdicCompletion I (schemeRing T)))) := by
  sorry

theorem affine_construction_finite_type_algebra
    {c : SchemeCoding.{u}} {α : Ordinal.{u}} {T : Scheme.{u}}
    (hT : SchemeInLevel c α T) [IsAffine T]
    (R' : Type u) [CommRing R'] [Algebra (schemeRing T) R']
    (hR' : (algebraMap (schemeRing T) R').FiniteType) :
    IsRepresentedAt c α (Spec (CommRingCat.of R')) := by
  sorry

theorem affine_construction_localization
    {c : SchemeCoding.{u}} {α : Ordinal.{u}} {T : Scheme.{u}}
    (hT : SchemeInLevel c α T) [IsAffine T] (M : Submonoid (schemeRing T)) :
    IsRepresentedAt c α (Spec (CommRingCat.of (Localization M))) := by
  sorry

theorem affine_construction_algebraic_closure_residue_field
    {c : SchemeCoding.{u}} {α : Ordinal.{u}} {T : Scheme.{u}}
    (hT : SchemeInLevel c α T) [IsAffine T]
    (p : PrimeSpectrum (schemeRing T))
    : IsRepresentedAt c α
      (Spec (CommRingCat.of (residueFieldAlgebraicClosure (schemeRing T) p))) := by
  sorry

theorem affine_construction_subring
    {c : SchemeCoding.{u}} {α : Ordinal.{u}} {T : Scheme.{u}}
    (hT : SchemeInLevel c α T) [IsAffine T] (R' : Subring (schemeRing T)) :
    IsRepresentedAt c α (Spec (CommRingCat.of R')) := by
  sorry

theorem affine_construction_finite_type_over_bounded_ring
    {c : SchemeCoding.{u}} {α : Ordinal.{u}} {T : Scheme.{u}}
    (hT : SchemeInLevel c α T) [IsAffine T]
    (A : Type u) [CommRing A]
    (hA : Cardinal.mk A ≤ (Cardinal.mk (schemeRing T)) ^ Cardinal.aleph0)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (hf : IsFiniteTypeSchemeMorphism f) :
    IsRepresentedAt c α X := by
  sorry

/-! ### The warnings and bounds in the two remarks -/

/-- A faster bound such as `κ ↦ κ ^ κ` has the same closure role as `Bound`. -/
theorem alternativeBound_is_admissible (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ) :
    Bound κ ≤ alternativeBound κ := by
  sorry

/-- The underlying family of the product of residue fields over a prime spectrum. -/
def residueFieldProduct (R : CommRingCat.{u}) : Type u :=
  ∀ p : PrimeSpectrum R, (Spec R).residueField p

/-- The residue-field product has the expected coarse cardinal upper bound. -/
theorem residueFieldProduct_cardinal_bound (R : CommRingCat.{u}) :
    Cardinal.mk (residueFieldProduct R) ≤
      (Cardinal.mk R) ^ ((2 : Cardinal.{u}) ^ Cardinal.mk R) := by
  sorry

/- The two concrete rings used in the source warning.  The first is `ℂ[x]`;
the second is the countable product of copies of `𝔽₂`. -/
abbrev complexPolynomialRing : CommRingCat :=
  CommRingCat.of (Polynomial ℂ)

abbrev binarySequenceRing : CommRingCat :=
  CommRingCat.of (∀ _ : ℕ, ZMod 2)

/-- For `R = ℂ[x]`, the residue-field product is not bounded by `|R|^ℵ₀`. -/
theorem residueFieldProduct_complexPolynomial_not_countable_power :
    ¬ Cardinal.mk (residueFieldProduct complexPolynomialRing) ≤
      (Cardinal.mk complexPolynomialRing) ^ Cardinal.aleph0 := by
  sorry

/-- For `R = ∏ₙ 𝔽₂`, the residue-field product is not bounded by `|R|^|R|`. -/
theorem residueFieldProduct_binarySequence_not_self_power :
    ¬ Cardinal.mk (residueFieldProduct binarySequenceRing) ≤
      (Cardinal.mk binarySequenceRing) ^ Cardinal.mk binarySequenceRing := by
  sorry

/-! ### fpqc and fppf bounds -/

/-- A presieve factors through a morphism. -/
def PresieveFactorsThrough {X Y : Scheme.{u}} (R : Presieve Y) (f : X ⟶ Y) : Prop :=
  ∀ ⦃Z : Scheme.{u}⦄ (g : Z ⟶ Y), R g → ∃ h : Z ⟶ X, h ≫ f = g

/-- The fpqc covering bound. -/
theorem schemeSize_le_of_fpqc_covering {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Presieve Y) (hR : R ∈ Scheme.fpqcPrecoverage Y)
    (hfactor : PresieveFactorsThrough R f) :
    schemeSize Y ≤ schemeSize X := by
  sorry

/-- An fppf covering family in the form used by the source. -/
structure FppfCover (X : Scheme.{u}) where
  I : Type u
  Y : I → Scheme.{u}
  f : ∀ i, Y i ⟶ X
  isCover : Presieve.ofArrows Y f ∈ Scheme.fppfPrecoverage X

/-- A refinement of fppf covering families. -/
structure FppfRefinement {X : Scheme.{u}} (𝒰 𝒲 : FppfCover X) where
  indexMap : 𝒲.I → 𝒰.I
  maps : ∀ j, 𝒲.Y j ⟶ 𝒰.Y (indexMap j)
  commutes : ∀ j, maps j ≫ 𝒰.f (indexMap j) = 𝒲.f j

/-- An fppf refinement whose coproduct has small size. -/
structure SmallFppfRefinement {X : Scheme.{u}} (𝒰 : FppfCover X) where
  refinement : FppfCover X
  witness : FppfRefinement 𝒰 refinement
  coproduct : Scheme.{u}
  coproductIso : Nonempty (coproduct ≅ colimit (Discrete.functor refinement.Y))
  size_le : schemeSize coproduct ≤ schemeSize X

/-- Every fppf cover admits a refinement with coproduct of size at most the base. -/
theorem exists_small_fppf_refinement {X : Scheme.{u}} (𝒰 : FppfCover X) :
    Nonempty (SmallFppfRefinement 𝒰) := by
  sorry

end

end Formalization.Books.Sets.Unit09
