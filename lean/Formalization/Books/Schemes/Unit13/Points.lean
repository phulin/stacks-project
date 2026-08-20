import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Schemes, Chapter 13: Points of schemes

This file follows the source section `Points of schemes`.  The canonical
stalk, residue-field, and field-valued point constructions are Mathlib's
`fromSpecStalk`, `fromSpecResidueField`, `SpecToEquivOfLocalRing`, and
`SpecToEquivOfField`.  The declarations below expose those constructions in
the chapter namespace and add the source-facing dominance and equivalence
interfaces for field-valued points.
-/

namespace Formalization.Books.Schemes.Unit13

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open Opposite

universe u

noncomputable section

/-! ## The functor of points -/

/-- The functor of points `T ↦ Hom(T, X)`, canonically the Yoneda functor. -/
abbrev functorOfPoints (X : Scheme.{u}) : Scheme.{u}ᵒᵖ ⥤ Type u :=
  CategoryTheory.yoneda.obj X

theorem functorOfPoints_obj (X : Scheme.{u}) (T : Scheme.{u}ᵒᵖ) :
    (functorOfPoints X).obj T = (unop T ⟶ X) := rfl

/-! ## Points seen from a local ring -/

/-- The local ring at a point, namely the stalk of the structure sheaf. -/
abbrev localRingAt (X : Scheme.{u}) (x : X) : CommRingCat.{u} :=
  X.presheaf.stalk x

/-- The canonical identification of the closed-point stalk of `Spec R` with `R`. -/
noncomputable def localRingAtSpecClosedPointIso (R : CommRingCat.{u}) [IsLocalRing R] :
  localRingAt (Spec R) (IsLocalRing.closedPoint R) ≅ R :=
  AlgebraicGeometry.stalkClosedPointIso R

/-- The local homomorphism attached to `f : Spec R ⟶ X` at the closed point. -/
noncomputable def localRingMapOfSpec {R : CommRingCat.{u}} [IsLocalRing R]
    {X : Scheme.{u}} (f : Spec R ⟶ X) :
    localRingAt X (f (IsLocalRing.closedPoint R)) ⟶ R :=
  Scheme.stalkClosedPointTo f

instance localRingMapOfSpec_isLocalHom {R : CommRingCat.{u}} [IsLocalRing R]
    {X : Scheme.{u}} (f : Spec R ⟶ X) :
    IsLocalHom (localRingMapOfSpec f).hom := by
  change IsLocalHom (Scheme.stalkClosedPointTo f).hom
  infer_instance

/-- The source's local-ring correspondence, using Mathlib's canonical equivalence. -/
noncomputable def morphismFromLocalRingEquiv (R : CommRingCat.{u}) [IsLocalRing R]
    (X : Scheme.{u}) :
    (Spec R ⟶ X) ≃
      Σ x : X, { φ : localRingAt X x ⟶ R // IsLocalHom φ.hom } :=
  AlgebraicGeometry.SpecToEquivOfLocalRing X R

/-- The canonical morphism `Spec(O_{X,x}) ⟶ X`. -/
abbrev canonicalFromSpecStalk (X : Scheme.{u}) (x : X) :
    Spec (localRingAt X x) ⟶ X :=
  X.fromSpecStalk x

theorem localRingMapOfSpec_factorization {R : CommRingCat.{u}} [IsLocalRing R]
    {X : Scheme.{u}} (f : Spec R ⟶ X) :
    f = Spec.map (localRingMapOfSpec f) ≫ canonicalFromSpecStalk X
      (f (IsLocalRing.closedPoint R)) := by
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk f).symm

theorem canonicalFromSpecStalk_closedPoint (X : Scheme.{u}) (x : X) :
    canonicalFromSpecStalk X x (IsLocalRing.closedPoint (localRingAt X x)) = x := by
  exact Scheme.fromSpecStalk_closedPoint

/-- Every morphism from the spectrum of a local ring has a unique image point
and factors through that point's canonical stalk morphism. -/
theorem existsUnique_localRing_factorization
    {R : CommRingCat.{u}} [IsLocalRing R] {X : Scheme.{u}} (f : Spec R ⟶ X) :
    ∃! x : X,
      ∃ φ : localRingAt X x ⟶ R,
        IsLocalHom φ.hom ∧ f = Spec.map φ ≫ canonicalFromSpecStalk X x := by
  let e := morphismFromLocalRingEquiv R X
  let y := e f
  refine ⟨y.1, ?_, ?_⟩
  · refine ⟨y.2.1, y.2.2, ?_⟩
    exact (e.left_inv f).symm
  · intro x' hx'
    obtain ⟨φ, hφ, hfactor⟩ := hx'
    have hx' : x' = f (IsLocalRing.closedPoint R) := by
      rw [hfactor]
      change x' = canonicalFromSpecStalk X x' (Spec.map φ (IsLocalRing.closedPoint R))
      rw [Spec_closedPoint, canonicalFromSpecStalk_closedPoint]
    have hy : y.1 = f (IsLocalRing.closedPoint R) := by
      rfl
    exact hx'.trans hy.symm

/-- The local-ring square induced by a morphism of schemes. -/
theorem localRing_stalk_square {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Spec.map (f.stalkMap x) ≫ canonicalFromSpecStalk S (f x) =
      canonicalFromSpecStalk X x ≫ f := by
  exact Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x)

/-! ## Specialization and generalization -/

/-- The image of `Spec(O_{X,x})` is exactly the generalizations of `x`. -/
theorem mem_canonicalFromSpecStalk_iff {X : Scheme.{u}} (x x' : X) :
    x' ∈ Set.range (canonicalFromSpecStalk X x) ↔ x' ⤳ x := by
  rw [Scheme.range_fromSpecStalk]
  rfl

/-! ## Residue fields and field-valued points -/

/-- The residue field at a point, using Mathlib's canonical construction. -/
abbrev residueFieldAt (X : Scheme.{u}) (x : X) : CommRingCat.{u} :=
  X.residueField x

/-- The factor of a local homomorphism through the residue field. -/
noncomputable def residueFieldFactor {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] (f : R →+* K) [IsLocalHom f] :
    IsLocalRing.ResidueField R →+* K :=
  IsLocalRing.ResidueField.lift f

theorem residueFieldFactor_comp_residue {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] (f : R →+* K) [IsLocalHom f] :
    (residueFieldFactor f).comp (IsLocalRing.residue R) = f := by
  exact IsLocalRing.ResidueField.lift_comp_residue f

/-- Morphisms `Spec K ⟶ X` are pairs consisting of a point and an embedding of
its residue field into `K`. -/
noncomputable def morphismFromFieldEquiv (K : Type u) [Field K] (X : Scheme.{u}) :
    (Spec (CommRingCat.of K) ⟶ X) ≃
      Σ x : X, residueFieldAt X x ⟶ CommRingCat.of K :=
  AlgebraicGeometry.Scheme.SpecToEquivOfField K X

/-- A field-valued point of `X`, with its source field retained as data. -/
structure FieldPoint (X : Scheme.{u}) where
  K : Type u
  [field : Field K]
  morphism : Spec (CommRingCat.of K) ⟶ X

attribute [instance] FieldPoint.field

/-- A field used as the common refinement in the field-point equivalence relation. -/
structure FieldData where
  carrier : Type u
  [field : Field carrier]

attribute [instance] FieldData.field

private theorem specField_morphism_eq_map
    {K L : Type u} [Field K] [Field L]
    (f : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) :
    ∃ φ : CommRingCat.of K ⟶ CommRingCat.of L, f = Spec.map φ := by
  let φ := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of L)).hom
  refine ⟨φ, ?_⟩
  have hnat : f ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom ≫ Spec.map f.appTop := by
    simpa only [SpecMap_ΓSpecIso_hom] using Scheme.toSpecΓ_naturality f
  dsimp [φ]
  rw [Spec.map_comp, Spec.map_comp, ← hnat]
  simp

namespace FieldPoint

private theorem common_field_refinement
    {K L M : Type u} [Field K] [Field L] [Field M]
    (f : CommRingCat.of K ⟶ CommRingCat.of L)
    (g : CommRingCat.of K ⟶ CommRingCat.of M) :
    ∃ Ω : FieldData,
      ∃ a : Spec (CommRingCat.of Ω.carrier) ⟶ Spec (CommRingCat.of L),
      ∃ b : Spec (CommRingCat.of Ω.carrier) ⟶ Spec (CommRingCat.of M),
        a ≫ Spec.map f = b ≫ Spec.map g := by
  let : Algebra K L := f.hom.toAlgebra
  let : Algebra K M := g.hom.toAlgebra
  let T := TensorProduct K L M
  let : Nontrivial T :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K L M
      (by simpa only [RingHom.algebraMap_toAlgebra] using RingHom.injective f.hom)
      (by simpa only [RingHom.algebraMap_toAlgebra] using RingHom.injective g.hom)
  obtain ⟨J, hJ⟩ := Ideal.exists_maximal T
  let : J.IsMaximal := hJ
  let Ω := T ⧸ J
  let : Field Ω := Ideal.Quotient.field J
  let iL : L →+* Ω := (Ideal.Quotient.mk J).comp
    (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := M))
  let iM : M →+* Ω := (Ideal.Quotient.mk J).comp
    (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := M)).toRingHom
  refine ⟨{ carrier := Ω }, Spec.map (CommRingCat.ofHom iL),
    Spec.map (CommRingCat.ofHom iM), ?_⟩
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  have hcomp :
      (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := M)).comp f.hom =
        (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := M)).toRingHom.comp g.hom := by
    simpa only [RingHom.algebraMap_toAlgebra] using
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
        (R := K) (A := L) (B := M))
  ext z
  change iL (f.hom z) = iM (g.hom z)
  dsimp [iL, iM]
  exact DFunLike.congr_fun
    (congrArg (fun k : K →+* T => (Ideal.Quotient.mk J).comp k) hcomp) z

/-- The unique point of `X` hit by a field-valued point. -/
def image {X : Scheme.{u}} (p : FieldPoint X) : X :=
  p.morphism (IsLocalRing.closedPoint p.K)

/-- `p` dominates `q` when the morphism represented by `p` factors through `q`. -/
def Dominates {X : Scheme.{u}} (p q : FieldPoint X) : Prop :=
  ∃ g : Spec (CommRingCat.of p.K) ⟶ Spec (CommRingCat.of q.K),
    g ≫ q.morphism = p.morphism

/-- The common-field relation from the source's commutative diagram. -/
def Equivalent {X : Scheme.{u}} (p q : FieldPoint X) : Prop :=
  ∃ Ω : FieldData.{u},
    ∃ g : Spec (CommRingCat.of Ω.carrier) ⟶ Spec (CommRingCat.of p.K),
    ∃ h : Spec (CommRingCat.of Ω.carrier) ⟶ Spec (CommRingCat.of q.K),
      g ≫ p.morphism = h ≫ q.morphism

theorem equivalent_same_image {X : Scheme.{u}} {p q : FieldPoint X}
    (h : Equivalent p q) : image p = image q := by
  obtain ⟨Ω, g, h, heq⟩ := h
  have heq' := congrArg (fun k : Spec (CommRingCat.of Ω.carrier) ⟶ X =>
    k (IsLocalRing.closedPoint Ω.carrier)) heq
  change p.morphism (g (IsLocalRing.closedPoint Ω.carrier)) =
    q.morphism (h (IsLocalRing.closedPoint Ω.carrier)) at heq'
  have hg : g (IsLocalRing.closedPoint Ω.carrier) =
      IsLocalRing.closedPoint p.K := Subsingleton.elim _ _
  have hh : h (IsLocalRing.closedPoint Ω.carrier) =
      IsLocalRing.closedPoint q.K := Subsingleton.elim _ _
  rw [hg, hh] at heq'
  exact heq'

theorem dominates_refl {X : Scheme.{u}} (p : FieldPoint X) : Dominates p p := by
  exact ⟨𝟙 _, by simp⟩

theorem dominates_trans {X : Scheme.{u}} {p q r : FieldPoint X}
    (hpq : Dominates p q) (hqr : Dominates q r) : Dominates p r := by
  obtain ⟨g, hg⟩ := hpq
  obtain ⟨h, hh⟩ := hqr
  refine ⟨g ≫ h, ?_⟩
  rw [Category.assoc, hh, hg]

/-- The preorder on morphisms from spectra of fields suggested in the source. -/
@[instance_reducible]
def preorder (X : Scheme.{u}) : Preorder (FieldPoint X) where
  le := Dominates
  le_refl := fun p => dominates_refl p
  le_trans := fun p q r hpq hqr => dominates_trans hpq hqr

/-- The common-field relation is the equivalence relation used for field-valued points. -/
theorem equivalent_is_equivalence (X : Scheme.{u}) :
    Equivalence (@Equivalent X) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    refine ⟨{ carrier := p.K }, 𝟙 _, 𝟙 _, ?_⟩
    simp
  · intro p q h
    obtain ⟨Ω, g, h, heq⟩ := h
    exact ⟨Ω, h, g, heq.symm⟩
  · intro p q r hpq hqr
    obtain ⟨Ω₁, a, b, hab⟩ := hpq
    obtain ⟨Ω₂, c, d, hcd⟩ := hqr
    obtain ⟨f, hf⟩ := specField_morphism_eq_map b
    obtain ⟨g, hg⟩ := specField_morphism_eq_map c
    obtain ⟨Ω, i, j, hij⟩ := common_field_refinement f g
    have hij' : i ≫ b = j ≫ c := by
      simpa [hf, hg] using hij
    refine ⟨Ω, i ≫ a, j ≫ d, ?_⟩
    calc
      (i ≫ a) ≫ p.morphism = i ≫ (a ≫ p.morphism) := Category.assoc _ _ _
      _ = i ≫ (b ≫ q.morphism) := by rw [hab]
      _ = (i ≫ b) ≫ q.morphism := (Category.assoc _ _ _).symm
      _ = (j ≫ c) ≫ q.morphism := by rw [hij']
      _ = j ≫ (c ≫ q.morphism) := Category.assoc _ _ _
      _ = j ≫ (d ≫ r.morphism) := by rw [hcd]
      _ = (j ≫ d) ≫ r.morphism := (Category.assoc _ _ _).symm

/-- The common-field relation is the equivalence relation used for field-valued points. -/
noncomputable def setoid (X : Scheme.{u}) : Setoid (FieldPoint X) where
  r := Equivalent
  iseqv := equivalent_is_equivalence X

end FieldPoint

/-- Equivalence classes of morphisms from spectra of fields into `X`. -/
abbrev fieldPointClasses (X : Scheme.{u}) := Quotient (FieldPoint.setoid X)

/-- The canonical field-valued point attached to `x`, namely
`Spec(κ(x)) ⟶ X`. -/
noncomputable def canonicalFieldPoint (X : Scheme.{u}) (x : X) : FieldPoint X where
  K := residueFieldAt X x
  morphism := X.fromSpecResidueField x

/-- The field-point classification of scheme points. -/
theorem exists_fieldPointClassEquiv (X : Scheme.{u}) :
    Nonempty (X ≃ fieldPointClasses X) := by
  let F : X → fieldPointClasses X := fun x =>
    Quotient.mk (FieldPoint.setoid X) (canonicalFieldPoint X x)
  have hsurj : Function.Surjective F := by
    intro c
    refine Quotient.inductionOn c ?_
    intro p
    let e := morphismFromFieldEquiv p.K X
    let y := e p.morphism
    refine ⟨y.1, ?_⟩
    apply Quotient.sound
    refine ⟨{ carrier := p.K }, Spec.map y.2, 𝟙 _, ?_⟩
    have hleft := e.left_inv p.morphism
    rw [Category.id_comp]
    dsimp [canonicalFieldPoint, e, y, morphismFromFieldEquiv,
      AlgebraicGeometry.Scheme.SpecToEquivOfField] at hleft ⊢
    convert hleft using 1
    rfl
  have hinj : Function.Injective F := by
    intro x y hxy
    have heq : FieldPoint.Equivalent (canonicalFieldPoint X x)
        (canonicalFieldPoint X y) := Quotient.exact hxy
    have himage := FieldPoint.equivalent_same_image heq
    have hcanon (z : X) : (canonicalFieldPoint X z).image = z := by
      change X.fromSpecResidueField z
        (IsLocalRing.closedPoint (residueFieldAt X z)) = z
      exact Scheme.fromSpecResidueField_apply z _
    exact (hcanon x).symm.trans (himage.trans (hcanon y))
  exact ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩⟩

/-- A chosen bijection between scheme points and field-point equivalence classes. -/
noncomputable def fieldPointClassEquiv (X : Scheme.{u}) :
    X ≃ fieldPointClasses X :=
  Classical.choice (exists_fieldPointClassEquiv X)

/-- Every field-valued morphism factors through the canonical morphism from
the residue field of its image point. -/
theorem fieldPoint_factor_through_canonicalResidueField
    {X : Scheme.{u}} (x : X) :
    X.fromSpecResidueField x =
      Spec.map (X.residue x) ≫ canonicalFromSpecStalk X x := by
  rfl

/-- The canonical representative is the smallest element of its field-point
equivalence class under domination. -/
theorem canonicalFieldPoint_is_smallest
    {X : Scheme.{u}} (x : X) (p : FieldPoint X)
    (hp : Quotient.mk (FieldPoint.setoid X) p =
      Quotient.mk (FieldPoint.setoid X) (canonicalFieldPoint X x)) :
    FieldPoint.Dominates p (canonicalFieldPoint X x) := by
  have heq : FieldPoint.Equivalent p (canonicalFieldPoint X x) :=
    Quotient.exact hp
  have himage := FieldPoint.equivalent_same_image heq
  have hcanon : (canonicalFieldPoint X x).image = x := by
    change X.fromSpecResidueField x
      (IsLocalRing.closedPoint (residueFieldAt X x)) = x
    exact Scheme.fromSpecResidueField_apply x _
  have hx : p.image = x := by
    exact himage.trans hcanon
  subst x
  let e := morphismFromFieldEquiv p.K X
  let y := e p.morphism
  refine ⟨Spec.map y.2, ?_⟩
  have hleft := e.left_inv p.morphism
  dsimp [canonicalFieldPoint, e, y, morphismFromFieldEquiv,
    AlgebraicGeometry.Scheme.SpecToEquivOfField] at hleft ⊢
  convert hleft using 1
  rfl

/-- The canonical smallest representatives are unique up to the unique
isomorphism over `X` supplied by the residue-field construction. -/
theorem canonicalFieldPoint_unique_up_to_unique_iso
    {X : Scheme.{u}} {x y : X}
    (h : Quotient.mk (FieldPoint.setoid X) (canonicalFieldPoint X x) =
      Quotient.mk (FieldPoint.setoid X) (canonicalFieldPoint X y)) :
    ∃! e : Spec (residueFieldAt X x) ⟶ Spec (residueFieldAt X y),
      e ≫ X.fromSpecResidueField y = X.fromSpecResidueField x := by
  have heq : FieldPoint.Equivalent (canonicalFieldPoint X x)
      (canonicalFieldPoint X y) := Quotient.exact h
  have himage := FieldPoint.equivalent_same_image heq
  have hcanon (z : X) : (canonicalFieldPoint X z).image = z := by
    change X.fromSpecResidueField z
      (IsLocalRing.closedPoint (residueFieldAt X z)) = z
    exact Scheme.fromSpecResidueField_apply z _
  have hxy : x = y := (hcanon x).symm.trans (himage.trans (hcanon y))
  subst y
  refine ⟨𝟙 _, by simp, ?_⟩
  intro e he
  exact (cancel_mono (X.fromSpecResidueField x)).1 (by simpa using he)

/-- The canonical field-point morphism is the smallest representative of the
class corresponding to `x`; the equivalence above identifies all classes. -/
theorem fieldPointClassEquiv_canonical (X : Scheme.{u}) (x : X) :
    fieldPointClassEquiv X x =
      Quotient.mk (FieldPoint.setoid X) (canonicalFieldPoint X x) := by
  sorry

/-! ## Relative and specialization diagrams for field-valued points -/

/-- A field-valued point over `x` factors through the canonical stalk morphism. -/
theorem fieldPoint_factors_through_stalk
    {X : Scheme.{u}} {x x' : X} (h : x' ⤳ x) :
    ∃ g : Spec (residueFieldAt X x') ⟶ Spec (localRingAt X x),
      g ≫ canonicalFromSpecStalk X x = X.fromSpecResidueField x' := by
  refine ⟨Spec.map (X.residue x') ≫ Spec.map (X.presheaf.stalkSpecializes h), ?_⟩
  rw [Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
  rfl

/-- The residue-field square induced by a morphism of schemes. -/
theorem residueField_square {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Spec.map (f.residueFieldMap x) ≫ S.fromSpecResidueField (f x) =
      X.fromSpecResidueField x ≫ f := by
  exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x

end
