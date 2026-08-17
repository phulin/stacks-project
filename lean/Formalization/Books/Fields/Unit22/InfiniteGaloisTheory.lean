import Formalization.Books.Fields.Unit21.GaloisTheory
import Formalization.Books.Topology.Unit29.TopologicalGroups
import Mathlib.Algebra.Exact.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# Fields, Chapter 22: Infinite Galois theory

The source's topology on an infinite Galois group is Mathlib's canonical
`krullTopology`.  Mathlib also supplies the finite Galois intermediate-field
index, its inverse system of finite groups, the profinite limit equivalence,
and the closed-subgroup form of the fundamental theorem.  This file records
the source-facing interfaces that assemble those declarations.
-/

namespace Formalization.Books.Fields.Unit22

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## The canonical topology -/

/- The action appearing in the source's universal property.  The topology on
   `Gal(E / F)` is the canonical `krullTopology F E` instance from Mathlib. -/
def galoisAction {F E : Type*} [Field F] [Field E] [Algebra F E] :
    Gal(E / F) × E → E := fun p => p.1 p.2

/- The source's topology is Mathlib's `krullTopology`, whose canonical
   `IsTopologicalGroup` instance is already attached to the Galois group. -/

/-! The two assertions in the universal-property part of the source lemma. -/

/-- The Galois action on a discrete algebraic extension is continuous for the
    Krull topology. -/
theorem galois_action_continuous
    {F E : Type*} [Field F] [Field E] [Algebra F E] [IsGalois F E]
    [TopologicalSpace E] [DiscreteTopology E] :
    Continuous (galoisAction (F := F) (E := E)) := by
  sorry

/-- The Krull topology has the source's universal property: a map into the
    Galois group is continuous whenever its induced action on the discrete
    extension is continuous. -/
theorem galois_krullTopology_universal
    {F E X : Type*} [Field F] [Field E] [Algebra F E] [IsGalois F E]
    [TopologicalSpace E] [DiscreteTopology E] [TopologicalSpace X]
    (f : X → Gal(E / F))
    (h : Continuous (fun p : X × E => f p.1 p.2)) :
    Continuous f := by
  sorry

/-- The Galois group of an infinite Galois extension is profinite for its
    canonical Krull topology. -/
theorem galois_krullTopology_is_profinite_group
    {F E : Type*} [Field F] [Field E] [Algebra F E] [IsGalois F E] :
    Formalization.Books.Topology.Unit29.IsProfiniteGroup (G := Gal(E / F)) := by
  sorry

/-! ## Restriction in a Galois tower -/

/- This is the canonical restriction homomorphism.  The normality required by
   `restrictNormalHom` is supplied by `IsGalois K M`. -/
def galoisRestrictionHom
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [IsGalois K M] :
    Gal(L / K) →* Gal(M / K) :=
  AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M

/-- Restriction from `Gal(L / K)` to `Gal(M / K)` is canonical, surjective,
    and continuous when both extensions are Galois over `K`. -/
theorem galoisRestrictionHom_surjective_continuous
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [IsGalois K M] [IsGalois K L] :
    Function.Surjective (galoisRestrictionHom (K := K) (M := M) (L := L)) ∧
      Continuous (galoisRestrictionHom (K := K) (M := M) (L := L)) := by
  sorry

/-! ## Finite Galois subextensions and the inverse limit -/

/- The source's index set `Λ` is Mathlib's canonical
   `FiniteGaloisIntermediateField K L`.  Its existing partial-order and
   lattice instances encode inclusion of the corresponding subextensions. -/

/-- The index of finite Galois subextensions is nonempty. -/
theorem finite_galois_subextension_index_nonempty
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Nonempty (FiniteGaloisIntermediateField K L) :=
  ⟨⊥⟩

/-- Finite Galois subextensions form a directed partially ordered set. -/
theorem finite_galois_subextension_index_is_directed
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    IsDirectedOrder (FiniteGaloisIntermediateField K L) := by
  constructor
  intro A B
  exact ⟨A ⊔ B, le_sup_left, le_sup_right⟩

/- The fields `L_λ` form the canonical system of `K`-extensions through the
   intermediate-field inclusions.  The following concrete union statement is
   the underlying-field form of the source's filtered-colimit assertion. -/

/-- Every element of a Galois extension lies in a finite Galois intermediate
    subextension; equivalently, these subextensions cover `L`. -/
theorem finite_galois_subextensions_cover
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    ∀ x : L, ∃ A : FiniteGaloisIntermediateField K L,
      x ∈ (A.toIntermediateField : Set L) := by
  sorry

/-- The finite Galois intermediate fields have supremum the whole extension;
    this is the intermediate-field form of the source's filtered-colimit
    equality `L = colim L_λ`. -/
theorem finite_galois_subextensions_iSup
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    (⨆ A : FiniteGaloisIntermediateField K L, A.toIntermediateField) =
      (⊤ : IntermediateField K L) := by
  sorry

/-- Each finite Galois intermediate field supplies the finite group used in
    the inverse system. -/
theorem finite_galois_subextension_group_finite
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (A : FiniteGaloisIntermediateField K L) :
    Finite (A.finGaloisGroup) := by
  infer_instance

/- Mathlib's `finGaloisGroupFunctor` is the source's inverse system: its
   opposite index records reverse inclusion and its values are `FiniteGrp`. -/

/-- The transition homomorphisms in the finite Galois-group system are
    surjective. -/
theorem finite_galois_group_transition_surjective
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {A B : (FiniteGaloisIntermediateField K L)ᵒᵖ} (f : A ⟶ B) :
    Function.Surjective
      (ConcreteCategory.hom (C := FiniteGrp)
        ((finGaloisGroupFunctor K L).map f)) := by
  sorry

/- The projection from the full Galois group to a finite Galois level is the
   canonical restriction map. -/
def finite_galois_projection
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : FiniteGaloisIntermediateField K L) :
    Gal(L / K) →* Gal(A / K) :=
  AlgEquiv.restrictNormalHom (F := K) (K₁ := L) A.toIntermediateField

/-- Every finite-level projection is continuous and surjective. -/
theorem finite_galois_projection_continuous_surjective
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (A : FiniteGaloisIntermediateField K L) :
    Continuous (finite_galois_projection (K := K) (L := L) A) ∧
      Function.Surjective (finite_galois_projection (K := K) (L := L) A) := by
  sorry

/-- The full Galois group is continuously isomorphic, as a topological group,
    to the inverse limit of its finite Galois groups. -/
theorem infinite_galois_group_is_profinite_limit
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Nonempty
      (Gal(L / K) ≃ₜ*
        ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K L)) :=
  ⟨InfiniteGalois.continuousMulEquivToLimit K L⟩

/-! ## The fundamental theorem of infinite Galois theory -/

/-- The fixed field of the full Galois group is the base field, expressed as
    equality of intermediate fields. -/
theorem infinite_galois_fixedField_top
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    IntermediateField.fixedField (⊤ : Subgroup Gal(L / K)) =
      (⊥ : IntermediateField K L) :=
  InfiniteGalois.fixedField_bot

/- The source's closed-subgroup-to-subextension bijection is the inverse of
   Mathlib's canonical order isomorphism, whose opposite-order domain is
   definitionally the same underlying type. -/
noncomputable def closedSubgroupEquivIntermediateField
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    ClosedSubgroup Gal(L / K) ≃ IntermediateField K L :=
  (InfiniteGalois.IntermediateFieldEquivClosedSubgroup (k := K) (K := L)).symm.toEquiv

/-- The correspondence sends a closed subgroup to its fixed field. -/
theorem closedSubgroupEquivIntermediateField_apply
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (H : ClosedSubgroup Gal(L / K)) :
    closedSubgroupEquivIntermediateField (K := K) (L := L) H =
      IntermediateField.fixedField (H : Subgroup Gal(L / K)) := by
  sorry

/-- The correspondence sends an intermediate field to its fixing subgroup. -/
theorem closedSubgroupEquivIntermediateField_symm_apply
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) :
    (closedSubgroupEquivIntermediateField (K := K) (L := L)).symm M =
      ⟨M.fixingSubgroup, InfiniteGalois.fixingSubgroup_isClosed M⟩ := by
  sorry

/-- The closed-subgroup/fixed-field correspondence is a bijection, with the
    inverse given by the subgroup fixing the intermediate field. -/
theorem infinite_galois_correspondence_bijective
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Function.Bijective
      (closedSubgroupEquivIntermediateField (K := K) (L := L)) := by
  exact (closedSubgroupEquivIntermediateField (K := K) (L := L)).bijective

/-- The fixing subgroup of an intermediate field is open exactly when the
    intermediate field is finite over the base. -/
theorem infinite_galois_open_iff_finite
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) :
    IsOpen (M.fixingSubgroup : Set Gal(L / K)) ↔ FiniteDimensional K M :=
  InfiniteGalois.isOpen_iff_finite M

/-- Under the correspondence, a closed subgroup is open exactly when its fixed
    field is finite over the base. -/
theorem infinite_galois_closed_subgroup_open_iff_finite_fixedField
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (H : ClosedSubgroup Gal(L / K)) :
    IsOpen (H : Set Gal(L / K)) ↔
      FiniteDimensional K (IntermediateField.fixedField (H : Subgroup Gal(L / K))) := by
  sorry

/-- Under the correspondence, a closed subgroup is normal exactly when its
    fixed field is Galois over the base. -/
theorem infinite_galois_closed_subgroup_normal_iff_galois_fixedField
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (H : ClosedSubgroup Gal(L / K)) :
    (H : Subgroup Gal(L / K)).Normal ↔
      IsGalois K (IntermediateField.fixedField (H : Subgroup Gal(L / K))) := by
  sorry

/-- The fixing subgroup of an intermediate field is normal exactly when the
    intermediate field is Galois over the base. -/
theorem infinite_galois_fixingSubgroup_normal_iff_galois
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) :
    M.fixingSubgroup.Normal ↔ IsGalois K M :=
  InfiniteGalois.normal_iff_isGalois M

/-! ## The profinite short exact sequence -/

/- The left arrow is the canonical inclusion obtained by restriction of
   scalars; the right arrow is the restriction homomorphism above. -/
def galoisInclusionHom
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L] :
    Gal(L / M) →* Gal(L / K) :=
  AlgEquiv.restrictScalarsHom (R := K) (S := M) (A := L)

/-- Restriction gives the short exact sequence of profinite topological groups
    in a Galois tower. -/
theorem infinite_galois_short_exact
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [IsGalois K M] [IsGalois K L] :
    let i : Gal(L / M) →* Gal(L / K) :=
      galoisInclusionHom (K := K) (M := M) (L := L)
    let p : Gal(L / K) →* Gal(M / K) :=
      galoisRestrictionHom (K := K) (M := M) (L := L)
    (Function.Injective i ∧ Function.MulExact i p ∧ Function.Surjective p) ∧
      Continuous i ∧ Continuous p ∧
        Formalization.Books.Topology.Unit29.IsProfiniteGroup (G := Gal(L / M)) ∧
          Formalization.Books.Topology.Unit29.IsProfiniteGroup (G := Gal(L / K)) ∧
            Formalization.Books.Topology.Unit29.IsProfiniteGroup (G := Gal(M / K)) := by
  sorry

end

end Formalization.Books.Fields.Unit22
