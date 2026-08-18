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
  change Continuous fun p : Gal(E / F) × E => p.1 • p.2
  exact (continuousSMul_iff_stabilizer_isOpen.mpr
    (fun x => stabilizer_isOpen_of_isIntegral x)).continuous_smul

/-- The Krull topology has the source's universal property: a map into the
    Galois group is continuous whenever its induced action on the discrete
    extension is continuous. -/
theorem galois_krullTopology_universal
    {F E X : Type*} [Field F] [Field E] [Algebra F E] [IsGalois F E]
    [TopologicalSpace E] [DiscreteTopology E] [TopologicalSpace X]
    (f : X → Gal(E / F))
    (h : Continuous (fun p : X × E => f p.1 p.2)) :
    Continuous f := by
  classical
  refine continuous_iff_continuousAt.mpr (fun x => continuousAt_def.mpr ?_)
  intro N hN
  let N' : Set Gal(E / F) := (fun g => f x * g) ⁻¹' N
  have hN' : N' ∈ nhds (1 : Gal(E / F)) := by
    have hc : Continuous (fun g : Gal(E / F) => f x * g) :=
      continuous_const.mul continuous_id
    change (fun g : Gal(E / F) => f x * g) ⁻¹' N ∈ nhds (1 : Gal(E / F))
    simpa using hc.continuousAt.preimage_mem_nhds hN
  obtain ⟨E', hEfin, hE⟩ :=
    (krullTopology_mem_nhds_one_iff F E N').mp hN'
  letI : FiniteDimensional F E' := hEfin
  let b := Module.finBasis F E'
  have hprod (i : Fin (Module.finrank F E')) :
      ∃ u ∈ nhds x, ∃ v ∈ nhds ((b i : E') : E), u ×ˢ v ⊆
        (fun p : X × E => f p.1 p.2) ⁻¹' {f x ((b i : E') : E)} := by
    have hi : (fun p : X × E => f p.1 p.2) ⁻¹' {f x ((b i : E') : E)} ∈
        nhds (x, ((b i : E') : E)) := by
      exact h.continuousAt.preimage_mem_nhds (isOpen_discrete _ |>.mem_nhds rfl)
    exact mem_nhds_prod_iff.mp hi
  choose u hu v hv huv using hprod
  have hU : (⋂ i, u i) ∈ nhds x := Filter.iInter_mem.mpr hu
  refine Filter.mem_of_superset hU ?_
  intro y hy
  have hbi : ∀ i, f y ((b i : E') : E) = f x ((b i : E') : E) := by
    intro i
    have hi : y ∈ u i := Set.mem_iInter.mp hy i
    have hvm : ((b i : E') : E) ∈ v i := mem_of_mem_nhds (hv i)
    have hi' := huv i
      (show (y, ((b i : E') : E)) ∈ u i ×ˢ v i from ⟨hi, hvm⟩)
    simpa using hi'
  have hlin :
      (f y).toLinearMap.comp E'.val.toLinearMap =
        (f x).toLinearMap.comp E'.val.toLinearMap := by
    apply b.ext
    intro i
    exact hbi i
  have hfix : (f x)⁻¹ * f y ∈ E'.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    apply (f x).injective
    rw [AlgEquiv.aut_inv, AlgEquiv.mul_apply, AlgEquiv.apply_symm_apply]
    have hz' := congrArg (fun q : E' →ₗ[F] E => q ⟨z, hz⟩) hlin
    simpa [LinearMap.comp_apply] using hz'
  have hNy : f x * ((f x)⁻¹ * f y) ∈ N := by
    exact hE hfix
  simpa [mul_assoc] using hNy

/-- The Galois group of an infinite Galois extension is profinite for its
    canonical Krull topology. -/
theorem galois_krullTopology_is_profinite_group
    {F E : Type*} [Field F] [Field E] [Algebra F E] [IsGalois F E] :
    Formalization.Books.Topology.Unit29.IsProfiniteGroup (G := Gal(E / F)) := by
  unfold Formalization.Books.Topology.Unit29.IsProfiniteGroup
  rw [Formalization.Books.Topology.Unit22.isProfiniteSpace_iff_hausdorff_quasiCompact_totallyDisconnected]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

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
  letI : TopologicalSpace M := ⊥
  letI : DiscreteTopology M := ⟨rfl⟩
  letI : MulAction (Gal(L / K)) M :=
    MulAction.compHom M (galoisRestrictionHom (K := K) (M := M) (L := L))
  refine ⟨AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) L, ?_⟩
  apply galois_krullTopology_universal
  refine (continuousSMul_iff_stabilizer_isOpen.mpr ?_).continuous_smul
  intro x
  have hx : IsOpen (MulAction.stabilizer (Gal(L / K))
      (algebraMap M L x) : Set (Gal(L / K))) :=
    stabilizer_isOpen_of_isIntegral (algebraMap M L x)
  convert hx using 1
  ext σ
  change galoisRestrictionHom (K := K) (M := M) (L := L) σ x = x ↔
    σ (algebraMap M L x) = algebraMap M L x
  constructor
  · intro h
    calc
      σ (algebraMap M L x) =
          algebraMap M L (galoisRestrictionHom (K := K) (M := M) (L := L) σ x) :=
        (AlgEquiv.restrictNormal_commutes σ M x).symm
      _ = algebraMap M L x := congrArg (algebraMap M L) h
  · intro h
    apply (algebraMap M L).injective
    calc
      algebraMap M L (galoisRestrictionHom (K := K) (M := M) (L := L) σ x) =
          σ (algebraMap M L x) :=
        AlgEquiv.restrictNormal_commutes σ M x
      _ = algebraMap M L x := h

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
  exact fun x => ⟨FiniteGaloisIntermediateField.adjoin K {x},
    FiniteGaloisIntermediateField.subset_adjoin K {x} (Set.mem_singleton x)⟩

/-- The finite Galois intermediate fields have supremum the whole extension;
    this is the intermediate-field form of the source's filtered-colimit
    equality `L = colim L_λ`. -/
theorem finite_galois_subextensions_iSup
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    (⨆ A : FiniteGaloisIntermediateField K L, A.toIntermediateField) =
      (⊤ : IntermediateField K L) := by
  exact eq_top_iff.mpr (fun x _ =>
    let h := finite_galois_subextensions_cover (K := K) (L := L) x
    let A := h.choose
    (le_iSup (fun A : FiniteGaloisIntermediateField K L => A.toIntermediateField) A)
      h.choose_spec)

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
  letI : Normal K B.unop := IsGalois.to_normal
  letI : Algebra B.unop A.unop :=
    RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom f.1)
  haveI : IsScalarTower K B.unop A.unop :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  change Function.Surjective (ConcreteCategory.hom (C := FiniteGrp)
    (finGaloisGroupMap f))
  exact AlgEquiv.restrictNormalHom_surjective (F := K)
    (K₁ := B.unop) (E := A.unop)

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
  constructor
  · exact InfiniteGalois.restrictNormalHom_continuous A.toIntermediateField
  · exact AlgEquiv.restrictNormalHom_surjective (F := K)
      (K₁ := A.toIntermediateField) (E := L)

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
  rfl

/-- The correspondence sends an intermediate field to its fixing subgroup. -/
theorem closedSubgroupEquivIntermediateField_symm_apply
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) :
    (closedSubgroupEquivIntermediateField (K := K) (L := L)).symm M =
      ⟨M.fixingSubgroup, InfiniteGalois.fixingSubgroup_isClosed M⟩ := by
  rfl

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
  change IsOpen H.carrier ↔ _
  have hH : (IntermediateField.fixedField (H : Subgroup Gal(L / K))).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField H
  constructor
  · intro h
    apply (InfiniteGalois.isOpen_iff_finite
      (IntermediateField.fixedField (H : Subgroup Gal(L / K)))).mp
    simpa only [hH] using h
  · intro h
    have h' := (InfiniteGalois.isOpen_iff_finite
      (IntermediateField.fixedField (H : Subgroup Gal(L / K)))).mpr h
    simpa only [hH] using h'

/-- Under the correspondence, a closed subgroup is normal exactly when its
    fixed field is Galois over the base. -/
theorem infinite_galois_closed_subgroup_normal_iff_galois_fixedField
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (H : ClosedSubgroup Gal(L / K)) :
    (H : Subgroup Gal(L / K)).Normal ↔
      IsGalois K (IntermediateField.fixedField (H : Subgroup Gal(L / K))) := by
  have hH : (IntermediateField.fixedField (H : Subgroup Gal(L / K))).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField H
  constructor
  · intro h
    apply (InfiniteGalois.normal_iff_isGalois
      (IntermediateField.fixedField (H : Subgroup Gal(L / K)))).mp
    simpa only [hH] using h
  · intro h
    have h' := (InfiniteGalois.normal_iff_isGalois
      (IntermediateField.fixedField (H : Subgroup Gal(L / K)))).mpr h
    simpa only [hH] using h'

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
  dsimp
  letI : IsGalois M L :=
    Formalization.Books.Fields.Unit21.galois_goes_up (F := K) (E := M) (K := L)
  letI : TopologicalSpace L := ⊥
  letI : DiscreteTopology L := ⟨rfl⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact AlgEquiv.restrictScalarsHom_injective K
  · apply MonoidHom.mulExact_of_comp_of_mem_range
    · ext σ x
      simp only [MonoidHom.comp_apply, AlgEquiv.restrictScalarsHom_apply]
      apply (algebraMap M L).injective
      change (algebraMap M L) ((AlgEquiv.restrictScalars K σ).restrictNormal M x) =
        algebraMap M L x
      rw [AlgEquiv.restrictNormal_commutes]
      exact σ.commutes x
    · intro τ hp
      let σ : Gal(L / M) :=
        { τ with
          commutes' := by
            intro x
            have hp' : τ.restrictNormal M = (1 : Gal(M / K)) := by
              simpa only [galoisRestrictionHom, AlgEquiv.restrictNormalHom,
                MonoidHom.mk'_apply, MonoidHom.mem_ker] using hp
            calc
              τ (algebraMap M L x) =
                  algebraMap M L ((τ.restrictNormal M) x) :=
                (AlgEquiv.restrictNormal_commutes τ M x).symm
              _ = algebraMap M L ((1 : Gal(M / K)) x) := by rw [hp']
              _ = algebraMap M L x := rfl }
      refine ⟨σ, ?_⟩
      ext x
      rfl
  · exact galoisRestrictionHom_surjective_continuous (K := K) (M := M) (L := L) |>.1
  · apply galois_krullTopology_universal
    change Continuous (galoisAction (F := M) (E := L))
    exact galois_action_continuous (F := M) (E := L)
  · exact (galoisRestrictionHom_surjective_continuous
      (K := K) (M := M) (L := L)).2
  · exact galois_krullTopology_is_profinite_group (F := M) (E := L)
  · exact galois_krullTopology_is_profinite_group (F := K) (E := L)
  · exact galois_krullTopology_is_profinite_group (F := K) (E := M)

end

end Formalization.Books.Fields.Unit22
