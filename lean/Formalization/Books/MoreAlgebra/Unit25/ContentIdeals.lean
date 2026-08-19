import Formalization.Books.Algebra.Unit39.FlatModules
import Formalization.Books.Algebra.Unit91.ExamplesAndNonExamples
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# More on Algebra, Chapter 25: Content ideals

The source's content ideal is represented by the predicate that an ideal is a
least member of the set of ideals carrying a specified module element.  The
flat intersection identity used below is already available as
`Formalization.Books.Algebra.Unit39.flat_intersect_ideals`.
-/

namespace Formalization.Books.MoreAlgebra.Unit25

universe u v

noncomputable section

open scoped TensorProduct

/-! ## Content ideals -/

/-- The ideals of `A` whose scalar multiple of `M` contains `x`. -/
def contentIdeals
    {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] (x : M) : Set (Ideal A) :=
  {I | x ∈ I • (⊤ : Submodule A M)}

/-- `I` is the content ideal of `x` when it is least among the ideals whose
scalar multiple of `M` contains `x`. -/
def IsContentIdeal
    {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] (x : M) (I : Ideal A) : Prop :=
  IsLeast (contentIdeals x) I

/- The displayed equality
`I M ∩ I' M = (I ∩ I') M` is the existing theorem
`Formalization.Books.Algebra.Unit39.flat_intersect_ideals`. -/

/-! ## The lemmas -/

/-- A content ideal, when it exists for a flat module, is finitely generated. -/
theorem contentIdeal_finitelyGenerated
    {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.Flat A M]
    {x : M} {I : Ideal A} (hI : IsContentIdeal x I) :
    I.FG := by
  classical
  obtain ⟨a, ha, hax⟩ :=
    (Submodule.mem_ideal_smul_span_iff_exists_sum I (id : M → M) x).mp (by
      simpa [contentIdeals] using hI.1)
  let J : Ideal A :=
    Ideal.span (a.support.image (fun i => a i) : Set A)
  have hJfg : J.FG := by
    dsimp [J]
    exact Submodule.fg_span (Finset.finite_toSet (a.support.image (fun i => a i)))
  have hJle : J ≤ I := by
    dsimp [J]
    rw [Ideal.span_le]
    intro r hr
    change r ∈ a.support.image (fun i => a i) at hr
    rcases Finset.mem_image.mp hr with ⟨i, hi, rfl⟩
    exact ha i
  have hxJ : x ∈ J • (⊤ : Submodule A M) := by
    rw [show (⊤ : Submodule A M) = Submodule.span A (Set.range (id : M → M)) by simp]
    refine (Submodule.mem_ideal_smul_span_iff_exists_sum J (id : M → M) x).mpr
      ⟨a, ?_, hax⟩
    intro i
    by_cases hi : i ∈ a.support
    · exact Ideal.subset_span (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    · rw [Finsupp.notMem_support_iff.mp hi]
      exact J.zero_mem
  have hIleJ : I ≤ J := hI.2 hxJ
  rw [le_antisymm hIleJ hJle]
  exact hJfg

/-- The map induced by an `A`-linear map on the quotients by the maximal ideal. -/
def maximalIdealQuotientMap
    {A : Type u} {M N : Type v} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (u : M →ₗ[A] N) :
    (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) →ₗ[A]
      (N ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N))) :=
  Submodule.mapQ
    (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))
    (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N)) u
    (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal A) u)

private lemma exists_nonzero_linearMap_to_residue
    {A P : Type u} [CommRing A] [IsLocalRing A]
    [AddCommGroup P] [Module A P] [Module.Finite A P]
    (hP : Nontrivial P) :
    ∃ f : P →ₗ[A] (A ⧸ IsLocalRing.maximalIdeal A), f ≠ 0 := by
  classical
  let V := IsLocalRing.ResidueField A ⊗[A] P
  have hV : Nontrivial V := by
    by_contra h
    have hsubV : Subsingleton V := not_nontrivial_iff_subsingleton.mp h
    have hsubP : Subsingleton P :=
      (IsLocalRing.subsingleton_tensorProduct (R := A) (M := P)).mp hsubV
    exact (not_nontrivial_iff_subsingleton.mpr hsubP) hP
  let b := Module.Basis.ofVectorSpace (IsLocalRing.ResidueField A) V
  obtain ⟨v, hv⟩ := (nontrivial_iff_exists_ne (0 : V)).mp hV
  obtain ⟨i, hi⟩ : ∃ i, b.coord i v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (b.forall_coord_eq_zero_iff.mp h)
  obtain ⟨p, hp⟩ :=
    TensorProduct.mk_surjective A P (IsLocalRing.ResidueField A)
      Ideal.Quotient.mk_surjective v
  let f : P →ₗ[A] (A ⧸ IsLocalRing.maximalIdeal A) :=
    (b.coord i).restrictScalars A |>.comp
      (TensorProduct.mk A (IsLocalRing.ResidueField A) P 1)
  refine ⟨f, ?_⟩
  intro hf
  apply hi
  have hfp := congrArg (fun g : P →ₗ[A] (A ⧸ IsLocalRing.maximalIdeal A) => g p) hf
  change (b.coord i) v = 0
  have hfp' :
      (b.coord i) ((TensorProduct.mk A (IsLocalRing.ResidueField A) P 1) p) = 0 := by
    change (b.coord i) ((TensorProduct.mk A (IsLocalRing.ResidueField A) P 1) p) = 0 at hfp
    exact hfp
  simpa [hp] using hfp'

/-- A map of flat modules over a local ring preserves the content ideal of an
element when its reduction modulo the maximal ideal is injective. -/
theorem contentIdeal_map_of_local
    {A : Type u} {M N : Type v} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Flat A M]
    [AddCommGroup N] [Module A N] [Module.Flat A N]
    (u : M →ₗ[A] N)
    (hu : Function.Injective (maximalIdealQuotientMap u))
    {x : M} {I : Ideal A} (hI : IsContentIdeal x I) :
    IsContentIdeal (u x) I := by
  classical
  have hIFG : I.FG := contentIdeal_finitelyGenerated hI
  constructor
  · change u x ∈ I • (⊤ : Submodule A N)
    have hmap : u x ∈ (I • (⊤ : Submodule A M)).map u :=
      Submodule.mem_map_of_mem hI.1
    rw [Submodule.map_smul'', Submodule.map_top] at hmap
    exact (Submodule.smul_mono le_rfl le_top) hmap
  · intro J hJ
    by_contra hIJ
    let K : Submodule A I :=
      Submodule.comap (I : Submodule A A).subtype (J : Submodule A A)
    have hKtop : K ≠ ⊤ := by
      intro hK
      apply hIJ
      intro a ha
      have haK : (⟨a, ha⟩ : I) ∈ K := by
        have haKtop : (⟨a, ha⟩ : I) ∈ (⊤ : Submodule A I) := Submodule.mem_top
        rw [← hK] at haKtop
        exact haKtop
      dsimp [K] at haK
      simpa using haK
    let hIfinite : Module.Finite A I := (Module.Finite.iff_fg).mpr hIFG
    let P : Type u := I ⧸ K
    let hPfinite : Module.Finite A P := by
      dsimp [P]
      exact Module.Finite.of_surjective (hM := hIfinite)
        ((Submodule.mkQ K).restrictScalars A) (Submodule.mkQ_surjective K)
    have hP : Nontrivial P := by
      dsimp [P]
      exact Submodule.Quotient.nontrivial_iff.mpr hKtop
    obtain ⟨χ, hχ⟩ :=
      @exists_nonzero_linearMap_to_residue A P _ _ _ _ hPfinite hP
    let χI : I →ₗ[A] (A ⧸ IsLocalRing.maximalIdeal A) :=
      χ.comp (Submodule.mkQ K)
    have hχI : χI ≠ 0 := by
      intro hzero
      apply hχ
      apply LinearMap.ext
      intro a
      obtain ⟨b, hb⟩ := Submodule.mkQ_surjective K a
      calc
        χ a = χ (Submodule.mkQ K b) := congrArg χ hb.symm
        _ = χI b := by rfl
        _ = 0 := by rw [hzero]; simp
    let L : Ideal A := (LinearMap.ker χI).map I.subtype
    have hLle : L ≤ I := by
      intro a ha
      rcases ha with ⟨b, hb, rfl⟩
      exact b.property
    have hLne : L ≠ I := by
      intro hLI
      apply hχI
      apply LinearMap.ext
      intro a
      have haL : (a : A) ∈ L := by
        rw [hLI]
        exact a.property
      rcases haL with ⟨b, hb, hba⟩
      have hba' : (b : I) = a := Subtype.ext hba
      rw [← hba']
      exact LinearMap.mem_ker.mp hb
    have hxL : x ∉ L • (⊤ : Submodule A M) := by
      intro hxL
      exact hLne (le_antisymm hLle (hI.2 hxL))
    obtain ⟨t, ht⟩ :
        ∃ t : TensorProduct A (I : Type u) M,
          (TensorProduct.lid A M) (I.subtype.rTensor M t) = x := by
      have hxrange : x ∈
          LinearMap.range ((TensorProduct.lid A M).comp (I.subtype.rTensor M)) := by
        rw [Ideal.subtype_rTensor_range]
        exact hI.1
      exact hxrange
    have hχt : χI.rTensor M t ≠ 0 := by
      intro hzero
      have hex : Function.Exact ((LinearMap.ker χI).subtype.rTensor M)
          (χI.rTensor M) :=
        Module.Flat.rTensor_exact (M := M)
          (LinearMap.exact_subtype_ker_map χI)
      have hrange : t ∈ LinearMap.range ((LinearMap.ker χI).subtype.rTensor M) := by
        rw [← hex.linearMap_ker_eq]
        exact hzero
      obtain ⟨s, hs⟩ := hrange
      have hLmem (s : TensorProduct A (LinearMap.ker χI : Type u) M) :
          (TensorProduct.lid A M)
              (I.subtype.rTensor M ((LinearMap.ker χI).subtype.rTensor M s)) ∈
            L • (⊤ : Submodule A M) := by
        induction s using TensorProduct.induction_on with
        | zero => simp
        | add s t hs ht =>
            simpa only [map_add] using add_mem hs ht
        | tmul a m =>
            change (a : A) • m ∈ L • (⊤ : Submodule A M)
            exact Submodule.smul_mem_smul ⟨a, a.property, rfl⟩ Submodule.mem_top
      apply hxL
      rw [← ht, ← hs]
      exact hLmem s
    change u x ∈ J • (⊤ : Submodule A N) at hJ
    have huxI : u x ∈ I • (⊤ : Submodule A N) := by
      have hmap : u x ∈ (I • (⊤ : Submodule A M)).map u :=
        Submodule.mem_map_of_mem hI.1
      rw [Submodule.map_smul'', Submodule.map_top] at hmap
      exact (Submodule.smul_mono le_rfl le_top) hmap
    have huxK : u x ∈ (I ⊓ J) • (⊤ : Submodule A N) := by
      rw [← Formalization.Books.Algebra.Unit39.flat_intersect_ideals I J]
      exact ⟨huxI, hJ⟩
    obtain ⟨y, hy⟩ :
        ∃ y : TensorProduct A ((I ⊓ J : Ideal A) : Type u) N,
          (TensorProduct.lid A N) ((I ⊓ J : Ideal A).subtype.rTensor N y) = u x := by
      rw [← Ideal.subtype_rTensor_range] at huxK
      exact huxK
    let inc : (I ⊓ J : Ideal A) →ₗ[A] I :=
      (I ⊓ J).inclusion inf_le_left
    have hinc :
        (TensorProduct.lid A N) (I.subtype.rTensor N (inc.rTensor N y)) = u x := by
      rw [← LinearMap.rTensor_comp_apply]
      have hcomp : I.subtype.comp inc = (I ⊓ J).subtype := by
        ext a
        rfl
      rw [hcomp, hy]
    have hcomm :
        ((TensorProduct.lid A N).comp (I.subtype.rTensor N)).comp
            (u.lTensor I) =
          u.comp ((TensorProduct.lid A M).comp (I.subtype.rTensor M)) := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp [map_add, hz, hw]
      | tmul a m => simp
    have htu :
        (TensorProduct.lid A N) (I.subtype.rTensor N ((u.lTensor I) t)) = u x := by
      change ((TensorProduct.lid A N).comp (I.subtype.rTensor N))
          ((u.lTensor I) t) = u x
      rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply]
      simpa [LinearMap.comp_apply] using congrArg u ht
    have hIinj : Function.Injective
        ((TensorProduct.lid A N).comp (I.subtype.rTensor N)) :=
      (TensorProduct.lid A N).injective.comp
        (Module.Flat.rTensor_preserves_injective_linearMap I.subtype
          Subtype.val_injective)
    have heq : (u.lTensor I) t = inc.rTensor N y :=
      hIinj (htu.trans hinc.symm)
    have hχinc : χI.comp inc = 0 := by
      apply LinearMap.ext
      intro a
      change χ (Submodule.mkQ K (inc a)) = 0
      have hmem : inc a ∈ K := by
        dsimp [K]
        exact a.property.2
      have hzero : Submodule.mkQ K (inc a) = 0 :=
        (Submodule.Quotient.mk_eq_zero K).mpr hmem
      rw [hzero]
      simp
    have hχu : χI.rTensor N ((u.lTensor I) t) = 0 := by
      rw [heq, ← LinearMap.rTensor_comp_apply, hχinc]
      simp
    let eM := TensorProduct.quotTensorEquivQuotSMul M
      (IsLocalRing.maximalIdeal A)
    let eN := TensorProduct.quotTensorEquivQuotSMul N
      (IsLocalRing.maximalIdeal A)
    have hquotcomm :
        eN.toLinearMap.comp
            (u.lTensor (A ⧸ IsLocalRing.maximalIdeal A)) =
          (maximalIdealQuotientMap u).comp eM.toLinearMap := by
      apply TensorProduct.ext'
      intro a m
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      change eN (Ideal.Quotient.mk _ r ⊗ₜ[A] u m) =
        maximalIdealQuotientMap u
          (eM (Ideal.Quotient.mk _ r ⊗ₜ[A] m))
      simp [eM, eN, TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
        maximalIdealQuotientMap, Submodule.mapQ_apply]
    have huTensor : Function.Injective
        (u.lTensor (A ⧸ IsLocalRing.maximalIdeal A)) := by
      intro a b hab
      apply eM.injective
      apply hu
      calc
        maximalIdealQuotientMap u (eM a) = eN ((u.lTensor _) a) := by
          simpa [LinearMap.comp_apply] using congrArg (fun f => f a) hquotcomm.symm
        _ = eN ((u.lTensor _) b) := congrArg eN hab
        _ = maximalIdealQuotientMap u (eM b) := by
          simpa [LinearMap.comp_apply] using congrArg (fun f => f b) hquotcomm
    have hcomm' :
        (u.lTensor (A ⧸ IsLocalRing.maximalIdeal A)).comp (χI.rTensor M) =
          (χI.rTensor N).comp (u.lTensor I) := by
      rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
    apply hχt
    apply huTensor
    change (u.lTensor (A ⧸ IsLocalRing.maximalIdeal A)) (χI.rTensor M t) = 0
    rw [← LinearMap.comp_apply, hcomm', LinearMap.comp_apply, hχu]

/-- Every element of a flat Mittag--Leffler module has a content ideal. -/
theorem exists_contentIdeal_of_flat_mittagLeffler
    {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.Flat A M]
    (hM : Formalization.Books.Algebra.Unit88.IsMittagLefflerModule
      (ModuleCat.of A M)) (x : M) :
    ∃ I : Ideal A, IsContentIdeal x I := by
  /- Prior attempt:
  let z : TensorProduct A A M := 1 ⊗ₜ[A] x
  obtain ⟨I, hI⟩ :=
    (Formalization.Books.Algebra.Unit91.flat_isMittagLeffler_iff_minimal_tensor_submodule
      (M := M) inferInstance).mp hM A (by infer_instance) (by infer_instance) z
  have hiff (J : Ideal A) :
      Formalization.Books.Algebra.Unit89.tensorProductContains J z ↔
        x ∈ J • (⊤ : Submodule A M) := by
    constructor
    · rintro ⟨y, hy⟩
      rw [← Ideal.subtype_rTensor_range]
      refine ⟨y, ?_⟩
      change (TensorProduct.lid A M) (J.subtype.rTensor M y) = x
      rw [hy]
      simp
    · intro hx
      rw [← Ideal.subtype_rTensor_range] at hx
      obtain ⟨y, hy⟩ := hx
      refine ⟨y, ?_⟩
      apply (TensorProduct.lid A M).injective
      change (TensorProduct.lid A M) (J.subtype.rTensor M y) =
        (TensorProduct.lid A M) (1 ⊗ₜ[A] x)
      rw [hy]
      simp
  refine ⟨I, ?_⟩
  constructor
  · intro J hJ
    exact hI.1 ((hiff J).mpr hJ)
  · exact (hiff I).mp hI.2
  -/
  sorry

end

end Formalization.Books.MoreAlgebra.Unit25
