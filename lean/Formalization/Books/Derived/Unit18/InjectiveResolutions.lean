import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Formalization.Books.Derived.Unit04.ElementaryResults
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Derived.Unit12.CanonicalDeltaFunctor
import Formalization.Books.Homology.Unit06.Extensions

/-!
# Derived Categories, Chapter 18: injective resolutions

The object-level resolution is Mathlib's canonical `InjectiveResolution`.
The source also uses resolutions of arbitrary complexes, so this file adds the
small source-facing package for a bounded-below termwise injective complex
quasi-isomorphic to a given complex.  The comparison statements use
Mathlib's `IsKInjective` and derived-category localization APIs.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u

namespace Formalization.Books.Derived.Unit18

/-! ## The two notions of injective resolution -/

/- The source's object-level notion is already Mathlib's canonical
  `CategoryTheory.InjectiveResolution`.  Its `cochainComplex` and `ι'`
  provide the source's integer-indexed complex and quasi-isomorphism. -/
abbrev ObjectInjectiveResolution
    {A : Type u} [Category.{v} A] [Abelian A] (X : A) :=
  CategoryTheory.InjectiveResolution X

/-- A bounded-below termwise injective complex equipped with a
quasi-isomorphism from `K`. -/
structure ComplexInjectiveResolution
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : BookComplex A) where
  /-- The complex used as the resolution. -/
  target : BookComplex A
  /-- The resolution map. -/
  map : K ⟶ target
  /-- The target is bounded below. -/
  boundedBelow : IsBoundedBelow target
  /-- Every term of the target is injective. -/
  termwiseInjective : ∀ n : ℤ, Injective (target.X n)
  /-- The resolution map is a quasi-isomorphism. -/
  quasiIso : QuasiIso map

/- The canonical object resolution also gives the corresponding resolution of
  the stalk complex in degree zero. -/
noncomputable def object_injective_resolution_as_complex
    {A : Type u} [Category.{v} A] [Abelian A] {X : A}
    (R : ObjectInjectiveResolution X) :
    ComplexInjectiveResolution ((CochainComplex.singleFunctor A 0).obj X) where
  target := R.cochainComplex
  map := R.ι'
  boundedBelow := ⟨0, inferInstance⟩
  termwiseInjective := fun _ => inferInstance
  quasiIso := inferInstance

/-- The source-facing predicate for a specified target and resolution map. -/
def IsComplexInjectiveResolution
    {A : Type u} [Category.{v} A] [Abelian A]
    (K I : BookComplex A) (f : K ⟶ I) : Prop :=
  IsBoundedBelow I ∧
    (∀ n : ℤ, Injective (I.X n)) ∧ QuasiIso f

/- The source's zero-degree kernel condition is exactly the canonical
  `isLimitKernelFork` field/API, and the positive cohomology vanishing is the
  corresponding consequence of the canonical quasi-isomorphism. -/
noncomputable def object_injective_resolution_zero_is_kernel
    {A : Type u} [Category.{v} A] [Abelian A] {X : A}
    (R : ObjectInjectiveResolution X) :
    IsLimit R.kernelFork :=
  R.isLimitKernelFork

theorem object_injective_resolution_cochain_properties
    {A : Type u} [Category.{v} A] [Abelian A] {X : A}
    (R : ObjectInjectiveResolution X) :
    IsBoundedBelow R.cochainComplex ∧
      (∀ n : ℤ, Injective (R.cochainComplex.X n)) ∧
        QuasiIso R.ι' := by
  exact ⟨⟨0, inferInstance⟩, (fun _ => inferInstance), inferInstance⟩

theorem object_injective_resolution_positive_cohomology_zero
    {A : Type u} [Category.{v} A] [Abelian A] {X : A}
    (R : ObjectInjectiveResolution X) :
    ∀ n : ℤ, 0 < n → IsZero (R.cochainComplex.homology n) := by
  let _ : QuasiIso R.ι' := inferInstance
  intro n hn
  exact IsZero.of_iso
    (((CochainComplex.singleFunctor A 0).obj X).isZero_of_isLE 0 n (by omega))
    (asIso (HomologicalComplex.homologyMap R.ι' n)).symm

/- The construction below is Mathlib's actual enough-injectives construction,
  rather than a second resolution construction. -/
noncomputable def canonical_object_injective_resolution
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (X : A) : ObjectInjectiveResolution X :=
  CategoryTheory.InjectiveResolution.of X

theorem object_injective_resolution_exists
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (X : A) : Nonempty (ObjectInjectiveResolution X) :=
  ⟨canonical_object_injective_resolution X⟩

/-! ## Boundedness and existence -/

theorem cohomology_bounded_below_of_injective_resolution
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : BookComplex A} (R : ComplexInjectiveResolution K) :
    ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.homology n) := by
  obtain ⟨a, ha⟩ := R.boundedBelow
  let _ : R.target.IsStrictlyGE a := ha
  let _ : QuasiIso R.map := R.quasiIso
  refine ⟨a, fun n hn => ?_⟩
  exact IsZero.of_iso (R.target.isZero_of_isGE a n (by omega))
    (asIso (HomologicalComplex.homologyMap R.map n))

theorem injective_resolution_of_cohomology_bounded_below
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : BookComplex A}
    (hK : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    ∃ (L : BookComplex A) (f : K ⟶ L),
      QuasiIso f ∧ IsBoundedBelow L := by
  obtain ⟨a, ha⟩ := hK
  obtain ⟨L, f, hf, hL⟩ :=
    boundedCohomology_replacement_below A K ⟨a - 1, by
      intro n hn
      exact ha n (by omega)⟩
  exact ⟨L, f, hf, hL⟩

theorem complex_injective_resolution_exists
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {K : BookComplex A}
    (hK : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    Nonempty (ComplexInjectiveResolution K) := by
  obtain ⟨L, f, hf, hLbelow⟩ :=
    injective_resolution_of_cohomology_bounded_below hK
  obtain ⟨b, hb⟩ := hLbelow
  let _ : L.IsStrictlyGE b := hb
  let LP : CochainComplex.Plus A := ⟨L, ⟨b, hb⟩⟩
  obtain ⟨I, hI, i, hi⟩ :=
    CochainComplex.Plus.exists_quasiIso_injective LP b
  have hi' : QuasiIso i.hom := by
    change QuasiIso i.hom at hi
    exact hi
  let _ : I.obj.IsStrictlyGE b := hI
  have htarget :
      ((InjectiveObject.ι A).mapCochainComplexPlus.obj I).obj.IsStrictlyGE b := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    change IsZero ((InjectiveObject.ι A).obj (I.obj.X n))
    exact (CategoryTheory.Functor.map_isZero (InjectiveObject.ι A)
      (CochainComplex.isZero_of_isStrictlyGE I.obj b n hn))
  have hInj (n : ℤ) :
      Injective (((InjectiveObject.ι A).mapCochainComplexPlus.obj I).obj.X n) := by
    change Injective ((InjectiveObject.ι A).obj (I.obj.X n))
    infer_instance
  let _ : QuasiIso f := hf
  let _ : QuasiIso i.hom := hi'
  let q : K ⟶ ((InjectiveObject.ι A).mapCochainComplexPlus.obj I).obj :=
    f ≫ i.hom
  have hq : QuasiIso q := by
    dsimp [q]
    infer_instance
  exact ⟨{
    target := ((InjectiveObject.ι A).mapCochainComplexPlus.obj I).obj
    map := q
    boundedBelow := ⟨b, htarget⟩
    termwiseInjective := hInj
    quasiIso := hq
  }⟩

theorem complex_injective_resolution_exists_with_mono
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (K : BookComplex A) (a : ℤ) (hK : K.IsStrictlyGE a) :
    ∃ R : ComplexInjectiveResolution K,
      R.target.IsStrictlyGE a ∧
        ∀ n : ℤ, Mono (R.map.f n) := by
  let _ : K.IsStrictlyGE a := hK
  obtain ⟨L, i, hi, hqi, hLinj, hL⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective K (a - 1) a
  let _ : L.IsStrictlyGE (a - 1) := hL
  let _ : Mono i := hi
  let _ : HasDerivedCategory A := HasDerivedCategory.standard A
  let _ : QuasiIso i := hqi
  have hLGE : L.IsGE a := by
    have hKGE : K.IsGE a := inferInstance
    rw [← DerivedCategory.isGE_Q_obj_iff] at hKGE ⊢
    exact DerivedCategory.TStructure.t.isGE_of_iso (asIso (DerivedCategory.Q.map i)) a
  let _ : L.IsGE a := hLGE
  let _ : QuasiIso (L.πTruncGE a) :=
    (L.quasiIso_πTruncGE_iff a).mpr inferInstance
  let q : K ⟶ L.truncGE a := i ≫ L.πTruncGE a
  let _ : QuasiIso q := by
    dsimp [q]
    infer_instance
  have htarget : (L.truncGE a).IsStrictlyGE a := by infer_instance
  have hLop : Injective (L.opcycles a) :=
    L.injective_opcycles (a - 1) a (L.exactAt_of_isGE a (a - 1))
  have htruncinj : ∀ n : ℤ, Injective ((L.truncGE a).X n) := by
    intro n
    obtain h | rfl | h := lt_trichotomy n a
    · exact (CochainComplex.isZero_of_isStrictlyGE (L.truncGE a) a n h).injective
    · exact Injective.of_iso (L.truncGEXIsoOpcycles n).symm hLop
    · exact Injective.of_iso (L.truncGEXIso a n h).symm (hLinj n)
  have hqmono : ∀ n : ℤ, Mono (q.f n) := by
    intro n
    obtain h | rfl | h := lt_trichotomy n a
    · constructor
      intro Z g h' _
      exact (CochainComplex.isZero_of_isStrictlyGE K a n h).eq_of_tgt g h'
    ·
      have hcomp :
          q.f n ≫ (L.truncGEXIsoOpcycles n).hom = i.f n ≫ L.pOpcycles n := by
        apply (cancel_mono (L.truncGEXIsoOpcycles n).inv).1
        change ((i.f n ≫ (L.πTruncGE n).f n) ≫
            (L.truncGEXIsoOpcycles n).hom) ≫
              (L.truncGEXIsoOpcycles n).inv =
          (i.f n ≫ L.pOpcycles n) ≫ (L.truncGEXIsoOpcycles n).inv
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
        dsimp [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
        have he : (ComplexShape.embeddingUpIntGE n).f 0 = n := by simp
        have hb : (ComplexShape.embeddingUpIntGE n).BoundaryGE 0 := by
          rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
        have hIsoInv :
            (L.truncGEXIsoOpcycles n).inv =
              (L.truncGE'XIsoOpcycles (ComplexShape.embeddingUpIntGE n) he hb).inv ≫
                ((L.truncGE' (ComplexShape.embeddingUpIntGE n)).extendXIso
                  (ComplexShape.embeddingUpIntGE n) he).inv := by
          rfl
        rw [ComplexShape.Embedding.liftExtend_f
          (ComplexShape.embeddingUpIntGE n)
          (L.restrictionToTruncGE' (ComplexShape.embeddingUpIntGE n))
          (L.restrictionToTruncGE'_hasLift (ComplexShape.embeddingUpIntGE n))
          (i := 0) (i' := n) he]
        rw [L.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
          (ComplexShape.embeddingUpIntGE n) (i := 0) (i' := n) he hb]
        rw [hIsoInv]
        simp [Category.assoc]
        rfl
      have hcompmono : Mono (i.f n ≫ L.pOpcycles n) := by
        constructor
        intro Z g g' hg
        apply sub_eq_zero.mp
        have hgq : (g - g') ≫ i.f n ≫ L.pOpcycles n = 0 := by
          rw [sub_comp, hg, sub_self]
        obtain ⟨Z', p, hp, x, hx⟩ :=
          (L.comp_pOpcycles_eq_zero_iff_up_to_refinements
            ((g - g') ≫ i.f n) (n - 1) (by simp)).1 (by
              simpa only [Category.assoc] using hgq)
        have hgi : p ≫ (g - g') ≫ i.f n ≫ L.d n (n + 1) = 0 := by
          calc
            p ≫ (g - g') ≫ i.f n ≫ L.d n (n + 1) =
                (p ≫ (g - g') ≫ i.f n) ≫ L.d n (n + 1) := by simp
            _ = (x ≫ L.d (n - 1) n) ≫ L.d n (n + 1) := by rw [hx]
            _ = 0 := by simp
        have hpcycle : (p ≫ (g - g')) ≫ K.d n (n + 1) = 0 := by
          apply (cancel_mono (i.f (n + 1))).1
          simpa only [Category.assoc, i.comm, comp_zero, zero_comp] using hgi
        obtain ⟨Z'', p', hp', x', hx'⟩ :=
          (HomologicalComplex.mono_homologyMap_iff_up_to_refinements
            i (n - 1) n (n + 1) (by simp) (by simp)).1 (by infer_instance)
              (p ≫ (g - g')) hpcycle x (by simpa only [Category.assoc] using hx)
        have hxzero : x' = 0 := by
          exact (CochainComplex.isZero_of_isStrictlyGE K n (n - 1) (by omega)).eq_of_tgt
            x' 0
        apply (cancel_epi (p' ≫ p)).1
        rw [Category.assoc, hx', hxzero, comp_zero, zero_comp]
      let _ : Mono (i.f n ≫ L.pOpcycles n) := hcompmono
      exact mono_of_mono_fac hcomp
    · dsimp [q]
      apply mono_of_mono_fac (f := (L.truncGEXIso a n h).hom) (h := i.f n)
      apply (cancel_mono (L.truncGEXIso a n h).inv).1
      have hk :
          (ComplexShape.embeddingUpIntGE a).f ((n - a).natAbs) = n := by
        change a + (n - a).natAbs = n
        rw [Int.natAbs_of_nonneg (by lia), add_sub_cancel]
      have hkB :
          ¬ (ComplexShape.embeddingUpIntGE a).BoundaryGE (n - a).natAbs := by
        rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero]
        lia
      change ((i.f n ≫ (L.πTruncGE a).f n) ≫
          (L.truncGEXIso a n h).hom) ≫ (L.truncGEXIso a n h).inv =
        i.f n ≫ (L.truncGEXIso a n h).inv
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      dsimp [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
      rw [ComplexShape.Embedding.liftExtend_f
        (ComplexShape.embeddingUpIntGE a)
        (L.restrictionToTruncGE' (ComplexShape.embeddingUpIntGE a))
        (L.restrictionToTruncGE'_hasLift (ComplexShape.embeddingUpIntGE a)) hk]
      rw [L.restrictionToTruncGE'_f_eq_iso_hom_iso_inv
        (ComplexShape.embeddingUpIntGE a) hk hkB]
      have hIsoInv :
          (L.truncGEXIso a n h).inv =
            (L.truncGE'XIso (ComplexShape.embeddingUpIntGE a) hk hkB).inv ≫
              ((L.truncGE' (ComplexShape.embeddingUpIntGE a)).extendXIso
                (ComplexShape.embeddingUpIntGE a) hk).inv := by
        rfl
      rw [hIsoInv]
      simp [Category.assoc]
  exact ⟨{
    target := L.truncGE a
    map := q
    boundedBelow := ⟨a, htarget⟩
    termwiseInjective := htruncinj
    quasiIso := inferInstance
  }, htarget, hqmono⟩

/-! ## Acyclic complexes and K-injective complexes -/

theorem isKInjective_of_bounded_below_termwise_injective
    {A : Type u} [Category.{v} A] [Abelian A]
    (I : BookComplex A) (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n)) :
    I.IsKInjective := by
  obtain ⟨a, ha⟩ := hI
  let _ : I.IsStrictlyGE a := ha
  let _ : ∀ n : ℤ, Injective (I.X n) := hIinj
  exact CochainComplex.isKInjective_of_injective I a

theorem acyclic_to_injective_is_homotopic_zero
    {A : Type u} [Category.{v} A] [Abelian A]
    {K I : BookComplex A} (hK : K.Acyclic)
    (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n)) (f : K ⟶ I) :
    Nonempty (Homotopy f 0) := by
  let _ : I.IsKInjective :=
    isKInjective_of_bounded_below_termwise_injective I hI hIinj
  exact CochainComplex.IsKInjective.nonempty_homotopy_zero f hK

/-! ## The cone remark -/

theorem quasiIso_mapping_cone_is_acyclic
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L : BookComplex A} (f : K ⟶ L) (hf : QuasiIso f) :
    (CochainComplex.mappingCone f).Acyclic := by
  let _ : HasDerivedCategory A := HasDerivedCategory.standard A
  let _ : QuasiIso f := hf
  apply (Formalization.Books.Homology.Unit13.cochain_acyclic_iff_cohomology_isZero _).2
  intro n
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)
  have hT : T ∈ distTriang (DerivedCategory A) := by
    dsimp [T]
    exact DerivedCategory.mappingCone_triangle_distinguished f
  have hfEpi : Epi ((DerivedCategory.homologyFunctor A n).map
      (DerivedCategory.Q.map f)) := by infer_instance
  have hfMono : Mono ((DerivedCategory.homologyFunctor A (n + 1)).map
      (DerivedCategory.Q.map f)) := by infer_instance
  have hconeZero :
      (DerivedCategory.homologyFunctor A n).map T.mor₂ = 0 := by
    exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff
      T hT n).1 hfEpi
  have hδ : DerivedCategory.HomologySequence.δ T n (n + 1) (by omega) = 0 := by
    exact (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      T hT n (n + 1) (by omega)).1 hfMono
  have hconeEpi : Epi ((DerivedCategory.homologyFunctor A n).map T.mor₂) := by
    exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
      T hT n (n + 1) (by omega)).2 hδ
  have hzeroDerived : IsZero ((DerivedCategory.homologyFunctor A n).obj T.obj₃) := by
    rw [IsZero.iff_id_eq_zero]
    apply (cancel_epi ((DerivedCategory.homologyFunctor A n).map T.mor₂)).1
    simp [hconeZero]
  have hzeroDerived' :
      IsZero ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor A n).obj
        (CochainComplex.mappingCone f)) := by
    change IsZero ((DerivedCategory.homologyFunctor A n).obj T.obj₃)
    exact hzeroDerived
  exact IsZero.of_iso hzeroDerived'
    ((DerivedCategory.homologyFunctorFactors A n).app (CochainComplex.mappingCone f)).symm

theorem mapping_cone_triangle_distinguished
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L : BookComplex A} (f : K ⟶ L) :
    CochainComplex.mappingCone.triangleh f ∈
      distTriang (BookHomotopyCategory A) :=
  HomotopyCategory.mappingCone_triangleh_distinguished f

/- The exact Hom sequence in the source remark is the standard co-special
  property of a distinguished triangle; the two outer vanishings are supplied
  by `acyclic_to_injective_is_homotopic_zero`. -/
theorem mapping_cone_triangle_coSpecial
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L : BookComplex A} (f : K ⟶ L) :
    Formalization.Books.Derived.Unit04.CoSpecialTriangle
      (CochainComplex.mappingCone.triangleh f) := by
  exact Formalization.Books.Derived.Unit04.distinguished_triangle_coSpecial _
    (mapping_cone_triangle_distinguished f)

/- The conclusion of the cone argument is the bijectivity of precomposition
  with a quasi-isomorphism on homotopy classes into a bounded-below injective
  complex. -/
theorem quasiIso_precomposition_to_injective_bijective
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L I : BookComplex A} (α : K ⟶ L) (hα : QuasiIso α)
    (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n)) :
    Function.Bijective
      (fun (β :
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L ⟶
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) =>
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map α ≫ β) := by
  let _ : HasDerivedCategory A := HasDerivedCategory.standard A
  let _ : I.IsKInjective :=
    isKInjective_of_bounded_below_termwise_injective I hI hIinj
  have hα' : HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map α) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact hα
  let _ : IsIso ((DerivedCategory.Qh (C := A)).map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map α)) :=
    Localization.inverts _ _ _ hα'
  let hK := CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) I
  let hL := CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) I
  constructor
  · intro β₁ β₂ hβ
    apply hL.1
    apply (cancel_epi ((DerivedCategory.Qh (C := A)).map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map α))).1
    simpa only [Functor.map_comp] using congrArg
      (fun f => (DerivedCategory.Qh (C := A)).map f) hβ
  · intro g
    obtain ⟨β, hβ⟩ := hL.2
      (inv ((DerivedCategory.Qh (C := A)).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map α)) ≫
        (DerivedCategory.Qh (C := A)).map g)
    refine ⟨β, hK.1 ?_⟩
    rw [Functor.map_comp, hβ]
    simp

private lemma imageSubobject_comp_epi_eq
    {A : Type u} [Category.{v} A] [Abelian A]
    {X Y Z : A} (e : X ⟶ Y) (g : Y ⟶ Z) [Epi e] :
    imageSubobject (e ≫ g) = imageSubobject g := by
  let h := imageSubobject_comp_le e g
  let _ : Epi (Subobject.ofLE _ _ h) :=
    imageSubobject_comp_le_epi_of_epi e g
  let _ : IsIso (Subobject.ofLE _ _ h) := isIso_of_mono_of_epi _
  exact Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ h)) (by simp)

/- The image/intersection identity used in the degreewise-monomorphism part
  of the lifting lemma is recorded with Mathlib's canonical subobject images. -/
theorem quasiIso_degreewise_mono_image_intersection
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L : BookComplex A} (α : K ⟶ L) (n : ℤ)
    (hα : QuasiIso α) (hmono : ∀ n : ℤ, Mono (α.f n)) :
    imageSubobject (K.d (n - 1) n ≫ α.f n) =
      imageSubobject (α.f n) ⊓ imageSubobject (L.d (n - 1) n) := by
  let _ : QuasiIso α := hα
  let _ : Mono (α.f n) := hmono n
  let P : Subobject (L.X n) :=
    imageSubobject (α.f n) ⊓ imageSubobject (L.d (n - 1) n)
  have hleft : imageSubobject (K.d (n - 1) n ≫ α.f n) ≤ P := by
    apply Subobject.le_inf
    · exact imageSubobject_comp_le (K.d (n - 1) n) (α.f n)
    · apply imageSubobject_le _
        (α.f (n - 1) ≫ factorThruImageSubobject (L.d (n - 1) n))
      rw [Category.assoc, imageSubobject_arrow_comp]
      exact α.comm (n - 1) n
  have hPα : P ≤ imageSubobject (α.f n) :=
    Subobject.le_of_factors (Subobject.inf_arrow_factors_left _ _)
  have hPα' : P ≤ Subobject.mk (α.f n) := by
    simpa only [imageSubobject_mono (α.f n)] using hPα
  let x : (P : A) ⟶ K.X n := Subobject.ofLEMk P (α.f n) hPα'
  have hx : x ≫ α.f n = P.arrow := Subobject.ofLEMk_comp hPα'
  have hPcycle : P.arrow ≫ L.d n (n + 1) = 0 := by
    have hPd := Subobject.inf_arrow_factors_right
      (imageSubobject (α.f n)) (imageSubobject (L.d (n - 1) n))
    rw [← Subobject.factorThru_arrow (imageSubobject (L.d (n - 1) n))
      P.arrow hPd, Category.assoc]
    rw [imageSubobject_arrow_comp_eq_zero (by simp)]
    simp
  have hxcycle : x ≫ K.d n (n + 1) = 0 := by
    apply (cancel_mono (α.f (n + 1))).1
    rw [Category.assoc, ← α.comm n (n + 1), ← Category.assoc, hx, hPcycle]
    simp
  let z : (P : A) ⟶ K.cycles n :=
    K.liftCycles x (n + 1) (by simp) (by simpa using hxcycle)
  have hz_i : z ≫ K.iCycles n = x := by
    dsimp [z]
    exact K.liftCycles_i x (n + 1) (by simp) _
  have hclassL :
      L.liftCycles (x ≫ α.f n) (n + 1) (by simp) (by
        calc
          (x ≫ α.f n) ≫ L.d n (n + 1) =
              (x ≫ K.d n (n + 1)) ≫ α.f (n + 1) := by
                rw [Category.assoc, α.comm n (n + 1), ← Category.assoc]
          _ = 0 := by rw [hxcycle, zero_comp]) ≫ L.homologyπ n = 0 := by
    have hPd := (Subobject.inf_arrow_factors_right
      (imageSubobject (α.f n)) (imageSubobject (L.d (n - 1) n)))
    let t := (imageSubobject (L.d (n - 1) n)).factorThru P.arrow hPd
    have ht : t ≫ (imageSubobject (L.d (n - 1) n)).arrow = P.arrow :=
      Subobject.factorThru_arrow _ _ hPd
    have hDclass :
      L.liftCycles (L.d (n - 1) n) (n + 1) (by simp) (by simp) ≫
            L.homologyπ n = 0 :=
      L.liftCycles_homologyπ_eq_zero_of_boundary (L.d (n - 1) n) (n + 1)
        (by simp) (𝟙 _) (by simp)
    have hImageZero :
        (imageSubobject (L.d (n - 1) n)).arrow ≫ L.d n (n + 1) = 0 := by
      apply imageSubobject_arrow_comp_eq_zero
      simp
    have hImageLift :
        factorThruImageSubobject (L.d (n - 1) n) ≫
            L.liftCycles ((imageSubobject (L.d (n - 1) n)).arrow)
              (n + 1) (by simp) hImageZero =
          L.liftCycles (L.d (n - 1) n) (n + 1) (by simp) (by simp) := by
      apply (cancel_mono (L.iCycles n)).1
      simp only [Category.assoc, L.liftCycles_i, imageSubobject_arrow_comp]
    have hImageClass :
        L.liftCycles ((imageSubobject (L.d (n - 1) n)).arrow)
              (n + 1) (by simp) hImageZero ≫ L.homologyπ n = 0 := by
      apply (cancel_epi (factorThruImageSubobject (L.d (n - 1) n))).1
      rw [← Category.assoc, hImageLift, hDclass]
      simp
    have hLift :
        L.liftCycles (x ≫ α.f n) (n + 1) (by simp) (by
          calc
            (x ≫ α.f n) ≫ L.d n (n + 1) =
                (x ≫ K.d n (n + 1)) ≫ α.f (n + 1) := by
                  rw [Category.assoc, α.comm n (n + 1), ← Category.assoc]
          _ = 0 := by rw [hxcycle, zero_comp]) =
          t ≫ L.liftCycles ((imageSubobject (L.d (n - 1) n)).arrow)
            (n + 1) (by simp) hImageZero := by
      apply (cancel_mono (L.iCycles n)).1
      simp only [Category.assoc, L.liftCycles_i]
      rw [hx, ht]
    rw [hLift, Category.assoc, hImageClass, comp_zero]
  have hclass : z ≫ K.homologyπ n = 0 := by
    apply (cancel_mono (HomologicalComplex.homologyMap α n)).1
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
      ← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
    simpa using hclassL
  let T : ShortComplex A := ShortComplex.mk
    (K.toCycles (n - 1) n) (K.homologyπ n) (by simp)
  have hT : T.Exact := by
    apply ShortComplex.exact_of_g_is_cokernel
    exact K.homologyIsCokernel (n - 1) n (by simp)
  have himageK :
      imageSubobject (K.toCycles (n - 1) n) =
        kernelSubobject (K.homologyπ n) := by
    exact T.exact_iff_image_eq_kernel.mp hT
  have hzTo : (imageSubobject (K.toCycles (n - 1) n)).Factors z := by
    rw [himageK]
    exact kernelSubobject_factors _ z hclass
  let t : (P : A) ⟶ (imageSubobject (K.toCycles (n - 1) n) : A) :=
    (imageSubobject (K.toCycles (n - 1) n)).factorThru z hzTo
  have ht_z : t ≫ (imageSubobject (K.toCycles (n - 1) n)).arrow = z := by
    dsimp [t]
    exact Subobject.factorThru_arrow _ _ hzTo
  let g : (imageSubobject (K.toCycles (n - 1) n) : A) ⟶ L.X n :=
    (imageSubobject (K.toCycles (n - 1) n)).arrow ≫ K.iCycles n ≫ α.f n
  have hpg : t ≫ g = P.arrow := by
    dsimp [g]
    rw [← Category.assoc, ht_z, ← Category.assoc, hz_i, hx]
  have hP_g : P ≤ imageSubobject g := by
    have h := imageSubobject_le P.arrow
      (t ≫ factorThruImageSubobject g) (by
        rw [Category.assoc, imageSubobject_arrow_comp, hpg])
    simpa only [imageSubobject_mono P.arrow, Subobject.mk_arrow] using h
  have himage_g : imageSubobject g =
      imageSubobject (K.d (n - 1) n ≫ α.f n) := by
    let g' : (imageSubobject (K.toCycles (n - 1) n) : A) ⟶ L.X n :=
      (imageSubobject (K.toCycles (n - 1) n)).arrow ≫ K.iCycles n ≫ α.f n
    have hcomp : factorThruImageSubobject (K.toCycles (n - 1) n) ≫ g' =
        K.d (n - 1) n ≫ α.f n := by
      dsimp [g']
      rw [← Category.assoc, imageSubobject_arrow_comp]
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ α.f n) (K.toCycles_i (n - 1) n)
    have h₁ := imageSubobject_comp_epi_eq
      (factorThruImageSubobject (K.toCycles (n - 1) n)) g'
    rw [hcomp] at h₁
    simpa only [g, g'] using h₁.symm
  apply le_antisymm hleft
  rw [← himage_g]
  exact hP_g

/-! ## Lifting and uniqueness -/

theorem injective_resolution_lift_up_to_homotopy
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L I : BookComplex A} (α : K ⟶ L) (γ : K ⟶ I)
    (hα : QuasiIso α) (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n)) :
    ∃ β : L ⟶ I, Nonempty (Homotopy (α ≫ β) γ) := by
  obtain ⟨b, hb⟩ :=
    (quasiIso_precomposition_to_injective_bijective α hα hI hIinj).2
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map γ)
  obtain ⟨β, rfl⟩ :=
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective b
  refine ⟨β, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  simpa only [Functor.map_comp] using hb

theorem injective_resolution_lift_of_degreewise_mono
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L I : BookComplex A} (α : K ⟶ L) (γ : K ⟶ I)
    (hα : QuasiIso α) (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n))
    (hmono : ∀ n : ℤ, Mono (α.f n)) :
    ∃ β : L ⟶ I, α ≫ β = γ := by
  obtain ⟨a, ha⟩ := hI
  let _ : I.IsStrictlyGE a := ha
  let _ : ∀ n : ℤ, Injective (I.X n) := hIinj
  let _ : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  let p : I ⟶ (0 : BookComplex A) := 0
  let sq : CommSq γ α p (0 : L ⟶ (0 : BookComplex A)) := ⟨by simp [p]⟩
  have hsq : ∀ n : ℤ,
      (sq.map (HomologicalComplex.eval A (ComplexShape.up ℤ) n)).LiftStruct := by
    intro n
    let _ : Mono (α.f n) := hmono n
    let l : L.X n ⟶ I.X n := Injective.factorThru (γ.f n) (α.f n)
    refine ⟨l, ?_, ?_⟩
    · exact Injective.comp_factorThru (γ.f n) (α.f n)
    · change l ≫ 0 = 0
      simp
  have hι : (𝟙 I) ≫ p = 0 := by
    dsimp [p]
    simp
  have hK : IsLimit (KernelFork.ofι (𝟙 I) hι) :=
    KernelFork.IsLimit.ofId p rfl
  let T : ShortComplex (BookComplex A) :=
    ShortComplex.mk α (cokernel.π α) (cokernel.condition α)
  let _ : Mono α := HomologicalComplex.mono_of_mono_f α hmono
  have hT : T.ShortExact := by
    dsimp [T]
    exact { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel α) }
  have hCoker : (cokernel α).Acyclic := hT.acyclic_X₃ hα
  let z : CochainComplex.HomComplex.Cocycle (cokernel α) I 1 :=
    CochainComplex.Lifting.cocycle₁ sq hsq
      (hπ := cokernel.condition α) (cokernelIsCokernel α) hK
  obtain ⟨u, hu⟩ := CochainComplex.IsKInjective.eq_δ_of_cocycle z hCoker 0 (by simp)
  have hsqLift : sq.HasLift :=
    CochainComplex.Lifting.hasLift sq hsq
      (hπ := cokernel.condition α) (cokernelIsCokernel α) hK u hu
  let _ : sq.HasLift := hsqLift
  exact ⟨sq.lift, CommSq.fac_left sq⟩

theorem injective_resolution_lift_unique_up_to_homotopy
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L I : BookComplex A} (α : K ⟶ L) (γ : K ⟶ I)
    (hα : QuasiIso α) (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n))
    (β₁ β₂ : L ⟶ I)
    (hβ₁ : Nonempty (Homotopy (α ≫ β₁) γ))
    (hβ₂ : Nonempty (Homotopy (α ≫ β₂) γ)) :
    Nonempty (Homotopy β₁ β₂) := by
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have hcomp : q.map α ≫ q.map β₁ = q.map α ≫ q.map β₂ := by
    rw [← q.map_comp, ← q.map_comp]
    exact (HomotopyCategory.eq_of_homotopy _ _ hβ₁.some).trans
      (HomotopyCategory.eq_of_homotopy _ _ hβ₂.some).symm
  have hβ : q.map β₁ = q.map β₂ :=
    (quasiIso_precomposition_to_injective_bijective α hα hI hIinj).1 hcomp
  exact ⟨HomotopyCategory.homotopyOfEq _ _ hβ⟩

/-! ## Morphisms into an injective complex -/

theorem morphisms_into_injective_complex_bijective
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (L : BookHomotopyCategory A) (I : BookComplex A)
    (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n)) :
    Function.Bijective
      ((DerivedCategory.Qh (C := A)).map :
        (L ⟶ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) → _) := by
  let _ : I.IsKInjective :=
    isKInjective_of_bounded_below_termwise_injective I hI hIinj
  exact derivedCategory_map_bijective_to_KInjective A L I

/-! ## Short exact sequences and their injective resolutions -/

/- The diagram in the source is recorded by the bottom short exact row,
  its two commutative squares, and three `ComplexInjectiveResolution`
  witnesses. -/
def InjectiveResolutionShortExactData
    {A : Type u} [Category.{v} A] [Abelian A]
    (S : ShortComplex (CompPlus A))
    (I₁ I₂ I₃ : CompPlus A)
    (a : S.X₁ ⟶ I₁) (b : S.X₂ ⟶ I₂) (c : S.X₃ ⟶ I₃) : Prop :=
  IsComplexInjectiveResolution S.X₁.obj I₁.obj a.hom ∧
    IsComplexInjectiveResolution S.X₂.obj I₂.obj b.hom ∧
      IsComplexInjectiveResolution S.X₃.obj I₃.obj c.hom ∧
        ∃ (u : I₁ ⟶ I₂) (v : I₂ ⟶ I₃) (h : u ≫ v = 0),
          (ShortComplex.mk u v h).ShortExact ∧
            a ≫ u = S.f ≫ b ∧ b ≫ v = S.g ≫ c

private theorem quasiIso_middle_of_shortExact_map
    {A : Type u} [Category.{v} A] [Abelian A]
    {S₁ S₂ : ShortComplex (BookComplex A)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  let _ : QuasiIso φ.τ₁ := h₁
  let _ : QuasiIso φ.τ₃ := h₃
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  haveI hτ₁ (i : ℤ) : IsIso (HomologicalComplex.homologyMap φ.τ₁ i) :=
    (quasiIsoAt_iff_isIso_homologyMap φ.τ₁ i).mp inferInstance
  haveI hτ₃ (i : ℤ) : IsIso (HomologicalComplex.homologyMap φ.τ₃ i) :=
    (quasiIsoAt_iff_isIso_homologyMap φ.τ₃ i).mp inferInstance
  have hmono : Mono (HomologicalComplex.homologyMap φ.τ₂ n) := by
    apply Abelian.mono_of_epi_of_mono_of_mono
      ((ComposableArrows.δ₀Functor ⋙ ComposableArrows.δ₀Functor).map
        (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂
          (n - 1) n (by simp)))
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact
        hS₁ (n - 1) n (by simp)).δ₀.δ₀
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact
        hS₂ (n - 1) n (by simp)).δ₀.δ₀
    · change Epi (HomologicalComplex.homologyMap φ.τ₃ (n - 1))
      infer_instance
    · change Mono (HomologicalComplex.homologyMap φ.τ₁ n)
      infer_instance
    · change Mono (HomologicalComplex.homologyMap φ.τ₃ n)
      infer_instance
  have hepi : Epi (HomologicalComplex.homologyMap φ.τ₂ n) := by
    apply Abelian.epi_of_epi_of_epi_of_mono
      ((ComposableArrows.δlastFunctor ⋙ ComposableArrows.δlastFunctor).map
        (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂
          n (n + 1) (by simp)))
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact
        hS₁ n (n + 1) (by simp)).δlast.δlast
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact
        hS₂ n (n + 1) (by simp)).δlast.δlast
    · change Epi (HomologicalComplex.homologyMap φ.τ₁ n)
      infer_instance
    · change Epi (HomologicalComplex.homologyMap φ.τ₃ n)
      infer_instance
    · change Mono (HomologicalComplex.homologyMap φ.τ₁ (n + 1))
      infer_instance
  let _ : Mono (HomologicalComplex.homologyMap φ.τ₂ n) := hmono
  let _ : Epi (HomologicalComplex.homologyMap φ.τ₂ n) := hepi
  exact isIso_of_mono_of_epi (HomologicalComplex.homologyMap φ.τ₂ n)

theorem injective_resolution_short_exact
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (S : ShortComplex (CompPlus A)) (hS : S.ShortExact) :
    ∃ (I₁ I₂ I₃ : CompPlus A)
      (a : S.X₁ ⟶ I₁) (b : S.X₂ ⟶ I₂) (c : S.X₃ ⟶ I₃),
      InjectiveResolutionShortExactData S I₁ I₂ I₃ a b c := by
  have hX₁ : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (S.X₁.obj.homology n) := by
    obtain ⟨a, ha⟩ := S.X₁.2
    let _ : S.X₁.obj.IsStrictlyGE a := ha
    exact ⟨a, fun n hn => S.X₁.obj.isZero_of_isGE a n hn⟩
  have hX₃ : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (S.X₃.obj.homology n) := by
    obtain ⟨a, ha⟩ := S.X₃.2
    let _ : S.X₃.obj.IsStrictlyGE a := ha
    exact ⟨a, fun n hn => S.X₃.obj.isZero_of_isGE a n hn⟩
  obtain ⟨R₁⟩ := complex_injective_resolution_exists hX₁
  let I₁ : CompPlus A := ⟨R₁.target, R₁.boundedBelow⟩
  let a : S.X₁ ⟶ I₁ := ObjectProperty.homMk R₁.map
  let E₀ := Formalization.Books.Homology.Unit06.extensionOfShortExact hS
  let E : Formalization.Books.Homology.Unit06.Extension
      (CompPlus A) I₁ S.X₃ :=
    Formalization.Books.Homology.Unit06.pushoutExtension E₀ a
  let T : ShortComplex (CompPlus A) := E.toShortComplex
  have hT : T.ShortExact := E.shortExact
  let b₀ : S.X₂ ⟶ T.X₂ := pushout.inr a E₀.inclusion
  have hb₀ : a ≫ T.f = S.f ≫ b₀ := by
    dsimp [T, E, b₀]
    exact pushout.condition
  have hb₀g : b₀ ≫ T.g = S.g := by
    change pushout.inr a E₀.inclusion ≫
      pushout.desc 0 E₀.projection _ = S.g
    rw [pushout.inr_desc]
    rfl
  let ι : CompPlus A ⥤ BookComplex A := CochainComplex.Plus.ι A
  let T' : ShortComplex (BookComplex A) := T.map ι
  let _ : (CochainComplex.plus A).ContainsZero :=
    Formalization.Books.Derived.Unit12.cochainPlus_containsZero A
  let _ : ObjectProperty.IsClosedUnderKernels (CochainComplex.plus A) :=
    Formalization.Books.Derived.Unit12.cochainPlus_isClosedUnderKernels A
  let _ : ObjectProperty.IsClosedUnderCokernels (CochainComplex.plus A) :=
    Formalization.Books.Derived.Unit12.cochainPlus_isClosedUnderCokernels A
  let _ : PreservesFiniteLimits ι := by
    apply (Functor.preservesFiniteLimits_tfae ι).out 2 3 |>.mp
    intro X Y f
    exact (CochainComplex.plus A).preservesKernels_ι f
  let _ : PreservesFiniteColimits ι := by
    apply (Functor.preservesFiniteColimits_tfae ι).out 2 3 |>.mp
    intro X Y f
    exact (CochainComplex.plus A).preservesCokernels_ι f
  have hT' : T'.ShortExact := by
    exact hT.map_of_exact ι
  have hsplit (n : ℤ) : (T'.map (HomologicalComplex.eval A
      (ComplexShape.up ℤ) n)).Splitting := by
    let _ : Injective (T'.map (HomologicalComplex.eval A
        (ComplexShape.up ℤ) n)).X₁ := by
      change Injective (I₁.obj.X n)
      exact R₁.termwiseInjective n
    exact (hT'.map_of_exact (HomologicalComplex.eval A
      (ComplexShape.up ℤ) n)).splittingOfInjective
  let Ssplit :
      Formalization.Books.Derived.Unit09.TermwiseSplitExactSequence
        I₁.obj T.X₂.obj S.X₃.obj := {
    f := T.f.hom
    g := T.g.hom
    zero := by
      change T.f.hom ≫ T.g.hom = 0
      exact congrArg (fun h => h.hom) T.zero
    splitting := hsplit }
  let δ : S.X₃.obj ⟶
      (CategoryTheory.shiftFunctor (BookComplex A) (1 : ℤ)).obj I₁.obj :=
    Formalization.Books.Derived.Unit09.termwiseSplitConnectingMap Ssplit
  obtain ⟨n₃, hn₃⟩ := S.X₃.2
  obtain ⟨R₃, hR₃below, hR₃mono⟩ :=
    complex_injective_resolution_exists_with_mono S.X₃.obj n₃ hn₃
  let I₃ : CompPlus A := ⟨R₃.target, R₃.boundedBelow⟩
  let c : S.X₃ ⟶ I₃ := ObjectProperty.homMk R₃.map
  have hshift : IsBoundedBelow
      ((CategoryTheory.shiftFunctor (BookComplex A) (1 : ℤ)).obj I₁.obj) := by
    obtain ⟨n₁, hn₁⟩ := R₁.boundedBelow
    let _ : I₁.obj.IsStrictlyGE n₁ := hn₁
    exact ⟨n₁ - 1, I₁.obj.isStrictlyGE_shift n₁ 1 (n₁ - 1) (by omega)⟩
  have hshiftinj : ∀ n : ℤ, Injective
      (((CategoryTheory.shiftFunctor (BookComplex A) (1 : ℤ)).obj I₁.obj).X n) := by
    intro n
    exact Injective.of_iso (I₁.obj.shiftFunctorObjXIso 1 n (n + 1) rfl)
      (R₁.termwiseInjective (n + 1))
  obtain ⟨δ', hδ'⟩ := injective_resolution_lift_of_degreewise_mono
    c.hom δ R₃.quasiIso hshift hshiftinj hR₃mono
  let B : BookComplex A := CochainComplex.mappingCocone δ'
  obtain ⟨n₁, hn₁⟩ := R₁.boundedBelow
  let _ : I₁.obj.IsStrictlyGE n₁ := hn₁
  let _ : I₃.obj.IsStrictlyGE n₃ := hR₃below
  let _ : CochainComplex.IsStrictlyGE
      ((CategoryTheory.shiftFunctor (BookComplex A) (1 : ℤ)).obj I₁.obj)
      (n₁ - 1) := by
    exact I₁.obj.isStrictlyGE_shift n₁ 1 (n₁ - 1) (by omega)
  have hBbelow : B.IsStrictlyGE (min (n₃ - 1) (n₁ - 1) + 1) := by
    dsimp [B, CochainComplex.mappingCocone]
    let _ : (CochainComplex.mappingCone δ').IsStrictlyGE
        (min (n₃ - 1) (n₁ - 1)) :=
      CochainComplex.isStrictlyGE_mappingCone δ' n₃ (n₁ - 1) _ (by omega) (by omega)
    exact (CochainComplex.mappingCone δ').isStrictlyGE_shift
      (min (n₃ - 1) (n₁ - 1)) (-1)
      (min (n₃ - 1) (n₁ - 1) + 1) (by omega)
  have hBinj : ∀ n : ℤ, Injective (B.X n) := by
    intro n
    let _ : Injective (I₃.obj.X n) := R₃.termwiseInjective n
    let _ : Injective
        (((CategoryTheory.shiftFunctor (BookComplex A) (1 : ℤ)).obj I₁.obj).X (n - 1)) :=
      hshiftinj (n - 1)
    have hsum : Injective
        (I₃.obj.X n ⊞
          ((CategoryTheory.shiftFunctor (BookComplex A) (1 : ℤ)).obj I₁.obj).X (n - 1)) := by
      infer_instance
    have hcone : Injective ((CochainComplex.mappingCone δ').X (n - 1)) := by
      apply Injective.of_iso
        (HomologicalComplex.homotopyCofiber.XIsoBiprod δ' (n - 1) n (by simp)).symm
      exact hsum
    apply Injective.of_iso
      (CochainComplex.shiftFunctorObjXIso (CochainComplex.mappingCone δ')
        (-1) n (n - 1) (by omega)).symm
    exact hcone
  let I₂ : CompPlus A :=
    ⟨B, ⟨min (n₃ - 1) (n₁ - 1) + 1, hBbelow⟩⟩
  let u₀ : I₁.obj ⟶ B :=
    CochainComplex.HomComplex.Cocycle.homOf
      ((CochainComplex.mappingCocone.inr δ').leftUnshift 0 (by omega))
  let v₀ : B ⟶ I₃.obj := CochainComplex.mappingCocone.fst δ'
  let u : I₁ ⟶ I₂ := ObjectProperty.homMk u₀
  let v : I₂ ⟶ I₃ := ObjectProperty.homMk v₀
  have huv₀ : u₀ ≫ v₀ = 0 := by
    ext n
    dsimp [u₀, v₀, B]
    change ((CochainComplex.mappingCocone.inr δ').1.leftUnshift 0 (by omega)).v n n
        (by omega) ≫
      (CochainComplex.mappingCocone.fst δ').f n = 0
    rw [CochainComplex.HomComplex.Cochain.leftUnshift_v
      (CochainComplex.mappingCocone.inr δ').1 0 (by omega) n n (by omega)
      (n - 1) (by omega)]
    simp
  have huv : u ≫ v = 0 := by
    apply ObjectProperty.hom_ext
    exact huv₀
  let r : ∀ n : ℤ, B.X n ⟶ I₁.obj.X n := fun n =>
    -((CochainComplex.mappingCocone.snd δ').rightUnshift 0 (by omega)).v n n (by omega)
  let s : ∀ n : ℤ, I₃.obj.X n ⟶ B.X n := fun n =>
    (CochainComplex.mappingCocone.inl δ').v n n (by omega)
  have hfr : ∀ n : ℤ, u₀.f n ≫ r n = 𝟙 _ := by
    intro n
    dsimp [u₀, r]
    change ((CochainComplex.mappingCocone.inr δ').1.leftUnshift 0 (by omega)).v n n
      (by omega) ≫
      (-((CochainComplex.mappingCocone.snd δ').rightUnshift 0 (by omega)).v n n
        (by omega)) = 𝟙 _
    rw [CochainComplex.HomComplex.Cochain.leftUnshift_v
      (CochainComplex.mappingCocone.inr δ').1 0 (by omega) n n (by omega)
      (n - 1) (by omega)]
    rw [CochainComplex.HomComplex.Cochain.rightUnshift_v
      (CochainComplex.mappingCocone.snd δ') 0 (by omega) n n (by omega)
      (n - 1) (by omega)]
    simp only [Linear.units_smul_comp, Linear.comp_units_smul,
      Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]
    have hzero :
        (CochainComplex.mappingCocone.inr δ').1.v (n - 1) n (by omega) ≫
            (CochainComplex.mappingCocone.snd δ').v n (n - 1) (by omega) = 𝟙 _ := by
      exact CochainComplex.mappingCocone.inr_v_snd_v δ' (n - 1) n (by omega)
    rw [← Category.assoc
      ((CochainComplex.mappingCocone.inr δ').1.v (n - 1) n (by omega))
      ((CochainComplex.mappingCocone.snd δ').v n (n - 1) (by omega))
      (I₁.obj.shiftFunctorObjXIso 1 (n - 1) n (by omega)).hom]
    rw [hzero]
    dsimp [CochainComplex.shiftFunctorObjXIso, CochainComplex.shiftFunctor]
    simp
  have hsg : ∀ n : ℤ, s n ≫ v₀.f n = 𝟙 _ := by
    intro n
    exact CochainComplex.mappingCocone.inl_v_fst_f δ' n
  have hid : ∀ n : ℤ, r n ≫ u₀.f n + v₀.f n ≫ s n = 𝟙 _ := by
    intro n
    dsimp [r, u₀, v₀, s, B]
    change
      (-((CochainComplex.mappingCocone.snd δ').rightUnshift 0 (by omega)).v n n
          (by omega)) ≫
          ((CochainComplex.mappingCocone.inr δ').1.leftUnshift 0 (by omega)).v n n
            (by omega) +
        (CochainComplex.mappingCocone.fst δ').f n ≫
          (CochainComplex.mappingCocone.inl δ').v n n (by omega) = 𝟙 _
    rw [CochainComplex.HomComplex.Cochain.rightUnshift_v
      (CochainComplex.mappingCocone.snd δ') 0 (by omega) n n (by omega)
      (n - 1) (by omega)]
    rw [CochainComplex.HomComplex.Cochain.leftUnshift_v
      (CochainComplex.mappingCocone.inr δ').1 0 (by omega) n n (by omega)
      (n - 1) (by omega)]
    simp only [Linear.units_smul_comp, Linear.comp_units_smul,
      Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]
    have hsign : (1 * 1 + 1 * (1 - 1) / 2 : ℤ).negOnePow = -1 := by
      norm_num [Int.negOnePow_def]
    rw [hsign]
    simp only [Linear.units_smul_comp, Linear.comp_units_smul,
      Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc,
      Iso.hom_inv_id_assoc]
    simp
    rw [add_comm]
    exact CochainComplex.mappingCocone.id_X δ' n (n - 1) (by omega)
  let S₂ :
      Formalization.Books.Derived.Unit09.TermwiseSplitExactSequence
        I₁.obj B I₃.obj := {
    f := u₀
    g := v₀
    zero := huv₀
    splitting := fun n => {
      r := r n
      s := s n
      f_r := hfr n
      s_g := hsg n
      id := hid n } }
  have hS₂ : (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex S₂).ShortExact :=
    termwiseSplitShortComplex_shortExact A S₂
  let rT : ∀ n : ℤ, T.X₂.obj.X n ⟶ I₁.obj.X n := fun n =>
    (Ssplit.splitting n).r
  let β : CochainComplex.HomComplex.Cochain T.X₂.obj
      ((CategoryTheory.shiftFunctor (BookComplex A) (1 : ℤ)).obj I₁.obj) (-1) :=
    (-(CochainComplex.HomComplex.Cochain.ofHoms rT)).rightShift 1 (-1) (by omega)
  let αT : T.X₂.obj ⟶ I₃.obj := Ssplit.g ≫ c.hom
  have hαδ : αT ≫ δ' = Ssplit.g ≫ δ := by
    dsimp [αT]
    rw [Category.assoc, hδ']
  have hconnect (p : ℤ) :
      (Ssplit.g ≫ δ).f p =
        T.X₂.obj.d p (p + 1) ≫ rT (p + 1) -
          rT p ≫ I₁.obj.d p (p + 1) := by
    rw [HomologicalComplex.comp_f]
    rw [Formalization.Books.Derived.Unit09.termwiseSplitConnectingMap_f
      Ssplit p]
    dsimp [Formalization.Books.Derived.Unit09.termwiseSplitConnectingFamily,
      Formalization.Books.Derived.Unit09.termwiseSplitSection,
      Formalization.Books.Derived.Unit09.termwiseSplitProjection]
    let fS : ∀ i : ℤ, (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex Ssplit).X₁.X i ⟶
        (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex Ssplit).X₂.X i := fun i =>
      Ssplit.f.f i
    let gS : ∀ i : ℤ, (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex Ssplit).X₂.X i ⟶
        (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex Ssplit).X₃.X i := fun i =>
      Ssplit.g.f i
    let rS : ∀ i : ℤ, (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex Ssplit).X₂.X i ⟶
        (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex Ssplit).X₁.X i := fun i => by
      exact (Ssplit.splitting i).r
    let sS : ∀ i : ℤ, (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex Ssplit).X₃.X i ⟶
        (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex Ssplit).X₂.X i := fun i => by
      exact (Ssplit.splitting i).s
    let dB : ∀ i : ℤ, (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex Ssplit).X₂.X i ⟶
        (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex Ssplit).X₂.X (i + 1) := fun i =>
      (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex Ssplit).X₂.d i (i + 1)
    have hgs : gS p ≫ sS p =
        𝟙 _ - rS p ≫ fS p := by
      dsimp [fS, gS, rT, rS, sS]
      exact (Ssplit.splitting p).g_s
    have hfr : fS (p + 1) ≫ rS (p + 1) = 𝟙 _ := by
      dsimp [fS, rS]
      exact (Ssplit.splitting (p + 1)).f_r
    have hfS : fS p ≫ dB p =
        (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex Ssplit).X₁.d p (p + 1) ≫
          fS (p + 1) := by
      dsimp [fS]
      exact Ssplit.f.comm p (p + 1)
    change gS p ≫ sS p ≫ dB p ≫ rS (p + 1) =
      dB p ≫ rS (p + 1) - rS p ≫
        (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex Ssplit).X₁.d p (p + 1)
    rw [← Category.assoc, hgs]
    simp only [Preadditive.sub_comp, Preadditive.comp_sub,
      Category.assoc, Category.id_comp]
    have hcomp : rS p ≫ fS p ≫ dB p ≫ rS (p + 1) =
        rS p ≫
            (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex Ssplit).X₁.d
              p (p + 1) ≫ fS (p + 1) ≫ rS (p + 1) := by
      simpa only [Category.assoc] using congrArg
        (fun z => rS p ≫ z ≫ rS (p + 1)) hfS
    rw [hcomp, hfr]
    simp
  have hαβ : CochainComplex.HomComplex.δ (-1) 0 β +
      CochainComplex.HomComplex.Cochain.ofHom (αT ≫ δ') = 0 := by
    rw [hαδ]
    ext p q hpq
    dsimp [β]
    rw [CochainComplex.HomComplex.Cochain.δ_rightShift
      (-(CochainComplex.HomComplex.Cochain.ofHoms rT))
      1 (-1) 0 (by norm_num) 1 (by norm_num)]
    rw [CochainComplex.HomComplex.Cochain.units_smul_v]
    rw [CochainComplex.HomComplex.Cochain.rightShift_v
      (CochainComplex.HomComplex.δ 0 1
        (-CochainComplex.HomComplex.Cochain.ofHoms rT))
      1 0 (by norm_num) p p (by omega) (p + 1) (by omega)]
    simp only [CochainComplex.HomComplex.δ_zero_cochain_v,
      CochainComplex.HomComplex.Cochain.neg_v,
      CochainComplex.HomComplex.Cochain.ofHoms_v,
      CochainComplex.HomComplex.Cochain.ofHom_v]
    simp only [CochainComplex.shiftFunctor_obj_X,
      CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]
    simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      Category.comp_id, Category.id_comp]
    rw [show (1 : ℤ).negOnePow = -1 by
      rw [Int.negOnePow_one]]
    simp only [Units.neg_smul, one_smul, Preadditive.neg_comp,
      Preadditive.comp_neg, Preadditive.sub_comp, Category.assoc]
    rw [hconnect p]
    change
      -((-rT p ≫ I₁.obj.d p (p + 1)) -
        (-(T.X₂.obj.d p (p + 1) ≫ rT (p + 1)))) ≫ 𝟙 _ +
        (T.X₂.obj.d p (p + 1) ≫ rT (p + 1) -
          rT p ≫ I₁.obj.d p (p + 1)) = 0
    simp only [Category.comp_id, Category.id_comp, Units.neg_smul,
      one_smul, Preadditive.neg_comp, Preadditive.comp_neg,
      Preadditive.sub_comp, Preadditive.comp_sub]
    abel
  let bT₀ : T.X₂.obj ⟶ B := CochainComplex.mappingCocone.lift δ' αT β hαβ
  let bT : T.X₂ ⟶ I₂ := ObjectProperty.homMk bT₀
  have hTfb : Ssplit.f ≫ bT₀ = u₀ := by
    ext n
    rw [HomologicalComplex.comp_f]
    rw [← Category.comp_id (bT₀.f n)]
    rw [← CochainComplex.mappingCocone.id_X δ' n (n - 1) (by omega)]
    simp only [Category.assoc, Preadditive.comp_add]
    dsimp [bT₀]
    simp only [CochainComplex.mappingCocone.lift_f_fst_f_assoc]
    have hlift := CochainComplex.mappingCocone.lift_f_snd_v δ' αT β hαβ
      n (n - 1) (by omega)
    have hsecond :
        Ssplit.f.f n ≫
            (CochainComplex.mappingCocone.lift δ' αT β hαβ).f n ≫
            (CochainComplex.mappingCocone.snd δ').v n (n - 1) (by omega) ≫
            (CochainComplex.mappingCocone.inr δ').1.v (n - 1) n (by omega) =
          Ssplit.f.f n ≫ β.v n (n - 1) (by omega) ≫
            (CochainComplex.mappingCocone.inr δ').1.v (n - 1) n (by omega) := by
      simpa only [Category.assoc] using
        congrArg (fun z => Ssplit.f.f n ≫ z ≫
          (CochainComplex.mappingCocone.inr δ').1.v (n - 1) n (by omega)) hlift
    calc
      Ssplit.f.f n ≫ αT.f n ≫
            (CochainComplex.mappingCocone.inl δ').v n n (by omega) +
          Ssplit.f.f n ≫
            (CochainComplex.mappingCocone.lift δ' αT β hαβ).f n ≫
              (CochainComplex.mappingCocone.snd δ').v n (n - 1) (by omega) ≫
                (CochainComplex.mappingCocone.inr δ').1.v (n - 1) n (by omega) =
        Ssplit.f.f n ≫ αT.f n ≫
            (CochainComplex.mappingCocone.inl δ').v n n (by omega) +
          Ssplit.f.f n ≫ β.v n (n - 1) (by omega) ≫
            (CochainComplex.mappingCocone.inr δ').1.v (n - 1) n (by omega) := by
          congr 1
      _ = u₀.f n := by
        dsimp [αT, β]
        have hzero : Ssplit.f.f n ≫ Ssplit.g.f n = 0 := by
          exact congrArg (fun z => z.f n) Ssplit.zero
        have hbeta :
            ((-(CochainComplex.HomComplex.Cochain.ofHoms rT)).rightShift
                1 (-1) (by omega)).v n (n - 1) (by omega) ≫
              (CochainComplex.mappingCocone.inr δ').1.v (n - 1) n (by omega) =
            rT n ≫ u₀.f n := by
          rw [CochainComplex.HomComplex.Cochain.rightShift_v
            (-(CochainComplex.HomComplex.Cochain.ofHoms rT))
            1 (-1) (by omega) n (n - 1) (by omega) n (by omega)]
          simp only [CochainComplex.HomComplex.Cochain.neg_v,
            CochainComplex.HomComplex.Cochain.ofHoms_v]
          dsimp [u₀]
          change
            ((-rT n) ≫
                (I₁.obj.shiftFunctorObjXIso 1 (n - 1) n (by omega)).inv) ≫
              (CochainComplex.mappingCocone.inr δ').1.v (n - 1) n (by omega) =
            rT n ≫
              ((CochainComplex.mappingCocone.inr δ').1.leftUnshift 0
                (by omega)).v n n (by omega)
          rw [CochainComplex.HomComplex.Cochain.leftUnshift_v
            (CochainComplex.mappingCocone.inr δ').1 0 (by omega)
            n n (by omega) (n - 1) (by omega)]
          simp only [Linear.units_smul_comp, Linear.comp_units_smul,
            Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]
          have hsign : (1 * 1 + 1 * (1 - 1) / 2 : ℤ).negOnePow = -1 := by
            norm_num [Int.negOnePow_def]
          rw [hsign]
          simp
        have hfirst :
            Ssplit.f.f n ≫ Ssplit.g.f n ≫ c.hom.f n ≫
                (CochainComplex.mappingCocone.inl δ').v n n (by omega) = 0 := by
          simpa only [Category.assoc, zero_comp] using
            congrArg (fun z => z ≫ c.hom.f n ≫
              (CochainComplex.mappingCocone.inl δ').v n n (by omega)) hzero
        have hsecond0 :
            Ssplit.f.f n ≫
                ((-(CochainComplex.HomComplex.Cochain.ofHoms rT)).rightShift
                  1 (-1) (by omega)).v n (n - 1) (by omega) ≫
              (CochainComplex.mappingCocone.inr δ').1.v (n - 1) n (by omega) =
            Ssplit.f.f n ≫ rT n ≫ u₀.f n := by
          simpa only [Category.assoc] using
            congrArg (fun z => Ssplit.f.f n ≫ z) hbeta
        have hfinal :
            Ssplit.f.f n ≫ Ssplit.g.f n ≫ c.hom.f n ≫
                (CochainComplex.mappingCocone.inl δ').v n n (by omega) +
              Ssplit.f.f n ≫
                ((-(CochainComplex.HomComplex.Cochain.ofHoms rT)).rightShift
                  1 (-1) (by omega)).v n (n - 1) (by omega) ≫
                (CochainComplex.mappingCocone.inr δ').1.v (n - 1) n (by omega) =
            u₀.f n := by
          rw [hfirst, hsecond0]
          simp only [zero_add]
          have hfrT : Ssplit.f.f n ≫ rT n = 𝟙 _ := by
            dsimp [rT]
            exact (Ssplit.splitting n).f_r
          rw [← Category.assoc (Ssplit.f.f n) (rT n) (u₀.f n), hfrT]
          simp
        convert hfinal using 1 <;> simp only [Category.assoc] <;> rfl
  sorry

theorem injective_resolution_short_exact_with_left
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (S : ShortComplex (CompPlus A)) (hS : S.ShortExact)
    (I₁ : CompPlus A) (a : S.X₁ ⟶ I₁)
    (ha : IsComplexInjectiveResolution S.X₁.obj I₁.obj a.hom) :
    ∃ (I₂ I₃ : CompPlus A)
      (b : S.X₂ ⟶ I₂) (c : S.X₃ ⟶ I₃),
      InjectiveResolutionShortExactData S I₁ I₂ I₃ a b c := by
  sorry

theorem injective_resolution_short_exact_nonnegative
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (S : ShortComplex (CompPlus A)) (hS : S.ShortExact)
    (hS₀ : S.X₁.obj.IsStrictlyGE 0 ∧
      S.X₂.obj.IsStrictlyGE 0 ∧ S.X₃.obj.IsStrictlyGE 0) :
    ∃ (I₁ I₂ I₃ : CompPlus A)
      (a : S.X₁ ⟶ I₁) (b : S.X₂ ⟶ I₂) (c : S.X₃ ⟶ I₃),
      InjectiveResolutionShortExactData S I₁ I₂ I₃ a b c ∧
        I₁.obj.IsStrictlyGE 0 ∧ I₂.obj.IsStrictlyGE 0 ∧ I₃.obj.IsStrictlyGE 0 := by
  sorry

theorem injective_resolution_short_exact_with_left_nonnegative
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (S : ShortComplex (CompPlus A)) (hS : S.ShortExact)
    (I₁ : CompPlus A) (a : S.X₁ ⟶ I₁)
    (ha : IsComplexInjectiveResolution S.X₁.obj I₁.obj a.hom)
    (hS₀ : S.X₁.obj.IsStrictlyGE 0 ∧
      S.X₂.obj.IsStrictlyGE 0 ∧ S.X₃.obj.IsStrictlyGE 0)
    (hI₁₀ : I₁.obj.IsStrictlyGE 0) :
    ∃ (I₂ I₃ : CompPlus A)
      (b : S.X₂ ⟶ I₂) (c : S.X₃ ⟶ I₃),
      InjectiveResolutionShortExactData S I₁ I₂ I₃ a b c ∧
        I₂.obj.IsStrictlyGE 0 ∧ I₃.obj.IsStrictlyGE 0 := by
  sorry

/- The source's item (4) is literally the placeholder `add more here`; it
  does not specify a mathematical assertion and therefore has no Lean field. -/

end Formalization.Books.Derived.Unit18
