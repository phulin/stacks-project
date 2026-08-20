import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Formalization.Books.Derived.Unit04.ElementaryResults
import Formalization.Books.Derived.Unit11.DerivedCategories

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
  letI : HasDerivedCategory A := HasDerivedCategory.standard A
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
  letI : HasDerivedCategory A := HasDerivedCategory.standard A
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
  sorry

/- The image/intersection identity used in the degreewise-monomorphism part
  of the lifting lemma is recorded with Mathlib's canonical subobject images. -/
theorem quasiIso_degreewise_mono_image_intersection
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L : BookComplex A} (α : K ⟶ L) (n : ℤ)
    (hα : QuasiIso α) (hmono : ∀ n : ℤ, Mono (α.f n)) :
    imageSubobject (K.d (n - 1) n ≫ α.f n) =
      imageSubobject (α.f n) ⊓ imageSubobject (L.d (n - 1) n) := by
  sorry

/-! ## Lifting and uniqueness -/

theorem injective_resolution_lift_up_to_homotopy
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L I : BookComplex A} (α : K ⟶ L) (γ : K ⟶ I)
    (hα : QuasiIso α) (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n)) :
    ∃ β : L ⟶ I, Nonempty (Homotopy (α ≫ β) γ) := by
  sorry

theorem injective_resolution_lift_of_degreewise_mono
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L I : BookComplex A} (α : K ⟶ L) (γ : K ⟶ I)
    (hα : QuasiIso α) (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n))
    (hmono : ∀ n : ℤ, Mono (α.f n)) :
    ∃ β : L ⟶ I, α ≫ β = γ := by
  sorry

theorem injective_resolution_lift_unique_up_to_homotopy
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L I : BookComplex A} (α : K ⟶ L) (γ : K ⟶ I)
    (hα : QuasiIso α) (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n))
    (β₁ β₂ : L ⟶ I)
    (hβ₁ : Nonempty (Homotopy (α ≫ β₁) γ))
    (hβ₂ : Nonempty (Homotopy (α ≫ β₂) γ)) :
    Nonempty (Homotopy β₁ β₂) := by
  sorry

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

theorem injective_resolution_short_exact
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (S : ShortComplex (CompPlus A)) (hS : S.ShortExact) :
    ∃ (I₁ I₂ I₃ : CompPlus A)
      (a : S.X₁ ⟶ I₁) (b : S.X₂ ⟶ I₂) (c : S.X₃ ⟶ I₃),
      InjectiveResolutionShortExactData S I₁ I₂ I₃ a b c := by
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
