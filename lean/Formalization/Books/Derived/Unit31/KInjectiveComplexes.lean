import Formalization.Books.Derived.Unit10.DistinguishedTriangles
import Formalization.Books.Derived.Unit14.DerivedFunctors
import Formalization.Books.Derived.Unit18.InjectiveResolutions
import Formalization.Books.Homology.Unit31.InverseSystems
import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-!
# Derived Categories, Chapter 31: K-injective complexes

The canonical K-injective predicate is Mathlib's
`CochainComplex.IsKInjective`.  This file records the source's
characterizations, closure properties, product and inverse-limit results, and
the right-derived-functor interfaces built from K-injective complexes.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit14
open Formalization.Books.Derived.Unit18
open Formalization.Books.Homology.Unit31
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u v' u'

namespace Formalization.Books.Derived.Unit31

/-! ## The definition and the Hom comparison -/

/- Mathlib's `CochainComplex.IsKInjective` is the canonical definition: maps
   from acyclic complexes are homotopic to zero.  The following theorem gives
   the source's equivalent homotopy-category formulation. -/
theorem isKInjective_iff_homotopy_hom_zero
    {A : Type u} [Category.{v} A] [Abelian A]
    (I : BookComplex A) :
    I.IsKInjective ↔
      ∀ (M : BookComplex A), M.Acyclic →
        ∀ f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M ⟶
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I,
          f = 0 := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal]
  refine ⟨fun hI M hM f ↦ ?_, fun hI ↦ ?_⟩
  · apply hI f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
    exact hM
  · intro K f hK
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    exact hI K hK ((HomotopyCategory.quotient _ _).map f)

/- The source's shift observation is recorded for every integer shift. -/
theorem isKInjective_homotopy_hom_zero_of_shift
    {A : Type u} [Category.{v} A] [Abelian A]
    {I M : BookComplex A} (hI : I.IsKInjective) (hM : M.Acyclic) (n : ℤ) :
    ∀ f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (M⟦n⟧) ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I,
      f = 0 := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal] at hI
  intro f
  apply hI f
  apply ObjectProperty.prop_of_iso _
    (((HomotopyCategory.quotient A (.up ℤ)).commShiftIso n).symm.app M)
  apply (HomotopyCategory.subcategoryAcyclic A).le_shift n _
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact hM

/- The three criteria in the source are recorded as adjacent equivalences.
   Criterion (2) uses precomposition by a quasi-isomorphism, and criterion
   (3) uses the canonical localization functor `DerivedCategory.Qh`. -/
theorem isKInjective_iff_quasiIso_precomposition_bijective_iff_derived_hom_bijective
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (I : BookComplex A) :
    (I.IsKInjective ↔
        ∀ {M N : BookComplex A} (s : M ⟶ N), QuasiIso s →
          Function.Bijective
            (fun (f :
                (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N ⟶
                  (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) =>
              (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s ≫ f)) ∧
      ((∀ {M N : BookComplex A} (s : M ⟶ N), QuasiIso s →
          Function.Bijective
            (fun (f :
                (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N ⟶
                  (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) =>
              (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s ≫ f)) ↔
        ∀ (N : BookComplex A),
          Function.Bijective
            ((DerivedCategory.Qh (C := A)).map :
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N ⟶
                (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) →
                ((DerivedCategory.Qh (C := A)).obj
                    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N) ⟶
                  (DerivedCategory.Qh (C := A)).obj
                    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))) := by
  have hQmap_of_isKInjective :
      I.IsKInjective →
        ∀ {M N : BookComplex A} (s : M ⟶ N), QuasiIso s →
          Function.Bijective
            (fun (f :
                (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N ⟶
                  (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) =>
              (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s ≫ f) := by
    intro hI M N s hs
    have : I.IsKInjective := hI
    have hs' : HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s) := by
      rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
      exact hs
    have : IsIso ((DerivedCategory.Qh (C := A)).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s)) :=
      Localization.inverts _ _ _ hs'
    let hM := CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M) I
    let hN := CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N) I
    constructor
    · intro f₁ f₂ hf
      apply hN.1
      apply (cancel_epi ((DerivedCategory.Qh (C := A)).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s))).1
      simpa only [Functor.map_comp] using
        congrArg (fun f => (DerivedCategory.Qh (C := A)).map f) hf
    · intro g
      obtain ⟨f, hf⟩ := hN.2
        (inv ((DerivedCategory.Qh (C := A)).map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s)) ≫
          (DerivedCategory.Qh (C := A)).map g)
      refine ⟨f, hM.1 ?_⟩
      rw [Functor.map_comp, hf]
      simp
  have isKInjective_of_hQmap :
      (∀ (N : BookComplex A),
          Function.Bijective
            ((DerivedCategory.Qh (C := A)).map :
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N ⟶
                (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) →
                ((DerivedCategory.Qh (C := A)).obj
                    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N) ⟶
                  (DerivedCategory.Qh (C := A)).obj
                    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))) →
        I.IsKInjective := by
    intro hQ
    refine ⟨fun {M} f hM => ?_⟩
    have hzero : IsZero
        ((DerivedCategory.Qh (C := A)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (0 : BookComplex A))) :=
      Functor.map_isZero _ (Functor.map_isZero _ (isZero_zero _))
    have hq : QuasiIso (0 : M ⟶ (0 : BookComplex A)) := by
      rw [quasiIso_iff]
      intro n
      rw [quasiIsoAt_iff_exactAt _ _ (hM n)]
      exact HomologicalComplex.ExactAt.of_isZero
        (Functor.map_isZero (HomologicalComplex.eval A (ComplexShape.up ℤ) n)
          (isZero_zero _))
    have hq' : HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (0 : M ⟶ (0 : BookComplex A))) := by
      rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
      exact hq
    have : IsIso ((DerivedCategory.Qh (C := A)).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (0 : M ⟶ (0 : BookComplex A)))) :=
      Localization.inverts _ _ _ hq'
    have hzeroM : IsZero
        ((DerivedCategory.Qh (C := A)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M)) :=
      IsZero.of_iso hzero (asIso ((DerivedCategory.Qh (C := A)).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (0 : M ⟶ (0 : BookComplex A)))))
    have hf : (DerivedCategory.Qh (C := A)).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f) = 0 :=
      hzeroM.eq_of_src _ _
    exact ⟨HomotopyCategory.homotopyOfEq _ _
      ((hQ M).1 (by simpa using hf))⟩
  have isKInjective_of_precomposition :
      (∀ {M N : BookComplex A} (s : M ⟶ N), QuasiIso s →
          Function.Bijective
            (fun (f :
                (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N ⟶
                  (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) =>
              (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s ≫ f)) →
        I.IsKInjective := by
    intro h
    refine ⟨fun {M} f hM => ?_⟩
    have hq : QuasiIso (0 : M ⟶ (0 : BookComplex A)) := by
      rw [quasiIso_iff]
      intro n
      rw [quasiIsoAt_iff_exactAt _ _ (hM n)]
      exact HomologicalComplex.ExactAt.of_isZero
        (Functor.map_isZero (HomologicalComplex.eval A (ComplexShape.up ℤ) n)
          (isZero_zero _))
    obtain ⟨g, hg⟩ := (h (0 : M ⟶ (0 : BookComplex A)) hq).2
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)
    have hg0 : g = 0 := by
      apply (Functor.map_isZero
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)) (isZero_zero _)).eq_of_src
    have hf0 :
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f = 0 := by
      rw [← hg, hg0]
      simp
    exact ⟨HomotopyCategory.homotopyOfEq _ _ hf0⟩
  refine ⟨?_, ?_⟩
  · exact ⟨hQmap_of_isKInjective, isKInjective_of_precomposition⟩
  · constructor
    · intro h
      have : I.IsKInjective := isKInjective_of_precomposition h
      intro N
      exact CochainComplex.IsKInjective.Qh_map_bijective
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N) I
    · exact fun h => hQmap_of_isKInjective (isKInjective_of_hQmap h)

/-! ## Distinguished triangles and bounded-below complexes -/

/- The source quantifies over the three objects in a distinguished triangle.
   Here the objects are represented by explicit complexes, so the three
   possible choices of the two K-injective objects are visible in the result. -/
theorem isKInjective_two_out_of_three_of_distinguished_triangle
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L M : BookComplex A}
    (f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)
    (g : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M)
    (h : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M ⟶
      (shiftFunctor (BookHomotopyCategory A) (1 : ℤ)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))
    (hT : Triangle.mk f g h ∈ distTriang (BookHomotopyCategory A)) :
    ((K.IsKInjective ∧ L.IsKInjective) → M.IsKInjective) ∧
        ((L.IsKInjective ∧ M.IsKInjective) → K.IsKInjective) ∧
        ((M.IsKInjective ∧ K.IsKInjective) → L.IsKInjective) := by
  let P := HomotopyCategory.subcategoryAcyclic A
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hK, hL⟩
    rw [CochainComplex.isKInjective_iff_rightOrthogonal] at hK hL ⊢
    exact P.rightOrthogonal.ext_of_isTriangulatedClosed₃
      (Triangle.mk f g h) hT hK hL
  · rintro ⟨hL, hM⟩
    rw [CochainComplex.isKInjective_iff_rightOrthogonal] at hL hM ⊢
    exact P.rightOrthogonal.ext_of_isTriangulatedClosed₁
      (Triangle.mk f g h) hT hL hM
  · rintro ⟨hM, hK⟩
    rw [CochainComplex.isKInjective_iff_rightOrthogonal] at hM hK ⊢
    exact P.rightOrthogonal.ext_of_isTriangulatedClosed₂
      (Triangle.mk f g h) hT hK hM

/- Mathlib's bounded-below injective-complex theorem is reused directly. -/
theorem isKInjective_of_bounded_below_injective
    {A : Type u} [Category.{v} A] [Abelian A]
    (I : BookComplex A) (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n)) :
    I.IsKInjective :=
  isKInjective_of_bounded_below_termwise_injective I hI hIinj

/-! ## Products of K-injective complexes -/

/- The termwise products in the source are represented by the canonical
   product of complexes; evaluation of this product is the corresponding
   product of terms. -/
noncomputable def productComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    {T : Type w} [HasProductsOfShape T A]
    (I : T → BookComplex A) : BookComplex A :=
  ∏ᶜ I

noncomputable def productComplexProjection
    {A : Type u} [Category.{v} A] [Abelian A]
    {T : Type w} [HasProductsOfShape T A]
    (I : T → BookComplex A) (t : T) : productComplex I ⟶ I t :=
  Pi.π I t

theorem productComplex_eval_isProduct
    {A : Type u} [Category.{v} A] [Abelian A]
    {T : Type w} [HasProductsOfShape T A]
    (I : T → BookComplex A) (n : ℤ) :
    Nonempty
      (IsLimit
        (Fan.mk ((productComplex I).X n)
          (fun t => (productComplexProjection I t).f n))) := by
  change Nonempty
    (IsLimit (Fan.mk ((∏ᶜ I).X n) (fun t => (Pi.π I t).f n)))
  exact ⟨by
    exact (Fan.isLimitMapConeEquiv
      (HomologicalComplex.eval A (ComplexShape.up ℤ) n) I
      (Fan.mk (∏ᶜ I) (Pi.π I))).1
      (isLimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) n)
        (productIsProduct I))⟩

/- The displayed complexes `C`, `C_t`, and the identity `C = ∏ C_t` in the
   source proof are the Hom-complex calculation underlying the following
   stronger interface; they are not separate objects needed by users. -/
noncomputable def productDerivedCone
    {A : Type u} [Category.{v} A] [Abelian A]
    {T : Type w} [HasProductsOfShape T A]
    [HasDerivedCategory.{w} A] (I : T → BookComplex A) :
    Fan (fun t : T =>
      (DerivedCategory.Qh (C := A)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (I t))) :=
  Fan.mk
    ((DerivedCategory.Qh (C := A)).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        (productComplex I)))
    (fun t =>
      (DerivedCategory.Qh (C := A)).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (productComplexProjection I t)))

theorem productComplex_isKInjective_and_represents_derived_product
    {A : Type u} [Category.{v} A] [Abelian A]
    {T : Type w} [HasProductsOfShape T A]
    [HasDerivedCategory.{w} A] (I : T → BookComplex A)
    (hI : ∀ t : T, (I t).IsKInjective) :
    (productComplex I).IsKInjective ∧
      Nonempty (IsLimit (productDerivedCone I)) := by
  classical
  have hKInjective : (productComplex I).IsKInjective := by
    refine ⟨fun {K} f hK => ?_⟩
    have hHt (t : T) : Nonempty (Homotopy (f ≫ productComplexProjection I t) 0) := by
      have : (I t).IsKInjective := hI t
      exact CochainComplex.IsKInjective.nonempty_homotopy_zero
        (f ≫ productComplexProjection I t) hK
    let Ht (t : T) : Homotopy (f ≫ productComplexProjection I t) 0 := (hHt t).some
    let H : Homotopy f 0 :=
      { hom := fun i j => (productComplex_eval_isProduct I j).some.lift
          (Fan.mk (K.X i) (fun t => (Ht t).hom i j))
        zero := by
          intro i j hij
          apply (productComplex_eval_isProduct I j).some.hom_ext
          intro t
          rw [(productComplex_eval_isProduct I j).some.fac]
          rw [zero_comp]
          change (Ht t.as).hom i j = 0
          exact (Ht t.as).zero i j hij
        comm := by
          intro i
          apply (productComplex_eval_isProduct I i).some.hom_ext
          intro t
          change f.f i ≫ (productComplexProjection I t.as).f i =
            (dNext i (fun i j => (productComplex_eval_isProduct I j).some.lift
                (Fan.mk (K.X i) (fun t => (Ht t).hom i j))) +
              prevD i (fun i j => (productComplex_eval_isProduct I j).some.lift
                (Fan.mk (K.X i) (fun t => (Ht t).hom i j))) +
              (0 : K ⟶ productComplex I).f i) ≫
                (productComplexProjection I t.as).f i
          rw [Preadditive.add_comp, Preadditive.add_comp,
            HomologicalComplex.zero_f, zero_comp,
            ← dNext_comp_right, ← prevD_comp_right]
          have hcomp :
              (fun i j => (productComplex_eval_isProduct I j).some.lift
                (Fan.mk (K.X i) (fun t => (Ht t).hom i j)) ≫
                  (productComplexProjection I t.as).f j) =
                (Ht t.as).hom := by
            funext i j
            change (Fan.IsLimit.lift (productComplex_eval_isProduct I j).some
                (fun t => (Ht t).hom i j)) ≫
              (Fan.mk ((productComplex I).X j)
                (fun t => (productComplexProjection I t).f j)).proj t.as =
                (Ht t.as).hom i j
            exact Fan.IsLimit.fac (productComplex_eval_isProduct I j).some
              (fun t => (Ht t).hom i j) t.as
          rw [hcomp]
          simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
            (Ht t.as).comm i }
    exact ⟨H⟩
  have hHomotopyProduct : Nonempty (IsLimit
      (Fan.mk
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (productComplex I))
        (fun t => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (productComplexProjection I t)))) := by
    let lift : ∀ s : Fan (fun t : T =>
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (I t)),
        s.pt ⟶ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (productComplex I) :=
      fun s =>
        let K := Classical.choose (HomotopyCategory.quotient_obj_surjective s.pt)
        let e : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K = s.pt :=
          Classical.choose_spec (HomotopyCategory.quotient_obj_surjective s.pt)
        let f : ∀ t : T, K ⟶ I t := fun t =>
          Classical.choose ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective
            (eqToHom e ≫ s.proj t))
        eqToHom e.symm ≫
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (Pi.lift f)
    refine ⟨Fan.IsLimit.mk _ lift ?_ ?_⟩
    · intro s t
      unfold productComplex productComplexProjection at ⊢
      dsimp [lift, productComplex, productComplexProjection]
      rw [Category.assoc, ← Functor.map_comp, Pi.lift_π]
      rw [Classical.choose_spec
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective
          (eqToHom (Classical.choose_spec
            (HomotopyCategory.quotient_obj_surjective s.pt)) ≫ s.proj t))]
      simp
    · intro s m hm
      let K := Classical.choose (HomotopyCategory.quotient_obj_surjective s.pt)
      let e : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K = s.pt :=
        Classical.choose_spec (HomotopyCategory.quotient_obj_surjective s.pt)
      let f : ∀ t : T, K ⟶ I t := fun t =>
        Classical.choose ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective
          (eqToHom e ≫ s.proj t))
      have hf (t : T) :
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (f t) =
            eqToHom e ≫ s.proj t :=
        Classical.choose_spec ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective
          (eqToHom e ≫ s.proj t))
      obtain ⟨m', hm'⟩ :=
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective
          (eqToHom e ≫ m)
      let pLift : K ⟶ productComplex I := Pi.lift f
      have hm_t (t : T) :
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
              (m' ≫ productComplexProjection I t -
                pLift ≫ productComplexProjection I t) = 0 := by
        have hproj :
            pLift ≫ productComplexProjection I t = f t := by
          simp [pLift, productComplexProjection, productComplex]
        simp only [Functor.map_sub, Functor.map_comp]
        rw [hm', Category.assoc]
        change eqToHom e ≫
            (m ≫
              (Fan.mk
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (productComplex I))
                (fun t => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                  (productComplexProjection I t))).proj t) -
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            (pLift ≫ productComplexProjection I t) = 0
        rw [hm t, hproj, hf t, sub_self]
      have hHt (t : T) :
          Nonempty (Homotopy (m' ≫ productComplexProjection I t)
            (pLift ≫ productComplexProjection I t)) := by
        obtain ⟨H⟩ :=
          (HomotopyCategory.quotient_map_eq_zero_iff _).mp (hm_t t)
        exact ⟨Homotopy.equivSubZero.symm H⟩
      let Ht (t : T) : Homotopy (m' ≫ productComplexProjection I t)
          (pLift ≫ productComplexProjection I t) := (hHt t).some
      let H : Homotopy m' pLift :=
        { hom := fun i j => (productComplex_eval_isProduct I j).some.lift
            (Fan.mk (K.X i) (fun t => (Ht t).hom i j))
          zero := by
            intro i j hij
            apply (productComplex_eval_isProduct I j).some.hom_ext
            intro t
            rw [(productComplex_eval_isProduct I j).some.fac]
            rw [zero_comp]
            change (Ht t.as).hom i j = 0
            exact (Ht t.as).zero i j hij
          comm := by
            intro i
            apply (productComplex_eval_isProduct I i).some.hom_ext
            intro t
            change m'.f i ≫ (productComplexProjection I t.as).f i =
              (dNext i (fun i j => (productComplex_eval_isProduct I j).some.lift
                (Fan.mk (K.X i) (fun t => (Ht t).hom i j))) +
              prevD i (fun i j => (productComplex_eval_isProduct I j).some.lift
                (Fan.mk (K.X i) (fun t => (Ht t).hom i j))) + pLift.f i) ≫
                (productComplexProjection I t.as).f i
            rw [Preadditive.add_comp, Preadditive.add_comp,
              ← dNext_comp_right, ← prevD_comp_right]
            have hcomp :
                (fun i j => (productComplex_eval_isProduct I j).some.lift
                  (Fan.mk (K.X i) (fun t => (Ht t).hom i j)) ≫
                    (productComplexProjection I t.as).f j) =
                  (Ht t.as).hom := by
              funext i j
              change (Fan.IsLimit.lift (productComplex_eval_isProduct I j).some
                  (fun t => (Ht t).hom i j)) ≫
                (Fan.mk ((productComplex I).X j)
                  (fun t => (productComplexProjection I t).f j)).proj t.as =
                  (Ht t.as).hom i j
              exact Fan.IsLimit.fac (productComplex_eval_isProduct I j).some
                (fun t => (Ht t).hom i j) t.as
            rw [hcomp]
            simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
              (Ht t.as).comm i }
      have hm_eq := HomotopyCategory.eq_of_homotopy m' pLift H
      change m = eqToHom e.symm ≫
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map pLift
      calc
        m = eqToHom e.symm ≫ (eqToHom e ≫ m) := by simp
        _ = eqToHom e.symm ≫
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map m' := by
          rw [← hm']
        _ = eqToHom e.symm ≫
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map pLift := by
          rw [hm_eq]
  refine ⟨hKInjective, ?_⟩
  refine ⟨Fan.IsLimit.mk (productDerivedCone I) ?_ ?_ ?_⟩
  · intro s
    let K := (DerivedCategory.Qh (C := A)).objPreimage s.pt
    let e := (DerivedCategory.Qh (C := A)).objObjPreimageIso s.pt
    let f : ∀ t : T, K ⟶
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (I t) := fun t =>
      letI : (I t).IsKInjective := hI t
      Classical.choose
        (((CochainComplex.IsKInjective.Qh_map_bijective K (I t) :
          Function.Bijective (DerivedCategory.Qh (C := A)).map)).2
          (e.hom ≫ s.proj t))
    have hf (t : T) :
        (DerivedCategory.Qh (C := A)).map (f t) = e.hom ≫ s.proj t := by
      let : (I t).IsKInjective := hI t
      exact Classical.choose_spec
        (((CochainComplex.IsKInjective.Qh_map_bijective K (I t) :
          Function.Bijective (DerivedCategory.Qh (C := A)).map)).2
          (e.hom ≫ s.proj t))
    let u := hHomotopyProduct.some.lift (Fan.mk K f)
    exact e.inv ≫ (DerivedCategory.Qh (C := A)).map u
  · intro s t
    let K := (DerivedCategory.Qh (C := A)).objPreimage s.pt
    let e := (DerivedCategory.Qh (C := A)).objObjPreimageIso s.pt
    let f : ∀ t : T, K ⟶
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (I t) := fun t =>
      letI : (I t).IsKInjective := hI t
      Classical.choose
        (((CochainComplex.IsKInjective.Qh_map_bijective K (I t) :
          Function.Bijective (DerivedCategory.Qh (C := A)).map)).2
          (e.hom ≫ s.proj t))
    have hf (t : T) :
        (DerivedCategory.Qh (C := A)).map (f t) = e.hom ≫ s.proj t := by
      let : (I t).IsKInjective := hI t
      exact Classical.choose_spec
        (((CochainComplex.IsKInjective.Qh_map_bijective K (I t) :
          Function.Bijective (DerivedCategory.Qh (C := A)).map)).2
          (e.hom ≫ s.proj t))
    let u := hHomotopyProduct.some.lift (Fan.mk K f)
    dsimp [productDerivedCone]
    rw [Category.assoc, ← Functor.map_comp]
    have hfac :
        hHomotopyProduct.some.lift (Fan.mk K f) ≫
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
              (productComplexProjection I t) = f t := by
      simpa only [Fan.proj, Fan.mk_π_app] using
        hHomotopyProduct.some.fac (Fan.mk K f) (Discrete.mk t)
    have hresult :
        e.inv ≫ (DerivedCategory.Qh (C := A)).map
            (hHomotopyProduct.some.lift (Fan.mk K f) ≫
              (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                (productComplexProjection I t)) = s.proj t := by
      rw [hfac, hf t]
      simp [e]
    simpa [K, f, u] using hresult
  · intro s m hm
    let K := (DerivedCategory.Qh (C := A)).objPreimage s.pt
    let e := (DerivedCategory.Qh (C := A)).objObjPreimageIso s.pt
    unfold productDerivedCone at m hm ⊢
    let : (productComplex I).IsKInjective := hKInjective
    let f : ∀ t : T, K ⟶
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (I t) := fun t =>
      letI : (I t).IsKInjective := hI t
      Classical.choose
        (((CochainComplex.IsKInjective.Qh_map_bijective K (I t) :
          Function.Bijective (DerivedCategory.Qh (C := A)).map)).2
          (e.hom ≫ s.proj t))
    have hf (t : T) :
        (DerivedCategory.Qh (C := A)).map (f t) = e.hom ≫ s.proj t := by
      let : (I t).IsKInjective := hI t
      exact Classical.choose_spec
        (((CochainComplex.IsKInjective.Qh_map_bijective K (I t) :
          Function.Bijective (DerivedCategory.Qh (C := A)).map)).2
          (e.hom ≫ s.proj t))
    let u := hHomotopyProduct.some.lift (Fan.mk K f)
    have hvu :
        (Classical.choose
          (((CochainComplex.IsKInjective.Qh_map_bijective K (productComplex I) :
            Function.Bijective (DerivedCategory.Qh (C := A)).map)).2
            (e.hom ≫ m))) = u := by
      apply Fan.IsLimit.hom_ext hHomotopyProduct.some
      intro t
      apply (CochainComplex.IsKInjective.Qh_map_bijective K (I t)).1
      let v := Classical.choose
        (((CochainComplex.IsKInjective.Qh_map_bijective K (productComplex I) :
          Function.Bijective (DerivedCategory.Qh (C := A)).map)).2
          (e.hom ≫ m))
      have hv :
          (DerivedCategory.Qh (C := A)).map v = e.hom ≫ m :=
        Classical.choose_spec
          (((CochainComplex.IsKInjective.Qh_map_bijective K (productComplex I) :
            Function.Bijective (DerivedCategory.Qh (C := A)).map)).2
            (e.hom ≫ m))
      have hleft :
          (DerivedCategory.Qh (C := A)).map
              (v ≫
                (Fan.mk
                  ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
                    (productComplex I))
                  (fun t => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                    (productComplexProjection I t))).proj t) =
            e.hom ≫ s.proj t := by
        rw [Functor.map_comp, hv, Category.assoc]
        change e.hom ≫
            (m ≫
              (Fan.mk
                ((DerivedCategory.Qh (C := A)).obj
                  ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
                    (productComplex I)))
                (fun t => (DerivedCategory.Qh (C := A)).map
                  ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                    (productComplexProjection I t)))).proj t) =
          e.hom ≫ s.proj t
        rw [hm t]
      have hright :
          (DerivedCategory.Qh (C := A)).map
              (u ≫
                (Fan.mk
                  ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
                    (productComplex I))
                  (fun t => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                    (productComplexProjection I t))).proj t) =
            e.hom ≫ s.proj t := by
        change (DerivedCategory.Qh (C := A)).map
            (hHomotopyProduct.some.lift (Fan.mk K f) ≫
              (Fan.mk
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (productComplex I))
                (fun t => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                  (productComplexProjection I t))).proj t) =
          e.hom ≫ s.proj t
        have hfac :
            hHomotopyProduct.some.lift (Fan.mk K f) ≫
                (Fan.mk
                  ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (productComplex I))
                  (fun t => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                    (productComplexProjection I t))).proj t = f t := by
          simpa only [Fan.proj, Fan.mk_π_app] using
            hHomotopyProduct.some.fac (Fan.mk K f) (Discrete.mk t)
        rw [hfac, hf t]
      simpa [v, u] using hleft.trans hright.symm
    let v := Classical.choose
      (((CochainComplex.IsKInjective.Qh_map_bijective K (productComplex I) :
        Function.Bijective (DerivedCategory.Qh (C := A)).map)).2
        (e.hom ≫ m))
    have hv :
        (DerivedCategory.Qh (C := A)).map v = e.hom ≫ m :=
      Classical.choose_spec
        (((CochainComplex.IsKInjective.Qh_map_bijective K (productComplex I) :
          Function.Bijective (DerivedCategory.Qh (C := A)).map)).2
          (e.hom ≫ m))
    have hfinal : m = e.inv ≫ (DerivedCategory.Qh (C := A)).map u := by
      calc
        m = e.inv ≫ (e.hom ≫ m) := by simp
        _ = e.inv ≫ (DerivedCategory.Qh (C := A)).map v := by rw [hv]
        _ = e.inv ≫ (DerivedCategory.Qh (C := A)).map u := by
          have h := congrArg
            (fun z => e.inv ≫ (DerivedCategory.Qh (C := A)).map z) hvu
          simpa [v] using h
    simpa [K, e, f, u] using hfinal

/-! ## Derived functors computed on K-injectives -/

section DerivedFunctor

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A]
  {D' : Type u'} [Category.{v'} D'] [Preadditive D']
  [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D'] [CategoryTheory.IsTriangulated D']

open Formalization.Books.Categories.Unit27
open Formalization.Books.Categories.Unit22

private theorem kInjective_computes_rightDerived
    (F : BookHomotopyCategory A ⥤ D') (I : BookComplex A)
    (hI : I.IsKInjective) :
    ComputesRightDerived
      (quasiIsoHomotopyProperty A)
      (quasiIsoHomotopyProperty_properties A).1 F
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) := by
  let S : MorphismProperty (BookHomotopyCategory A) := quasiIsoHomotopyProperty A
  let hS : SaturatedMultiplicativeSystem S :=
    by simpa [S] using (quasiIsoHomotopyProperty_properties A).1
  let X : BookHomotopyCategory A :=
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I
  let _ : LeftMultiplicativeSystem S := hS.1.1
  let _ : IsFiltered (LeftDenominatorCategory S X) :=
    left_denominator_category_is_filtered X
  have hK : CochainComplex.IsKInjective X.1 := by
    change CochainComplex.IsKInjective I
    exact hI
  let _ : I.IsKInjective := hI
  have hRetract : ∀ s : LeftDenominatorCategory S X,
      ∃ r : s.right ⟶ X, s.hom ≫ r = 𝟙 X := by
    intro s
    let _ : IsIso (DerivedCategory.Qh.map s.hom) :=
      Localization.inverts _ _ _ s.prop
    obtain ⟨r, hr⟩ :=
      (CochainComplex.IsKInjective.Qh_map_bijective s.right I).surjective
        (inv (DerivedCategory.Qh.map s.hom))
    refine ⟨r, ?_⟩
    apply (CochainComplex.IsKInjective.Qh_map_bijective X I).injective
    rw [Functor.map_comp, hr]
    simp
  let r : ∀ s : LeftDenominatorCategory S X, s.right ⟶ X :=
    fun s => (hRetract s).choose
  have hr (s : LeftDenominatorCategory S X) : s.hom ≫ r s = 𝟙 X :=
    (hRetract s).choose_spec
  have hRetractUnique (s : LeftDenominatorCategory S X)
      (a b : s.right ⟶ X) (ha : s.hom ≫ a = 𝟙 X)
      (hb : s.hom ≫ b = 𝟙 X) : a = b := by
    let _ : IsIso (DerivedCategory.Qh.map s.hom) :=
      Localization.inverts _ _ _ s.prop
    apply (CochainComplex.IsKInjective.Qh_map_bijective s.right I).injective
    apply (cancel_epi (DerivedCategory.Qh.map s.hom)).1
    rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp, ha, hb]
  let M := rightDerivedDiagram S F X
  let c : Cocone M :=
    { pt := F.obj X
      ι :=
        { app := fun s => F.map (r s)
          naturality := by
            intro s t f
            change F.map f.right ≫ F.map (r t) = F.map (r s) ≫ 𝟙 _
            simp only [Category.comp_id]
            rw [← F.map_comp]
            exact congrArg (fun q => F.map q)
              (hRetractUnique s (f.right ≫ r t) (r s)
                (by rw [← Category.assoc, MorphismProperty.Under.w f, hr]) (hr s)) } }
  have hr₀ : r (rightDerivedIdentityIndex S X) = 𝟙 X := by
    apply hRetractUnique (rightDerivedIdentityIndex S X)
      (r (rightDerivedIdentityIndex S X)) (𝟙 X)
    · exact hr (rightDerivedIdentityIndex S X)
    · change (𝟙 X) ≫ 𝟙 X = 𝟙 X
      simp
  have hc : IsEssentiallyConstantInd M c := by
    refine ⟨rightDerivedIdentityIndex S X, 𝟙 _, ?_, ?_⟩
    · change 𝟙 (F.obj X) ≫ F.map (r (rightDerivedIdentityIndex S X)) = 𝟙 (F.obj X)
      rw [hr₀]
      simp
    · intro j
      let g : j ⟶ rightDerivedIdentityIndex S X :=
        MorphismProperty.Under.homMk (r j) (hr j)
      refine ⟨rightDerivedIdentityIndex S X, 𝟙 _, g, ?_⟩
      dsimp [rightDerivedIdentityIndex, MorphismProperty.Under.mk]
      dsimp [M, c, g, rightDerivedDiagram, rightDerivedIdentityIndex,
        MorphismProperty.Under.mk]
      simp
  let hX : rightDerivedDefined S hS F X := ⟨c, hc⟩
  let c' := rightDerivedCocone S hS F X hX
  have hc' : IsEssentiallyConstantInd M c' := by
    exact Classical.choose_spec hX
  obtain ⟨i, s, hs, hfactor⟩ := hc'
  let gi : i ⟶ rightDerivedIdentityIndex S X :=
    MorphismProperty.Under.homMk (r i) (hr i)
  have hgi : M.map gi ≫ c'.ι.app (rightDerivedIdentityIndex S X) = c'.ι.app i :=
    c'.w gi
  obtain ⟨k, f, g, hfg⟩ := hfactor (rightDerivedIdentityIndex S X)
  let gk : k ⟶ rightDerivedIdentityIndex S X :=
    MorphismProperty.Under.homMk (r k) (hr k)
  have hgk : g ≫ gk = 𝟙 (rightDerivedIdentityIndex S X) := by
    dsimp [rightDerivedIdentityIndex, MorphismProperty.Under.mk] at g gk ⊢
    apply MorphismProperty.Under.Hom.ext
    rw [MorphismProperty.Comma.comp_right]
    dsimp [MorphismProperty.Under.homMk]
    change g.right ≫ r k = 𝟙 X
    have hg : g.right = k.hom := by
      simpa using MorphismProperty.Under.w g
    rw [hg, hr k]
  let a := c'.ι.app (rightDerivedIdentityIndex S X)
  let b := s ≫ M.map gi
  let q := s ≫ M.map f ≫ M.map gk
  have hba : b ≫ a = 𝟙 c'.pt := by
    dsimp [b]
    rw [Category.assoc, hgi, hs]
  have haq : a ≫ q = 𝟙 (M.obj (rightDerivedIdentityIndex S X)) := by
    calc
      a ≫ q = (a ≫ s ≫ M.map f) ≫ M.map gk := by simp [q, Category.assoc]
      _ = M.map g ≫ M.map gk := by rw [hfg]
      _ = M.map (g ≫ gk) := by rw [M.map_comp]
      _ = 𝟙 (M.obj (rightDerivedIdentityIndex S X)) := by rw [hgk]; simp
  have hbq : b = q := by
    calc
      b = b ≫ 𝟙 (M.obj (rightDerivedIdentityIndex S X)) := by simp
      _ = b ≫ (a ≫ q) := by rw [haq]
      _ = (b ≫ a) ≫ q := by simp [Category.assoc]
      _ = q := by rw [hba]; simp
  have ha : IsIso a := by
    let _ : IsIso a := IsIso.mk ⟨q, haq, by rw [← hbq, hba]; simp⟩
    infer_instance
  refine ⟨hX, ?_⟩
  have haFinal : IsIso ((rightDerivedCocone S hS F X hX).ι.app
      ({ left := ⟨⟨⟩⟩, right := X, hom := 𝟙 X, prop := S.id_mem X } :
        LeftDenominatorCategory S X)) := by
    simpa [c', a, rightDerivedIdentityIndex, MorphismProperty.Under.mk] using ha
  have hcomp : IsIso (𝟙 (F.obj X) ≫
      (rightDerivedCocone S hS F X hX).ι.app
        ({ left := ⟨⟨⟩⟩, right := X, hom := 𝟙 X, prop := S.id_mem X } :
          LeftDenominatorCategory S X)) := by
    let leg : F.obj X ⟶ (rightDerivedCocone S hS F X hX).pt := by
      dsimp [rightDerivedDiagram, MorphismProperty.Under.mk]
      exact (rightDerivedCocone S hS F X hX).ι.app
        ({ left := ⟨⟨⟩⟩, right := X, hom := 𝟙 X, prop := S.id_mem X } :
          LeftDenominatorCategory S X)
    have hleg : IsIso leg := by
      dsimp [leg]
      exact haFinal
    let _ : IsIso leg := hleg
    have hcomp' : IsIso (𝟙 (F.obj X) ≫ leg) := by infer_instance
    simpa [leg, rightDerivedDiagram, MorphismProperty.Under.mk] using hcomp'
  simpa [rightDerivedCanonicalMap, rightDerivedValue, rightDerivedDiagram,
    rightDerivedIdentityIndex, MorphismProperty.Under.mk] using hcomp

/- The source's first K-injective derived-functor lemma is expressed using
   the canonical `rightDerivedDefined` and `ComputesRightDerived` predicates.
   `HasKInjectiveResolution` is the earlier chapter's source-facing package
   for a quasi-isomorphism towards a K-injective complex. -/
theorem kInjective_rightDerived_defined_and_computes
    (F : BookHomotopyCategory A ⥤ D')
    (hF : Nonempty (ExactTriangulatedFunctorData F)) :
    (∀ K : BookComplex A,
      HasKInjectiveResolution A K →
        rightDerivedDefined
          (quasiIsoHomotopyProperty A)
          (quasiIsoHomotopyProperty_properties A).1 F
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ∧
      (∀ I : BookComplex A, I.IsKInjective →
        ComputesRightDerived
          (quasiIsoHomotopyProperty A)
          (quasiIsoHomotopyProperty_properties A).1 F
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := by
  let S : MorphismProperty (BookHomotopyCategory A) := quasiIsoHomotopyProperty A
  let hS : SaturatedMultiplicativeSystem S :=
    by simpa [S] using (quasiIsoHomotopyProperty_properties A).1
  constructor
  · intro K hK
    obtain ⟨I, f, hf, hI⟩ := hK
    have hIcomp := kInjective_computes_rightDerived F I hI
    have hs : S ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f) := by
      change HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)
      exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf
    exact (rightDerived_defined_iff_of_mem hS F
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f) hs).mpr hIcomp.1
  · intro I hI
    exact kInjective_computes_rightDerived F I hI

/- The phrase `RF(I) = F(I)` is made precise by requiring the comparison
   component of a right derived functor to be an isomorphism on every
   K-injective complex. -/
theorem rightDerived_exists_of_enough_kInjectives
    (F : BookHomotopyCategory A ⥤ D')
    (hF : Nonempty (ExactTriangulatedFunctorData F))
    (hEnough : ∀ K : BookComplex A, HasKInjectiveResolution A K) :
    ∃ (RF : DerivedCategory A ⥤ D')
      (α : F ⟶ (DerivedCategory.Qh (C := A)) ⋙ RF),
      Functor.IsRightDerivedFunctor RF α (quasiIsoHomotopyProperty A) ∧
        ∀ I : BookComplex A, I.IsKInjective →
          IsIso
            (α.app
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := by
  sorry

end DerivedFunctor

open CochainComplex.HomComplex

private noncomputable def splitSurjectionCochainLift
    {A : Type u} [Category.{v} A] [Abelian A]
    {M K L : BookComplex A} {n : ℤ}
    (p : K ⟶ L)
    (hp : Formalization.Books.Derived.Unit09.termwiseSplitSurjection p)
    (z : Cochain M L n) : Cochain M K n :=
  Cochain.mk (fun i j hij =>
    z.v i j hij ≫ (hp j).exists_splitEpi.some.section_)

private lemma splitSurjectionCochainLift_comp
    {A : Type u} [Category.{v} A] [Abelian A]
    {M K L : BookComplex A} {n : ℤ}
    (p : K ⟶ L)
    (hp : Formalization.Books.Derived.Unit09.termwiseSplitSurjection p)
    (z : Cochain M L n) :
    (splitSurjectionCochainLift p hp z).comp
        (Cochain.ofHom p) (add_zero n) = z := by
  ext i j hij
  rw [Cochain.comp_v _ _ (add_zero n) i j j hij (add_zero j)]
  rw [Cochain.ofHom_v]
  dsimp [splitSurjectionCochainLift]
  rw [Category.assoc, (hp j).exists_splitEpi.some.id, Category.comp_id]

private lemma splitSurjection_homotopy_lift
    {A : Type u} [Category.{v} A] [Abelian A]
    {M K L : BookComplex A} (p : K ⟶ L)
    (hp : Formalization.Books.Derived.Unit09.termwiseSplitSurjection p)
    (f : M ⟶ K) (hM : M.Acyclic) [K.IsKInjective] [L.IsKInjective]
    (h : Homotopy (f ≫ p) 0) :
    ∃ z : Cochain M K (-1),
      Cochain.ofHom f = δ (-1) 0 z ∧
        z.comp (Cochain.ofHom p) (add_zero (-1)) =
          Cochain.ofHomotopy h := by
  let k : Cochain M K (-1) :=
    splitSurjectionCochainLift p hp (Cochain.ofHomotopy h)
  have hk : k.comp (Cochain.ofHom p) (add_zero (-1)) =
      Cochain.ofHomotopy h := by
    exact splitSurjectionCochainLift_comp p hp (Cochain.ofHomotopy h)
  let q : Cochain M K 0 := Cochain.ofHom f - δ (-1) 0 k
  have hq : δ 0 1 q = 0 := by
    dsimp [q]
    rw [δ_sub, δ_ofHom, δ_δ]
    simp
  let g : M ⟶ K :=
    Cocycle.homOf (Cocycle.mk q 1 (zero_add 1) hq)
  have hg : Cochain.ofHom g = q := by
    exact Cocycle.cochain_ofHom_homOf_eq_coe _
  obtain ⟨hg'⟩ := CochainComplex.IsKInjective.nonempty_homotopy_zero g hM
  let r₀ : Cochain M K (-1) := Cochain.ofHomotopy hg'
  have hr₀ : δ (-1) 0 r₀ = q := by
    dsimp [r₀]
    rw [δ_ofHomotopy, Cochain.ofHom_zero, sub_zero, hg]
  have hqp : q.comp (Cochain.ofHom p) (zero_add 0) = 0 := by
    dsimp [q]
    rw [Cochain.sub_comp, ← Cochain.ofHom_comp, ← δ_comp_ofHom, hk]
    rw [δ_ofHomotopy h, Cochain.ofHom_zero, sub_zero]
    simp
  have hr₀p : δ (-1) 0 (r₀.comp (Cochain.ofHom p) (add_zero (-1))) = 0 := by
    rw [δ_comp_ofHom, hr₀, hqp]
  let rp : Cocycle M L (-1) :=
    Cocycle.mk (r₀.comp (Cochain.ofHom p) (add_zero (-1))) 0
      (by simp) hr₀p
  obtain ⟨s, hs⟩ :=
    CochainComplex.IsKInjective.eq_δ_of_cocycle rp hM (-2) (by simp)
  have hs' : δ (-2) (-1) s =
      r₀.comp (Cochain.ofHom p) (add_zero (-1)) := by
    simpa [rp] using hs
  let t : Cochain M K (-2) :=
    splitSurjectionCochainLift p hp s
  have ht : t.comp (Cochain.ofHom p) (add_zero (-2)) = s := by
    exact splitSurjectionCochainLift_comp p hp s
  let r : Cochain M K (-1) := r₀ - δ (-2) (-1) t
  have hrp : r.comp (Cochain.ofHom p) (add_zero (-1)) = 0 := by
    dsimp [r]
    rw [Cochain.sub_comp, ← δ_comp_ofHom, ht, hs']
    simp
  let z : Cochain M K (-1) := k + r
  refine ⟨z, ?_, ?_⟩
  · dsimp [z]
    rw [δ_add]
    dsimp [r]
    rw [δ_sub, hr₀, δ_δ]
    dsimp [q]
    abel
  · dsimp [z]
    rw [Cochain.add_comp, hk, hrp, add_zero]

/-! ## Split inverse systems -/

/- The source's inverse system is the positive-integer inverse system supplied
   by Homology, Chapter 31.  Its termwise split-surjection condition is the
   earlier `termwiseSplitSurjection` interface. -/
theorem inverseSystemLimit_isKInjective_of_split_surjective
    {A : Type u} [Category.{v} A] [Abelian A]
    (I : NatInverseSystem (BookComplex A))
    [∀ m : ℤ, HasLimit
      (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) m)]
    (hI : ∀ n : ℕ+, (I.obj (Opposite.op n)).IsKInjective)
    (hsplit : ∀ n : ℕ+,
      Formalization.Books.Derived.Unit09.termwiseSplitSurjection
        (successiveTransitionMap I n)) :
    (inverseSystemLimit I).IsKInjective := by
  classical
  refine ⟨fun {M} f hM => ?_⟩
  let f_p (n : ℕ+) : M ⟶ I.obj (Opposite.op n) :=
    f ≫ limit.π I (Opposite.op n)
  have hpcomp (n : ℕ+) :
      f_p (n + 1) ≫ successiveTransitionMap I n = f_p n := by
    dsimp [f_p]
    rw [Category.assoc]
    simpa [successiveTransitionMap, transitionMap] using
      (limit.w I (opHomOfLE (PNat.lt_add_right n 1).le))
  let h₁ : Homotopy (f_p 1) 0 := by
    letI : (I.obj (Opposite.op (1 : ℕ+))).IsKInjective := hI 1
    exact CochainComplex.IsKInjective.nonempty_homotopy_zero (f_p 1) hM |>.some
  let step (n : ℕ+) (h : Homotopy (f_p n) 0) :
      {h' : Homotopy (f_p (n + 1)) 0 //
        Cochain.ofHomotopy (h'.compRight (successiveTransitionMap I n)) =
          Cochain.ofHomotopy h} := by
    letI : (I.obj (Opposite.op (n + 1))).IsKInjective := hI (n + 1)
    letI : (I.obj (Opposite.op n)).IsKInjective := hI n
    let hh : Homotopy
        (f_p (n + 1) ≫ successiveTransitionMap I n) 0 :=
      { hom := h.hom
        zero := h.zero
        comm := by
          intro i
          rw [hpcomp n]
          exact h.comm i }
    let z : Cochain M (I.obj (Opposite.op (n + 1))) (-1) :=
      Classical.choose (splitSurjection_homotopy_lift
        (successiveTransitionMap I n) (hsplit n) (f_p (n + 1)) hM hh)
    have hzdata := Classical.choose_spec (splitSurjection_homotopy_lift
      (successiveTransitionMap I n) (hsplit n) (f_p (n + 1)) hM hh)
    have hz : Cochain.ofHom (f_p (n + 1)) = δ (-1) 0 z := hzdata.1
    have hzcomp : z.comp (Cochain.ofHom (successiveTransitionMap I n))
        (add_zero (-1)) = Cochain.ofHomotopy hh := hzdata.2
    let hzsub : {z : Cochain M (I.obj (Opposite.op (n + 1))) (-1) //
        Cochain.ofHom (f_p (n + 1)) =
          δ (-1) 0 z + Cochain.ofHom
            (0 : M ⟶ I.obj (Opposite.op (n + 1)))} :=
      ⟨z, by
        have hz' : Cochain.ofHom (f_p (n + 1)) =
            δ (-1) 0 z + Cochain.ofHom
              (0 : M ⟶ I.obj (Opposite.op (n + 1))) := by
          rw [Cochain.ofHom_zero, add_zero]
          exact hz
        exact hz'⟩
    let h' : Homotopy (f_p (n + 1)) 0 :=
      (Cochain.equivHomotopy (f_p (n + 1)) 0).symm hzsub
    have hz' : Cochain.ofHomotopy h' = z := by
      ext i j hij
      change h'.hom i j = z.v i j hij
      dsimp [h']
      exact congrArg (fun w => w.1.v i j hij)
        ((Cochain.equivHomotopy (f_p (n + 1)) 0).apply_symm_apply hzsub)
    have hcomp : Cochain.ofHomotopy
        (h'.compRight (successiveTransitionMap I n)) =
        (Cochain.ofHomotopy h').comp
          (Cochain.ofHom (successiveTransitionMap I n)) (add_zero (-1)) := by
      ext i j hij
      simp [Cochain.ofHomotopy, Homotopy.compRight, Cochain.comp_v]
    have hhh : Cochain.ofHomotopy hh = Cochain.ofHomotopy h := by
      ext i j hij
      change hh.hom i j = h.hom i j
      dsimp [hh]
    exact ⟨h', by rw [hcomp, hz', hzcomp, hhh]⟩
  let H (n : ℕ+) : Homotopy (f_p n) 0 :=
    PNat.recOn n h₁ (fun n h => (step n h).1)
  have Hcomp (n : ℕ+) :
      Cochain.ofHomotopy ((H (n + 1)).compRight (successiveTransitionMap I n)) =
        Cochain.ofHomotopy (H n) := by
    simpa only [H, PNat.recOn_succ] using (step n (H n)).2
  have hcompRight {K L N : BookComplex A} {a b : K ⟶ L} (h : Homotopy a b)
      (p : L ⟶ N) :
      Cochain.ofHomotopy (h.compRight p) =
        (Cochain.ofHomotopy h).comp (Cochain.ofHom p) (add_zero (-1)) := by
    ext i j hij
    simp [Cochain.ofHomotopy, Homotopy.compRight, Cochain.comp_v]
  have hcompRight_assoc {K L N P : BookComplex A} {a : K ⟶ L}
      (h : Homotopy a 0) (p : L ⟶ N) (q : N ⟶ P) :
      Cochain.ofHomotopy ((h.compRight p).compRight q) =
        ((Cochain.ofHomotopy h).comp (Cochain.ofHom p) (add_zero (-1))).comp
          (Cochain.ofHom q) (add_zero (-1)) := by
    calc
      Cochain.ofHomotopy ((h.compRight p).compRight q) =
          (Cochain.ofHomotopy (h.compRight p)).comp
            (Cochain.ofHom q) (add_zero (-1)) :=
        hcompRight (h.compRight p) q
      _ = ((Cochain.ofHomotopy h).comp (Cochain.ofHom p) (add_zero (-1))).comp
            (Cochain.ofHom q) (add_zero (-1)) := by rw [hcompRight h p]
  have Hmap : ∀ (n m : ℕ+) (hmn : m ≤ n),
      Cochain.ofHomotopy ((H n).compRight (transitionMap I hmn)) =
        Cochain.ofHomotopy (H m) := by
    intro n
    induction n using PNat.recOn with
    | one =>
        intro m hm
        have hm1 : m = 1 := le_antisymm hm (PNat.one_le m)
        subst m
        have hmproof : hm = le_rfl := Subsingleton.elim _ _
        subst hm
        rw [transitionMap_refl]
        ext i j hij
        simp [Homotopy.compRight, Cochain.ofHomotopy]
    | succ n ih =>
        intro m hmn
        by_cases hEq : m = n + 1
        · subst m
          have hmproof : hmn = le_rfl := Subsingleton.elim _ _
          subst hmn
          rw [transitionMap_refl]
          ext i j hij
          simp [Homotopy.compRight, Cochain.ofHomotopy]
        · have hmn' : m ≤ n := PNat.lt_add_one_iff.mp (lt_of_le_of_ne hmn hEq)
          have htrans : transitionMap I hmn =
              successiveTransitionMap I n ≫ transitionMap I hmn' := by
            simpa [successiveTransitionMap] using
              (transitionMap_comp I (PNat.lt_add_right n 1).le hmn').symm
          rw [htrans]
          calc
            Cochain.ofHomotopy ((H (n + 1)).compRight
                (successiveTransitionMap I n ≫ transitionMap I hmn')) =
                Cochain.ofHomotopy
                  (((H (n + 1)).compRight (successiveTransitionMap I n)).compRight
                    (transitionMap I hmn')) := by
                  ext i j hij
                  simp [Cochain.ofHomotopy, Homotopy.compRight]
            _ = ((Cochain.ofHomotopy (H (n + 1))).comp
                (Cochain.ofHom (successiveTransitionMap I n)) (add_zero (-1))).comp
                  (Cochain.ofHom (transitionMap I hmn')) (add_zero (-1)) := by
                  exact hcompRight_assoc (H (n + 1))
                    (successiveTransitionMap I n) (transitionMap I hmn')
            _ = (Cochain.ofHomotopy (H n)).comp
                (Cochain.ofHom (transitionMap I hmn')) (add_zero (-1)) := by
                  rw [← hcompRight (H (n + 1)) (successiveTransitionMap I n),
                    Hcomp n]
            _ = Cochain.ofHomotopy ((H n).compRight (transitionMap I hmn')) :=
                (hcompRight (H n) _).symm
            _ = Cochain.ofHomotopy (H m) := ih m hmn'
  let e (j : ℤ) (n : ℕ+ᵒᵖ) : (I.obj n).X j =
      (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) j).obj n := rfl
  have he (j : ℤ) (n : ℕ+ᵒᵖ) : e j n = (by rfl) := Subsingleton.elim _ _
  let Hcone (i j : ℤ) :
      Cone (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) j) :=
    { pt := M.X i
      π :=
        { app := fun n => (H n.unop).hom i j ≫ eqToHom (e j n)
          naturality := by
            rintro ⟨x⟩ ⟨y⟩ fxy
            let hxy : y ≤ x := le_of_op_hom fxy
            have hf : fxy = opHomOfLE hxy := Subsingleton.elim _ _
            rw [hf]
            simp only [Functor.const_obj_map, Category.id_comp, Category.assoc]
            by_cases hij : i + (-1) = j
            · have hval : (H x).hom i j ≫ (I.map (opHomOfLE hxy)).f j =
                  (H y).hom i j := by
                simpa [Cochain.ofHomotopy, Homotopy.compRight, transitionMap]
                  using congrArg (fun z => z.v i j hij) (Hmap x y hxy)
              have hmap : eqToHom (e j (Opposite.op x)) ≫
                    (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) j).map
                      (opHomOfLE hxy) =
                  (I.map (opHomOfLE hxy)).f j ≫ eqToHom (e j (Opposite.op y)) := by
                cases e j (Opposite.op x)
                cases e j (Opposite.op y)
                dsimp [HomologicalComplex.eval]
                simp
              have hval' := congrArg
                (fun z => z ≫ eqToHom (e j (Opposite.op y))) hval.symm
              rw [Category.assoc, ← hmap, ← Category.assoc] at hval'
              rw [Category.assoc] at hval'
              simpa [he, e] using hval'
            · rw [(H y).zero i j (by
                    intro hrel
                    have hrel' : j + 1 = i := by
                      simpa only [ComplexShape.up_Rel] using hrel
                    apply hij
                    omega),
                  (H x).zero i j (by
                    intro hrel
                    have hrel' : j + 1 = i := by
                      simpa only [ComplexShape.up_Rel] using hrel
                    apply hij
                    omega)]
              simp [he, e] } }
  let eLimit (j : ℤ) : (inverseSystemLimit I).X j ≅
      limit (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) j) :=
    preservesLimitIso (HomologicalComplex.eval A (ComplexShape.up ℤ) j) I
  let hHom (i j : ℤ) : M.X i ⟶ (inverseSystemLimit I).X j :=
    limit.lift (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) j)
        (Hcone i j) ≫ (eLimit j).inv
  let h : Homotopy f 0 :=
    { hom := hHom
      zero := by
        intro i j hij
        have hij' : ¬ i + (-1) = j := by
          intro hrel
          apply hij
          simp only [ComplexShape.up_Rel]
          omega
        apply (cancel_mono (eLimit j).hom).1
        dsimp [hHom]
        simp [Category.assoc]
        apply (limit.isLimit (I ⋙ HomologicalComplex.eval A
          (ComplexShape.up ℤ) j)).hom_ext
        intro n
        change limit.lift (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) j)
            (Hcone i j) ≫ limit.π (I ⋙ HomologicalComplex.eval A
              (ComplexShape.up ℤ) j) n =
          0 ≫ limit.π (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) j) n
        rw [limit.lift_π]
        dsimp [Hcone]
        rw [(H n.unop).zero i j hij]
        simp
      comm := by
        intro i
        apply (cancel_mono (eLimit i).hom).1
        apply (limit.isLimit (I ⋙ HomologicalComplex.eval A
          (ComplexShape.up ℤ) i)).hom_ext
        intro n
        change (f.f i ≫ (eLimit i).hom) ≫
            limit.π (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) i) n =
          (((dNext i) hHom + (prevD i) hHom +
            (0 : M ⟶ inverseSystemLimit I).f i) ≫ (eLimit i).hom) ≫
            limit.π (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) i) n
        have hπhom : (eLimit i).hom ≫
              limit.π (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) i) n =
            (limit.π I n).f i := by
          dsimp [eLimit]
          exact preservesLimitIso_hom_π
            (HomologicalComplex.eval A (ComplexShape.up ℤ) i) I n
        have hπinv (k : ℤ) : (eLimit k).inv ≫ (limit.π I n).f k =
              limit.π (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) k) n := by
          dsimp [eLimit]
          exact preservesLimitIso_inv_π
            (HomologicalComplex.eval A (ComplexShape.up ℤ) k) I n
        have hHomπ (k l : ℤ) : hHom k l ≫ (eLimit l).hom ≫
              limit.π (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) l) n =
              (Hcone k l).π.app n := by
          dsimp [hHom]
          simp only [Category.assoc]
          rw [Iso.inv_hom_id_assoc]
          exact limit.lift_π (Hcone k l) n
        let coneApp (k l : ℤ) : M.X k ⟶
              (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) l).obj n := by
          change M.X k ⟶ (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) l).obj n
          exact (Hcone k l).π.app n
        rw [dNext_eq hHom (i' := i + 1) (by simp),
          prevD_eq hHom (j' := i - 1) (by simp)]
        have hstage := (H n.unop).comm i
        dsimp [f_p] at hstage
        have hnextTerm :
            HomologicalComplex.dFrom M i ≫
                fromNext i (H n.unop).hom =
              M.d i (i + 1) ≫ (H n.unop).hom (i + 1) i := by
          rw [← dNext_eq_dFrom_fromNext]
          rw [dNext_eq (H n.unop).hom (i' := i + 1) (by simp)]
        have hprevTerm :
            toPrev i (H n.unop).hom ≫ HomologicalComplex.dTo (I.obj n) i =
              (H n.unop).hom i (i - 1) ≫ (I.obj n).d (i - 1) i := by
          rw [← prevD_eq_toPrev_dTo]
          rw [prevD_eq (H n.unop).hom (j' := i - 1) (by simp)]
        rw [hnextTerm, hprevTerm] at hstage
        simp only [add_zero] at hstage
        have hnext : M.d i (i + 1) ≫ hHom (i + 1) i ≫
              (eLimit i).hom ≫
                limit.π (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) i) n =
            M.d i (i + 1) ≫ coneApp (i + 1) i := by
          dsimp [hHom]
          simp only [Category.assoc]
          rw [Iso.inv_hom_id_assoc]
          rw [limit.lift_π]
        have hprev : hHom i (i - 1) ≫ (inverseSystemLimit I).d (i - 1) i ≫
              (limit.π I n).f i =
            coneApp i (i - 1) ≫ (I.obj n).d (i - 1) i := by
          rw [← (limit.π I n).comm' (i - 1) i (by simp)]
          have hπhomPrev : (eLimit (i - 1)).hom ≫
                limit.π (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) (i - 1)) n =
              (limit.π I n).f (i - 1) := by
            dsimp [eLimit]
            exact preservesLimitIso_hom_π
              (HomologicalComplex.eval A (ComplexShape.up ℤ) (i - 1)) I n
          have hfactor : hHom i (i - 1) ≫ (limit.π I n).f (i - 1) =
              (Hcone i (i - 1)).π.app n := by
            rw [← hπhomPrev]
            exact hHomπ i (i - 1)
          rw [← Category.assoc, hfactor]
          rfl
        let dEval :
            (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) (i - 1)).obj n ⟶
              (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) i).obj n := by
          change (I.obj n).X (i - 1) ⟶ (I.obj n).X i
          exact (I.obj n).d (i - 1) i
        have hprevEval : hHom i (i - 1) ≫ (inverseSystemLimit I).d (i - 1) i ≫
              (eLimit i).hom ≫
                limit.π (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) i) n =
            coneApp i (i - 1) ≫ dEval := by
          rw [hπhom]
          simpa [coneApp, dEval, HomologicalComplex.eval, Category.assoc] using hprev
        have hstageEval :
            f.f i ≫ (limit.π I n).f i =
              M.d i (i + 1) ≫ coneApp (i + 1) i +
                coneApp i (i - 1) ≫ dEval := by
          convert hstage using 1 <;>
            (try simp [coneApp, dEval, Hcone, e, HomologicalComplex.eval,
              Category.assoc]) <;>
            rfl
        have hstageEval' :
            (f.f i ≫ (eLimit i).hom) ≫
                limit.π (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) i) n =
              M.d i (i + 1) ≫ coneApp (i + 1) i +
                coneApp i (i - 1) ≫ dEval := by
          simp only [Category.assoc]
          rw [hπhom]
          exact hstageEval
        rw [hstageEval']
        rw [Preadditive.add_comp, Preadditive.add_comp,
          Preadditive.add_comp, Preadditive.add_comp,
          HomologicalComplex.zero_f, zero_comp]
        simp only [Category.assoc]
        rw [hnext, hprevEval]
        simp only [zero_comp, add_zero] }
  exact ⟨h⟩

/- The source notes that the split-tower lemma extends to larger ordinals;
   the earlier inverse-system chapter already exposes the ordinal-limit
   infrastructure.  The source also warns that combining the countable
   construction with bounded-below injective resolutions may fail to produce
   enough K-injectives; this warning is not an additional theorem. -/

/-! ## Exact adjoints preserve K-injectives -/

private def adjointComplexMap
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (adj : v ⊣ u) {K : BookComplex B} {I : BookComplex A}
    (f : K ⟶ (u.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :
    (v.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I :=
  { f := fun i => by
      change v.obj (K.X i) ⟶ I.X i
      exact (adj.homEquiv _ _).symm (by
        simpa [Functor.mapHomologicalComplex] using f.f i)
    comm' := fun i j hij => by
      apply (adj.homEquiv _ _).injective
      dsimp [Functor.mapHomologicalComplex]
      rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
      simpa [Functor.mapHomologicalComplex] using f.comm i j }

private def adjointUnitComplexMap
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (adj : v ⊣ u) (K : BookComplex B) :
    K ⟶ (u.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((v.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  { f := fun i => adj.unit.app (K.X i)
    comm' := fun i j hij => by
      simpa [Functor.mapHomologicalComplex] using adj.unit.naturality (K.d i j) }

theorem additive_right_adjoint_preserves_isKInjective
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (adj : v ⊣ u)
    (hv : Formalization.Books.Categories.Unit23.IsExact v)
    {I : BookComplex A} (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  letI : PreservesFiniteLimits v := hv.1
  letI : PreservesFiniteColimits v := hv.2
  have hvExact : ∀ (S : ShortComplex B), S.Exact → (S.map v).Exact :=
    ((Functor.exact_tfae v).out 3 1).mp
      (show PreservesFiniteLimits v ∧ PreservesFiniteColimits v from
        ⟨hv.1, hv.2⟩)
  have hAcyclic : ∀ K : BookComplex B, K.Acyclic →
      ((v.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
    intro K hK n
    rw [HomologicalComplex.exactAt_iff]
    exact hvExact _ ((HomologicalComplex.exactAt_iff K n).mp (hK n))
  letI : I.IsKInjective := hI
  constructor
  intro K f hK
  let f' := adjointComplexMap u v adj f
  obtain ⟨h'⟩ := CochainComplex.IsKInjective.nonempty_homotopy_zero f'
    (hAcyclic K hK)
  let η := adjointUnitComplexMap u v adj K
  have hEq : f = η ≫
      (u.mapHomologicalComplex (ComplexShape.up ℤ)).map f' := by
    ext i
    dsimp [η, adjointUnitComplexMap, f', adjointComplexMap,
      Functor.mapHomologicalComplex]
    rw [← adj.homEquiv_unit]
    simp
  have hzero : η ≫
      (u.mapHomologicalComplex (ComplexShape.up ℤ)).map (0 :
        (v.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I) = 0 := by
    simp
  have hEqHom : Homotopy f
      (η ≫ (u.mapHomologicalComplex (ComplexShape.up ℤ)).map f') :=
    Homotopy.ofEq hEq
  have hMap : Homotopy
      (η ≫ (u.mapHomologicalComplex (ComplexShape.up ℤ)).map f')
      (η ≫ (u.mapHomologicalComplex (ComplexShape.up ℤ)).map 0) :=
    (Functor.mapHomotopy u h').compLeft η
  have hZeroHom : Homotopy
      (η ≫ (u.mapHomologicalComplex (ComplexShape.up ℤ)).map 0) 0 :=
    Homotopy.ofEq hzero
  exact ⟨hEqHom.trans (hMap.trans hZeroHom)⟩

end Formalization.Books.Derived.Unit31
