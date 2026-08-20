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
  sorry

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
  sorry

/- The source notes that the split-tower lemma extends to larger ordinals;
   the earlier inverse-system chapter already exposes the ordinal-limit
   infrastructure.  The source also warns that combining the countable
   construction with bounded-below injective resolutions may fail to produce
   enough K-injectives; this warning is not an additional theorem. -/

/-! ## Exact adjoints preserve K-injectives -/

theorem additive_right_adjoint_preserves_isKInjective
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (adj : v ⊣ u)
    (hv : Formalization.Books.Categories.Unit23.IsExact v)
    {I : BookComplex A} (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  sorry

end Formalization.Books.Derived.Unit31
