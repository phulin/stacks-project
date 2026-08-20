import Mathlib.Algebra.Homology.Localization
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Homology.Unit19.Filtrations

/-!
# Derived Categories, Chapter 13: filtered derived categories

The finite filtered objects, associated graded functors, and strictness API are
the canonical constructions from Homology, Chapter 19.  This file adds the
homotopy-category and localization interfaces used for the filtered derived
category in the source section.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit27
open Formalization.Books.Derived.Unit05
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit16
open Formalization.Books.Homology.Unit19
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u

namespace Formalization.Books.Derived.Unit13

/-! ## Finite filtered objects and their functors -/

/-- The object property defining the finite filtered-object category. -/
def finiteFilteredProperty (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (FilteredObject C) :=
  fun A => A.IsFinite

/-- The source's `Fil^f(𝒜)`, as a full subcategory of filtered objects. -/
abbrev FiniteFilteredObject
    (C : Type u) [Category.{v} C] [Abelian C] :=
  (finiteFilteredProperty C).FullSubcategory

/-- The inclusion `Fil^f(𝒜) ⥤ Fil(𝒜)`. -/
abbrev finiteFilteredInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    FiniteFilteredObject C ⥤ FilteredObject C :=
  (finiteFilteredProperty C).ι

/-- The additive-category structure on finite filtered objects. -/
theorem finiteFiltered_additiveCategory_exists
    (C : Type u) [Category.{v} C] [Abelian C] :
    Nonempty (AdditiveCategory (FiniteFilteredObject C)) := by
  have hzero : (zeroFilteredObject (C := C)).IsFinite := by
    refine ⟨0, 0, ?_, ?_⟩
    · change Subobject.mk (𝟙 (0 : C)) = ⊤
      exact Subobject.mk_eq_top_of_isIso _
    · change Subobject.mk (𝟙 (0 : C)) = ⊥
      apply Subobject.mk_eq_bot_iff_zero.mpr
      exact (isZero_zero C).eq_of_src _ _
  let Z : FiniteFilteredObject C :=
    ⟨zeroFilteredObject (C := C), show finiteFilteredProperty C _ from hzero⟩
  let : ∀ A B : FiniteFilteredObject C,
      HasLimit (pair A B) := by
    intro A B
    let hA := A.property
    let hB := B.property
    rcases hA with ⟨a₁, a₂, ha₁, ha₂⟩
    rcases hB with ⟨b₁, b₂, hb₁, hb₂⟩
    let P : FilteredObject C := filteredBiproduct A.obj B.obj
    have hP : P.IsFinite := by
      refine ⟨min a₁ b₁, max a₂ b₂, ?_, ?_⟩
      · have hA' : A.obj.filtration.obj (min a₁ b₁) = ⊤ := by
          apply top_unique
          rw [← ha₁]
          exact A.obj.filtration.antitone (min_le_left _ _)
        have hB' : B.obj.filtration.obj (min a₁ b₁) = ⊤ := by
          apply top_unique
          rw [← hb₁]
          exact B.obj.filtration.antitone (min_le_right _ _)
        change Subobject.mk (biprod.map
          (A.obj.filtration.obj (min a₁ b₁)).arrow
          (B.obj.filtration.obj (min a₁ b₁)).arrow) = ⊤
        rw [hA', hB']
        let : IsIso (biprod.map (⊤ : Subobject A.obj.carrier).arrow
            (⊤ : Subobject B.obj.carrier).arrow) := by
          apply isIso_of_mono_of_epi
        exact Subobject.mk_eq_top_of_isIso _
      · have hA' : A.obj.filtration.obj (max a₂ b₂) = ⊥ := by
          apply bot_unique
          rw [← ha₂]
          exact A.obj.filtration.antitone (le_max_left _ _)
        have hB' : B.obj.filtration.obj (max a₂ b₂) = ⊥ := by
          apply bot_unique
          rw [← hb₂]
          exact B.obj.filtration.antitone (le_max_right _ _)
        change Subobject.mk (biprod.map
          (A.obj.filtration.obj (max a₂ b₂)).arrow
          (B.obj.filtration.obj (max a₂ b₂)).arrow) = ⊥
        rw [hA', hB']
        apply Subobject.mk_eq_bot_iff_zero.mpr
        apply biprod.hom_ext <;> simp
    let P' : FiniteFilteredObject C :=
      ⟨P, show finiteFilteredProperty C P from hP⟩
    let p₁ : P' ⟶ A := by
      exact (finiteFilteredProperty C).homMk
        (filteredBiproductDesc (A := A.obj) (B := A.obj) (D := B.obj)
          (𝟙 A.obj) 0)
    let p₂ : P' ⟶ B := by
      exact (finiteFilteredProperty C).homMk
        (filteredBiproductDesc (A := B.obj) (B := A.obj) (D := B.obj)
          0 (𝟙 B.obj))
    let t : BinaryFan A B := BinaryFan.mk p₁ p₂
    exact ⟨⟨t, BinaryFan.IsLimit.mk t
      (fun {T : FiniteFilteredObject C} f g => by
        exact (finiteFilteredProperty C).homMk
          (filteredBiproductLift (A := T.obj) (B := A.obj) (D := B.obj)
            f.hom g.hom))
      (by
        intro T f g
        apply (finiteFilteredProperty C).hom_ext
        apply FilteredHom.ext
        change (biprod.lift f.hom.hom g.hom.hom) ≫
            biprod.desc (𝟙 A.obj.carrier) 0 = f.hom.hom
        simp [biprod.desc_eq])
      (by
        intro T f g
        apply (finiteFilteredProperty C).hom_ext
        apply FilteredHom.ext
        change (biprod.lift f.hom.hom g.hom.hom) ≫
            biprod.desc 0 (𝟙 B.obj.carrier) = g.hom.hom
        simp [biprod.desc_eq])
      (by
        intro T f g m hm₁ hm₂
        apply (finiteFilteredProperty C).hom_ext
        apply FilteredHom.ext
        change m.hom.hom = biprod.lift f.hom.hom g.hom.hom
        apply biprod.hom_ext
        · have hm₁' := congrArg (fun k => k.hom.hom) hm₁
          change m.hom.hom ≫ biprod.desc (𝟙 A.obj.carrier) 0 = f.hom.hom at hm₁'
          simp only [biprod.desc_eq, Category.comp_id, comp_zero, add_zero,
            biprod.lift_fst] at hm₁' ⊢
          exact hm₁'
        · have hm₂' := congrArg (fun k => k.hom.hom) hm₂
          change m.hom.hom ≫ biprod.desc 0 (𝟙 B.obj.carrier) = g.hom.hom at hm₂'
          simp only [biprod.desc_eq, Category.comp_id, comp_zero, zero_add,
            biprod.lift_snd] at hm₂' ⊢
          exact hm₂')⟩⟩
  let : HasBinaryProducts (FiniteFilteredObject C) :=
    hasBinaryProducts_of_hasLimit_pair (FiniteFilteredObject C)
  let : ∀ A : FiniteFilteredObject C,
      Unique (A ⟶ Z) :=
    fun A =>
      { default := 0
        uniq := by
          intro f
          apply (finiteFilteredProperty C).hom_ext
          apply FilteredHom.ext
          apply (isZero_zero C).eq_of_tgt }
  let : HasTerminal (FiniteFilteredObject C) :=
    hasTerminal_of_unique (C := FiniteFilteredObject C)
      (X := Z)
  let : HasFiniteProducts (FiniteFilteredObject C) :=
    hasFiniteProducts_of_has_binary_and_terminal
  exact ⟨{ toPreadditive := inferInstance, toHasFiniteProducts := inferInstance }⟩

noncomputable instance finiteFiltered_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (FiniteFilteredObject C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts :=
      (Classical.choice (finiteFiltered_additiveCategory_exists C)).toHasFiniteProducts }

/-- Forget the filtration and retain the underlying object of `𝒜`. -/
def filteredForgetful
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredObject C ⥤ C where
  obj A := A.carrier
  map {_A _B} f := f.hom
  map_id _A := rfl
  map_comp _f _g := rfl

noncomputable instance filteredForgetful_additive
    (C : Type u) [Category.{v} C] [Abelian C] :
    (filteredForgetful C).Additive where
  map_add := by
    intro A B f g
    rfl

/-- The forgetful functor on finite filtered objects. -/
abbrev finiteForgetful
    (C : Type u) [Category.{v} C] [Abelian C] :
    FiniteFilteredObject C ⥤ C :=
  finiteFilteredInclusion C ⋙ filteredForgetful C

/-- The `p`th associated graded-piece functor on finite filtrations. -/
abbrev finiteGradedPieceFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
    FiniteFilteredObject C ⥤ C :=
  finiteFilteredInclusion C ⋙ gradedPieceFunctor (C := C) p

/-- The associated graded functor on finite filtrations. -/
abbrev finiteAssociatedGraded
    (C : Type u) [Category.{v} C] [Abelian C] :
    FiniteFilteredObject C ⥤ GradedObject ℤ C :=
  finiteFilteredInclusion C ⋙ associatedGraded (C := C)

noncomputable instance finiteGradedPieceFunctor_additive
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
    (finiteGradedPieceFunctor C p).Additive := by
  let _ : (gradedPieceFunctor (C := C) p).Additive :=
    gradedPieceFunctor_is_additive (C := C) p
  infer_instance

noncomputable instance finiteAssociatedGraded_additive
    (C : Type u) [Category.{v} C] [Abelian C] :
    (finiteAssociatedGraded C).Additive := by
  let _ : (associatedGraded (C := C)).Additive :=
    associatedGraded_is_additive (C := C)
  infer_instance

theorem finiteAssociatedGraded_piece
    (C : Type u) [Category.{v} C] [Abelian C]
    (A : FiniteFilteredObject C) (p : ℤ) :
    (finiteAssociatedGraded C).obj A p = gradedPiece A.obj p := rfl

theorem finiteAssociatedGraded_direct_sum_description
    (C : Type u) [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : FiniteFilteredObject C) :
    (gradedTotal C).obj ((finiteAssociatedGraded C).obj A) =
      ∐ fun p : ℤ => gradedPiece A.obj p := rfl

private theorem finiteFiltered_not_strict_of_bot_top
    {C : Type u} [Category.{v} C] [Abelian C]
    {A D : FilteredObject C} (k : A ⟶ D) (hk : k.hom ≠ 0)
    (hA0 : A.filtration.obj 0 = ⊥)
    (hD0 : D.filtration.obj 0 = ⊤) :
    ¬ Strict k := by
  intro hs
  have hi := hs 0
  change (Subobject.«exists» k.hom).obj
      (A.filtration.obj 0) =
    (Subobject.«exists» k.hom).obj (⊤ : Subobject A.carrier) ⊓
      D.filtration.obj 0 at hi
  have hexbot : (Subobject.«exists» k.hom).obj
      (⊥ : Subobject A.carrier) = ⊥ := by
    apply le_antisymm
    · exact ((Subobject.existsPullbackAdj k.hom).homEquiv
        (⊥ : Subobject A.carrier) (⊥ : Subobject D.carrier)).symm
        (CategoryTheory.homOfLE bot_le) |>.le
    · exact bot_le
  rw [hA0, hexbot, hD0] at hi
  rw [inf_top_eq] at hi
  have hi' : (⊥ : Subobject D.carrier) =
      (Subobject.«exists» k.hom).obj (⊤ : Subobject A.carrier) := hi
  let I := Subobject.imageFactorisation k.hom
    (⊤ : Subobject A.carrier)
  have hF : Subobject.mk I.F.m =
      (Subobject.«exists» k.hom).obj (⊤ : Subobject A.carrier) := by
    change Subobject.mk
        ((Subobject.«exists» k.hom).obj
          (⊤ : Subobject A.carrier)).arrow = _
    simp
  have hfac' : (Subobject.mk I.F.m).Factors k.hom := by
    change ∃ h : A.carrier ⟶ I.F.I, h ≫ I.F.m = k.hom
    refine ⟨(asIso (⊤ : Subobject A.carrier).arrow).inv ≫ I.F.e, ?_⟩
    rw [Category.assoc, I.F.fac]
    simp
  have hfac :
      ((Subobject.«exists» k.hom).obj
          (⊤ : Subobject A.carrier)).Factors k.hom := by
    rw [← hF]
    exact hfac'
  have hbotfac : (⊥ : Subobject D.carrier).Factors k.hom := by
    rw [hi']
    exact hfac
  exact hk ((Subobject.bot_factors_iff_zero _).mp hbotfac)

private def finiteSingleStepFiltration {C : Type u} [Category.{v} C]
    [HasZeroObject C] {W : C} (U : Subobject W) : DecreasingFiltration C W where
  obj i := if i < 0 then ⊤ else if i = 0 then U else ⊥
  antitone := by
    intro i j hij
    by_cases hi : i < 0
    · simp [hi]
    · by_cases hi0 : i = 0
      · subst i
        by_cases hj : j < 0
        · omega
        · by_cases hj0 : j = 0
          · simp [hj0]
          · simp [hj, hj0]
      · have hipos : 0 < i := by omega
        have hjpos : 0 < j := lt_of_lt_of_le hipos hij
        have hj : ¬ j < 0 := by omega
        have hj0 : ¬ j = 0 := by omega
        simp [hi, hi0, hj, hj0]

private theorem finiteFiltered_diagonal_pullback_bot
    {C : Type u} [Category.{v} C] [Abelian C]
    {V : C} (u d : V ⟶ V ⊞ V) [Mono u] [Mono d]
    (hds : (Subobject.mk d).arrow ≫ biprod.snd =
      (Subobject.underlyingIso d).hom)
    (hus : (Subobject.mk u).arrow ≫ biprod.snd = 0) :
    (Subobject.pullback (Subobject.mk d).arrow).obj
        (Subobject.mk u) = ⊥ := by
  apply le_antisymm
  · apply Subobject.le_of_factors
    apply (Subobject.bot_factors_iff_zero _).2
    have hp := (Subobject.isPullback (Subobject.mk d).arrow
      (Subobject.mk u)).w
    have hp' := congrArg (fun t => t ≫ biprod.snd) hp
    simp only [Category.assoc] at hp'
    rw [hus, hds, comp_zero] at hp'
    apply (cancel_mono (Subobject.underlyingIso d).hom).mp
    calc
      ((Subobject.pullback (Subobject.mk d).arrow).obj
          (Subobject.mk u)).arrow ≫
          (Subobject.underlyingIso d).hom = 0 := hp'.symm
      _ = 0 ≫ (Subobject.underlyingIso d).hom := by simp
  · exact bot_le

private theorem inducedFiltered_isFinite
    {C : Type u} [Category.{u} C] [Abelian C]
    {A : FilteredObject C} (X : Subobject A.carrier)
    (hA : A.IsFinite) : (inducedFilteredObject A X).IsFinite := by
  rcases hA with ⟨n, m, hn, hm⟩
  refine ⟨n, m, ?_, ?_⟩
  · dsimp [inducedFilteredObject, inducedFiltration]
    rw [hn, Subobject.pullback_top]
    rfl
  · dsimp [inducedFilteredObject, inducedFiltration]
    rw [hm]
    apply le_antisymm
    · apply Subobject.le_of_factors
      apply (Subobject.bot_factors_iff_zero _).2
      apply (cancel_mono X.arrow).mp
      rw [← (Subobject.isPullback X.arrow (⊥ : Subobject A.carrier)).w]
      simp
    · exact bot_le

private theorem quotientFiltered_isFinite
    {C : Type u} [Category.{u} C] [Abelian C]
    {A : FilteredObject C} {Y : C} (π : A.carrier ⟶ Y) [Epi π]
    (hA : A.IsFinite) : (quotientFilteredObject A π).IsFinite := by
  rcases hA with ⟨n, m, hn, hm⟩
  refine ⟨n, m, ?_, ?_⟩
  · dsimp [quotientFilteredObject, quotientFiltration]
    rw [hn, exists_top_of_epi]
    rfl
  · dsimp [quotientFilteredObject, quotientFiltration]
    rw [hm]
    apply le_antisymm
    · apply Subobject.le_of_factors
      apply (Subobject.bot_factors_iff_zero _).2
      let I := Subobject.imageFactorisation π (⊥ : Subobject A.carrier)
      let _ : Epi I.F.e :=
        (strongEpi_of_strongEpiMonoFactorisation
          (Abelian.imageStrongEpiMonoFactorisation
            ((⊥ : Subobject A.carrier).arrow ≫ π)) I.isImage).epi
      change I.F.m = 0
      apply (cancel_epi I.F.e).mp
      calc
        I.F.e ≫ I.F.m = (⊥ : Subobject A.carrier).arrow ≫ π := I.F.fac
        _ = I.F.e ≫ 0 := by simp
    · exact bot_le

private theorem finiteFiltered_composite_data
    {C : Type u} [Category.{u} C] [Abelian C]
    {V : C} (d : V ⟶ V ⊞ V) [Mono d]
    (X Y : Subobject (V ⊞ V)) (F : DecreasingFiltration C (V ⊞ V))
    (q : V ⊞ V ⟶ cokernel Y.arrow) [Epi q]
    (r : cokernel Y.arrow ⟶ V)
    (hX : X = Subobject.mk d) (hdiag : d = biprod.lift (𝟙 V) (𝟙 V))
    (hinr : biprod.inr ≫ q = 0)
    (hqr : q ≫ r = biprod.fst)
    (hqinl : biprod.fst ≫ biprod.inl ≫ q = q)
    (hA0 : (inducedFilteredObject { carrier := V ⊞ V, filtration := F } X).filtration.obj 0 = ⊥)
    (hD0 : (quotientFilteredObject { carrier := V ⊞ V, filtration := F } q).filtration.obj 0 = ⊤)
    (hnonzero : (inducedFilteredHom { carrier := V ⊞ V, filtration := F } X).hom ≫
      (quotientFilteredHom { carrier := V ⊞ V, filtration := F } q).hom ≠ 0) :
      IsIso ((inducedFilteredHom { carrier := V ⊞ V, filtration := F } X).hom ≫
        (quotientFilteredHom { carrier := V ⊞ V, filtration := F } q).hom) ∧
        ¬ Strict (inducedFilteredHom { carrier := V ⊞ V, filtration := F } X ≫
          quotientFilteredHom { carrier := V ⊞ V, filtration := F } q) := by
  cases hdiag
  cases hX
  let d : V ⟶ V ⊞ V := biprod.lift (𝟙 V) (𝟙 V)
  letI : Mono d := by
    dsimp [d]
    exact mono_of_mono_fac (biprod.lift_fst _ _)
  have hknotstrict : ¬ Strict
      (inducedFilteredHom { carrier := V ⊞ V, filtration := F } (Subobject.mk d) ≫
        quotientFilteredHom { carrier := V ⊞ V, filtration := F } q) :=
    finiteFiltered_not_strict_of_bot_top
      (inducedFilteredHom { carrier := V ⊞ V, filtration := F } (Subobject.mk d) ≫
        quotientFilteredHom { carrier := V ⊞ V, filtration := F } q)
      hnonzero hA0 hD0
  let ik : cokernel Y.arrow ⟶ (Subobject.mk d : C) :=
    r ≫ (Subobject.underlyingIso d).inv
  have hfst : (Subobject.mk d).arrow ≫ biprod.fst =
      (Subobject.underlyingIso d).hom := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
    simp [d]
  have hdinv : (Subobject.underlyingIso d).inv ≫
      (Subobject.mk d).arrow = d := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    simp [d]
  have hqr_d : ((Subobject.mk d).arrow ≫ q) ≫ r =
      (Subobject.mk d).arrow ≫ biprod.fst := by
    simpa only [Category.assoc] using
      congrArg (fun t => (Subobject.mk d).arrow ≫ t) hqr
  have hqr_tail :
      q ≫ (r ≫ ((Subobject.underlyingIso d).inv ≫
        ((Subobject.mk d).arrow ≫ q))) =
        biprod.fst ≫ ((Subobject.underlyingIso d).inv ≫
          ((Subobject.mk d).arrow ≫ q)) := by
    simpa only [Category.assoc] using
      congrArg (fun t => t ≫
        ((Subobject.underlyingIso d).inv ≫ ((Subobject.mk d).arrow ≫ q))) hqr
  have hdinv_q : (Subobject.underlyingIso d).inv ≫
      ((Subobject.mk d).arrow ≫ q) = d ≫ q := by
    rw [← Category.assoc, hdinv]
  have hqr_d_iso : (((Subobject.mk d).arrow ≫ q) ≫ r) ≫
      (Subobject.underlyingIso d).inv =
        ((Subobject.mk d).arrow ≫ biprod.fst) ≫
          (Subobject.underlyingIso d).inv := by
    exact congrArg (fun t => t ≫ (Subobject.underlyingIso d).inv) hqr_d
  have hfst_iso : ((Subobject.mk d).arrow ≫ biprod.fst) ≫
      (Subobject.underlyingIso d).inv =
        (Subobject.underlyingIso d).hom ≫
          (Subobject.underlyingIso d).inv := by
    exact congrArg (fun t => t ≫ (Subobject.underlyingIso d).inv) hfst
  have hq_d :
      q ≫ (r ≫ ((Subobject.underlyingIso d).inv ≫
        ((Subobject.mk d).arrow ≫ q))) = biprod.fst ≫ (d ≫ q) := by
    calc
      q ≫ (r ≫ ((Subobject.underlyingIso d).inv ≫
          ((Subobject.mk d).arrow ≫ q))) =
          biprod.fst ≫ ((Subobject.underlyingIso d).inv ≫
            ((Subobject.mk d).arrow ≫ q)) := hqr_tail
      _ = biprod.fst ≫ (d ≫ q) := by rw [hdinv_q]
  have hfd : biprod.fst ≫ (d ≫ q) = q := by
    dsimp [d]
    rw [biprod.lift_eq]
    simp only [Category.assoc, Category.id_comp, Preadditive.add_comp,
      Preadditive.comp_add, hqinl, hinr, comp_zero, add_zero]
  have hkisoRaw : IsIso ((Subobject.mk d).arrow ≫ q) := by
    refine ⟨⟨ik, ?_, ?_⟩⟩
    · change ((Subobject.mk d).arrow ≫ q) ≫ ik = 𝟙 _
      dsimp [ik]
      simpa only [Category.assoc] using
        hqr_d_iso.trans (hfst_iso.trans (Iso.hom_inv_id _))
    · apply (cancel_epi q).mp
      simp only [Category.comp_id]
      change q ≫ ik ≫ ((Subobject.mk d).arrow ≫ q) = q
      dsimp [ik]
      simpa only [Category.assoc] using hq_d.trans hfd
  exact ⟨by
    change IsIso ((Subobject.mk d).arrow ≫ q)
    exact hkisoRaw, hknotstrict⟩

private theorem finiteFiltered_failure_filtration_data
    {C : Type u} [Category.{u} C] [Abelian C]
    (S : @StrictCompositionFailure C inferInstance inferInstance)
    (u v d : S.A.carrier ⟶ S.A.carrier ⊞ S.A.carrier)
    [Mono u] [Mono v] [Mono d]
    (U X Y : Subobject (S.A.carrier ⊞ S.A.carrier))
    (F : DecreasingFiltration C (S.A.carrier ⊞ S.A.carrier))
    (q : S.A.carrier ⊞ S.A.carrier ⟶ cokernel Y.arrow) [Epi q]
    (hu : u = biprod.inl) (hv : v = biprod.inr)
    (hdiag : d = biprod.lift (𝟙 S.A.carrier) (𝟙 S.A.carrier))
    (hU : U = Subobject.mk u) (hX : X = Subobject.mk d)
    (hY : Y = Subobject.mk v)
    (hF : F = finiteSingleStepFiltration U) (hvr : v ≫ q = 0) :
      (inducedFilteredObject
          { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F } X).filtration.obj 0 = ⊥ ∧
        (quotientFilteredObject
          { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F } q).filtration.obj 0 =
          (⊤ : Subobject (cokernel Y.arrow)) ∧
        biprod.fst ≫ biprod.inl ≫ q = q := by
  cases hu
  cases hv
  cases hdiag
  cases hU
  cases hY
  let p : S.A.carrier ⊞ S.A.carrier ⟶
      Subobject.mk (biprod.inl : S.A.carrier ⟶ S.A.carrier ⊞ S.A.carrier) :=
    biprod.fst ≫ (Subobject.underlyingIso
      (biprod.inl : S.A.carrier ⟶ S.A.carrier ⊞ S.A.carrier)).inv
  have hfactor : q = p ≫ ((Subobject.mk biprod.inl).arrow ≫ q) := by
    calc
      q = 𝟙 _ ≫ q := by simp
      _ = (biprod.fst ≫ biprod.inl +
          biprod.snd ≫ biprod.inr) ≫ q := by rw [biprod.total]
      _ = biprod.fst ≫ biprod.inl ≫ q +
          biprod.snd ≫ biprod.inr ≫ q := by
        rw [Preadditive.add_comp, Category.assoc, Category.assoc]
      _ = biprod.fst ≫ biprod.inl ≫ q := by
        rw [hvr, comp_zero, add_zero]
      _ = p ≫ ((Subobject.mk biprod.inl).arrow ≫ q) := by
        simp [p, Category.assoc]
  let : Epi ((Subobject.mk biprod.inl).arrow ≫ q) :=
    epi_of_epi_fac hfactor.symm
  have hqu : (Subobject.«exists» q).obj (Subobject.mk biprod.inl) =
      (⊤ : Subobject (cokernel
        (Subobject.mk (biprod.inr : S.A.carrier ⟶ S.A.carrier ⊞ S.A.carrier)).arrow)) := by
    apply (Subobject.isIso_arrow_iff_eq_top _).mp
    let I := Subobject.imageFactorisation q (Subobject.mk biprod.inl)
    let _ : Epi I.F.m := epi_of_epi_fac I.F.fac
    change IsIso I.F.m
    exact isIso_of_mono_of_epi I.F.m
  let B₀ : FilteredObject C :=
    { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F }
  have hB0 : B₀.filtration.obj 0 = Subobject.mk biprod.inl := by
    change F.obj 0 = Subobject.mk biprod.inl
    rw [hF]
    simp [finiteSingleStepFiltration]
  have hA0 :
      (inducedFilteredObject
          { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F } X).filtration.obj 0 =
        ⊥ := by
    rw [hF, hX]
    change (Subobject.pullback (Subobject.mk
      (biprod.lift (𝟙 S.A.carrier) (𝟙 S.A.carrier))).arrow).obj
        (Subobject.mk biprod.inl) = ⊥
    apply finiteFiltered_diagonal_pullback_bot
    · rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
      simp
    · rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
      simp
  have hD0 :
      (quotientFilteredObject
          { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F } q).filtration.obj 0 =
        (⊤ : Subobject (cokernel
          (Subobject.mk (biprod.inr : S.A.carrier ⟶ S.A.carrier ⊞ S.A.carrier)).arrow)) := by
    change (Subobject.«exists» q).obj (F.obj 0) = _
    rw [hF]
    simp [finiteSingleStepFiltration, hqu]
  exact ⟨hA0, hD0, by simpa [p, Category.assoc] using hfactor.symm⟩

private theorem finiteFiltered_failure_composite_nonzero
    {C : Type u} [Category.{u} C] [Abelian C]
    (S : @StrictCompositionFailure C inferInstance inferInstance)
    (d : S.A.carrier ⟶ S.A.carrier ⊞ S.A.carrier) [Mono d]
    (X Y : Subobject (S.A.carrier ⊞ S.A.carrier))
    (q : S.A.carrier ⊞ S.A.carrier ⟶ cokernel Y.arrow) [Epi q]
    (r : cokernel Y.arrow ⟶ S.A.carrier)
    (hX : X = Subobject.mk d)
    (hdiag : d = biprod.lift (𝟙 S.A.carrier) (𝟙 S.A.carrier))
    (hqr : q ≫ r = biprod.fst) : X.arrow ≫ q ≠ 0 := by
  subst X
  have hV : (𝟙 S.A.carrier : S.A.carrier ⟶ S.A.carrier) ≠ 0 := by
    intro h
    apply S.composite_nonzero
    rw [← Category.id_comp (S.f.hom ≫ S.g.hom), h]
    simp
  have hid : (Subobject.underlyingIso d).inv ≫ (Subobject.mk d).arrow ≫ q ≫ r =
      𝟙 S.A.carrier := by
    rw [hqr]
    rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    simp [hdiag]
  intro hz
  apply hV
  rw [← hid]
  simpa only [Category.assoc, zero_comp, comp_zero] using
    congrArg (fun t => (Subobject.underlyingIso d).inv ≫ t ≫ r) hz

private theorem finiteFiltered_failure_tail
    {C : Type u} [Category.{u} C] [Abelian C]
    {V : C} (d : V ⟶ V ⊞ V) [Mono d]
    (X Y : Subobject (V ⊞ V)) (F : DecreasingFiltration C (V ⊞ V))
    (q : V ⊞ V ⟶ cokernel Y.arrow) [Epi q]
    (r : cokernel Y.arrow ⟶ V)
    (hX : X = Subobject.mk d) (hdiag : d = biprod.lift (𝟙 V) (𝟙 V))
    (hinr : biprod.inr ≫ q = 0) (hqr : q ≫ r = biprod.fst)
    (hqinl : biprod.fst ≫ biprod.inl ≫ q = q)
    (hA0 : (inducedFilteredObject { carrier := V ⊞ V, filtration := F } X).filtration.obj 0 = ⊥)
    (hD0 : (quotientFilteredObject { carrier := V ⊞ V, filtration := F } q).filtration.obj 0 = ⊤)
    (hnonzero : (inducedFilteredHom { carrier := V ⊞ V, filtration := F } X).hom ≫
      (quotientFilteredHom { carrier := V ⊞ V, filtration := F } q).hom ≠ 0) :
      IsIso ((inducedFilteredHom { carrier := V ⊞ V, filtration := F } X).hom ≫
        (quotientFilteredHom { carrier := V ⊞ V, filtration := F } q).hom) ∧
        ¬ Strict (inducedFilteredHom { carrier := V ⊞ V, filtration := F } X ≫
          quotientFilteredHom { carrier := V ⊞ V, filtration := F } q) := by
  exact finiteFiltered_composite_data d X Y F q r
    hX hdiag hinr hqr hqinl hA0 hD0 hnonzero

private structure FiniteFilteredFailureData
    (C : Type u) [Category.{u} C] [Abelian C] where
  A : FilteredObject C
  B : FilteredObject C
  D : FilteredObject C
  f : A ⟶ B
  g : B ⟶ D
  A_isFinite : A.IsFinite
  B_isFinite : B.IsFinite
  D_isFinite : D.IsFinite
  f_strict : Strict f
  g_strict : Strict g
  composite_isIso : IsIso (f.hom ≫ g.hom)
  composite_nonzero : f.hom ≫ g.hom ≠ 0
  composite_not_strict : ¬ Strict (f ≫ g)

private abbrev finiteFilteredMiddle
    (C : Type u) [Category.{u} C] [Abelian C]
    (V : C) (F : DecreasingFiltration C (V ⊞ V)) : FilteredObject C :=
  { carrier := V ⊞ V, filtration := F }

private theorem finiteFiltered_failure_data_of_filtration
    {C : Type u} [Category.{u} C] [Abelian C]
    {V : C}
    (X Y : Subobject (V ⊞ V)) (F : DecreasingFiltration C (V ⊞ V))
    (q : V ⊞ V ⟶ cokernel Y.arrow) [Epi q]
    (hBfin : ({ carrier := V ⊞ V, filtration := F } : FilteredObject C).IsFinite)
    (hAfin : (inducedFilteredObject { carrier := V ⊞ V, filtration := F } X).IsFinite)
    (hDfin : (quotientFilteredObject { carrier := V ⊞ V, filtration := F } q).IsFinite)
    (hfstrict : Strict (inducedFilteredHom { carrier := V ⊞ V, filtration := F } X))
    (hgstrict : Strict (quotientFilteredHom { carrier := V ⊞ V, filtration := F } q))
    (htail : IsIso ((inducedFilteredHom { carrier := V ⊞ V, filtration := F } X).hom ≫
        (quotientFilteredHom { carrier := V ⊞ V, filtration := F } q).hom) ∧
      ¬ Strict (inducedFilteredHom { carrier := V ⊞ V, filtration := F } X ≫
        quotientFilteredHom { carrier := V ⊞ V, filtration := F } q))
    (hnonzero : (inducedFilteredHom { carrier := V ⊞ V, filtration := F } X).hom ≫
      (quotientFilteredHom { carrier := V ⊞ V, filtration := F } q).hom ≠ 0) :
      ∃ (A B D : FilteredObject C) (f : A ⟶ B) (g : B ⟶ D),
        A.IsFinite ∧ B.IsFinite ∧ D.IsFinite ∧ Strict f ∧ Strict g ∧
          IsIso (f.hom ≫ g.hom) ∧ f.hom ≫ g.hom ≠ 0 ∧ ¬ Strict (f ≫ g) := by
  exact ⟨inducedFilteredObject { carrier := V ⊞ V, filtration := F } X,
    { carrier := V ⊞ V, filtration := F },
    quotientFilteredObject { carrier := V ⊞ V, filtration := F } q,
    inducedFilteredHom { carrier := V ⊞ V, filtration := F } X,
    quotientFilteredHom { carrier := V ⊞ V, filtration := F } q,
    hAfin, hBfin, hDfin, hfstrict, hgstrict, htail.1, hnonzero, htail.2⟩

private theorem finiteFiltered_failure_data_from_setup
    {C : Type u} [Category.{u} C] [Abelian C]
    (S : @StrictCompositionFailure C inferInstance inferInstance)
    (u v d : S.A.carrier ⟶ S.A.carrier ⊞ S.A.carrier)
    [Mono u] [Mono v] [Mono d]
    (U X Y : Subobject (S.A.carrier ⊞ S.A.carrier))
    (F : DecreasingFiltration C (S.A.carrier ⊞ S.A.carrier))
    (q : S.A.carrier ⊞ S.A.carrier ⟶ cokernel Y.arrow) [Epi q]
    (hq : q = cokernel.π Y.arrow)
    (hBfin : ({ carrier := S.A.carrier ⊞ S.A.carrier, filtration := F } :
      FilteredObject C).IsFinite)
    (hu : u = biprod.inl) (hv : v = biprod.inr)
    (hdiag : d = biprod.lift (𝟙 S.A.carrier) (𝟙 S.A.carrier))
    (hU : U = Subobject.mk u) (hX : X = Subobject.mk d)
    (hY : Y = Subobject.mk v)
    (hF : F = finiteSingleStepFiltration U) (hvr : v ≫ q = 0) :
      ∃ (A B D : FilteredObject C) (f : A ⟶ B) (g : B ⟶ D),
        A.IsFinite ∧ B.IsFinite ∧ D.IsFinite ∧ Strict f ∧ Strict g ∧
          IsIso (f.hom ≫ g.hom) ∧ f.hom ≫ g.hom ≠ 0 ∧ ¬ Strict (f ≫ g) := by
  cases hv
  have hfil := finiteFiltered_failure_filtration_data S u biprod.inr d U X Y F q
    hu rfl hdiag hU hX hY hF hvr
  have hYarrow : Y.arrow ≫ biprod.fst = 0 := by
    rw [hY]
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
    simp
  let r : cokernel Y.arrow ⟶ S.A.carrier :=
    cokernel.desc Y.arrow biprod.fst hYarrow
  have hqr : q ≫ r = biprod.fst := by
    rw [hq]
    dsimp [r]
    exact cokernel.π_desc _ _ _
  have hnonzero : X.arrow ≫ q ≠ 0 :=
    finiteFiltered_failure_composite_nonzero S d X Y q r hX hdiag hqr
  have hAfin0 := inducedFiltered_isFinite (C := C)
    (A := { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F }) X hBfin
  have hAfin :
      (inducedFilteredObject
        { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F } X).IsFinite := hAfin0
  have hDfin0 := quotientFiltered_isFinite (C := C)
    (A := { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F }) q hBfin
  have hDfin :
      (quotientFilteredObject
        { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F } q).IsFinite := hDfin0
  have hfstrict : Strict (inducedFilteredHom
      { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F } X) :=
    strict_induced_iff
      (A := { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F }) X
  have hgstrict : Strict (quotientFilteredHom
      { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F } q) :=
    strict_quotient_iff
      (A := { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F }) (π := q)
  have htail :
      IsIso ((inducedFilteredHom
        { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F } X).hom ≫
        (quotientFilteredHom
          { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F } q).hom) ∧
      ¬ Strict (inducedFilteredHom
        { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F } X ≫
        quotientFilteredHom
          { carrier := S.A.carrier ⊞ S.A.carrier, filtration := F } q) :=
    finiteFiltered_failure_tail d X Y F q r
      hX hdiag hvr hqr hfil.2.2 hfil.1 hfil.2.1 (by
        change X.arrow ≫ q ≠ 0
        exact hnonzero)
  exact finiteFiltered_failure_data_of_filtration X Y F q hBfin hAfin hDfin
    hfstrict hgstrict htail (by
      change X.arrow ≫ q ≠ 0
      exact hnonzero)

private theorem finiteFiltered_failure_data
    {C : Type u} [Category.{u} C] [Abelian C]
    (S : @StrictCompositionFailure C inferInstance inferInstance) :
      ∃ (A B D : FilteredObject C) (f : A ⟶ B) (g : B ⟶ D),
        A.IsFinite ∧ B.IsFinite ∧ D.IsFinite ∧ Strict f ∧ Strict g ∧
          IsIso (f.hom ≫ g.hom) ∧ f.hom ≫ g.hom ≠ 0 ∧ ¬ Strict (f ≫ g) := by
  let V : C := S.A.carrier
  let W : C := V ⊞ V
  let u : V ⟶ W := biprod.inl
  let v : V ⟶ W := biprod.inr
  let d : V ⟶ W := biprod.lift (𝟙 V) (𝟙 V)
  letI : Mono u := by
    dsimp [u]
    exact mono_of_mono_fac biprod.inl_fst
  letI : Mono v := by
    dsimp [v]
    exact mono_of_mono_fac biprod.inr_snd
  letI : Mono d := by
    dsimp [d]
    exact mono_of_mono_fac (biprod.lift_fst _ _)
  let U : Subobject W := Subobject.mk u
  let X : Subobject W := Subobject.mk d
  let Y : Subobject W := Subobject.mk v
  let F : DecreasingFiltration C W := finiteSingleStepFiltration U
  let B₀ : FilteredObject C := { carrier := W, filtration := F }
  let A₀ : FilteredObject C := inducedFilteredObject B₀ X
  let q : W ⟶ cokernel Y.arrow := cokernel.π Y.arrow
  letI : Epi q := by
    dsimp [q]
    infer_instance
  let D₀ : FilteredObject C := quotientFilteredObject B₀ q
  have hBfin : B₀.IsFinite := by
    refine ⟨-1, 1, ?_, ?_⟩ <;> simp [B₀, F, finiteSingleStepFiltration]
  have hvr : v ≫ q = 0 := by
    apply (cancel_epi (Subobject.underlyingIso v).hom).mp
    dsimp [q]
    rw [← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
    simpa [Y] using (cokernel.condition Y.arrow)
  exact finiteFiltered_failure_data_from_setup S u v d U X Y F q rfl hBfin
    rfl rfl rfl rfl rfl rfl rfl hvr

private theorem finiteFiltered_not_abelian_of_failure
    {C : Type u} [Category.{u} C] [Abelian C]
    (S : @StrictCompositionFailure C inferInstance inferInstance) :
      ¬ Nonempty (Abelian (FiniteFilteredObject C)) := by
  obtain ⟨A₀, B₀, D₀, f₀, g₀, hAfin, hBfin, hDfin, hfstrict, hgstrict,
      hkiso, hnonzero, hknotstrict⟩ := finiteFiltered_failure_data S
  rintro ⟨hAb⟩
  letI : Abelian (FiniteFilteredObject C) := hAb
  let A' : FiniteFilteredObject C :=
    ⟨A₀, show finiteFilteredProperty C A₀ from hAfin⟩
  let B' : FiniteFilteredObject C :=
    ⟨B₀, show finiteFilteredProperty C B₀ from hBfin⟩
  let D' : FiniteFilteredObject C :=
    ⟨D₀, show finiteFilteredProperty C D₀ from hDfin⟩
  let f' : A' ⟶ B' := (finiteFilteredProperty C).homMk f₀
  let g' : B' ⟶ D' := (finiteFilteredProperty C).homMk g₀
  let k₀ : A₀ ⟶ D₀ := f₀ ≫ g₀
  let k' : A' ⟶ D' := f' ≫ g'
  letI : Mono k'.hom.hom := by
    dsimp [k', f', g']
    letI : IsIso (f₀.hom ≫ g₀.hom) := hkiso
    infer_instance
  letI : Epi k'.hom.hom := by
    dsimp [k', f', g']
    letI : IsIso (f₀.hom ≫ g₀.hom) := hkiso
    infer_instance
  letI : Mono k'.hom := by
    constructor
    intro Z a b hab
    apply FilteredHom.ext
    apply (cancel_mono k'.hom.hom).mp
    exact congrArg (fun z => z.hom) hab
  letI : Epi k'.hom := by
    constructor
    intro Z a b hab
    apply FilteredHom.ext
    apply (cancel_epi k'.hom.hom).mp
    exact congrArg (fun z => z.hom) hab
  letI : Mono k' := by
    constructor
    intro Z' a b hab
    apply (finiteFilteredProperty C).hom_ext
    apply (cancel_mono k'.hom).mp
    exact congrArg (fun z => z.hom) hab
  letI : Epi k' := by
    constructor
    intro Z' a b hab
    apply (finiteFilteredProperty C).hom_ext
    apply (cancel_epi k'.hom).mp
    exact congrArg (fun z => z.hom) hab
  letI : HasZeroMorphisms (FiniteFilteredObject C) :=
    @CategoryTheory.Preadditive.preadditiveHasZeroMorphisms _ _ hAb.toPreadditive
  letI : IsNormalEpiCategory (FiniteFilteredObject C) := hAb.toIsNormalEpiCategory
  letI : IsRegularEpiCategory (FiniteFilteredObject C) :=
    regularEpiCategoryOfNormalEpiCategory
  letI : StrongEpiCategory (FiniteFilteredObject C) :=
    strongEpiCategory_of_regularEpiCategory
  letI : Balanced (FiniteFilteredObject C) :=
    CategoryTheory.balanced_of_strongEpiCategory
  letI : IsIso k' := isIso_of_mono_of_epi k'
  have hkfull : IsIso k₀ := by
    change IsIso ((finiteFilteredInclusion C).map k')
    infer_instance
  exact hknotstrict ((strict_iff_isIso_of_hom_iso k₀ hkiso).2 hkfull)

/-- The finite filtered category is not abelian in general. -/
theorem finiteFilteredCategory_not_abelian :
    ∃ (C : Type u) (_ : Category.{u} C) (_ : Abelian C),
      ¬ Nonempty (Abelian (FiniteFilteredObject C)) := by
  obtain ⟨C, hcat, hAbC, ⟨S⟩⟩ :=
    Formalization.Books.Homology.Unit19.exists_strict_composition_failure
  refine ⟨C, hcat, hAbC, ?_⟩
  let : Category.{u} C := hcat
  let : Abelian C := hAbC
  exact finiteFiltered_not_abelian_of_failure S

/-! ## The homotopy-category functors and filtered acyclicity -/

abbrev FilteredComplex
    (C : Type u) [Category.{v} C] [Abelian C] :=
  Comp (FiniteFilteredObject C)

abbrev FilteredHomotopyCategory
    (C : Type u) [Category.{v} C] [Abelian C] :=
  HomotopyCategory (FiniteFilteredObject C) (ComplexShape.up ℤ)

theorem filteredHomotopyCategory_additiveCategory_exists
    (C : Type u) [Category.{v} C] [Abelian C] :
    Nonempty (AdditiveCategory (FilteredHomotopyCategory C)) := by
  exact ⟨{ toPreadditive := inferInstance, toHasFiniteProducts := inferInstance }⟩

noncomputable instance filteredHomotopyCategory_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (FilteredHomotopyCategory C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts :=
      (Classical.choice (filteredHomotopyCategory_additiveCategory_exists C)).toHasFiniteProducts }

/-- The homotopy functor induced by the `p`th graded piece. -/
noncomputable abbrev filteredGradedPieceHomotopyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
    FilteredHomotopyCategory C ⥤
      HomotopyCategory C (ComplexShape.up ℤ) :=
  (finiteGradedPieceFunctor C p).mapHomotopyCategory (ComplexShape.up ℤ)

/-- The homotopy functor induced by the associated graded object. -/
noncomputable abbrev filteredAssociatedGradedHomotopyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredHomotopyCategory C ⥤
      HomotopyCategory (GradedObject ℤ C) (ComplexShape.up ℤ) :=
  (finiteAssociatedGraded C).mapHomotopyCategory (ComplexShape.up ℤ)

/-- The homotopy functor induced by forgetting the filtration. -/
noncomputable abbrev filteredForgetfulHomotopyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredHomotopyCategory C ⥤
      HomotopyCategory C (ComplexShape.up ℤ) :=
  (finiteForgetful C).mapHomotopyCategory (ComplexShape.up ℤ)

theorem filteredGradedPieceHomotopyFunctor_is_exact
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
    (filteredGradedPieceHomotopyFunctor C p).IsTriangulated := by
  exact HomotopyCategory.instIsTriangulatedIntUpMapHomotopyCategory
    (finiteGradedPieceFunctor C p)

theorem filteredAssociatedGradedHomotopyFunctor_is_exact
    (C : Type u) [Category.{v} C] [Abelian C] :
    (filteredAssociatedGradedHomotopyFunctor C).IsTriangulated := by
  exact HomotopyCategory.instIsTriangulatedIntUpMapHomotopyCategory
    (finiteAssociatedGraded C)

theorem filteredForgetfulHomotopyFunctor_is_exact
    (C : Type u) [Category.{v} C] [Abelian C] :
    (filteredForgetfulHomotopyFunctor C).IsTriangulated := by
  exact HomotopyCategory.instIsTriangulatedIntUpMapHomotopyCategory
    (finiteForgetful C)

/-- The degree-`n` homology of the associated graded complex. -/
noncomputable abbrev filteredGradedHomologyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (n : ℤ) :
    FilteredHomotopyCategory C ⥤ GradedObject ℤ C :=
  filteredAssociatedGradedHomotopyFunctor C ⋙
    HomotopyCategory.homologyFunctor (GradedObject ℤ C)
      (ComplexShape.up ℤ) n

/-- The degree-`n` homology of the `p`th graded-piece complex. -/
noncomputable abbrev filteredGradedPieceHomologyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (p n : ℤ) :
    FilteredHomotopyCategory C ⥤ C :=
  filteredGradedPieceHomotopyFunctor C p ⋙
    HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n

/-- The degree-`n` homology after forgetting the filtration. -/
noncomputable abbrev filteredForgetfulHomologyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (n : ℤ) :
    FilteredHomotopyCategory C ⥤ C :=
  filteredForgetfulHomotopyFunctor C ⋙
    HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n

/-- The source's filtered-acyclic object property. -/
def filteredAcyclic
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (FilteredHomotopyCategory C) :=
  fun K => ∀ n : ℤ, IsZero ((filteredGradedHomologyFunctor C n).obj K)

/-- The quasi-isomorphism property on the `p`th graded-piece complex. -/
def filteredGradedPieceQuasiIso
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
    MorphismProperty (FilteredHomotopyCategory C) :=
  (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).inverseImage
    (filteredGradedPieceHomotopyFunctor C p)

/-- The source's filtered quasi-isomorphism property. -/
def filteredQuasiIso
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (FilteredHomotopyCategory C) :=
    (HomotopyCategory.quasiIso (GradedObject ℤ C) (ComplexShape.up ℤ)).inverseImage
    (filteredAssociatedGradedHomotopyFunctor C)

private noncomputable def finiteGradedPieceFunctor_iso
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
  finiteGradedPieceFunctor C p ≅
      finiteAssociatedGraded C ⋙ GradedObject.eval p := by
  let hAbelianGraded : Abelian (GradedObject ℤ C) := by infer_instance
  letI := hAbelianGraded
  let : Preadditive (ℤ → C) :=
    Preadditive.ofFullyFaithful
      (piEquivalenceFunctorDiscrete ℤ C).fullyFaithfulFunctor
  let : (piEquivalenceFunctorDiscrete ℤ C).functor.Additive :=
    (piEquivalenceFunctorDiscrete ℤ C).fullyFaithfulFunctor.additive_ofFullyFaithful
  letI : (GradedObject.eval (C := C) p).Additive := by
    exact Functor.additive_of_iso
      (piEquivalenceFunctorDiscreteCompEvaluationIso C p)
  have hobj : ∀ A : FiniteFilteredObject C,
      (finiteGradedPieceFunctor C p).obj A =
        (finiteAssociatedGraded C ⋙ GradedObject.eval p).obj A := by
    intro A
    rfl
  refine NatIso.ofComponents (fun A => eqToIso (hobj A)) ?_
  intro A B f
  have hmap :
      (finiteGradedPieceFunctor C p).map f =
        (finiteAssociatedGraded C ⋙ GradedObject.eval p).map f := by
    rfl
  apply eq_of_heq
  simpa only [eqToIso.hom] using
    (CategoryTheory.comp_eqToHom_heq _ (hobj B)).trans
      ((heq_of_eq hmap).trans
        (CategoryTheory.eqToHom_comp_heq _ (hobj A)).symm)

private noncomputable instance gradedObject_eval_additive
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
    (GradedObject.eval (C := C) p).Additive := by
  let : Preadditive (ℤ → C) :=
    Preadditive.ofFullyFaithful
      (piEquivalenceFunctorDiscrete ℤ C).fullyFaithfulFunctor
  let : (piEquivalenceFunctorDiscrete ℤ C).functor.Additive :=
    (piEquivalenceFunctorDiscrete ℤ C).fullyFaithfulFunctor.additive_ofFullyFaithful
  exact Functor.additive_of_iso
    (piEquivalenceFunctorDiscreteCompEvaluationIso C p)

private noncomputable def filteredGradedHomology_component_iso
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredHomotopyCategory C) (p n : ℤ) :
    (filteredGradedPieceHomologyFunctor C p n).obj K ≅
      ((filteredGradedHomologyFunctor C n).obj K) p := by
  let hAbelianGraded : Abelian (GradedObject ℤ C) := by
    infer_instance
  letI := hAbelianGraded
  letI : Preadditive (ℤ → C) :=
    Preadditive.ofFullyFaithful
      (piEquivalenceFunctorDiscrete ℤ C).fullyFaithfulFunctor
  let hZeroGraded : HasZeroMorphisms (GradedObject ℤ C) :=
    Preadditive.preadditiveHasZeroMorphisms
  letI := hZeroGraded
  let hHomologyGraded : CategoryWithHomology (GradedObject ℤ C) :=
    CategoryTheory.categoryWithHomology_of_abelian
  letI := hHomologyGraded
  let E : GradedObject ℤ C ⥤ C := (piEquivalenceFunctorDiscrete ℤ C).functor ⋙
    (evaluation (Discrete ℤ) C).obj ⟨p⟩
  let hEZero : E.PreservesZeroMorphisms := by
    infer_instance
  letI := hEZero
  let hEHomology : E.PreservesHomology := by
    infer_instance
  letI := hEHomology
  let Q := (filteredAssociatedGradedHomotopyFunctor C).obj K
  let e := (ShortComplex.homologyFunctorIso (F := E)).app (Q.as.sc n)
  let P := (filteredGradedPieceHomotopyFunctor C p).obj K
  let eC := (HomotopyCategory.homologyFunctorFactors C
    (ComplexShape.up ℤ) n).app P.as
  let eG := (HomotopyCategory.homologyFunctorFactors (GradedObject ℤ C)
    (ComplexShape.up ℤ) n).app Q.as
  have hP : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      P.as = P := by
    cases P
    rfl
  have hQ : (HomotopyCategory.quotient (GradedObject ℤ C)
      (ComplexShape.up ℤ)).obj Q.as = Q := by
    cases Q
    rfl
  simpa [Q, E, filteredAssociatedGradedHomotopyFunctor,
    filteredGradedPieceHomotopyFunctor, P, hP, hQ] using
    ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).mapIso
        (eqToIso hP.symm) ≪≫ eC ≪≫ e ≪≫ (E.mapIso eG).symm ≪≫
    E.mapIso ((HomotopyCategory.homologyFunctor (GradedObject ℤ C)
        (ComplexShape.up ℤ) n).mapIso (eqToIso hQ)))

private noncomputable def filteredGradedHomology_component_iso_aux
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredHomotopyCategory C) (p n : ℤ)
    (hP : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      ((filteredGradedPieceHomotopyFunctor C p).obj K).as =
      (filteredGradedPieceHomotopyFunctor C p).obj K)
    (hQ : (HomotopyCategory.quotient (GradedObject ℤ C)
      (ComplexShape.up ℤ)).obj
        ((filteredAssociatedGradedHomotopyFunctor C).obj K).as =
      (filteredAssociatedGradedHomotopyFunctor C).obj K) :
    (filteredGradedPieceHomologyFunctor C p n).obj K ≅
      ((filteredGradedHomologyFunctor C n).obj K) p := by
  let hAbelianGraded : Abelian (GradedObject ℤ C) := by
    infer_instance
  letI := hAbelianGraded
  let hZeroGraded : HasZeroMorphisms (GradedObject ℤ C) :=
    Preadditive.preadditiveHasZeroMorphisms
  letI := hZeroGraded
  let hHomologyGraded : CategoryWithHomology (GradedObject ℤ C) :=
    CategoryTheory.categoryWithHomology_of_abelian
  letI := hHomologyGraded
  let E : GradedObject ℤ C ⥤ C := (piEquivalenceFunctorDiscrete ℤ C).functor ⋙
    (evaluation (Discrete ℤ) C).obj ⟨p⟩
  let hEZero : E.PreservesZeroMorphisms := by
    infer_instance
  letI := hEZero
  let hEHomology : E.PreservesHomology := by
    infer_instance
  letI := hEHomology
  let e := (ShortComplex.homologyFunctorIso (F := E)).app
    (((filteredAssociatedGradedHomotopyFunctor C).obj K).as.sc n)
  let eC := (HomotopyCategory.homologyFunctorFactors C
    (ComplexShape.up ℤ) n).app
      ((filteredGradedPieceHomotopyFunctor C p).obj K).as
  let eG := (HomotopyCategory.homologyFunctorFactors (GradedObject ℤ C)
    (ComplexShape.up ℤ) n).app
      ((filteredAssociatedGradedHomotopyFunctor C).obj K).as
  exact
    (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).mapIso
        (eqToIso hP.symm) ≪≫ eC ≪≫ e ≪≫ (E.mapIso eG).symm ≪≫
      E.mapIso ((HomotopyCategory.homologyFunctor (GradedObject ℤ C)
        (ComplexShape.up ℤ) n).mapIso (eqToIso hQ))

/-
private noncomputable def filteredGradedHomology_eval_natIso
    (C : Type u) [Category.{v} C] [Abelian C] (p n : ℤ) :
    (GradedObject.eval p).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n ≅
      HomotopyCategory.homologyFunctor (GradedObject ℤ C)
          (ComplexShape.up ℤ) n ⋙ GradedObject.eval p := by
  let hAbelianGraded : Abelian (GradedObject ℤ C) := by
    infer_instance
  letI := hAbelianGraded
  letI : Preadditive (ℤ → C) :=
    Preadditive.ofFullyFaithful
      (piEquivalenceFunctorDiscrete ℤ C).fullyFaithfulFunctor
  let hZeroGraded : HasZeroMorphisms (GradedObject ℤ C) :=
    Preadditive.preadditiveHasZeroMorphisms
  letI := hZeroGraded
  let hHomologyGraded : CategoryWithHomology (GradedObject ℤ C) :=
    CategoryTheory.categoryWithHomology_of_abelian
  letI := hHomologyGraded
  letI : (piEquivalenceFunctorDiscrete ℤ C).functor.Additive :=
    (piEquivalenceFunctorDiscrete ℤ C).fullyFaithfulFunctor.additive_ofFullyFaithful
  letI : (GradedObject.eval (C := C) p).Additive := by
    exact Functor.additive_of_iso
      (piEquivalenceFunctorDiscreteCompEvaluationIso C p)
  let E : GradedObject ℤ C ⥤ C := (piEquivalenceFunctorDiscrete ℤ C).functor ⋙
    (evaluation (Discrete ℤ) C).obj ⟨p⟩
  let hEZero : E.PreservesZeroMorphisms := by
    infer_instance
  letI := hEZero
  let hEHomology : E.PreservesHomology := by
    infer_instance
  letI := hEHomology
  refine NatIso.ofComponents (fun Q => ?_) ?_
  · let P := ((GradedObject.eval p).mapHomotopyCategory (ComplexShape.up ℤ)).obj Q
    let hP : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P.as = P := by
      cases P
      rfl
    let hQ : (HomotopyCategory.quotient (GradedObject ℤ C)
        (ComplexShape.up ℤ)).obj Q.as = Q := by
      cases Q
      rfl
    let e := (ShortComplex.homologyFunctorIso (F := E)).app (Q.as.sc n)
    let eC := (HomotopyCategory.homologyFunctorFactors C
      (ComplexShape.up ℤ) n).app P.as
    let eG := (HomotopyCategory.homologyFunctorFactors (GradedObject ℤ C)
      (ComplexShape.up ℤ) n).app Q.as
    exact (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).mapIso
        (eqToIso hP.symm) ≪≫ eC ≪≫ e ≪≫ (E.mapIso eG).symm ≪≫
      E.mapIso ((HomotopyCategory.homologyFunctor (GradedObject ℤ C)
        (ComplexShape.up ℤ) n).mapIso (eqToIso hQ))
  · intro Q R f
    induction f using CategoryTheory.Quotient.induction with
  | @h X Y f =>
      dsimp
      rw [Functor.mapHomotopyCategory_map]
      simp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom, Category.assoc]

private noncomputable def filteredGradedHomology_component_natIso
    (C : Type u) [Category.{v} C] [Abelian C] (p n : ℤ) :
    filteredGradedPieceHomologyFunctor C p n ≅
      filteredGradedHomologyFunctor C n ⋙ GradedObject.eval p := by
  let hP : ∀ K : FilteredHomotopyCategory C,
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          ((filteredGradedPieceHomotopyFunctor C p).obj K).as =
        (filteredGradedPieceHomotopyFunctor C p).obj K := by
    intro K
    cases K
    rfl
  let hQ : ∀ K : FilteredHomotopyCategory C,
      (HomotopyCategory.quotient (GradedObject ℤ C)
        (ComplexShape.up ℤ)).obj
          ((filteredAssociatedGradedHomotopyFunctor C).obj K).as =
        (filteredAssociatedGradedHomotopyFunctor C).obj K := by
    intro K
    cases K
    rfl
  refine NatIso.ofComponents
    (fun K => by
      change (filteredGradedPieceHomologyFunctor C p n).obj K ≅
        ((filteredGradedHomologyFunctor C n).obj K) p
      exact filteredGradedHomology_component_iso_aux C K p n (hP K) (hQ K)) ?_
  intro K L f
  let hAbelianGraded : Abelian (GradedObject ℤ C) := by
    infer_instance
  letI := hAbelianGraded
  let hZeroGraded : HasZeroMorphisms (GradedObject ℤ C) :=
    Preadditive.preadditiveHasZeroMorphisms
  letI := hZeroGraded
  let hHomologyGraded : CategoryWithHomology (GradedObject ℤ C) :=
    CategoryTheory.categoryWithHomology_of_abelian
  letI := hHomologyGraded
  let E : GradedObject ℤ C ⥤ C := (piEquivalenceFunctorDiscrete ℤ C).functor ⋙
    (evaluation (Discrete ℤ) C).obj ⟨p⟩
  let hEZero : E.PreservesZeroMorphisms := by
    infer_instance
  letI := hEZero
  let hEHomology : E.PreservesHomology := by
    infer_instance
  letI := hEHomology
  have hC := (HomotopyCategory.homologyFunctorFactors C
    (ComplexShape.up ℤ) n).hom.naturality
      ((filteredGradedPieceHomotopyFunctor C p).map f).out
  have hE := (ShortComplex.homologyFunctorIso (F := E)).hom.naturality
      ((HomologicalComplex.shortComplexFunctor (GradedObject ℤ C)
        (ComplexShape.up ℤ) n).map
        ((filteredAssociatedGradedHomotopyFunctor C).map f).out)
  have hG := (HomotopyCategory.homologyFunctorFactors (GradedObject ℤ C)
    (ComplexShape.up ℤ) n).hom.naturality
      ((filteredAssociatedGradedHomotopyFunctor C).map f).out
  have hPnat :
      (filteredGradedPieceHomotopyFunctor C p).map f ≫
          eqToHom (hP L).symm =
        eqToHom (hP K).symm ≫
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
            ((filteredGradedPieceHomotopyFunctor C p).map f).out := by
    induction f using CategoryTheory.Quotient.induction with
    | @h X Y f =>
      rw [HomotopyCategory.quotient_map_out]
      have hX := hP ({ as := X } : FilteredHomotopyCategory C)
      have hY := hP ({ as := Y } : FilteredHomotopyCategory C)
      change
        (filteredGradedPieceHomotopyFunctor C p).map
            ((Quotient.functor (homotopic (FiniteFilteredObject C)
              (ComplexShape.up ℤ))).map f) ≫ eqToHom hY.symm =
          eqToHom hX.symm ≫
            (filteredGradedPieceHomotopyFunctor C p).map
              ((Quotient.functor (homotopic (FiniteFilteredObject C)
                (ComplexShape.up ℤ))).map f)
      apply eq_of_heq
      exact (CategoryTheory.comp_eqToHom_heq _ _).trans
        (CategoryTheory.eqToHom_comp_heq _ _).symm
  have hQnat :
      (filteredAssociatedGradedHomotopyFunctor C).map f ≫
          eqToHom (hQ L).symm =
        eqToHom (hQ K).symm ≫
          (HomotopyCategory.quotient (GradedObject ℤ C)
            (ComplexShape.up ℤ)).map
            ((filteredAssociatedGradedHomotopyFunctor C).map f).out := by
    induction f using CategoryTheory.Quotient.induction with
    | @h X Y f =>
      rw [HomotopyCategory.quotient_map_out]
      have hX := hQ ({ as := X } : FilteredHomotopyCategory C)
      have hY := hQ ({ as := Y } : FilteredHomotopyCategory C)
      change
        (filteredAssociatedGradedHomotopyFunctor C).map
            ((Quotient.functor (homotopic (FiniteFilteredObject C)
              (ComplexShape.up ℤ))).map f) ≫ eqToHom hY.symm =
          eqToHom hX.symm ≫
            (filteredAssociatedGradedHomotopyFunctor C).map
              ((Quotient.functor (homotopic (FiniteFilteredObject C)
                (ComplexShape.up ℤ))).map f)
      apply eq_of_heq
      exact (CategoryTheory.comp_eqToHom_heq _ _).trans
        (CategoryTheory.eqToHom_comp_heq _ _).symm
  dsimp
  let eK := filteredGradedHomology_component_iso_aux C K p n (hP K) (hQ K)
  let eL := filteredGradedHomology_component_iso_aux C L p n (hP L) (hQ L)
  change
    (filteredGradedPieceHomologyFunctor C p n).map f ≫ eL.hom =
      eK.hom ≫ (filteredGradedHomologyFunctor C n ⋙ GradedObject.eval p).map f
  dsimp [eK, eL, filteredGradedHomology_component_iso_aux]
  rw [← Category.assoc, ← Functor.map_comp, hPnat]
  rw [Functor.map_comp, HomotopyCategory.quotient_map_out]
  have hC_transport := congrArg
    (fun k =>
      (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).map
          (eqToHom (hP K).symm) ≫ k) hC
  simp only [Functor.comp_map, HomotopyCategory.quotient_map_out,
    ← Category.assoc] at hC_transport
  simp only [← Category.assoc]
  rw [hC_transport]
  rw [← hE]
  rw [hG]

-/

theorem filteredAcyclic_iff_gr_piece_acyclic
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredHomotopyCategory C) :
    filteredAcyclic C K ↔
      ∀ p n : ℤ,
        IsZero ((filteredGradedPieceHomologyFunctor C p n).obj K) := by
  constructor
  · intro h p n
    have h' := h n
    let hEvalZero : (GradedObject.eval (C := C) p).PreservesZeroMorphisms := ⟨by
      intro X Y
      change 0 = 0
      rfl⟩
    let _ := hEvalZero
    exact IsZero.of_iso
      ((GradedObject.eval (C := C) p).map_isZero h')
      (filteredGradedHomology_component_iso C K p n)
  · intro h n
    rw [IsZero.iff_id_eq_zero]
    apply GradedObject.hom_ext
    intro p
    exact (IsZero.iff_id_eq_zero _).mp
      (IsZero.of_iso (h p n) (filteredGradedHomology_component_iso C K p n).symm)

theorem filteredQuasiIso_iff_gr_piece
    (C : Type u) [Category.{v} C] [Abelian C]
    {K L : FilteredHomotopyCategory C} (f : K ⟶ L) :
    filteredQuasiIso C f ↔ ∀ p : ℤ, filteredGradedPieceQuasiIso C p f := by
  induction f using CategoryTheory.Quotient.induction with
  | @h X Y f =>
    change (∀ n : ℤ, IsIso ((filteredGradedHomologyFunctor C n).map
        ((HomotopyCategory.quotient (FiniteFilteredObject C)
          (ComplexShape.up ℤ)).map f))) ↔
      ∀ p n : ℤ, IsIso ((filteredGradedPieceHomologyFunctor C p n).map
        ((HomotopyCategory.quotient (FiniteFilteredObject C)
          (ComplexShape.up ℤ)).map f))
    let Efun := piEquivalenceFunctorDiscrete ℤ C
    let : Preadditive (ℤ → C) :=
      Preadditive.ofFullyFaithful Efun.fullyFaithfulFunctor
    let : HasZeroMorphisms (ℤ → C) :=
      Preadditive.preadditiveHasZeroMorphisms
    let : Preadditive (GradedObject ℤ C) :=
      Preadditive.ofFullyFaithful Efun.fullyFaithfulFunctor
    let : HasZeroMorphisms (GradedObject ℤ C) :=
      Preadditive.preadditiveHasZeroMorphisms
    let : (finiteAssociatedGraded C).Additive := by
      let _ : (associatedGraded (C := C)).Additive :=
        associatedGraded_is_additive (C := C)
      infer_instance
    let : Efun.functor.Additive :=
      Efun.fullyFaithfulFunctor.additive_ofFullyFaithful
    let hEfunHomology : Efun.functor.PreservesHomology := by
      infer_instance
    let _ := hEfunHomology
    have htest := HomologicalComplex.quasiIso_map_iff_of_preservesHomology
      (C₁ := GradedObject ℤ C) (C₂ := Discrete ℤ ⥤ C)
      (c := ComplexShape.up ℤ)
      (K := ((finiteAssociatedGraded C).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X)
      (L := ((finiteAssociatedGraded C).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Y)
      (φ := ((finiteAssociatedGraded C).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
      (F := Efun.functor)
    have hEval :
        QuasiIso
            ((Efun.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (((finiteAssociatedGraded C).mapHomologicalComplex
                (ComplexShape.up ℤ)).map f)) ↔
          ∀ p : ℤ,
            QuasiIso
              ((((evaluation (Discrete ℤ) C).obj ⟨p⟩).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map
                ((Efun.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map
                  (((finiteAssociatedGraded C).mapHomologicalComplex
                    (ComplexShape.up ℤ)).map f))) := by
      rw [quasiIso_iff]
      simp only [HomologicalComplex.quasiIsoAt_iff_evaluation, quasiIso_iff]
      tauto
    have hcomp : ∀ p : ℤ,
        Efun.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            ((evaluation (Discrete ℤ) C).obj ⟨p⟩).mapHomologicalComplex
              (ComplexShape.up ℤ) ≅
          (Efun.functor ⋙ (evaluation (Discrete ℤ) C).obj ⟨p⟩).mapHomologicalComplex
            (ComplexShape.up ℤ) := by
      intro p
      letI : ((evaluation (Discrete ℤ) C).obj ⟨p⟩).Additive :=
        { map_add := by
            intro X Y f g
            rfl }
      letI : (Pi.eval (fun _ : ℤ => C) p).Additive :=
        gradedObject_eval_additive C p
      exact Functor.mapHomologicalComplexCompIso
        (piEquivalenceFunctorDiscreteCompEvaluationIso C p)
        (ComplexShape.up ℤ)
    have hPieces :
        (∀ p : ℤ,
            QuasiIso
              ((((evaluation (Discrete ℤ) C).obj ⟨p⟩).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map
                ((Efun.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map
                  (((finiteAssociatedGraded C).mapHomologicalComplex
                    (ComplexShape.up ℤ)).map f)))) ↔
          ∀ p : ℤ,
            QuasiIso
              (((finiteGradedPieceFunctor C p).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map f) := by
      constructor
      · intro h p
        let : (GradedObject.eval (C := C) p).Additive :=
          gradedObject_eval_additive C p
        let eEvalBase :
            Pi.eval (fun _ : ℤ => C) p ≅ GradedObject.eval p := by
          refine NatIso.ofComponents (fun X => Iso.refl _) ?_
          intro X Y f
          dsimp [Pi.eval, GradedObject.eval]
          simp
        let : (Pi.eval (fun _ : ℤ => C) p).Additive := by
          exact Functor.additive_of_iso eEvalBase.symm
        let ePiEval :
            finiteAssociatedGraded C ⋙ Pi.eval (fun _ : ℤ => C) p ≅
              finiteAssociatedGraded C ⋙ GradedObject.eval p := by
          refine NatIso.ofComponents (fun A => Iso.refl _) ?_
          intro A B f
          simp [finiteAssociatedGraded, Functor.comp_obj,
            Functor.comp_map, Pi.eval, GradedObject.eval]
        let eEval0 :
            finiteAssociatedGraded C ⋙
                (Efun.functor ⋙ (evaluation (Discrete ℤ) C).obj ⟨p⟩) ≅
              finiteAssociatedGraded C ⋙ Pi.eval (fun _ : ℤ => C) p := by
          refine NatIso.ofComponents
            (fun A => (piEquivalenceFunctorDiscreteCompEvaluationIso C p).app
              ((finiteAssociatedGraded C).obj A)) ?_
          intro A B f
          simpa only [finiteAssociatedGraded, finiteFilteredInclusion, Efun,
            Functor.comp_obj, Functor.comp_map, Iso.app_hom] using
            (piEquivalenceFunctorDiscreteCompEvaluationIso C p).hom.naturality
              ((finiteAssociatedGraded C).map f)
        let eEval :=
          NatIso.mapHomologicalComplex eEval0 (ComplexShape.up ℤ) ≪≫
            NatIso.mapHomologicalComplex ePiEval (ComplexShape.up ℤ)
        let eComp := Functor.mapHomologicalComplexCompIso
          (Iso.refl (finiteAssociatedGraded C ⋙
            (Efun.functor ⋙ (evaluation (Discrete ℤ) C).obj ⟨p⟩)))
          (ComplexShape.up ℤ)
        let ePiece :
            (finiteGradedPieceFunctor C p).mapHomologicalComplex
                (ComplexShape.up ℤ) ≅
              (finiteAssociatedGraded C ⋙ GradedObject.eval p).mapHomologicalComplex
                (ComplexShape.up ℤ) :=
          NatIso.mapHomologicalComplex (finiteGradedPieceFunctor_iso C p)
            (ComplexShape.up ℤ)
        let hcomp' :
            (finiteAssociatedGraded C).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
                (Efun.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
                  ((evaluation (Discrete ℤ) C).obj ⟨p⟩).mapHomologicalComplex
                    (ComplexShape.up ℤ)) ≅
              (finiteAssociatedGraded C).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
                (Efun.functor ⋙ (evaluation (Discrete ℤ) C).obj ⟨p⟩).mapHomologicalComplex
                  (ComplexShape.up ℤ) := by
          refine NatIso.ofComponents
            (fun Z => asIso ((hcomp p).hom.app
              (((finiteAssociatedGraded C).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj Z))) ?_
          intro Z W g
          simpa only [Functor.comp_map, asIso_hom] using
            (hcomp p).hom.naturality
              (((finiteAssociatedGraded C).mapHomologicalComplex
                (ComplexShape.up ℤ)).map g)
        let hTotal := hcomp' ≪≫ eComp ≪≫ eEval ≪≫ ePiece.symm
        let eX := hTotal.app X
        let eY := hTotal.app Y
        let φEval :=
          (((evaluation (Discrete ℤ) C).obj ⟨p⟩).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
            ((Efun.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (((finiteAssociatedGraded C).mapHomologicalComplex
                (ComplexShape.up ℤ)).map f))
        let φPiece :=
          ((finiteGradedPieceFunctor C p).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f
        have hArrow : Arrow.mk φEval ≅ Arrow.mk φPiece := by
          refine Arrow.isoMk eX eY ?_
          dsimp [φEval, φPiece, eX, eY]
          simpa only [Functor.comp_map] using
            (hTotal.hom.naturality f).symm
        let : QuasiIso φEval := h p
        exact quasiIso_of_arrow_mk_iso φEval φPiece hArrow
      · intro h p
        let : (GradedObject.eval (C := C) p).Additive :=
          gradedObject_eval_additive C p
        let eEvalBase :
            Pi.eval (fun _ : ℤ => C) p ≅ GradedObject.eval p := by
          refine NatIso.ofComponents (fun X => Iso.refl _) ?_
          intro X Y f
          dsimp [Pi.eval, GradedObject.eval]
          simp
        let : (Pi.eval (fun _ : ℤ => C) p).Additive := by
          exact Functor.additive_of_iso eEvalBase.symm
        let ePiEval :
            finiteAssociatedGraded C ⋙ Pi.eval (fun _ : ℤ => C) p ≅
              finiteAssociatedGraded C ⋙ GradedObject.eval p := by
          refine NatIso.ofComponents (fun A => Iso.refl _) ?_
          intro A B f
          simp [finiteAssociatedGraded, Functor.comp_obj,
            Functor.comp_map, Pi.eval, GradedObject.eval]
        let eEval0 :
            finiteAssociatedGraded C ⋙
                (Efun.functor ⋙ (evaluation (Discrete ℤ) C).obj ⟨p⟩) ≅
              finiteAssociatedGraded C ⋙ Pi.eval (fun _ : ℤ => C) p := by
          refine NatIso.ofComponents
            (fun A => (piEquivalenceFunctorDiscreteCompEvaluationIso C p).app
              ((finiteAssociatedGraded C).obj A)) ?_
          intro A B f
          simpa only [finiteAssociatedGraded, finiteFilteredInclusion, Efun,
            Functor.comp_obj, Functor.comp_map, Iso.app_hom] using
            (piEquivalenceFunctorDiscreteCompEvaluationIso C p).hom.naturality
              ((finiteAssociatedGraded C).map f)
        let eEval :=
          NatIso.mapHomologicalComplex eEval0 (ComplexShape.up ℤ) ≪≫
            NatIso.mapHomologicalComplex ePiEval (ComplexShape.up ℤ)
        let eComp := Functor.mapHomologicalComplexCompIso
          (Iso.refl (finiteAssociatedGraded C ⋙
            (Efun.functor ⋙ (evaluation (Discrete ℤ) C).obj ⟨p⟩)))
          (ComplexShape.up ℤ)
        let ePiece :
            (finiteGradedPieceFunctor C p).mapHomologicalComplex
                (ComplexShape.up ℤ) ≅
              (finiteAssociatedGraded C ⋙ GradedObject.eval p).mapHomologicalComplex
                (ComplexShape.up ℤ) :=
          NatIso.mapHomologicalComplex (finiteGradedPieceFunctor_iso C p)
            (ComplexShape.up ℤ)
        let hcomp' :
            (finiteAssociatedGraded C).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
                (Efun.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
                  ((evaluation (Discrete ℤ) C).obj ⟨p⟩).mapHomologicalComplex
                    (ComplexShape.up ℤ)) ≅
              (finiteAssociatedGraded C).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
                (Efun.functor ⋙ (evaluation (Discrete ℤ) C).obj ⟨p⟩).mapHomologicalComplex
                  (ComplexShape.up ℤ) := by
          refine NatIso.ofComponents
            (fun Z => asIso ((hcomp p).hom.app
              (((finiteAssociatedGraded C).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj Z))) ?_
          intro Z W g
          simpa only [Functor.comp_map, asIso_hom] using
            (hcomp p).hom.naturality
              (((finiteAssociatedGraded C).mapHomologicalComplex
                (ComplexShape.up ℤ)).map g)
        let hTotal := hcomp' ≪≫ eComp ≪≫ eEval ≪≫ ePiece.symm
        let eX := hTotal.app X
        let eY := hTotal.app Y
        let φEval :=
          (((evaluation (Discrete ℤ) C).obj ⟨p⟩).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
            ((Efun.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (((finiteAssociatedGraded C).mapHomologicalComplex
                (ComplexShape.up ℤ)).map f))
        let φPiece :=
          ((finiteGradedPieceFunctor C p).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f
        have hArrow : Arrow.mk φEval ≅ Arrow.mk φPiece := by
          refine Arrow.isoMk eX eY ?_
          dsimp [φEval, φPiece, eX, eY]
          simpa only [Functor.comp_map] using
            (hTotal.hom.naturality f).symm
        let : QuasiIso φPiece := h p
        exact quasiIso_of_arrow_mk_iso φPiece φEval hArrow.symm
    change
      HomotopyCategory.quasiIso (GradedObject ℤ C) (ComplexShape.up ℤ)
          ((filteredAssociatedGradedHomotopyFunctor C).map
            ((HomotopyCategory.quotient (FiniteFilteredObject C)
              (ComplexShape.up ℤ)).map f)) ↔
        ∀ p : ℤ,
          HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
            ((filteredGradedPieceHomotopyFunctor C p).map
              ((HomotopyCategory.quotient (FiniteFilteredObject C)
                (ComplexShape.up ℤ)).map f))
    rw [Functor.mapHomotopyCategory_map]
    have hqAssoc := HomotopyCategory.quotient_map_mem_quasiIso_iff
      (((finiteAssociatedGraded C).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)
    have hRight :
        (∀ p : ℤ,
          HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
            ((filteredGradedPieceHomotopyFunctor C p).map
              ((HomotopyCategory.quotient (FiniteFilteredObject C)
                (ComplexShape.up ℤ)).map f))) ↔
          ∀ p : ℤ,
            QuasiIso
              (((finiteGradedPieceFunctor C p).mapHomologicalComplex
                (ComplexShape.up ℤ)).map f) := by
      constructor
      · intro h p
        have hp := h p
        dsimp [filteredGradedPieceHomotopyFunctor] at hp
        exact (HomotopyCategory.quotient_map_mem_quasiIso_iff
          (((finiteGradedPieceFunctor C p).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f)).mp hp
      · intro h p
        rw [Functor.mapHomotopyCategory_map]
        exact (HomotopyCategory.quotient_map_mem_quasiIso_iff
          (((finiteGradedPieceFunctor C p).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f)).mpr (h p)
    exact hqAssoc.trans
      ((htest.symm.trans (hEval.trans hPieces)).trans hRight.symm)

theorem filteredQuasiIso_iff_associated_grading
    (C : Type u) [Category.{v} C] [Abelian C]
    {K L : FilteredHomotopyCategory C} (f : K ⟶ L) :
    filteredQuasiIso C f ↔
      HomotopyCategory.quasiIso (GradedObject ℤ C) (ComplexShape.up ℤ)
        ((filteredAssociatedGradedHomotopyFunctor C).map f) := Iff.rfl

/- The three homological functors in the source lemma. -/
noncomputable abbrev filteredGradedHomologyZeroFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredHomotopyCategory C ⥤ GradedObject ℤ C :=
  filteredGradedHomologyFunctor C 0

noncomputable abbrev filteredGradedPieceHomologyZeroFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
    FilteredHomotopyCategory C ⥤ C :=
  filteredGradedPieceHomologyFunctor C p 0

noncomputable abbrev filteredForgetfulHomologyZeroFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredHomotopyCategory C ⥤ C :=
  filteredForgetfulHomologyFunctor C 0

theorem filteredGradedHomologyZero_is_homological
    (C : Type u) [Category.{v} C] [Abelian C] :
    (filteredGradedHomologyZeroFunctor C).IsHomological := by
  infer_instance

theorem filteredGradedPieceHomologyZero_is_homological
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ) :
    (filteredGradedPieceHomologyZeroFunctor C p).IsHomological := by
  infer_instance

theorem filteredForgetfulHomologyZero_is_homological
    (C : Type u) [Category.{v} C] [Abelian C] :
    (filteredForgetfulHomologyZeroFunctor C).IsHomological := by
  infer_instance

theorem filteredAcyclic_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    IsStrictlyFullSaturatedPretriangulated (filteredAcyclic C) := by
  have hEq : filteredAcyclic C =
      (filteredGradedHomologyZeroFunctor C).homologicalKernel := by
    ext K
    rw [Functor.mem_homologicalKernel_iff]
    rfl
  rw [hEq]
  exact homologicalFunctorKernel_properties (filteredGradedHomologyZeroFunctor C)

theorem filteredQuasiIso_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    SaturatedMultiplicativeSystem (filteredQuasiIso C) ∧
      CompatibleWithTriangulation (filteredQuasiIso C) := by
  have hEq : filteredQuasiIso C =
      homologicalFunctorMorphismProperty (filteredGradedHomologyZeroFunctor C) := by
    ext X Y f
    dsimp [filteredQuasiIso, MorphismProperty.inverseImage, HomotopyCategory.quasiIso,
      homologicalFunctorMorphismProperty,
      Formalization.Books.Derived.Unit03.homologicalDegree]
    change (∀ n : ℤ, IsIso ((filteredGradedHomologyFunctor C n).map f)) ↔ _
    constructor
    · intro h i
      exact (NatIso.isIso_map_iff
        ((filteredGradedHomologyZeroFunctor C).isoShift i) f).2 (h i)
    · intro h i
      exact (NatIso.isIso_map_iff
        ((filteredGradedHomologyZeroFunctor C).isoShift i) f).1 (h i)
  change SaturatedMultiplicativeSystem (filteredQuasiIso C) ∧
    CompatibleWithTriangulation (filteredQuasiIso C)
  rw [hEq]
  exact homologicalFunctorMorphismProperty_saturated
    (H := filteredGradedHomologyZeroFunctor C)

noncomputable instance filteredQuasiIso_leftCalculus
    (C : Type u) [Category.{v} C] [Abelian C] :
    LeftMultiplicativeSystem (filteredQuasiIso C) :=
  (filteredQuasiIso_properties C).1.1.1

noncomputable instance filteredQuasiIso_rightCalculus
    (C : Type u) [Category.{v} C] [Abelian C] :
    RightMultiplicativeSystem (filteredQuasiIso C) :=
  (filteredQuasiIso_properties C).1.1.2

noncomputable instance filteredQuasiIso_compatible
    (C : Type u) [Category.{v} C] [Abelian C] :
    CompatibleWithTriangulation (filteredQuasiIso C) :=
  (filteredQuasiIso_properties C).2

/-! ## The filtered derived category -/

/-- The filtered derived category `DF(𝒜)`. -/
abbrev FilteredDerivedCategory
    (C : Type u) [Category.{v} C] [Abelian C] :=
  (filteredQuasiIso C).Localization

/-- The localization functor `K(Fil^f(𝒜)) ⥤ DF(𝒜)`. -/
abbrev filteredLocalizationFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredHomotopyCategory C ⥤ FilteredDerivedCategory C :=
  (filteredQuasiIso C).Q

theorem filteredDerivedCategory_additiveCategory_exists
    (C : Type u) [Category.{v} C] [Abelian C] :
    Nonempty (AdditiveCategory (FilteredDerivedCategory C)) := by
  exact ⟨{ toPreadditive := inferInstance, toHasFiniteProducts := inferInstance }⟩

noncomputable instance filteredDerivedCategory_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (FilteredDerivedCategory C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts :=
      (Classical.choice (filteredDerivedCategory_additiveCategory_exists C)).toHasFiniteProducts }

noncomputable instance filteredDerivedCategory_isTriangulated
    (C : Type u) [Category.{v} C] [Abelian C] :
    CategoryTheory.IsTriangulated (FilteredDerivedCategory C) := by
  exact localization_triangulated (S := filteredQuasiIso C)

theorem filteredLocalizationFunctor_is_localization
    (C : Type u) [Category.{v} C] [Abelian C] :
    (filteredLocalizationFunctor C).IsLocalization (filteredQuasiIso C) := by
  infer_instance

/- The source also records the factorization of the degree-zero homology of
   the associated graded complex through the filtered localization.  Keep
   this interface independent of the optional derived-category construction. -/
theorem filteredGradedHomologyZero_inverts
    (C : Type u) [Category.{v} C] [Abelian C] :
    (filteredQuasiIso C).IsInvertedBy (filteredGradedHomologyZeroFunctor C) := by
  intro X Y f hf
  change IsIso ((filteredGradedHomologyFunctor C 0).map f)
  change HomotopyCategory.quasiIso (GradedObject ℤ C) (ComplexShape.up ℤ)
    ((filteredAssociatedGradedHomotopyFunctor C).map f) at hf
  exact (HomotopyCategory.homologyFunctor_inverts_quasiIso
    (GradedObject ℤ C) (ComplexShape.up ℤ) 0)
    ((filteredAssociatedGradedHomotopyFunctor C).map f) hf

noncomputable def filteredGradedHomologyZeroLocalizationFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredDerivedCategory C ⥤ GradedObject ℤ C :=
  Localization.lift (filteredGradedHomologyZeroFunctor C)
    (filteredGradedHomologyZero_inverts C) (filteredLocalizationFunctor C)

noncomputable def filteredGradedHomologyZeroLocalizationFunctor_fac
    (C : Type u) [Category.{v} C] [Abelian C] :
    filteredLocalizationFunctor C ⋙
        filteredGradedHomologyZeroLocalizationFunctor C ≅
      filteredGradedHomologyZeroFunctor C :=
  Localization.fac (filteredGradedHomologyZeroFunctor C)
    (filteredGradedHomologyZero_inverts C) (filteredLocalizationFunctor C)

theorem filteredDerivedLocalization_kernel
    (C : Type u) [Category.{v} C] [Abelian C] :
    functorKernel (filteredLocalizationFunctor C) = filteredAcyclic C := by
  sorry

theorem filteredQuasiIso_forgetful
    (C : Type u) [Category.{v} C] [Abelian C]
    {K L : FilteredHomotopyCategory C} (f : K ⟶ L)
    (hf : filteredQuasiIso C f) :
    HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
      ((filteredForgetfulHomotopyFunctor C).map f) := by
  sorry

theorem filteredQuasiIso_gr_piece
    (C : Type u) [Category.{v} C] [Abelian C]
    {K L : FilteredHomotopyCategory C} (f : K ⟶ L) (p : ℤ)
    (hf : filteredQuasiIso C f) :
    HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
      ((filteredGradedPieceHomotopyFunctor C p).map f) := by
  exact (filteredQuasiIso_iff_gr_piece C f).1 hf p

theorem filteredQuasiIso_associated_grading
    (C : Type u) [Category.{v} C] [Abelian C]
    {K L : FilteredHomotopyCategory C} (f : K ⟶ L)
    (hf : filteredQuasiIso C f) :
    HomotopyCategory.quasiIso (GradedObject ℤ C) (ComplexShape.up ℤ)
      ((filteredAssociatedGradedHomotopyFunctor C).map f) :=
  hf

/-- The exact functor induced by the associated graded construction. -/
noncomputable def filteredDerivedGradedFunctor
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    FilteredDerivedCategory C ⥤ DerivedCategory (GradedObject ℤ C) :=
  Localization.lift
    (filteredAssociatedGradedHomotopyFunctor C ⋙
      DerivedCategory.Qh (C := GradedObject ℤ C))
    (by
      intro K L f hf
      exact Localization.inverts (DerivedCategory.Qh (C := GradedObject ℤ C))
        (HomotopyCategory.quasiIso (GradedObject ℤ C) (ComplexShape.up ℤ)) _
        (filteredQuasiIso_associated_grading C f hf))
    (filteredLocalizationFunctor C)

/-- The exact functor induced by the `p`th graded piece. -/
noncomputable def filteredDerivedGradedPieceFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ)
    [HasDerivedCategory.{w} C] :
    FilteredDerivedCategory C ⥤ DerivedCategory C :=
  Localization.lift
    (filteredGradedPieceHomotopyFunctor C p ⋙
      DerivedCategory.Qh (C := C))
    (by
      intro K L f hf
      exact Localization.inverts (DerivedCategory.Qh (C := C))
        (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _
        (filteredQuasiIso_gr_piece C f p hf))
    (filteredLocalizationFunctor C)

/-- The exact functor induced by forgetting the filtration. -/
noncomputable def filteredDerivedForgetfulFunctor
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] :
    FilteredDerivedCategory C ⥤ DerivedCategory C :=
  Localization.lift
    (filteredForgetfulHomotopyFunctor C ⋙ DerivedCategory.Qh (C := C))
    (by
      intro K L f hf
      exact Localization.inverts (DerivedCategory.Qh (C := C))
        (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _
        (filteredQuasiIso_forgetful C f hf))
    (filteredLocalizationFunctor C)

noncomputable def filteredDerivedGradedFunctor_fac
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    filteredLocalizationFunctor C ⋙ filteredDerivedGradedFunctor C ≅
      filteredAssociatedGradedHomotopyFunctor C ⋙
        DerivedCategory.Qh (C := GradedObject ℤ C) := by
  sorry

noncomputable def filteredDerivedGradedPieceFunctor_fac
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ)
    [HasDerivedCategory.{w} C] :
    filteredLocalizationFunctor C ⋙ filteredDerivedGradedPieceFunctor C p ≅
      filteredGradedPieceHomotopyFunctor C p ⋙
        DerivedCategory.Qh (C := C) := by
  sorry

noncomputable def filteredDerivedForgetfulFunctor_fac
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] :
    filteredLocalizationFunctor C ⋙ filteredDerivedForgetfulFunctor C ≅
      filteredForgetfulHomotopyFunctor C ⋙ DerivedCategory.Qh (C := C) := by
  sorry

noncomputable instance filteredDerivedGradedFunctor_commShift
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredDerivedGradedFunctor C).CommShift ℤ := by
  sorry

noncomputable instance filteredDerivedGradedPieceFunctor_commShift
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ)
    [HasDerivedCategory.{w} C] :
    (filteredDerivedGradedPieceFunctor C p).CommShift ℤ := by
  sorry

noncomputable instance filteredDerivedForgetfulFunctor_commShift
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] :
    (filteredDerivedForgetfulFunctor C).CommShift ℤ := by
  sorry

theorem filteredDerivedGradedFunctor_is_exact
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredDerivedGradedFunctor C).IsTriangulated := by
  sorry

theorem filteredDerivedGradedPieceFunctor_is_exact
    (C : Type u) [Category.{v} C] [Abelian C] (p : ℤ)
    [HasDerivedCategory.{w} C] :
    (filteredDerivedGradedPieceFunctor C p).IsTriangulated := by
  sorry

theorem filteredDerivedForgetfulFunctor_is_exact
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] :
    (filteredDerivedForgetfulFunctor C).IsTriangulated := by
  sorry

noncomputable def filteredDerivedGradedCohomologyZero_fac
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    filteredLocalizationFunctor C ⋙ filteredDerivedGradedFunctor C ⋙
        derivedCohomologyFunctor (GradedObject ℤ C) 0 ≅
      filteredGradedHomologyZeroFunctor C := by
  sorry

/-! ## Bounded filtered derived categories -/

def filteredDerivedPlusProperty
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    ObjectProperty (FilteredDerivedCategory C) :=
  (derivedPlusProperty (GradedObject ℤ C)).inverseImage
    (filteredDerivedGradedFunctor C)

def filteredDerivedMinusProperty
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    ObjectProperty (FilteredDerivedCategory C) :=
  (derivedMinusProperty (GradedObject ℤ C)).inverseImage
    (filteredDerivedGradedFunctor C)

def filteredDerivedBoundedProperty
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    ObjectProperty (FilteredDerivedCategory C) :=
  (derivedBoundedProperty (GradedObject ℤ C)).inverseImage
    (filteredDerivedGradedFunctor C)

/-- The bounded-below filtered derived category. -/
abbrev FilteredDerivedPlus
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :=
  (filteredDerivedPlusProperty C).FullSubcategory

/-- The bounded-above filtered derived category. -/
abbrev FilteredDerivedMinus
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :=
  (filteredDerivedMinusProperty C).FullSubcategory

/-- The bounded filtered derived category. -/
abbrev FilteredDerivedBounded
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :=
  (filteredDerivedBoundedProperty C).FullSubcategory

theorem filteredDerivedBoundedSubcategory_properties
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    IsStrictlyFullSaturatedPretriangulated (filteredDerivedPlusProperty C) ∧
      IsStrictlyFullSaturatedPretriangulated (filteredDerivedMinusProperty C) ∧
      IsStrictlyFullSaturatedPretriangulated (filteredDerivedBoundedProperty C) := by
  sorry

/-! ## Boundedness replacements for filtered complexes -/

/- A complex-level filtered quasi-isomorphism is the source's notion applied
   to the induced morphism in the homotopy category. -/
def filteredComplexQuasiIso
    (C : Type u) [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (f : K ⟶ L) : Prop :=
  filteredQuasiIso C
    ((HomotopyCategory.quotient (FiniteFilteredObject C) (ComplexShape.up ℤ)).map f)

noncomputable abbrev filteredComplexGradedHomology
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n : ℤ) : GradedObject ℤ C :=
  (filteredGradedHomologyFunctor C n).obj
    ((HomotopyCategory.quotient (FiniteFilteredObject C) (ComplexShape.up ℤ)).obj K)

def filteredComplexGradedHomologyVanishesBelow
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) : Prop :=
  ∃ a : ℤ, ∀ n : ℤ, n < a →
    IsZero (filteredComplexGradedHomology C K n)

def filteredComplexGradedHomologyVanishesAbove
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) : Prop :=
  ∃ b : ℤ, ∀ n : ℤ, b < n →
    IsZero (filteredComplexGradedHomology C K n)

def filteredComplexGradedHomologyVanishesBounded
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) : Prop :=
  filteredComplexGradedHomologyVanishesBelow C K ∧
    filteredComplexGradedHomologyVanishesAbove C K

def filteredComplexIsZeroBelow
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (a : ℤ) : Prop :=
  ∀ n : ℤ, n < a → IsZero (K.X n)

def filteredComplexIsZeroAbove
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (b : ℤ) : Prop :=
  ∀ n : ℤ, b < n → IsZero (K.X n)

def filteredComplexIsBounded
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) : Prop :=
  ∃ a b : ℤ, filteredComplexIsZeroBelow C K a ∧
    filteredComplexIsZeroAbove C K b

theorem filteredComplex_cohomology_bounded_below
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (a : ℤ)
    (hK : ∀ n : ℤ, n < a → IsZero (filteredComplexGradedHomology C K n)) :
    ∃ (L : FilteredComplex C) (f : K ⟶ L),
      filteredComplexQuasiIso C f ∧ filteredComplexIsZeroBelow C L a := by
  sorry

theorem filteredComplex_cohomology_bounded_above
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (b : ℤ)
    (hK : ∀ n : ℤ, b < n → IsZero (filteredComplexGradedHomology C K n)) :
    ∃ (M : FilteredComplex C) (f : M ⟶ K),
      filteredComplexQuasiIso C f ∧ filteredComplexIsZeroAbove C M b := by
  sorry

theorem filteredComplex_cohomology_bounded
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : FilteredComplex C)
    (hK : filteredComplexGradedHomologyVanishesBounded C K) :
    ∃ (L M N : FilteredComplex C)
      (f : K ⟶ L) (g : M ⟶ K) (u : M ⟶ N) (v : N ⟶ L),
      g ≫ f = u ≫ v ∧
      filteredComplexQuasiIso C f ∧ filteredComplexQuasiIso C g ∧
      filteredComplexQuasiIso C u ∧ filteredComplexQuasiIso C v ∧
      (∃ a : ℤ, filteredComplexIsZeroBelow C L a) ∧
      (∃ b : ℤ, filteredComplexIsZeroAbove C M b) ∧
      filteredComplexIsBounded C N := by
  sorry

/-! ## Bounded filtered homotopy localizations -/

abbrev FilteredKPlus
    (C : Type u) [Category.{v} C] [Abelian C] :=
  KPlus (FiniteFilteredObject C)

abbrev FilteredKMinus
    (C : Type u) [Category.{v} C] [Abelian C] :=
  KMinus (FiniteFilteredObject C)

abbrev FilteredKBounded
    (C : Type u) [Category.{v} C] [Abelian C] :=
  KBounded (FiniteFilteredObject C)

theorem filteredKPlus_additiveCategory_exists
    (C : Type u) [Category.{v} C] [Abelian C] :
    Nonempty (AdditiveCategory (FilteredKPlus C)) := by
  sorry

noncomputable instance filteredKPlus_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (FilteredKPlus C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts :=
      (Classical.choice (filteredKPlus_additiveCategory_exists C)).toHasFiniteProducts }

theorem filteredKMinus_additiveCategory_exists
    (C : Type u) [Category.{v} C] [Abelian C] :
    Nonempty (AdditiveCategory (FilteredKMinus C)) := by
  sorry

noncomputable instance filteredKMinus_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (FilteredKMinus C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts :=
      (Classical.choice (filteredKMinus_additiveCategory_exists C)).toHasFiniteProducts }

theorem filteredKBounded_additiveCategory_exists
    (C : Type u) [Category.{v} C] [Abelian C] :
    Nonempty (AdditiveCategory (FilteredKBounded C)) := by
  sorry

noncomputable instance filteredKBounded_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (FilteredKBounded C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts :=
      (Classical.choice (filteredKBounded_additiveCategory_exists C)).toHasFiniteProducts }

noncomputable instance filteredKPlus_shift_additive
    (C : Type u) [Category.{v} C] [Abelian C] (n : ℤ) :
    (shiftFunctor (FilteredKPlus C) n).Additive := by
  infer_instance

noncomputable instance filteredKMinus_shift_additive
    (C : Type u) [Category.{v} C] [Abelian C] (n : ℤ) :
    (shiftFunctor (FilteredKMinus C) n).Additive := by
  infer_instance

noncomputable instance filteredKBounded_shift_additive
    (C : Type u) [Category.{v} C] [Abelian C] (n : ℤ) :
    (shiftFunctor (FilteredKBounded C) n).Additive := by
  infer_instance

abbrev filteredKPlusInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredKPlus C ⥤
      HomotopyCategory (FiniteFilteredObject C) (ComplexShape.up ℤ) :=
  (boundedBelowHomotopyProperty (FiniteFilteredObject C)).ι

abbrev filteredKMinusInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredKMinus C ⥤
      HomotopyCategory (FiniteFilteredObject C) (ComplexShape.up ℤ) :=
  (boundedAboveHomotopyProperty (FiniteFilteredObject C)).ι

abbrev filteredKBoundedInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredKBounded C ⥤
      HomotopyCategory (FiniteFilteredObject C) (ComplexShape.up ℤ) :=
  (boundedHomotopyProperty (FiniteFilteredObject C)).ι

def filteredAcyclicPlusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (FilteredKPlus C) :=
  (filteredAcyclic C).inverseImage (filteredKPlusInclusion C)

def filteredAcyclicMinusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (FilteredKMinus C) :=
  (filteredAcyclic C).inverseImage (filteredKMinusInclusion C)

def filteredAcyclicBoundedProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (FilteredKBounded C) :=
  (filteredAcyclic C).inverseImage (filteredKBoundedInclusion C)

abbrev filteredQuasiIsoPlusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (FilteredKPlus C) :=
  restrictedMorphismProperty (filteredQuasiIso C)
    (boundedBelowHomotopyProperty (FiniteFilteredObject C))

abbrev filteredQuasiIsoMinusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (FilteredKMinus C) :=
  restrictedMorphismProperty (filteredQuasiIso C)
    (boundedAboveHomotopyProperty (FiniteFilteredObject C))

abbrev filteredQuasiIsoBoundedProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (FilteredKBounded C) :=
  restrictedMorphismProperty (filteredQuasiIso C)
    (boundedHomotopyProperty (FiniteFilteredObject C))

theorem filteredBoundedAcyclic_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    IsStrictlyFullSaturatedPretriangulated (filteredAcyclicPlusProperty C) ∧
      IsStrictlyFullSaturatedPretriangulated (filteredAcyclicMinusProperty C) ∧
      IsStrictlyFullSaturatedPretriangulated (filteredAcyclicBoundedProperty C) := by
  sorry

theorem filteredBoundedQuasiIso_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    SaturatedMultiplicativeSystem (filteredQuasiIsoPlusProperty C) ∧
      SaturatedMultiplicativeSystem (filteredQuasiIsoMinusProperty C) ∧
      SaturatedMultiplicativeSystem (filteredQuasiIsoBoundedProperty C) := by
  sorry

theorem filteredDerived_maps_KPlus_to_DPlus
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    (X : FilteredKPlus C) :
    filteredDerivedPlusProperty C
      ((filteredKPlusInclusion C ⋙ filteredLocalizationFunctor C).obj X) := by
  sorry

theorem filteredDerived_maps_KMinus_to_DMinus
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    (X : FilteredKMinus C) :
    filteredDerivedMinusProperty C
      ((filteredKMinusInclusion C ⋙ filteredLocalizationFunctor C).obj X) := by
  sorry

theorem filteredDerived_maps_KBounded_to_DBounded
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)]
    (X : FilteredKBounded C) :
    filteredDerivedBoundedProperty C
      ((filteredKBoundedInclusion C ⋙ filteredLocalizationFunctor C).obj X) := by
  sorry

noncomputable def filteredPlusDerivedLocalizationFunctor
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    FilteredKPlus C ⥤ FilteredDerivedPlus C :=
  (filteredDerivedPlusProperty C).lift
    (filteredKPlusInclusion C ⋙ filteredLocalizationFunctor C)
    (filteredDerived_maps_KPlus_to_DPlus C)

noncomputable def filteredMinusDerivedLocalizationFunctor
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    FilteredKMinus C ⥤ FilteredDerivedMinus C :=
  (filteredDerivedMinusProperty C).lift
    (filteredKMinusInclusion C ⋙ filteredLocalizationFunctor C)
    (filteredDerived_maps_KMinus_to_DMinus C)

noncomputable def filteredBoundedDerivedLocalizationFunctor
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    FilteredKBounded C ⥤ FilteredDerivedBounded C :=
  (filteredDerivedBoundedProperty C).lift
    (filteredKBoundedInclusion C ⋙ filteredLocalizationFunctor C)
    (filteredDerived_maps_KBounded_to_DBounded C)

theorem filteredPlusDerivedLocalizationFunctor_is_localization
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredPlusDerivedLocalizationFunctor C).IsLocalization
      (filteredQuasiIsoPlusProperty C) := by
  sorry

theorem filteredMinusDerivedLocalizationFunctor_is_localization
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredMinusDerivedLocalizationFunctor C).IsLocalization
      (filteredQuasiIsoMinusProperty C) := by
  sorry

theorem filteredBoundedDerivedLocalizationFunctor_is_localization
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredBoundedDerivedLocalizationFunctor C).IsLocalization
      (filteredQuasiIsoBoundedProperty C) := by
  sorry

noncomputable def filteredPlusLocalizationComparison
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredQuasiIsoPlusProperty C).Localization ⥤ FilteredDerivedPlus C :=
  Localization.Construction.lift (filteredPlusDerivedLocalizationFunctor C)
    (by exact (filteredPlusDerivedLocalizationFunctor_is_localization C).inverts)

noncomputable def filteredMinusLocalizationComparison
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredQuasiIsoMinusProperty C).Localization ⥤ FilteredDerivedMinus C :=
  Localization.Construction.lift (filteredMinusDerivedLocalizationFunctor C)
    (by exact (filteredMinusDerivedLocalizationFunctor_is_localization C).inverts)

noncomputable def filteredBoundedLocalizationComparison
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    (filteredQuasiIsoBoundedProperty C).Localization ⥤ FilteredDerivedBounded C :=
  Localization.Construction.lift (filteredBoundedDerivedLocalizationFunctor C)
    (by exact (filteredBoundedDerivedLocalizationFunctor_is_localization C).inverts)

theorem filteredPlusLocalizationComparison_is_equivalence
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    Functor.IsEquivalence (filteredPlusLocalizationComparison C) := by
  sorry

theorem filteredMinusLocalizationComparison_is_equivalence
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    Functor.IsEquivalence (filteredMinusLocalizationComparison C) := by
  sorry

theorem filteredBoundedLocalizationComparison_is_equivalence
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    Functor.IsEquivalence (filteredBoundedLocalizationComparison C) := by
  sorry

theorem filteredPlusDerivedLocalizationFunctor_kernel
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    functorKernel (filteredPlusDerivedLocalizationFunctor C) =
      filteredAcyclicPlusProperty C := by
  sorry

theorem filteredMinusDerivedLocalizationFunctor_kernel
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    functorKernel (filteredMinusDerivedLocalizationFunctor C) =
      filteredAcyclicMinusProperty C := by
  sorry

theorem filteredBoundedDerivedLocalizationFunctor_kernel
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} (GradedObject ℤ C)] :
    functorKernel (filteredBoundedDerivedLocalizationFunctor C) =
      filteredAcyclicBoundedProperty C := by
  sorry

end Formalization.Books.Derived.Unit13
