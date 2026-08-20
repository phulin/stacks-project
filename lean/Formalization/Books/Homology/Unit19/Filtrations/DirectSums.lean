import Formalization.Books.Homology.Unit19.Filtrations.Strict

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open scoped ZeroObject

universe v u

namespace Formalization.Books.Homology.Unit19

/-! ### Direct sums and the two basic strictness lemmas -/

def filteredBiproduct {C : Type u} [Category.{v} C] [Abelian C]
    (A B : FilteredObject C) : FilteredObject C where
  carrier := A.carrier ⊞ B.carrier
  filtration :=
    { obj := fun i =>
        Subobject.mk (biprod.map (A.filtration.obj i).arrow (B.filtration.obj i).arrow)
      antitone := by
        intro i j hij
        have hA : A.filtration.obj j ≤ A.filtration.obj i :=
          A.filtration.antitone hij
        have hB : B.filtration.obj j ≤ B.filtration.obj i :=
          B.filtration.antitone hij
        apply Subobject.mk_le_mk_of_comm
          (biprod.map (Subobject.ofLE _ _ hA) (Subobject.ofLE _ _ hB))
        apply biprod.hom_ext <;> simp }

def filteredBiproductLift {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : A ⟶ D) :
    A ⟶ filteredBiproduct B D := by
  refine ⟨biprod.lift f.hom g.hom, ?_⟩
  intro i
  change (Subobject.mk
    (biprod.map (B.filtration.obj i).arrow (D.filtration.obj i).arrow)).Factors
    ((A.filtration.obj i).arrow ≫ biprod.lift f.hom g.hom)
  apply (Subobject.factors_iff _ _).mpr
  let u := (B.filtration.obj i).factorThru
    ((A.filtration.obj i).arrow ≫ f.hom) (f.map_filtration i)
  let v := (D.filtration.obj i).factorThru
    ((A.filtration.obj i).arrow ≫ g.hom) (g.map_filtration i)
  refine ⟨biprod.lift u v ≫
    (Subobject.underlyingIso
      (biprod.map (B.filtration.obj i).arrow (D.filtration.obj i).arrow)).inv, ?_⟩
  dsimp [u, v]
  apply biprod.hom_ext <;> simp [Category.assoc]

theorem strict_biproduct_lift_of_strict_mono {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : A ⟶ D)
    (hf : Strict f) (hfmono : FilteredInjective f) :
    Strict (filteredBiproductLift f g) ∧
      FilteredInjective (filteredBiproductLift f g) := by
  let : Mono f.hom := hfmono
  let h := filteredBiproductLift f g
  have hmono : FilteredInjective h := by
    change Mono (biprod.lift f.hom g.hom)
    constructor
    intro Z a b hab
    apply (cancel_mono f.hom).mp
    simpa only [Category.assoc, biprod.lift_fst] using
      congrArg (fun k => k ≫ biprod.fst) hab
  refine ⟨?_, hmono⟩
  apply (strict_iff_induced_filtration h hmono).2
  intro i
  let T : Subobject (B.carrier ⊞ D.carrier) :=
    Subobject.mk (biprod.map (B.filtration.obj i).arrow
      (D.filtration.obj i).arrow)
  let H : A.carrier ⟶ (B.carrier ⊞ D.carrier) :=
    biprod.lift f.hom g.hom
  let P := (Subobject.pullback H).obj T
  change A.filtration.obj i = P
  apply le_antisymm
  · apply Subobject.le_of_factors
    apply (CategoryTheory.Limits.pullback_factors_iff H T
      (A.filtration.obj i).arrow).2
    change T.Factors
      ((A.filtration.obj i).arrow ≫ biprod.lift f.hom g.hom)
    simpa [h, H, filteredBiproductLift, filteredBiproduct, T] using
      h.map_filtration i
  · rw [(strict_iff_induced_filtration f hfmono).1 hf i]
    apply Subobject.le_of_factors
    apply (CategoryTheory.Limits.pullback_factors_iff f.hom
      (B.filtration.obj i) P.arrow).2
    have hPfac : T.Factors (P.arrow ≫ H) :=
      (CategoryTheory.Limits.pullback_factors_iff H T P.arrow).1
        (Subobject.factors_self P)
    have hTfst : (B.filtration.obj i).Factors
        (T.arrow ≫ biprod.fst) := by
      have hfac := Subobject.factors_comp_arrow
        ((Subobject.underlyingIso
          (biprod.map (B.filtration.obj i).arrow
            (D.filtration.obj i).arrow)).hom ≫ biprod.fst)
      rw [Category.assoc, ← biprod.map_fst
        (B.filtration.obj i).arrow (D.filtration.obj i).arrow,
        ← Category.assoc,
        Subobject.underlyingIso_hom_comp_eq_mk] at hfac
      exact hfac
    have hcomp := Subobject.factors_of_factors_right
      (T.factorThru (P.arrow ≫ H) hPfac)
      (g := T.arrow ≫ biprod.fst) hTfst
    have heq :
        T.factorThru (P.arrow ≫ H) hPfac ≫
            (T.arrow ≫ biprod.fst) =
          (P.arrow ≫ H) ≫ biprod.fst := by
      calc
        T.factorThru (P.arrow ≫ H) hPfac ≫
              (T.arrow ≫ biprod.fst) =
            (T.factorThru (P.arrow ≫ H) hPfac ≫ T.arrow) ≫
              biprod.fst := (Category.assoc _ _ _).symm
        _ = (P.arrow ≫ H) ≫ biprod.fst := by
          rw [Subobject.factorThru_arrow]
    rw [heq] at hcomp
    have hh : H ≫ biprod.fst = f.hom := by
      dsimp [H]
      simp
    rw [Category.assoc, hh] at hcomp
    exact hcomp

def filteredBiproductDesc {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A) :
    filteredBiproduct B D ⟶ A := by
  refine ⟨biprod.desc f.hom g.hom, ?_⟩
  intro i
  let T : Subobject (B.carrier ⊞ D.carrier) :=
    Subobject.mk (biprod.map (B.filtration.obj i).arrow
      (D.filtration.obj i).arrow)
  change (A.filtration.obj i).Factors
    (T.arrow ≫ biprod.desc f.hom g.hom)
  apply (Subobject.factors_iff _ _).mpr
  let u := (A.filtration.obj i).factorThru
    ((B.filtration.obj i).arrow ≫ f.hom) (f.map_filtration i)
  let v := (A.filtration.obj i).factorThru
    ((D.filtration.obj i).arrow ≫ g.hom) (g.map_filtration i)
  refine ⟨(Subobject.underlyingIso
      (biprod.map (B.filtration.obj i).arrow (D.filtration.obj i).arrow)).hom ≫
    biprod.desc u v, ?_⟩
  have hT : T.arrow =
      (Subobject.underlyingIso
        (biprod.map (B.filtration.obj i).arrow
          (D.filtration.obj i).arrow)).hom ≫
        biprod.map (B.filtration.obj i).arrow
          (D.filtration.obj i).arrow := by
    simp [T]
  dsimp [u, v]
  calc
    ((Subobject.underlyingIso
      (biprod.map (B.filtration.obj i).arrow
        (D.filtration.obj i).arrow)).hom ≫
      biprod.desc
        ((A.filtration.obj i).factorThru
          ((B.filtration.obj i).arrow ≫ f.hom) (f.map_filtration i))
        ((A.filtration.obj i).factorThru
          ((D.filtration.obj i).arrow ≫ g.hom) (g.map_filtration i))) ≫
        (A.filtration.obj i).arrow =
      (Subobject.underlyingIso
        (biprod.map (B.filtration.obj i).arrow
          (D.filtration.obj i).arrow)).hom ≫
        (biprod.map (B.filtration.obj i).arrow
          (D.filtration.obj i).arrow) ≫
        biprod.desc f.hom g.hom := by
            rw [Category.assoc]
            congr 1
            simp [biprod.desc_eq, Category.assoc]
    _ = T.arrow ≫ biprod.desc f.hom g.hom := by
      rw [hT]
      simp only [Category.assoc]

theorem strict_biproduct_desc_of_strict_epi {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A)
    (hf : Strict f) (hfepi : FilteredSurjective f) :
    Strict (filteredBiproductDesc f g) ∧
      FilteredSurjective (filteredBiproductDesc f g) := by
  let : Epi f.hom := hfepi
  have hdesc_epi : FilteredSurjective (filteredBiproductDesc f g) := by
    change Epi (biprod.desc f.hom g.hom)
    have hfac : biprod.inl ≫ biprod.desc f.hom g.hom = f.hom :=
      biprod.inl_desc _ _
    exact epi_of_epi_fac hfac
  refine ⟨?_, hdesc_epi⟩
  apply (strict_iff_quotient_filtration
    (filteredBiproductDesc f g) hdesc_epi).2
  intro i
  let T : Subobject (B.carrier ⊞ D.carrier) :=
    Subobject.mk (biprod.map (B.filtration.obj i).arrow
      (D.filtration.obj i).arrow)
  let d : (B.carrier ⊞ D.carrier) ⟶ A.carrier :=
    biprod.desc f.hom g.hom
  let J := (Subobject.«exists» d).obj T
  change A.filtration.obj i = J
  apply le_antisymm
  · rw [(strict_iff_quotient_filtration f hfepi).1 hf i]
    have hBinl : (B.filtration.obj i) ≤
        (Subobject.pullback biprod.inl).obj T := by
      apply Subobject.le_of_factors
      apply (CategoryTheory.Limits.pullback_factors_iff biprod.inl T
        (B.filtration.obj i).arrow).2
      apply (Subobject.factors_iff _ _).mpr
      refine ⟨biprod.inl ≫ (Subobject.underlyingIso
        (biprod.map (B.filtration.obj i).arrow
          (D.filtration.obj i).arrow)).inv, ?_⟩
      simp [T, Category.assoc]
    have hunit : T ≤ (Subobject.pullback d).obj J :=
      ((Subobject.existsPullbackAdj
        d).homEquiv T J
        (CategoryTheory.homOfLE (show
          (Subobject.«exists» d).obj T ≤ J
            from le_rfl))).le
    have hcomp : f.hom = biprod.inl ≫ d := by
      symm
      dsimp [d]
      exact biprod.inl_desc _ _
    have hBpull : (B.filtration.obj i) ≤
        (Subobject.pullback f.hom).obj J := by
      rw [hcomp, Subobject.pullback_comp]
      exact hBinl.trans ((Subobject.pullback biprod.inl).monotone hunit)
    exact ((Subobject.existsPullbackAdj f.hom).homEquiv
      (B.filtration.obj i) J).symm
      (CategoryTheory.homOfLE hBpull) |>.le
  · have hTle : T ≤ (Subobject.pullback
        d).obj (A.filtration.obj i) := by
      apply Subobject.le_of_factors
      apply (CategoryTheory.Limits.pullback_factors_iff
        d (A.filtration.obj i) T.arrow).2
      change (A.filtration.obj i).Factors
        (T.arrow ≫ biprod.desc f.hom g.hom)
      exact (filteredBiproductDesc f g).map_filtration i
    exact ((Subobject.existsPullbackAdj
      d).homEquiv T
        (A.filtration.obj i)).symm
      (CategoryTheory.homOfLE hTle) |>.le

theorem strict_induced_iff {C : Type u} [Category.{v} C] [Abelian C]
    {A : FilteredObject C} (X : Subobject A.carrier) :
    Strict (inducedFilteredHom A X) := by
  have hmono : FilteredInjective (inducedFilteredHom A X) := by
    change Mono X.arrow
    infer_instance
  apply (strict_iff_induced_filtration (inducedFilteredHom A X) hmono).2
  exact fun _ => rfl

theorem strict_quotient_iff {C : Type u} [Category.{v} C] [Abelian C]
    {A : FilteredObject C} {Y : C} (π : A.carrier ⟶ Y) [Epi π] :
    Strict (quotientFilteredHom A π) := by
  apply (strict_iff_quotient_filtration (quotientFilteredHom A π)
    (by change Epi π; infer_instance)).2
  intro i
  rfl

theorem strict_composition_of_strict_of_mono {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hf : Strict f) (hg : Strict g) (hgmono : FilteredInjective g) :
    Strict (f ≫ g) := by
  let : Mono g.hom := hgmono
  have image_comp (X Y Z : C) (f₀ : X ⟶ Y) (g₀ : Y ⟶ Z)
      (P : Subobject X) :
      (Subobject.«exists» (f₀ ≫ g₀)).obj P =
        (Subobject.«exists» g₀).obj
          ((Subobject.«exists» f₀).obj P) := by
    apply le_antisymm
    · exact (((Subobject.existsPullbackAdj (f₀ ≫ g₀)).homEquiv P
          ((Subobject.«exists» g₀).obj
            ((Subobject.«exists» f₀).obj P))).symm
        (by
          rw [Subobject.pullback_comp]
          exact (Subobject.existsPullbackAdj f₀).homEquiv _ _
            ((Subobject.existsPullbackAdj g₀).unit.app
              ((Subobject.«exists» f₀).obj P)))).le
    · exact (((Subobject.existsPullbackAdj g₀).homEquiv
          ((Subobject.«exists» f₀).obj P)
          ((Subobject.«exists» (f₀ ≫ g₀)).obj P)).symm
        (((Subobject.existsPullbackAdj f₀).homEquiv P
            ((Subobject.pullback g₀).obj
              ((Subobject.«exists» (f₀ ≫ g₀)).obj P))).symm
          (by
            rw [← Subobject.pullback_comp]
            exact (Subobject.existsPullbackAdj (f₀ ≫ g₀)).unit.app P))).le
  intro i
  change (Subobject.«exists» (f.hom ≫ g.hom)).obj
      (A.filtration.obj i) =
    (Subobject.«exists» (f.hom ≫ g.hom)).obj (⊤ : Subobject A.carrier) ⊓
      D.filtration.obj i
  have hgi := hg i
  rw [Subobject.exists_iso_map g.hom] at hgi
  rw [image_comp, hf i, image_comp, Subobject.exists_iso_map g.hom,
    Subobject.inf_map, hgi]
  have hle_top :
      (Subobject.map g.hom).obj
          ((Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier)) ≤
        (Subobject.map g.hom).obj (⊤ : Subobject B.carrier) := by
    exact (Subobject.map g.hom).monotone le_top
  apply le_antisymm
  · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
  · exact le_inf inf_le_left
      (le_inf (inf_le_left.trans hle_top) inf_le_right)

theorem strict_composition_of_strict_of_epi {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hf : Strict f) (hg : Strict g) (hfepi : FilteredSurjective f) :
    Strict (f ≫ g) := by
  let : Epi f.hom := hfepi
  have image_comp (X Y Z : C) (f₀ : X ⟶ Y) (g₀ : Y ⟶ Z)
      (P : Subobject X) :
      (Subobject.«exists» (f₀ ≫ g₀)).obj P =
        (Subobject.«exists» g₀).obj
          ((Subobject.«exists» f₀).obj P) := by
    apply le_antisymm
    · exact (((Subobject.existsPullbackAdj (f₀ ≫ g₀)).homEquiv P
          ((Subobject.«exists» g₀).obj
            ((Subobject.«exists» f₀).obj P))).symm
        (by
          rw [Subobject.pullback_comp]
          exact (Subobject.existsPullbackAdj f₀).homEquiv _ _
            ((Subobject.existsPullbackAdj g₀).unit.app
              ((Subobject.«exists» f₀).obj P)))).le
    · exact (((Subobject.existsPullbackAdj g₀).homEquiv
          ((Subobject.«exists» f₀).obj P)
          ((Subobject.«exists» (f₀ ≫ g₀)).obj P)).symm
        (((Subobject.existsPullbackAdj f₀).homEquiv P
            ((Subobject.pullback g₀).obj
              ((Subobject.«exists» (f₀ ≫ g₀)).obj P))).symm
          (by
            rw [← Subobject.pullback_comp]
            exact (Subobject.existsPullbackAdj (f₀ ≫ g₀)).unit.app P))).le
  have htop :
      (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) =
        (⊤ : Subobject B.carrier) := by
    apply (Subobject.isIso_arrow_iff_eq_top _).mp
    let F := Subobject.imageFactorisation f.hom (⊤ : Subobject A.carrier)
    let _ : Epi F.F.e := by
      exact (strongEpi_of_strongEpiMonoFactorisation
        (Abelian.imageStrongEpiMonoFactorisation
          ((⊤ : Subobject A.carrier).arrow ≫ f.hom)) F.isImage).epi
    let _ : Epi F.F.m := epi_of_epi_fac F.F.fac
    change IsIso F.F.m
    exact isIso_of_mono_of_epi F.F.m
  have hfi := (strict_iff_quotient_filtration f hfepi).1 hf
  intro i
  change (Subobject.«exists» (f.hom ≫ g.hom)).obj
      (A.filtration.obj i) =
    (Subobject.«exists» (f.hom ≫ g.hom)).obj (⊤ : Subobject A.carrier) ⊓
      D.filtration.obj i
  rw [image_comp, ← hfi i, image_comp, htop, hg i]

structure StrictCompositionFailure {C : Type u} [Category.{v} C]
    [Abelian C] where
  A : FilteredObject C
  B : FilteredObject C
  D : FilteredObject C
  f : @FilteredHom C _ A B
  g : @FilteredHom C _ B D
  f_strict : Strict f
  g_strict : Strict g
  composite_nonzero : f.hom ≫ g.hom ≠ (0 : A.carrier ⟶ D.carrier)
  composite_not_strict : ¬ Strict (f ≫ g)

@[instance_reducible]
private noncomputable def fgModuleReprAbelian :
    Abelian (FGModuleRepr (ZMod 2)) := by
  let E : FGModuleRepr (ZMod 2) ≌ FGModuleCat.{0} (ZMod 2) :=
    (FGModuleRepr.embed (ZMod 2)).asEquivalence
  letI : Preadditive (FGModuleRepr (ZMod 2)) :=
    Preadditive.ofFullyFaithful E.fullyFaithfulFunctor
  letI : HasFiniteProducts (FGModuleRepr (ZMod 2)) :=
    { out := fun n =>
        Adjunction.hasLimitsOfShape_of_equivalence E.functor }
  exact abelianOfEquivalence E.functor

@[instance_reducible]
private noncomputable def uliftFgModuleReprAbelian :
    letI : Category.{0} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
      CategoryTheory.uliftCategory _
    Abelian (ULift.{u} (FGModuleRepr (ZMod 2))) := by
  letI : Category.{0} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    CategoryTheory.uliftCategory _
  letI : Abelian (FGModuleRepr (ZMod 2)) := fgModuleReprAbelian
  letI : Preadditive (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    Preadditive.ofFullyFaithful
      (ULift.equivalence (C := FGModuleRepr (ZMod 2))).symm.fullyFaithfulFunctor
  letI : HasFiniteProducts (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    { out := fun n =>
        Adjunction.hasLimitsOfShape_of_equivalence
          (ULift.equivalence (C := FGModuleRepr (ZMod 2))).inverse }
  exact abelianOfEquivalence
    (ULift.equivalence (C := FGModuleRepr (ZMod 2))).inverse

@[instance_reducible]
private noncomputable def uliftHomFgModuleReprAbelian :
    letI : Category.{0} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
      CategoryTheory.uliftCategory _
    letI : Category.{v} (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
      ULiftHom.category
    Abelian (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) := by
  letI : Category.{0} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    CategoryTheory.uliftCategory _
  letI : Category.{v} (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    ULiftHom.category
  letI : Abelian (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    uliftFgModuleReprAbelian
  letI : Preadditive (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    Preadditive.ofFullyFaithful
      (ULiftHom.equiv (C := ULift.{u} (FGModuleRepr (ZMod 2)))).symm.fullyFaithfulFunctor
  letI : HasFiniteProducts
      (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    { out := fun n =>
        Adjunction.hasLimitsOfShape_of_equivalence
          (ULiftHom.equiv (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse }
  exact abelianOfEquivalence
    (ULiftHom.equiv (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse

private theorem uliftHomFgModuleReprUnit_ne_zero
    : letI : Abelian (FGModuleRepr (ZMod 2)) := fgModuleReprAbelian
      letI : Preadditive (FGModuleRepr (ZMod 2)) :=
        fgModuleReprAbelian.toPreadditive
      letI : Category.{0} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
        CategoryTheory.uliftCategory _
      letI : Preadditive (ULift.{u} (FGModuleRepr (ZMod 2))) :=
        Preadditive.ofFullyFaithful
          (ULift.equivalence (C := FGModuleRepr (ZMod 2))).symm.fullyFaithfulFunctor
      letI : Category.{v} (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
        ULiftHom.category
      letI : Abelian (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
        uliftHomFgModuleReprAbelian
    (𝟙 (ULiftHom.objUp (ULift.up (FGModuleRepr.ofFinite (ZMod 2) (ZMod 2)))) :
      _ ⟶ _) ≠ 0 := by
  let : Abelian (FGModuleRepr (ZMod 2)) := fgModuleReprAbelian
  let : Preadditive (FGModuleRepr (ZMod 2)) :=
    fgModuleReprAbelian.toPreadditive
  let : Category.{0} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    CategoryTheory.uliftCategory _
  let : Preadditive (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    Preadditive.ofFullyFaithful
      (ULift.equivalence (C := FGModuleRepr (ZMod 2))).symm.fullyFaithfulFunctor
  let : Category.{v} (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    ULiftHom.category
  let : Preadditive (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    Preadditive.ofFullyFaithful
      (ULiftHom.equiv
        (C := ULift.{u} (FGModuleRepr (ZMod 2)))).symm.fullyFaithfulFunctor
  let : (FGModuleRepr.embed (ZMod 2)).Additive :=
    Functor.FullyFaithful.additive_ofFullyFaithful
      (FGModuleRepr.embed (ZMod 2)).asEquivalence.fullyFaithfulFunctor
  let : (ULift.equivalence
      (C := FGModuleRepr (ZMod 2))).inverse.Additive :=
    Functor.FullyFaithful.additive_ofFullyFaithful
      (ULift.equivalence
        (C := FGModuleRepr (ZMod 2))).symm.fullyFaithfulFunctor
  let : (ULiftHom.equiv
      (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse.Additive :=
    Functor.FullyFaithful.additive_ofFullyFaithful
      (ULiftHom.equiv
        (C := ULift.{u} (FGModuleRepr (ZMod 2)))).symm.fullyFaithfulFunctor
  let V : ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    ULiftHom.objUp (ULift.up (FGModuleRepr.ofFinite (ZMod 2) (ZMod 2)))
  let e := FGModuleRepr.ofFiniteEquiv (ZMod 2) (ZMod 2)
  let x : ((FGModuleRepr.embed (ZMod 2)).obj
      ((ULift.equivalence
        (C := FGModuleRepr (ZMod 2))).inverse.obj
        ((ULiftHom.equiv
          (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse.obj V)) : Type) :=
    ULift.up (e.symm 1)
  have hx : x ≠ 0 := by
    intro hx
    apply (by decide : (1 : ZMod 2) ≠ 0)
    have hx' := congrArg (fun y => e (ULift.down y)) hx
    change e x.down = e 0 at hx'
    simpa [x] using hx'
  intro h
  have h' := congrArg
    (fun k : V ⟶ V =>
      (FGModuleRepr.embed (ZMod 2)).map
        ((ULift.equivalence
          (C := FGModuleRepr (ZMod 2))).inverse.map
          ((ULiftHom.equiv
            (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse.map k))) h
  have hzero :
      (FGModuleRepr.embed (ZMod 2)).map
          ((ULift.equivalence
            (C := FGModuleRepr (ZMod 2))).inverse.map
            ((ULiftHom.equiv
              (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse.map
              (0 : V ⟶ V))) = 0 := by
    rw [Functor.map_zero, Functor.map_zero, Functor.map_zero]
  have h'zero := h'.trans hzero
  have hmap :
      (FGModuleRepr.embed (ZMod 2)).map
          ((ULift.equivalence
            (C := FGModuleRepr (ZMod 2))).inverse.map
            ((ULiftHom.equiv
              (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse.map
              (𝟙 (ULiftHom.objUp
                (ULift.up (FGModuleRepr.ofFinite (ZMod 2) (ZMod 2))))))) =
        𝟙 _ := by
    simp
  have h'' := congrArg
    (fun k => k.hom x) h'zero
  rw [hmap] at h''
  have hid_apply :
      (ConcreteCategory.hom
        ((𝟙 ((FGModuleRepr.embed (ZMod 2)).obj
          ((ULift.equivalence
            (C := FGModuleRepr (ZMod 2))).inverse.obj
            ((ULiftHom.equiv
              (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse.obj V))) :
          _ ⟶ _).hom)) x = x := by
    simp [ModuleCat.hom_id, LinearMap.id_apply]
  rw [hid_apply] at h''
  exact hx h''

private theorem nonzero_of_subobject_factor
    {C : Type u} [Category.{v} C] [Abelian C]
    {V W Z : C} (d : V ⟶ W) [Mono d]
    (q : W ⟶ Z) (r : Z ⟶ V) (hId : (𝟙 V : V ⟶ V) ≠ 0)
    (hfactor : (Subobject.underlyingIso d).inv ≫
      (Subobject.mk d).arrow ≫ q ≫ r = 𝟙 V) :
    (Subobject.mk d).arrow ≫ q ≠ 0 := by
  intro hz
  apply hId
  rw [← hfactor]
  simpa only [Category.assoc, zero_comp, comp_zero] using
    congrArg (fun t => (Subobject.underlyingIso d).inv ≫ t ≫ r) hz

private theorem not_strict_of_bot_top
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
      (Subobject.«exists» k.hom).obj
        (⊤ : Subobject A.carrier) := hi
  let I := Subobject.imageFactorisation k.hom
    (⊤ : Subobject A.carrier)
  have hF : Subobject.mk I.F.m =
      (Subobject.«exists» k.hom).obj
        (⊤ : Subobject A.carrier) := by
    change Subobject.mk
        ((Subobject.«exists» k.hom).obj
          (⊤ : Subobject A.carrier)).arrow = _
    simp
  have hfac' : (Subobject.mk I.F.m).Factors k.hom := by
    change ∃ h : A.carrier ⟶ I.F.I,
      h ≫ I.F.m = k.hom
    refine ⟨(asIso (⊤ : Subobject A.carrier).arrow).inv ≫
      I.F.e, ?_⟩
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

private theorem diagonal_pullback_bot
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

private def singleStepFiltration {C : Type u} [Category.{v} C]
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

private theorem diagonalBiproduct_singleStep_zero
    {C : Type u} [Category.{v} C] [Abelian C] (V : C) :
    (Subobject.pullback
      (Subobject.mk (biprod.lift (𝟙 V) (𝟙 V))).arrow).obj
        ((singleStepFiltration (Subobject.mk (biprod.inl : V ⟶ V ⊞ V))).obj 0) = ⊥ := by
  change (Subobject.pullback
    (Subobject.mk (biprod.lift (𝟙 V) (𝟙 V))).arrow).obj
      (Subobject.mk (biprod.inl : V ⟶ V ⊞ V)) = ⊥
  apply diagonal_pullback_bot
  · rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
    simp
  · rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
    simp

set_option maxHeartbeats 8000000 in
theorem exists_strict_composition_failure :
    ∃ (C : Type u) (_ : Category.{v} C) (_ : Abelian C),
      Nonempty (@StrictCompositionFailure C _ _) := by
  let : Abelian (FGModuleRepr (ZMod 2)) :=
    fgModuleReprAbelian
  let : Preadditive (FGModuleRepr (ZMod 2)) :=
    fgModuleReprAbelian.toPreadditive
  let : Category.{0} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    CategoryTheory.uliftCategory _
  let : Preadditive (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    Preadditive.ofFullyFaithful
      (ULift.equivalence (C := FGModuleRepr (ZMod 2))).symm.fullyFaithfulFunctor
  let : Category.{v} (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    ULiftHom.category
  let : Abelian (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    uliftHomFgModuleReprAbelian
  let V : ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    ULiftHom.objUp (ULift.up (FGModuleRepr.ofFinite (ZMod 2) (ZMod 2)))
  let W : ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2))) := V ⊞ V
  let u : V ⟶ W := biprod.inl
  let v : V ⟶ W := biprod.inr
  let d : V ⟶ W := biprod.lift (𝟙 V) (𝟙 V)
  let : Mono u := by
    dsimp [u]
    exact mono_of_mono_fac (biprod.inl_fst)
  let : Mono v := by
    dsimp [v]
    exact mono_of_mono_fac (biprod.inr_snd)
  let : Mono d := by
    dsimp [d]
    exact mono_of_mono_fac (biprod.lift_fst _ _)
  let U : Subobject W := Subobject.mk u
  let X : Subobject W := Subobject.mk d
  let Y : Subobject W := Subobject.mk v
  let F : DecreasingFiltration
      (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) W :=
    singleStepFiltration U
  let B₀ : FilteredObject
      (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    { carrier := W, filtration := F }
  let A₀ : FilteredObject
      (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    inducedFilteredObject B₀ X
  let q : W ⟶ cokernel Y.arrow := cokernel.π Y.arrow
  let D₀ : FilteredObject
      (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    quotientFilteredObject B₀ q
  let f₀ : A₀ ⟶ B₀ := inducedFilteredHom B₀ X
  let g₀ : B₀ ⟶ D₀ := quotientFilteredHom B₀ q
  have hUfst : IsIso (U.arrow ≫ biprod.fst) := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
    rw [biprod.inl_fst]
    infer_instance
  have hvr : biprod.inr ≫ q = 0 := by
    apply (cancel_epi (Subobject.underlyingIso v).hom).mp
    rw [← Category.assoc,
      Subobject.underlyingIso_hom_comp_eq_mk,
      cokernel.condition, comp_zero]
  have hY : Y.arrow ≫ biprod.fst = 0 := by
    change (Subobject.mk v).arrow ≫ biprod.fst = 0
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
    simp [v]
  let r : cokernel Y.arrow ⟶ V := cokernel.desc Y.arrow biprod.fst hY
  have hqr : q ≫ r = biprod.fst := by
    dsimp [q, r]
    exact cokernel.π_desc _ _ _
  let p : W ⟶ (U : ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    biprod.fst ≫ (Subobject.underlyingIso u).inv
  have hfactor : q = p ≫ (U.arrow ≫ q) := by
    calc
      q = 𝟙 W ≫ q := by simp
      _ = (biprod.fst ≫ biprod.inl +
          biprod.snd ≫ biprod.inr) ≫ q := by rw [biprod.total]
      _ = biprod.fst ≫ biprod.inl ≫ q +
          biprod.snd ≫ biprod.inr ≫ q := by
        rw [Preadditive.add_comp, Category.assoc, Category.assoc]
      _ = biprod.fst ≫ biprod.inl ≫ q := by rw [hvr, comp_zero, add_zero]
      _ = p ≫ (U.arrow ≫ q) := by
        simp [p, U, u, Category.assoc]
  let : Epi (U.arrow ≫ q) := epi_of_epi_fac hfactor.symm
  have hqu : (Subobject.«exists» q).obj U =
      (⊤ : Subobject (cokernel Y.arrow)) := by
    apply (Subobject.isIso_arrow_iff_eq_top _).mp
    let I := Subobject.imageFactorisation q U
    let _ : Epi I.F.m := epi_of_epi_fac I.F.fac
    change IsIso I.F.m
    exact isIso_of_mono_of_epi I.F.m
  have hnonzero : f₀.hom ≫ g₀.hom ≠
      (0 : A₀.carrier ⟶ D₀.carrier) := by
    change X.arrow ≫ q ≠ 0
    have hId : (𝟙 V : V ⟶ V) ≠ 0 := by
      simpa [V] using uliftHomFgModuleReprUnit_ne_zero
    have hid : (Subobject.underlyingIso d).inv ≫ X.arrow ≫ q ≫ r =
        𝟙 V := by
      rw [hqr]
      rw [← Subobject.underlyingIso_hom_comp_eq_mk]
      simp [d]
    simpa [X] using
      nonzero_of_subobject_factor d q r hId (by simpa [X] using hid)
  have hB0 : B₀.filtration.obj 0 = U := by
    simp [B₀, F, singleStepFiltration]
  have hA0 : A₀.filtration.obj 0 = ⊥ := by
    exact diagonalBiproduct_singleStep_zero V
  have hD0 : D₀.filtration.obj 0 =
      (⊤ : Subobject (cokernel Y.arrow)) := by
    change (Subobject.«exists» q).obj (B₀.filtration.obj 0) = _
    rw [hB0, hqu]
  have hnotstrict : ¬ Strict (f₀ ≫ g₀) :=
    not_strict_of_bot_top (f₀ ≫ g₀) hnonzero hA0 hD0
  have hfstrict : Strict f₀ := by
    simpa only [f₀] using (strict_induced_iff (A := B₀) X)
  have hgstrict : Strict g₀ := by
    exact strict_quotient_iff (A := B₀) (π := q)
  refine ⟨ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2))),
    inferInstance, inferInstance, ?_⟩
  let S : StrictCompositionFailure :=
    { A := A₀, B := B₀, D := D₀, f := f₀, g := g₀,
      f_strict := hfstrict,
      g_strict := hgstrict,
      composite_nonzero := hnonzero,
      composite_not_strict := hnotstrict }
  exact ⟨S⟩

theorem exists_filtered_category_not_abelian :
    ∃ (C : Type u) (_ : Category.{v} C) (_ : Abelian C),
      ¬ Nonempty (CategoryTheory.Abelian (FilteredObject C)) := by
  obtain ⟨C, hcat, hAbC, hC⟩ := exists_strict_composition_failure
  refine ⟨C, hcat, hAbC, ?_⟩
  let : Category.{v} C := hcat
  let : Abelian C := hAbC
  rintro ⟨hAb⟩
  let : Abelian (FilteredObject C) := hAb
  let : Preadditive (FilteredObject C) := hAb.toPreadditive
  let : HasFiniteBiproducts (FilteredObject C) :=
    CategoryTheory.Abelian.hasFiniteBiproducts
  let : HasBinaryProducts (FilteredObject C) :=
    CategoryTheory.Limits.hasBinaryProducts_of_hasLimit_pair _
  have hpre : hAb.toPreadditive =
      Formalization.Books.Homology.Unit19.filteredPreadditive (C := C) :=
    Subsingleton.elim _ _
  let hAb' : Abelian (FilteredObject C) :=
    { toPreadditive := Formalization.Books.Homology.Unit19.filteredPreadditive (C := C)
      toIsNormalMonoCategory := hpre ▸ hAb.toIsNormalMonoCategory
      toIsNormalEpiCategory := hpre ▸ hAb.toIsNormalEpiCategory
      has_finite_products := hAb.has_finite_products
      has_kernels := hpre ▸ hAb.has_kernels
      has_cokernels := hpre ▸ hAb.has_cokernels }
  let : Abelian (FilteredObject C) := hAb'
  obtain ⟨S⟩ := hC
  let k : S.A ⟶ S.D := S.f ≫ S.g
  apply S.composite_not_strict
  apply (strict_iff_coimage_image_isIso k).2
  exact (Abelian.coimageIsoImage k).isIso_hom

end Formalization.Books.Homology.Unit19
