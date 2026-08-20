import Formalization.Books.Homology.Unit19.Filtrations.DirectSums

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open scoped ZeroObject

universe v u

namespace Formalization.Books.Homology.Unit19

/-! ### Subquotients -/

def inducedSubobjectMap {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    inducedFilteredObject A X ⟶ inducedFilteredObject A Y := by
  refine ⟨Subobject.ofLE X Y hXY, ?_⟩
  intro i
  change ((Subobject.pullback Y.arrow).obj (A.filtration.obj i)).Factors
    (((Subobject.pullback X.arrow).obj (A.filtration.obj i)).arrow ≫
      X.ofLE Y hXY)
  rw [CategoryTheory.Limits.pullback_factors_iff]
  rw [Category.assoc, Subobject.ofLE_arrow]
  rw [← CategoryTheory.Limits.pullback_factors_iff]
  apply Subobject.factors_self

def filteredSubquotient {C : Type u} [Category.{v} C] [Abelian C]
    {A : FilteredObject C} {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    FilteredObject C :=
  filteredCokernel (inducedSubobjectMap A hXY)

def subquotientQuotientMap {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    quotientFilteredObject A (cokernel.π X.arrow) ⟶
      quotientFilteredObject A (cokernel.π Y.arrow) := by
  refine ⟨cokernel.desc X.arrow (cokernel.π Y.arrow) ?_, ?_⟩
  · change X.arrow ≫ cokernel.π Y.arrow = 0
    rw [← Subobject.ofLE_arrow hXY, Category.assoc, cokernel.condition, comp_zero]
  · intro i
    let F := A.filtration.obj i
    let qX := cokernel.π X.arrow
    let qY := cokernel.π Y.arrow
    let d := cokernel.desc X.arrow qY (by
      rw [← Subobject.ofLE_arrow hXY, Category.assoc, cokernel.condition, comp_zero])
    let TX := (Subobject.«exists» qX).obj F
    let TY := (Subobject.«exists» qY).obj F
    have hunit : F ≤ (Subobject.pullback qY).obj TY :=
      ((Subobject.existsPullbackAdj qY).homEquiv F TY)
        (CategoryTheory.homOfLE (show
          (Subobject.«exists» qY).obj F ≤ TY from le_rfl)) |>.le
    have hcomp : qX ≫ d = qY := by
      exact cokernel.π_desc _ _ _
    have hXle : F ≤ (Subobject.pullback (qX ≫ d)).obj TY := by
      rw [hcomp]
      exact hunit
    have hXle' : F ≤ (Subobject.pullback qX).obj
        ((Subobject.pullback d).obj TY) := by
      simpa only [Subobject.pullback_comp] using hXle
    have hIle : TX ≤ (Subobject.pullback d).obj TY :=
      ((Subobject.existsPullbackAdj qX).homEquiv F
        ((Subobject.pullback d).obj TY)).symm
        (CategoryTheory.homOfLE hXle') |>.le
    apply (CategoryTheory.Limits.pullback_factors_iff d TY TX.arrow).mp
    exact Subobject.factors_of_le TX.arrow hIle (Subobject.factors_self TX)

def ambientSubquotientKernel {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    FilteredObject C :=
  filteredKernel (subquotientQuotientMap A hXY)

private theorem exists_pullback_of_epi {C : Type u} [Category.{v} C]
    [Abelian C] {X Y : C} (q : X ⟶ Y) [Epi q] (P : Subobject Y) :
    (Subobject.«exists» q).obj ((Subobject.pullback q).obj P) = P := by
  apply le_antisymm
  · exact ((Subobject.existsPullbackAdj q).homEquiv
      ((Subobject.pullback q).obj P) P).symm
      (CategoryTheory.homOfLE le_rfl) |>.le
  · apply Subobject.le_of_factors
    let F := Subobject.imageFactorisation q
      ((Subobject.pullback q).obj P)
    let hpb := Subobject.isPullback q P
    let : Epi hpb.cone.fst :=
      Abelian.epi_fst_of_isLimit P.arrow q (s := hpb.cone) hpb.isLimit
    let : Epi (Subobject.pullbackπ q P) := by
      change Epi hpb.cone.fst
      infer_instance
    let : Epi F.F.e := by
      exact (strongEpi_of_strongEpiMonoFactorisation
        (Abelian.imageStrongEpiMonoFactorisation
          (((Subobject.pullback q).obj P).arrow ≫ q))
        F.isImage).epi
    have hfac : (Subobject.pullbackπ q P) ≫ P.arrow =
        ((Subobject.pullback q).obj P).arrow ≫ q := by
      exact (Subobject.isPullback q P).w
    have heq : imageSubobject (F.F.e ≫ F.F.m) =
        imageSubobject F.F.m := by
      have hle : imageSubobject (F.F.e ≫ F.F.m) ≤
          imageSubobject F.F.m :=
        Limits.imageSubobject_comp_le F.F.e F.F.m
      let : Epi (Subobject.ofLE (imageSubobject (F.F.e ≫ F.F.m))
          (imageSubobject F.F.m) hle) :=
        Limits.imageSubobject_comp_le_epi_of_epi F.F.e F.F.m
      let : IsIso (Subobject.ofLE (imageSubobject (F.F.e ≫ F.F.m))
          (imageSubobject F.F.m) hle) :=
        isIso_of_mono_of_epi _
      exact Subobject.eq_of_comm (asIso
        (Subobject.ofLE (imageSubobject (F.F.e ≫ F.F.m))
          (imageSubobject F.F.m) hle))
        (Subobject.ofLE_arrow hle)
    have hmk : Subobject.mk F.F.m = P := by
      calc
        Subobject.mk F.F.m = imageSubobject F.F.m :=
          (imageSubobject_mono F.F.m).symm
        _ = imageSubobject (F.F.e ≫ F.F.m) := heq.symm
        _ = imageSubobject (((Subobject.pullback q).obj P).arrow ≫ q) := by
          rw [F.F.fac]
        _ = imageSubobject ((Subobject.pullbackπ q P) ≫ P.arrow) := by
          rw [hfac]
        _ = imageSubobject P.arrow := by
          let hle := Limits.imageSubobject_comp_le
            (Subobject.pullbackπ q P) P.arrow
          let : Epi (Subobject.ofLE
              (imageSubobject ((Subobject.pullbackπ q P) ≫ P.arrow))
              (imageSubobject P.arrow) hle) :=
            Limits.imageSubobject_comp_le_epi_of_epi
              (Subobject.pullbackπ q P) P.arrow
          let : IsIso (Subobject.ofLE
              (imageSubobject ((Subobject.pullbackπ q P) ≫ P.arrow))
              (imageSubobject P.arrow) hle) :=
            isIso_of_mono_of_epi _
          exact Subobject.eq_of_comm (asIso
            (Subobject.ofLE
              (imageSubobject ((Subobject.pullbackπ q P) ≫ P.arrow))
              (imageSubobject P.arrow) hle))
            (Subobject.ofLE_arrow hle)
        _ = P := by simpa using (imageSubobject_mono P.arrow)
    have hF : Subobject.mk F.F.m =
        (Subobject.«exists» q).obj ((Subobject.pullback q).obj P) := by
      change Subobject.mk
        ((Subobject.«exists» q).obj ((Subobject.pullback q).obj P)).arrow = _
      simp
    have hEq :
        (Subobject.«exists» q).obj ((Subobject.pullback q).obj P) = P := by
      rw [← hF]
      exact hmk
    rw [hEq]
    exact Subobject.factors_self _

theorem exists_inf_pullback_eq_exists_inf_ab {C : Type u}
    [Category.{v} C] [Abelian C] {S T : C} (q : S ⟶ T)
    (P : Subobject S) (Q : Subobject T) :
    (Subobject.«exists» q).obj
        (P ⊓ (Subobject.pullback q).obj Q) =
      (Subobject.«exists» q).obj P ⊓ Q := by
  let F := Subobject.imageFactorisation q P
  have hF : Subobject.mk F.F.m =
      (Subobject.«exists» q).obj P := by
    change Subobject.mk ((Subobject.«exists» q).obj P).arrow = _
    simp
  let eF : F.F.I ≅ ((Subobject.«exists» q).obj P : C) :=
    Subobject.isoOfMkEqMk F.F.m
      ((Subobject.«exists» q).obj P).arrow (by
        simpa only [Subobject.mk_arrow] using hF)
  let : Epi F.F.e := by
    exact (strongEpi_of_strongEpiMonoFactorisation
      (Abelian.imageStrongEpiMonoFactorisation (P.arrow ≫ q))
      F.isImage).epi
  let : Epi eF.hom := by
    dsimp [eF]
    infer_instance
  have heF_arrow : eF.hom ≫ ((Subobject.«exists» q).obj P).arrow = F.F.m := by
    dsimp [eF, F]
    exact Subobject.ofMkLEMk_comp _
  have heF_m : eF.hom ≫ (Subobject.imageFactorisation q P).F.m = F.F.m := by
    change eF.hom ≫ ((Subobject.«exists» q).obj P).arrow = F.F.m
    exact heF_arrow
  have hcomp0 : (F.F.e ≫ eF.hom) ≫
      ((Subobject.«exists» q).obj P).arrow = P.arrow ≫ q := by
    simp only [Category.assoc]
    rw [heF_arrow, F.F.fac]
  let φ : ((P ⊓ (Subobject.pullback q).obj Q : Subobject S) : C) ⟶
      (((Subobject.«exists» q).obj P ⊓ Q : Subobject T) : C) :=
    (Subobject.inf_isPullback ((Subobject.«exists» q).obj P) Q).flip.lift
      ((Subobject.ofLE _ _
        (Subobject.inf_le_right P ((Subobject.pullback q).obj Q))) ≫
        (Subobject.pullbackπ q Q))
      ((Subobject.ofLE _ _
        (Subobject.inf_le_left P ((Subobject.pullback q).obj Q))) ≫
          F.F.e ≫ eF.hom)
      (by
        rw [Category.assoc, (Subobject.isPullback q Q).w,
          ← Category.assoc, Subobject.ofLE_arrow]
        simp only [Category.assoc]
        rw [heF_arrow, F.F.fac]
        simp)
  have hφ : IsPullback φ
      (Subobject.ofLE _ _
        (Subobject.inf_le_left P ((Subobject.pullback q).obj Q)))
      (Subobject.ofLE _ _
      (Subobject.inf_le_left ((Subobject.«exists» q).obj P) Q))
      (F.F.e ≫ eF.hom) := by
    apply IsPullback.of_right
      (t := (Subobject.inf_isPullback ((Subobject.«exists» q).obj P) Q).flip)
      (p := by simp [φ])
    rw [hcomp0]
    simpa [φ, IsPullback.lift_fst,
      (Subobject.isPullback q Q).paste_horiz_iff] using
      (Subobject.inf_isPullback P ((Subobject.pullback q).obj Q)).flip
  have hφepi : Epi φ := by
    let : Epi (F.F.e ≫ eF.hom) := by infer_instance
    let : Epi hφ.cone.fst :=
      Abelian.epi_fst_of_isLimit
        (Subobject.ofLE _ _
          (Subobject.inf_le_left ((Subobject.«exists» q).obj P) Q))
        (F.F.e ≫ eF.hom)
        (s := hφ.cone) hφ.isLimit
    change Epi hφ.cone.fst
    infer_instance
  let : Epi φ := hφepi
  let H : StrongEpiMonoFactorisation
      ((P ⊓ (Subobject.pullback q).obj Q).arrow ≫ q) :=
    { I := (((Subobject.«exists» q).obj P ⊓ Q : Subobject T) : C)
      m := ((Subobject.«exists» q).obj P ⊓ Q).arrow
      e := φ
      fac := by
        rw [← Subobject.inf_comp_left, ← Category.assoc,
          (Subobject.inf_isPullback ((Subobject.«exists» q).obj P) Q).flip.lift_snd]
        simp only [Category.assoc]
        rw [heF_arrow, F.F.fac, ← Category.assoc,
          Subobject.ofLE_arrow]
      e_strong_epi := strongEpi_of_epi φ }
  let J := Subobject.imageFactorisation q
    (P ⊓ (Subobject.pullback q).obj Q)
  have hJ : Subobject.mk J.F.m =
      (Subobject.«exists» q).obj (P ⊓ (Subobject.pullback q).obj Q) := by
    change Subobject.mk
      ((Subobject.«exists» q).obj (P ⊓ (Subobject.pullback q).obj Q)).arrow = _
    simp
  let eJ : ((Subobject.«exists» q).obj
      (P ⊓ (Subobject.pullback q).obj Q) : C) ≅ J.F.I :=
    (Subobject.isoOfMkEqMk J.F.m
      ((Subobject.«exists» q).obj
        (P ⊓ (Subobject.pullback q).obj Q)).arrow (by
          simpa only [Subobject.mk_arrow] using hJ)).symm
  let i : ((Subobject.«exists» q).obj
      (P ⊓ (Subobject.pullback q).obj Q) : C) ≅ H.I :=
    eJ ≪≫ IsImage.isoExt J.isImage H.toMonoIsImage
  have hi : i.hom ≫ H.m =
      ((Subobject.«exists» q).obj
        (P ⊓ (Subobject.pullback q).obj Q)).arrow := by
    dsimp [i, eJ]
    rw [Category.assoc, IsImage.isoExt_hom_m]
    exact Subobject.ofMkLEMk_comp _
  exact Subobject.eq_of_comm i hi

theorem exists_top_eq_imageSubobject {C : Type u}
    [Category.{v} C] [Abelian C] {X Y : C} (q : X ⟶ Y) :
    (Subobject.«exists» q).obj (⊤ : Subobject X) = imageSubobject q := by
  let F := Subobject.imageFactorisation q (⊤ : Subobject X)
  have hF : Subobject.mk F.F.m =
      (Subobject.«exists» q).obj (⊤ : Subobject X) := by
    change Subobject.mk
      ((Subobject.«exists» q).obj (⊤ : Subobject X)).arrow = _
    simp
  have heq : imageSubobject (F.F.e ≫ F.F.m) =
      imageSubobject F.F.m := by
    let hE : Epi F.F.e :=
      (strongEpi_of_strongEpiMonoFactorisation
        (Abelian.imageStrongEpiMonoFactorisation
          ((⊤ : Subobject X).arrow ≫ q)) F.isImage).epi
    have hle : imageSubobject (F.F.e ≫ F.F.m) ≤
        imageSubobject F.F.m :=
      Limits.imageSubobject_comp_le F.F.e F.F.m
    let hE' : Epi (Subobject.ofLE
        (imageSubobject (F.F.e ≫ F.F.m))
        (imageSubobject F.F.m) hle) :=
      Limits.imageSubobject_comp_le_epi_of_epi F.F.e F.F.m
    let : IsIso (Subobject.ofLE
        (imageSubobject (F.F.e ≫ F.F.m))
        (imageSubobject F.F.m) hle) :=
      isIso_of_mono_of_epi _
    exact Subobject.eq_of_comm (asIso
      (Subobject.ofLE (imageSubobject (F.F.e ≫ F.F.m))
        (imageSubobject F.F.m) hle))
      (Subobject.ofLE_arrow hle)
  calc
    (Subobject.«exists» q).obj (⊤ : Subobject X) =
        Subobject.mk F.F.m := hF.symm
    _ = imageSubobject F.F.m := (imageSubobject_mono F.F.m).symm
    _ = imageSubobject (F.F.e ≫ F.F.m) := heq.symm
    _ = imageSubobject ((⊤ : Subobject X).arrow ≫ q) := by
      rw [F.F.fac]
    _ = imageSubobject q := imageSubobject_iso_comp _ _

private theorem strict_induced_quotient_of_le_core {C : Type u} [Category.{v} C]
    [Abelian C] (A : FilteredObject C) {X Y : Subobject A.carrier}
    (hXY : X ≤ Y) :
    Strict (inducedFilteredHom A Y ≫
      quotientFilteredHom A (cokernel.π X.arrow)) := by
  let qX := cokernel.π X.arrow
  intro i
  let Fi := A.filtration.obj i
  let Yi := (Subobject.pullback Y.arrow).obj Fi
  let Qi := (Subobject.«exists» qX).obj Fi
  have hXlimit :
      IsLimit (KernelFork.ofι X.arrow (cokernel.condition X.arrow)) :=
    Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ qX (cokernel.condition X.arrow))
      (cokernelIsCokernel X.arrow)
  let eX := hXlimit.conePointUniqueUpToIso (kernelIsKernel qX)
  have heX : eX.hom ≫ kernel.ι qX = X.arrow := by
    simpa [eX] using
      IsLimit.conePointUniqueUpToIso_hom_comp hXlimit
        (kernelIsKernel qX) WalkingParallelPair.zero
  have hpre (R : Subobject A.carrier) :
      (Subobject.pullback qX).obj
          ((Subobject.«exists» qX).obj R) = R ⊔ X := by
    have h := pullback_exists_eq_sup_kernel
      (quotientFilteredHom A qX) R
    change (Subobject.pullback qX).obj
        ((Subobject.«exists» qX).obj R) =
      R ⊔ Subobject.mk (kernel.ι qX) at h
    have hkX : Subobject.mk (kernel.ι qX) = X := by
      simpa only [Subobject.mk_arrow] using
        (Subobject.mk_eq_mk_of_comm X.arrow (kernel.ι qX) eX heX).symm
    simpa only [hkX] using h
  have hYmap : (Subobject.map Y.arrow).obj Yi = Y ⊓ Fi := by
    simpa [Yi] using (Subobject.inf_eq_map_pullback Y Fi).symm
  have hYtop :
      (Subobject.«exists» Y.arrow).obj (⊤ : Subobject (Y : C)) = Y := by
    rw [Subobject.exists_iso_map Y.arrow, Subobject.map_top]
    simp
  have hYimage :
      (Subobject.«exists» qX).obj (Y ⊓ Fi) =
        (Subobject.«exists» qX).obj Y ⊓ Qi := by
    apply le_antisymm
    · apply le_inf
      · exact (Subobject.«exists» qX).monotone inf_le_left
      · exact ((Subobject.existsPullbackAdj qX).homEquiv
          (Y ⊓ Fi) Qi).symm
          (CategoryTheory.homOfLE
            (inf_le_right.trans
              ((Subobject.existsPullbackAdj qX).unit.app Fi).le)) |>.le
    · let R := (Subobject.«exists» qX).obj Y ⊓ Qi
      have hRle : (Subobject.pullback qX).obj R ≤
          (Subobject.pullback qX).obj
              ((Subobject.«exists» qX).obj Y) ⊓
            (Subobject.pullback qX).obj Qi := by
        exact le_inf
          ((Subobject.pullback qX).monotone inf_le_left)
          ((Subobject.pullback qX).monotone inf_le_right)
      rw [hpre Y, hpre Fi] at hRle
      have hmod : (Y ⊔ X) ⊓ (Fi ⊔ X) = (Y ⊓ Fi) ⊔ X := by
        rw [sup_eq_left.mpr hXY]
        exact (inf_sup_assoc_of_le (x := Y) (y := Fi) (z := X) hXY).symm
      rw [hmod] at hRle
      have hRle' :
          (Subobject.pullback qX).obj R ≤
            (Subobject.pullback qX).obj
              ((Subobject.«exists» qX).obj (Y ⊓ Fi)) := by
        rw [hpre (Y ⊓ Fi)]
        exact hRle
      calc
        R = (Subobject.«exists» qX).obj
            ((Subobject.pullback qX).obj R) :=
          (exists_pullback_of_epi qX R).symm
        _ ≤ (Subobject.«exists» qX).obj
            ((Subobject.pullback qX).obj
              ((Subobject.«exists» qX).obj (Y ⊓ Fi))) :=
          (Subobject.«exists» qX).monotone hRle'
        _ = (Subobject.«exists» qX).obj (Y ⊓ Fi) :=
          exists_pullback_of_epi qX _
  change (Subobject.«exists» (Y.arrow ≫ qX)).obj Yi =
    (Subobject.«exists» (Y.arrow ≫ qX)).obj
        (⊤ : Subobject (Y : C)) ⊓ Qi
  calc
    (Subobject.«exists» (Y.arrow ≫ qX)).obj Yi =
        (Subobject.«exists» qX).obj
          ((Subobject.«exists» Y.arrow).obj Yi) :=
      exists_comp Y.arrow qX Yi
    _ = (Subobject.«exists» qX).obj
          ((Subobject.map Y.arrow).obj Yi) := by
      rw [Subobject.exists_iso_map Y.arrow]
    _ = (Subobject.«exists» qX).obj (Y ⊓ Fi) := by rw [hYmap]
    _ = (Subobject.«exists» qX).obj Y ⊓ Qi := hYimage
    _ = (Subobject.«exists» (Y.arrow ≫ qX)).obj
          (⊤ : Subobject (Y : C)) ⊓ Qi := by
      have htop :
          (Subobject.«exists» (Y.arrow ≫ qX)).obj
              (⊤ : Subobject (Y : C)) =
            (Subobject.«exists» qX).obj Y := by
        rw [exists_comp, hYtop]
      exact congrArg (fun R => R ⊓ Qi) htop.symm

theorem filteredSubquotientComparison_exists {C : Type u} [Category.{v} C]
    [Abelian C] (A : FilteredObject C) (X Y : Subobject A.carrier) (hXY : X ≤ Y) :
    Nonempty (filteredSubquotient hXY ≅ ambientSubquotientKernel A hXY) := by
  let qX := cokernel.π X.arrow
  let qY := cokernel.π Y.arrow
  let d := cokernel.desc X.arrow qY (by
    rw [← Subobject.ofLE_arrow hXY, Category.assoc, cokernel.condition, comp_zero])
  have hd : qX ≫ d = qY := by
    exact cokernel.π_desc _ _ _
  have hzero : (Y.arrow ≫ qX) ≫ d = 0 := by
    rw [Category.assoc, hd, cokernel.condition]
  have hdcolim : IsColimit (CokernelCofork.ofπ d hzero) := by
    refine CokernelCofork.IsColimit.ofπ d hzero
      (fun z hz => by
        let w := cokernel.desc Y.arrow (qX ≫ z) (by
          simpa [Category.assoc] using hz)
        exact w) ?_ ?_
    · intro Z z hz
      apply (cancel_epi qX).mp
      let w := cokernel.desc Y.arrow (qX ≫ z) (by
        simpa [Category.assoc] using hz)
      have hw : qY ≫ w = qX ≫ z := by
        exact cokernel.π_desc _ _ _
      calc
        qX ≫ d ≫ w = qY ≫ w := by
          rw [← Category.assoc, hd]
        _ = qX ≫ z := hw
    · intro Z z hz m hm
      apply (cancel_epi qY).mp
      let w := cokernel.desc Y.arrow (qX ≫ z) (by
        simpa [Category.assoc] using hz)
      have hw : qY ≫ w = qX ≫ z := by
        exact cokernel.π_desc _ _ _
      calc
        qY ≫ m = qX ≫ d ≫ m := by
          rw [← hd]
          exact Category.assoc _ _ _
        _ = qX ≫ z := by rw [hm]
        _ = qY ≫ w := hw.symm
  let S0 : ShortComplex C := ShortComplex.mk (Y.arrow ≫ qX) d hzero
  have hExact : S0.Exact := by
    apply (ShortComplex.exact_iff_of_forks (S := S0)
      (kernelIsKernel d) hdcolim).2
    exact kernel.condition d
  have himage : imageSubobject (Y.arrow ≫ qX) = kernelSubobject d :=
    (ShortComplex.exact_iff_image_eq_kernel (S := S0)).mp hExact
  have htopimage :
      (Subobject.«exists» (Y.arrow ≫ qX)).obj (⊤ : Subobject (Y : C)) =
        imageSubobject (Y.arrow ≫ qX) :=
    exists_top_eq_imageSubobject (Y.arrow ≫ qX)
  have hk :
      kernelSubobject d =
        Subobject.mk (kernelSubobject d).arrow := by
    change Subobject.mk (kernel.ι d) =
      Subobject.mk (Subobject.mk (kernel.ι d)).arrow
    exact Subobject.mk_eq_mk_of_comm (kernel.ι d)
      (Subobject.mk (kernel.ι d)).arrow
      (Subobject.underlyingIso (kernel.ι d)).symm (by simp)
  have htotal :
      (Subobject.«exists» (Y.arrow ≫ qX)).obj (⊤ : Subobject (Y : C)) =
        (Subobject.map (Subobject.mk (kernel.ι d)).arrow).obj
          (⊤ : Subobject (Subobject.mk (kernel.ι d) : C)) := by
    rw [Subobject.map_top, htopimage, himage, hk]
  let f : inducedFilteredObject A X ⟶ inducedFilteredObject A Y :=
    inducedSubobjectMap A hXY
  let g : quotientFilteredObject A qX ⟶ quotientFilteredObject A qY :=
    subquotientQuotientMap A hXY
  let u : inducedFilteredObject A Y ⟶ quotientFilteredObject A qX :=
    inducedFilteredHom A Y ≫ quotientFilteredHom A qX
  have hgd : g.hom = d := by
    rfl
  have hfu : f.hom ≫ u.hom = 0 := by
    change (Subobject.ofLE X Y hXY) ≫ Y.arrow ≫ qX = 0
    rw [← Category.assoc, Subobject.ofLE_arrow, cokernel.condition]
  have hug : u ≫ g = 0 := by
    apply FilteredHom.ext _ _
    change u.hom ≫ g.hom = (0 : filteredHomAddSubgroup _ _).1
    rw [hgd]
    change (Y.arrow ≫ qX) ≫ d = 0
    exact hzero
  have hXlimit :
      IsLimit (KernelFork.ofι X.arrow (cokernel.condition X.arrow)) :=
    Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ qX (cokernel.condition X.arrow))
      (cokernelIsCokernel X.arrow)
  let eX := hXlimit.conePointUniqueUpToIso (kernelIsKernel qX)
  have heX : eX.hom ≫ kernel.ι qX = X.arrow := by
    simpa [eX] using
      IsLimit.conePointUniqueUpToIso_hom_comp hXlimit
        (kernelIsKernel qX) WalkingParallelPair.zero
  have heX_inv : eX.inv ≫ X.arrow = kernel.ι qX := by
    calc
      eX.inv ≫ X.arrow = eX.inv ≫ (eX.hom ≫ kernel.ι qX) :=
        congrArg (fun t => eX.inv ≫ t) heX.symm
      _ = kernel.ι qX := by simp
  let lift (Z : C) (z : Z ⟶ (Y : C))
      (hz : z ≫ Y.arrow ≫ qX = 0) : Z ⟶ (X : C) :=
    kernel.lift qX (z ≫ Y.arrow) (by
      simpa [Category.assoc] using hz) ≫ eX.inv
  have lift_fac (Z : C) (z : Z ⟶ (Y : C))
      (hz : z ≫ Y.arrow ≫ qX = 0) :
      lift Z z hz ≫ Subobject.ofLE X Y hXY = z := by
    apply (cancel_mono Y.arrow).mp
    dsimp [lift]
    rw [Category.assoc, Subobject.ofLE_arrow, Category.assoc,
      heX_inv, kernel.lift_ι]
  have hfk : IsLimit (KernelFork.ofι f.hom hfu) := by
    refine KernelFork.IsLimit.ofι f.hom hfu (fun {Z} z hz => ?_) ?_ ?_
    · change z ≫ Y.arrow ≫ qX = 0 at hz
      change Z ⟶ (Y : C) at z
      exact lift Z z hz
    · intro Z z hz
      change Z ⟶ (Y : C) at z
      exact lift_fac Z z hz
    · intro Z z hz m hm
      change z ≫ Y.arrow ≫ qX = 0 at hz
      change Z ⟶ (Y : C) at z
      change Z ⟶ (X : C) at m
      change m ≫ Subobject.ofLE X Y hXY = z at hm
      apply (cancel_mono (Subobject.ofLE X Y hXY)).mp
      rw [hm]
      exact (lift_fac Z z hz).symm
  let ι := filteredKernelι g
  let v : inducedFilteredObject A Y ⟶ filteredKernel g :=
    (filteredKernelFork_isLimit g).lift (KernelFork.ofι u hug)
  have hv : v ≫ ι = u := by
    exact (filteredKernelFork_isLimit g).fac
      (KernelFork.ofι u hug) WalkingParallelPair.zero
  have hv' : v.hom ≫ ι.hom = u.hom := congrArg FilteredHom.hom hv
  let : Mono ι.hom := by
    change Mono (Subobject.mk (kernel.ι g.hom)).arrow
    infer_instance
  have hfv : f ≫ v = 0 := by
    apply FilteredHom.ext _ _
    change f.hom ≫ v.hom = 0
    let : Mono ι.hom := by
      change Mono (Subobject.mk (kernel.ι g.hom)).arrow
      infer_instance
    apply (cancel_mono ι.hom).mp
    rw [Category.assoc, hv', zero_comp]
    exact hfu
  let κ : (Subobject.mk (kernel.ι d) : C) ⟶ cokernel X.arrow :=
    (Subobject.mk (kernel.ι d)).arrow
  have hικ : ι.hom = κ := by
    dsimp [ι, filteredKernelι, inducedFilteredHom, g,
      subquotientQuotientMap, d, qX, qY, κ]
    rfl
  have htotalι :
      (Subobject.«exists» u.hom).obj (⊤ : Subobject (Y : C)) =
        (Subobject.map κ).obj
          (⊤ : Subobject (Subobject.mk (kernel.ι d) : C)) := by
    change (Subobject.«exists» (Y.arrow ≫ qX)).obj (⊤ : Subobject (Y : C)) =
      (Subobject.map (Subobject.mk (kernel.ι d)).arrow).obj
        (⊤ : Subobject (Subobject.mk (kernel.ι d) : C))
    exact htotal
  let I := Subobject.imageFactorisation (Y.arrow ≫ qX)
    (⊤ : Subobject (Y : C))
  have hI : Subobject.mk I.F.m =
      (Subobject.«exists» u.hom).obj (⊤ : Subobject (Y : C)) := by
    change Subobject.mk
      ((Subobject.«exists» u.hom).obj (⊤ : Subobject (Y : C))).arrow = _
    simp
  have hmkκ : Subobject.mk I.F.m = Subobject.mk κ := by
    rw [hI, htotalι, Subobject.map_top]
  let eI : I.F.I ≅ (Subobject.mk (kernel.ι d) : C) :=
    Subobject.isoOfMkEqMk I.F.m κ hmkκ
  have hIe : Epi I.F.e := by
    exact (strongEpi_of_strongEpiMonoFactorisation
      (Abelian.imageStrongEpiMonoFactorisation
        ((⊤ : Subobject (Y : C)).arrow ≫ (Y.arrow ≫ qX)))
      I.isImage).epi
  let w : (inducedFilteredObject A Y).carrier ⟶ (filteredKernel g).carrier := by
    change (Y : C) ⟶ (Subobject.mk (kernel.ι d) : C)
    exact inv (⊤ : Subobject (Y : C)).arrow ≫ I.F.e ≫ eI.hom
  have hwι : w ≫ ι.hom = Y.arrow ≫ qX := by
    change (inv (⊤ : Subobject (Y : C)).arrow ≫ I.F.e ≫ eI.hom) ≫ κ =
      Y.arrow ≫ qX
    calc
      (inv (⊤ : Subobject (Y : C)).arrow ≫ I.F.e ≫ eI.hom) ≫ κ =
          inv (⊤ : Subobject (Y : C)).arrow ≫ I.F.e ≫
          (eI.hom ≫ κ) := by simp [Category.assoc]
      _ = inv (⊤ : Subobject (Y : C)).arrow ≫ I.F.e ≫ I.F.m := by
        simp [eI]
      _ = inv (⊤ : Subobject (Y : C)).arrow ≫
          ((⊤ : Subobject (Y : C)).arrow ≫ (Y.arrow ≫ qX)) := by
        rw [I.F.fac]
      _ = Y.arrow ≫ qX := by simp
  have hw_epi : Epi w := by
    change Epi (inv (⊤ : Subobject (Y : C)).arrow ≫ I.F.e ≫ eI.hom)
    let : Epi I.F.e := hIe
    infer_instance
  have hu_raw : u.hom = Y.arrow ≫ qX := by
    rfl
  have hwι' : w ≫ ι.hom = u.hom := by
    rw [hwι]
    exact hu_raw.symm
  have hvw : v.hom = w := by
    apply (cancel_mono ι.hom).mp
    exact hv'.trans hwι'.symm
  have hv_epi : Epi v.hom := by
    rw [hvw]
    exact hw_epi
  let : Epi v.hom := hv_epi
  have hfv' : f.hom ≫ v.hom = 0 := by
    exact congrArg FilteredHom.hom hfv
  have hkv : IsLimit (KernelFork.ofι f.hom hfv') :=
    isKernelOfComp ι.hom u.hom hfk hfv' hv'
  have hvc : IsColimit (CokernelCofork.ofπ v.hom hfv') :=
    Abelian.epiIsCokernelOfKernel (KernelFork.ofι f.hom hfv') hkv
  let s : filteredCokernel f ⟶ filteredKernel g :=
    (filteredCokernelCofork_isColimit f).desc
      (CokernelCofork.ofπ v hfv)
  have hsπ : filteredCokernelπ f ≫ s = v :=
    (filteredCokernelCofork_isColimit f).fac
      (CokernelCofork.ofπ v hfv) WalkingParallelPair.one
  have hsπ' : cokernel.π f.hom ≫ s.hom = v.hom := by
    have h := congrArg FilteredHom.hom hsπ
    change (filteredCokernelπ f).hom ≫ s.hom = v.hom at h
    change cokernel.π f.hom ≫ s.hom = v.hom
    exact h
  let eS : (filteredCokernel f).carrier ≅ (filteredKernel g).carrier :=
    (cokernelIsCokernel f.hom).coconePointUniqueUpToIso hvc
  have heS : cokernel.π f.hom ≫ eS.hom = v.hom := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel f.hom) hvc WalkingParallelPair.one
  have hse : s.hom = eS.hom := by
    apply (cancel_epi (cokernel.π f.hom)).mp
    rw [hsπ', heS]
  have hu_strict : Strict u := strict_induced_quotient_of_le_core A hXY
  have hs_strict : Strict s := by
    apply (strict_iff_quotient_filtration s (by
      change Epi s.hom
      rw [hse]
      infer_instance)).2
    intro i
    let Fi := A.filtration.obj i
    let Yi := (Subobject.pullback Y.arrow).obj Fi
    let Qi := (Subobject.«exists» qX).obj Fi
    let Ki := (Subobject.pullback κ).obj Qi
    have hu_step :
        (Subobject.«exists» u.hom).obj Yi =
          (Subobject.«exists» u.hom).obj (⊤ : Subobject (Y : C)) ⊓ Qi := by
      change (Subobject.«exists» u.hom).obj
          ((inducedFilteredObject A Y).filtration.obj i) =
        (Subobject.«exists» u.hom).obj (⊤ : Subobject (Y : C)) ⊓
          (quotientFilteredObject A qX).filtration.obj i
      exact hu_strict i
    have hcomp_step : cokernel.π f.hom ≫ s.hom ≫
        FilteredHom.hom ι = u.hom := by
      calc
        cokernel.π f.hom ≫ s.hom ≫ FilteredHom.hom ι =
            (cokernel.π f.hom ≫ s.hom) ≫ FilteredHom.hom ι :=
          (Category.assoc _ _ _).symm
        _ = v.hom ≫ FilteredHom.hom ι :=
          congrArg (fun z => z ≫ FilteredHom.hom ι) hsπ'
        _ = u.hom := hv'
    have hKi : Ki = (Subobject.pullback (FilteredHom.hom ι)).obj Qi := by
      dsimp [Ki]
      rw [hικ]
      rfl
    change Ki = (Subobject.«exists» s.hom).obj
      ((Subobject.«exists» (cokernel.π f.hom)).obj Yi)
    exact ((filtration_step_iff (cokernel.π f.hom) s.hom
      (FilteredHom.hom ι) u.hom
      Yi ((Subobject.«exists» (cokernel.π f.hom)).obj Yi) Ki Qi
      hcomp_step rfl hKi htotalι).mpr hu_step).symm
  have hs_hom_iso : IsIso s.hom := by
    rw [hse]
    infer_instance
  have hs_iso : IsIso s := by
    exact (strict_iff_isIso_of_hom_iso s hs_hom_iso).1 hs_strict
  rcases hs_iso.out with ⟨s_inv, hs_inv₁, hs_inv₂⟩
  exact ⟨⟨s, s_inv, hs_inv₁, hs_inv₂⟩⟩

private theorem strict_induced_quotient_of_le {C : Type u} [Category.{v} C]
    [Abelian C] (A : FilteredObject C) {X Y : Subobject A.carrier}
    (hXY : X ≤ Y) :
    Strict (inducedFilteredHom A Y ≫
      quotientFilteredHom A (cokernel.π X.arrow)) := by
  exact strict_induced_quotient_of_le_core A hXY

noncomputable def filteredSubquotientComparison {C : Type u} [Category.{v} C]
    [Abelian C] (A : FilteredObject C) {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    filteredSubquotient hXY ≅ ambientSubquotientKernel A hXY :=
  Classical.choice (filteredSubquotientComparison_exists A X Y hXY)

def subquotientXToY {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    inducedFilteredObject A X ⟶ inducedFilteredObject A Y :=
  inducedSubobjectMap A hXY

def subquotientXToA {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) :
    inducedFilteredObject A X ⟶ A :=
  inducedFilteredHom A X

def subquotientYToA {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (Y : Subobject A.carrier) :
    inducedFilteredObject A Y ⟶ A :=
  inducedFilteredHom A Y

def subquotientYToAX {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) {X Y : Subobject A.carrier} :
    inducedFilteredObject A Y ⟶ quotientFilteredObject A (cokernel.π X.arrow) :=
  inducedFilteredHom A Y ≫ quotientFilteredHom A (cokernel.π X.arrow)

def subquotientYToYX {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    inducedFilteredObject A Y ⟶ filteredSubquotient hXY :=
  filteredCokernelπ (inducedSubobjectMap A hXY)

def subquotientYXToAX {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    filteredSubquotient hXY ⟶ quotientFilteredObject A (cokernel.π X.arrow) :=
  (filteredSubquotientComparison A hXY).hom ≫
    filteredKernelι (subquotientQuotientMap A hXY)

theorem filtered_subquotient_maps_strict {C : Type u} [Category.{v} C]
    [Abelian C] (A : FilteredObject C) (X Y : Subobject A.carrier) (hXY : X ≤ Y) :
    Strict (subquotientXToY A hXY) ∧
      Strict (subquotientXToA A X) ∧
      Strict (subquotientYToA A Y) ∧
      Strict (subquotientYToAX A (X := X) (Y := Y)) ∧
      Strict (subquotientYToYX A hXY) ∧
      Strict (subquotientYXToAX A hXY) := by
  refine ⟨?_, strict_induced_iff X, strict_induced_iff Y, ?_, ?_, ?_⟩
  · apply (strict_iff_induced_filtration (subquotientXToY A hXY) (by
      change Mono (Subobject.ofLE X Y hXY)
      infer_instance)).2
    intro i
    change (Subobject.pullback X.arrow).obj (A.filtration.obj i) =
      (Subobject.pullback (Subobject.ofLE X Y hXY)).obj
        ((Subobject.pullback Y.arrow).obj (A.filtration.obj i))
    rw [← Subobject.pullback_comp, Subobject.ofLE_arrow]
  · simpa [subquotientYToAX] using
      (strict_induced_quotient_of_le A hXY)
  · exact strict_quotient_iff (A := inducedFilteredObject A Y)
      (π := cokernel.π (inducedSubobjectMap A hXY).hom)
  · let e := filteredSubquotientComparison A hXY
    let k := subquotientQuotientMap A hXY
    have he_hom : IsIso e.hom.hom := by
      refine ⟨e.inv.hom, ?_, ?_⟩
      · exact congrArg FilteredHom.hom (Iso.hom_inv_id e)
      · exact congrArg FilteredHom.hom (Iso.inv_hom_id e)
    have he : Strict e.hom := by
      apply (strict_iff_isIso_of_hom_iso e.hom he_hom).2
      exact e.isIso_hom
    have hk : Strict (filteredKernelι k) := by
      exact strict_induced_iff
        (A := quotientFilteredObject A (cokernel.π X.arrow))
        (Subobject.mk (kernel.ι k.hom))
    have hkmono : FilteredInjective (filteredKernelι k) := by
      change Mono (Subobject.mk (kernel.ι k.hom)).arrow
      infer_instance
    simpa [subquotientYXToAX, e, k] using
      (strict_composition_of_strict_of_mono e.hom
        (filteredKernelι k) he hk hkmono)

end Formalization.Books.Homology.Unit19
