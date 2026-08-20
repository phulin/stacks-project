import Formalization.Books.Homology.Unit19.Filtrations.Basic

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open scoped ZeroObject

universe v u

namespace Formalization.Books.Homology.Unit19

/-! ## Strict morphisms -/

/-- A filtered morphism is strict when the image of every step is the
    intersection of its total image with the target step. -/
def Strict {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) : Prop :=
  ∀ i : ℤ,
    (Subobject.«exists» f.hom).obj (A.filtration.obj i) =
      (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) ⊓ B.filtration.obj i

theorem strict_iff_induced_filtration {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (u : A ⟶ B)
    (hu : FilteredInjective u) :
    Strict u ↔
      ∀ i : ℤ,
        A.filtration.obj i = (Subobject.pullback u.hom).obj (B.filtration.obj i) := by
  let _ : Mono u.hom := hu
  have hmap (G : Subobject B.carrier) :
      (Subobject.map u.hom).obj ((Subobject.pullback u.hom).obj G) =
        (Subobject.map u.hom).obj (⊤ : Subobject A.carrier) ⊓ G := by
    rw [Subobject.map_top]
    change (Subobject.map u.hom).obj ((Subobject.pullback u.hom).obj G) =
      (Subobject.inf.obj (Quotient.mk'' (MonoOver.mk u.hom))).obj G
    exact (Subobject.inf_eq_map_pullback' (MonoOver.mk u.hom) G).symm
  have hinj : Function.Injective
      (fun P : Subobject A.carrier => (Subobject.map u.hom).obj P) := by
    intro P Q h
    calc
      P = (Subobject.pullback u.hom).obj ((Subobject.map u.hom).obj P) :=
        (Subobject.pullback_map_self u.hom P).symm
      _ = (Subobject.pullback u.hom).obj ((Subobject.map u.hom).obj Q) :=
        congrArg _ h
      _ = Q := Subobject.pullback_map_self u.hom Q
  constructor
  · intro h i
    apply hinj
    change (Subobject.map u.hom).obj (A.filtration.obj i) =
      (Subobject.map u.hom).obj
        ((Subobject.pullback u.hom).obj (B.filtration.obj i))
    rw [hmap]
    simpa only [Subobject.exists_iso_map u.hom] using h i
  · intro h i
    rw [Subobject.exists_iso_map u.hom, h i, hmap]

theorem strict_iff_quotient_filtration {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (u : A ⟶ B)
    (hu : FilteredSurjective u) :
    Strict u ↔
      ∀ i : ℤ,
        B.filtration.obj i = (Subobject.«exists» u.hom).obj (A.filtration.obj i) := by
  let _ : Epi u.hom := hu
  have htop : (Subobject.«exists» u.hom).obj (⊤ : Subobject A.carrier) = ⊤ := by
    apply (Subobject.isIso_arrow_iff_eq_top _).mp
    let F := Subobject.imageFactorisation u.hom (⊤ : Subobject A.carrier)
    let _ : Epi F.F.e := by
      exact (strongEpi_of_strongEpiMonoFactorisation
        (Abelian.imageStrongEpiMonoFactorisation
          ((⊤ : Subobject A.carrier).arrow ≫ u.hom)) F.isImage).epi
    let _ : Epi F.F.m := epi_of_epi_fac F.F.fac
    change IsIso F.F.m
    exact isIso_of_mono_of_epi F.F.m
  constructor
  · intro h i
    rw [h i, htop]
    simp
  · intro h i
    rw [h i, htop]
    simp

private theorem abelian_regular {C : Type u} [Category.{v} C] [Abelian C] : Regular C :=
  { hasCoequalizer_of_isKernelPair := fun _ => inferInstance
    regularEpiIsStableUnderBaseChange :=
      MorphismProperty.IsStableUnderBaseChange.mk' fun X Y S f g _ hg => by
        rw [MorphismProperty.regularEpi_iff] at hg ⊢
        let _ : IsRegularEpi g := hg
        let _ : Epi g := inferInstance
        let _ : Epi (pullback.fst f g) := Abelian.epi_pullback_of_epi_g f g
        let _ : NormalEpi (pullback.fst f g) := normalEpiOfEpi _
        infer_instance }

private theorem image_pullback_eq {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B)
    (P : Subobject B.carrier) :
    (Subobject.«exists» f.hom).obj ((Subobject.pullback f.hom).obj P) =
      (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) ⊓ P := by
  let _ : Regular C := abelian_regular
  simpa using Regular.exists_inf_pullback_eq_exists_inf f.hom
    (⊤ : Subobject A.carrier) P

private theorem imagePullback_relation {C : Type u} [Category.{v} C]
    {Q A I B R T : C} (q : Q ⟶ A) (f : A ⟶ B) (e : Q ⟶ I)
    (m : I ⟶ B) (r : R ⟶ I) (a : R ⟶ A) (t : T ⟶ R)
    (p : T ⟶ Q) (hfac : q ≫ f = e ≫ m) (hpb : p ≫ e = t ≫ r)
    (hr : r ≫ m = a ≫ f) : (p ≫ q) ≫ f = (t ≫ a) ≫ f := by
  rw [Category.assoc, hfac, ← Category.assoc, hpb, Category.assoc, hr,
    ← Category.assoc]

private theorem sub_comp_eq_zero_of_comp_eq {C : Type u} [Category.{v} C]
    [Preadditive C] {X Y Z : C} (a b : X ⟶ Y) (f : Y ⟶ Z)
    (h : b ≫ f = a ≫ f) : (a - b) ≫ f = 0 := by
  rw [Preadditive.sub_comp, ← h, sub_self]

private theorem eq_add_of_eq_sub {G : Type*} [AddCommGroup G]
    (a b c : G) (h : c = a - b) : a = b + c := by
  rw [h]
  abel

private theorem kernel_ift_comp_eq_zero {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {X Y Z W : C} (t : X ⟶ Y) [HasKernel t]
    (w : X ⟶ Z) (m : Z ⟶ W) [Mono m] (r : Y ⟶ W)
    (h : w ≫ m = t ≫ r) : kernel.ι t ≫ w = 0 := by
  apply (cancel_mono m).mp
  rw [Category.assoc, h, ← Category.assoc, kernel.condition t, zero_comp,
    zero_comp]

private theorem eq_of_epi_comp_eq {C : Type u} [Category.{v} C]
    {X Y Z W : C} (t : X ⟶ Y) [Epi t] (d : Y ⟶ Z) (w : X ⟶ Z)
    (m : Z ⟶ W) (r : Y ⟶ W) (hd : t ≫ d = w)
    (hw : w ≫ m = t ≫ r) : d ≫ m = r := by
  apply (cancel_epi t).mp
  rw [← Category.assoc, hd, hw]

theorem pullback_exists_eq_sup_kernel {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B)
    (Q : Subobject A.carrier) :
    (Subobject.pullback f.hom).obj ((Subobject.«exists» f.hom).obj Q) =
      Q ⊔ Subobject.mk (kernel.ι f.hom) := by
    let P := (Subobject.«exists» f.hom).obj Q
    let R := (Subobject.pullback f.hom).obj P
    let K := Subobject.mk (kernel.ι f.hom)
    have hQle : Q ≤ R := by
      exact ((Subobject.existsPullbackAdj f.hom).homEquiv Q P
        (CategoryTheory.homOfLE (show
          (Subobject.«exists» f.hom).obj Q ≤ P from le_rfl))).le
    let hpb := Subobject.isPullback f.hom P
    have hKfac : R.Factors K.arrow := by
      apply (Subobject.factors_iff R K.arrow).mpr
      refine ⟨(Subobject.underlyingIso (kernel.ι f.hom)).hom ≫
        hpb.lift 0 (kernel.ι f.hom) (by simp), ?_⟩
      dsimp [K]
      rw [Category.assoc, hpb.lift_snd]
      exact Subobject.underlyingIso_hom_comp_eq_mk _
    have hKle : K ≤ R := Subobject.le_of_factors hKfac
    have hle : Q ⊔ K ≤ R := sup_le hQle hKle
    apply le_antisymm
    · let G := Subobject.imageFactorisation f.hom Q
      let _ : Epi G.F.e :=
        (strongEpi_of_strongEpiMonoFactorisation
          (Abelian.imageStrongEpiMonoFactorisation
            (Q.arrow ≫ f.hom)) G.isImage).epi
      have hG : Subobject.mk G.F.m = P := by
        change Subobject.mk P.arrow = P
        simp
      let r := Subobject.pullbackπ f.hom P
      let r' := r ≫ Subobject.ofLE P (Subobject.mk G.F.m) hG.symm.le ≫
        (Subobject.underlyingIso G.F.m).hom
      have hr' : r' ≫ G.F.m = R.arrow ≫ f.hom := by
        dsimp [r', r, R]
        simp [Category.assoc, hpb.w,
          Subobject.underlyingIso_hom_comp_eq_mk]
      let t := pullback.snd G.F.e r'
      let _ : Epi t := Abelian.epi_pullback_of_epi_f G.F.e r'
      let sQ := pullback.fst G.F.e r' ≫ Q.arrow
      let sA := t ≫ R.arrow
      have hs : sQ ≫ f.hom = sA ≫ f.hom :=
        imagePullback_relation Q.arrow f.hom G.F.e G.F.m r' R.arrow t
          (pullback.fst G.F.e r') G.F.fac.symm (pullback.condition) hr'
      have hdiff : (sA - sQ) ≫ f.hom = 0 :=
        sub_comp_eq_zero_of_comp_eq sA sQ f.hom hs
      let k := kernel.lift f.hom (sA - sQ) hdiff
      have hk : k ≫ kernel.ι f.hom = sA - sQ := by
        dsimp [k]
        simp
      have hdecomp : sA = sQ + k ≫ kernel.ι f.hom :=
        eq_add_of_eq_sub sA sQ (k ≫ kernel.ι f.hom) hk
      let S := Q ⊔ K
      have hQf : Q.Factors sQ :=
        Subobject.factors_comp_arrow (pullback.fst G.F.e r')
      have hQs : S.Factors sQ :=
        Subobject.sup_factors_of_factors_left hQf
      have hiK : (Subobject.underlyingIso (kernel.ι f.hom)).inv ≫
          K.arrow = kernel.ι f.hom := by
        apply (cancel_epi (Subobject.underlyingIso (kernel.ι f.hom)).hom).mp
        simp [K, Subobject.underlyingIso_hom_comp_eq_mk]
      let k' := k ≫ (Subobject.underlyingIso (kernel.ι f.hom)).inv
      have hKf : K.Factors (k ≫ kernel.ι f.hom) := by
        apply (Subobject.factors_iff K _).mpr
        refine ⟨k', ?_⟩
        dsimp [k']
        rw [Category.assoc, hiK]
      have hKs : S.Factors (k ≫ kernel.ι f.hom) :=
        Subobject.sup_factors_of_factors_right hKf
      have hsum : S.Factors (sQ + k ≫ kernel.ι f.hom) :=
        Subobject.factors_add sQ (k ≫ kernel.ι f.hom) hQs hKs
      have hSfac : S.Factors sA := by
        rw [hdecomp]
        exact hsum
      let w := S.factorThru sA hSfac
      have hw : w ≫ S.arrow = sA := by
        dsimp [w]
        simp
      have hzero : kernel.ι t ≫ w = 0 :=
        kernel_ift_comp_eq_zero t w S.arrow R.arrow (by simpa [sA] using hw)
      let d := Abelian.epiDesc t w hzero
      apply Subobject.le_of_comm d
      exact eq_of_epi_comp_eq t d w S.arrow R.arrow
        (Abelian.comp_epiDesc t w hzero) (by simpa [sA] using hw)
    · exact hle

theorem kernel_le_pullback {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B)
    (P : Subobject B.carrier) :
    Subobject.mk (kernel.ι f.hom) ≤
      (Subobject.pullback f.hom).obj P := by
    let R := (Subobject.pullback f.hom).obj P
    let K := Subobject.mk (kernel.ι f.hom)
    let hpb := Subobject.isPullback f.hom P
    have hKfac : R.Factors K.arrow := by
      apply (Subobject.factors_iff R K.arrow).mpr
      refine ⟨(Subobject.underlyingIso (kernel.ι f.hom)).hom ≫
        hpb.lift 0 (kernel.ι f.hom) (by simp), ?_⟩
      dsimp [K]
      rw [Category.assoc, hpb.lift_snd]
      exact Subobject.underlyingIso_hom_comp_eq_mk _
    exact Subobject.le_of_factors hKfac

theorem strict_iff_preimage_eq_sup_kernel {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) :
    Strict f ↔
      ∀ i : ℤ,
        (Subobject.pullback f.hom).obj (B.filtration.obj i) =
          A.filtration.obj i ⊔ Subobject.mk (kernel.ι f.hom) := by
  constructor
  · intro h i
    have him :
        (Subobject.«exists» f.hom).obj
            ((Subobject.pullback f.hom).obj (B.filtration.obj i)) =
          (Subobject.«exists» f.hom).obj (A.filtration.obj i) := by
      rw [image_pullback_eq f (B.filtration.obj i)]
      exact (h i).symm
    have hRle :
        (Subobject.pullback f.hom).obj (B.filtration.obj i) ≤
          (Subobject.pullback f.hom).obj
            ((Subobject.«exists» f.hom).obj (A.filtration.obj i)) :=
      ((Subobject.existsPullbackAdj f.hom).homEquiv _ _
        (CategoryTheory.homOfLE him.le)).le
    rw [pullback_exists_eq_sup_kernel f (A.filtration.obj i)] at hRle
    have hAle : A.filtration.obj i ≤
        (Subobject.pullback f.hom).obj (B.filtration.obj i) := by
      apply ((Subobject.existsPullbackAdj f.hom).homEquiv _ _
        (CategoryTheory.homOfLE (show
          (Subobject.«exists» f.hom).obj (A.filtration.obj i) ≤
            B.filtration.obj i by
              rw [h i]
              exact inf_le_right))).le
    exact le_antisymm hRle
      (sup_le hAle (kernel_le_pullback f (B.filtration.obj i)))
  · intro h i
    have hR :
        (Subobject.pullback f.hom).obj (B.filtration.obj i) =
          (Subobject.pullback f.hom).obj
            ((Subobject.«exists» f.hom).obj (A.filtration.obj i)) := by
      calc
        (Subobject.pullback f.hom).obj (B.filtration.obj i) =
            A.filtration.obj i ⊔ Subobject.mk (kernel.ι f.hom) := h i
        _ = (Subobject.pullback f.hom).obj
            ((Subobject.«exists» f.hom).obj (A.filtration.obj i)) :=
          (pullback_exists_eq_sup_kernel f (A.filtration.obj i)).symm
    have him :
        (Subobject.«exists» f.hom).obj
            ((Subobject.pullback f.hom).obj (B.filtration.obj i)) =
          (Subobject.«exists» f.hom).obj (A.filtration.obj i) := by
      rw [hR]
      calc
        (Subobject.«exists» f.hom).obj
              ((Subobject.pullback f.hom).obj
                ((Subobject.«exists» f.hom).obj (A.filtration.obj i))) =
            (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) ⊓
              (Subobject.«exists» f.hom).obj (A.filtration.obj i) :=
          image_pullback_eq f _
        _ = (Subobject.«exists» f.hom).obj (A.filtration.obj i) := by
          apply le_antisymm inf_le_right
          exact le_inf ((Subobject.«exists» f.hom).monotone le_top) le_rfl
    calc
      (Subobject.«exists» f.hom).obj (A.filtration.obj i) =
          (Subobject.«exists» f.hom).obj
            ((Subobject.pullback f.hom).obj (B.filtration.obj i)) := him.symm
      _ = (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) ⊓
          (B.filtration.obj i) := image_pullback_eq f _


theorem exists_comp {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (P : Subobject X) :
    (Subobject.«exists» (a ≫ b)).obj P =
      (Subobject.«exists» b).obj ((Subobject.«exists» a).obj P) := by
    apply le_antisymm
    · have h : P ≤ (Subobject.pullback (a ≫ b)).obj
          ((Subobject.«exists» b).obj ((Subobject.«exists» a).obj P)) := by
        rw [Subobject.pullback_comp]
        exact ((Subobject.existsPullbackAdj a).homEquiv P
          ((Subobject.pullback b).obj
            ((Subobject.«exists» b).obj ((Subobject.«exists» a).obj P))))
          (CategoryTheory.homOfLE
            (((Subobject.existsPullbackAdj b).homEquiv
              ((Subobject.«exists» a).obj P)
              ((Subobject.«exists» b).obj ((Subobject.«exists» a).obj P)))
              (CategoryTheory.homOfLE le_rfl)).le) |>.le
      exact ((Subobject.existsPullbackAdj (a ≫ b)).homEquiv P
        ((Subobject.«exists» b).obj ((Subobject.«exists» a).obj P))).symm
        (CategoryTheory.homOfLE h) |>.le
    · have h : (Subobject.«exists» a).obj P ≤
          (Subobject.pullback b).obj ((Subobject.«exists» (a ≫ b)).obj P) := by
        have h' : P ≤ (Subobject.pullback (a ≫ b)).obj
            ((Subobject.«exists» (a ≫ b)).obj P) :=
          (((Subobject.existsPullbackAdj (a ≫ b)).homEquiv P
            ((Subobject.«exists» (a ≫ b)).obj P))
            (CategoryTheory.homOfLE le_rfl)).le
        rw [Subobject.pullback_comp] at h'
        exact ((Subobject.existsPullbackAdj a).homEquiv P
          ((Subobject.pullback b).obj ((Subobject.«exists» (a ≫ b)).obj P))).symm
          (CategoryTheory.homOfLE h') |>.le
      exact ((Subobject.existsPullbackAdj b).homEquiv
        ((Subobject.«exists» a).obj P)
        ((Subobject.«exists» (a ≫ b)).obj P)).symm
        (CategoryTheory.homOfLE h) |>.le

theorem exists_top_of_epi {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (u : X ⟶ Y) [Epi u] :
    (Subobject.«exists» u).obj (⊤ : Subobject X) = ⊤ := by
    apply (Subobject.isIso_arrow_iff_eq_top _).mp
    let F := Subobject.imageFactorisation u (⊤ : Subobject X)
    let _ : Epi F.F.e := by
      exact (strongEpi_of_strongEpiMonoFactorisation
        (Abelian.imageStrongEpiMonoFactorisation
          ((⊤ : Subobject X).arrow ≫ u)) F.isImage).epi
    let _ : Epi F.F.m := epi_of_epi_fac F.F.fac
    change IsIso F.F.m
    exact isIso_of_mono_of_epi F.F.m

private theorem strict_iff_exists_eq_of_epi
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : FilteredObject C} (u : X ⟶ Y) [Epi u.hom] :
    Strict u ↔ ∀ i : ℤ,
      (Subobject.«exists» u.hom).obj (X.filtration.obj i) =
        Y.filtration.obj i := by
  simp only [Strict, exists_top_of_epi u.hom, top_inf_eq]

private theorem subobjectMap_injective_of_mono
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {X Y : C} (u : X ⟶ Y) [Mono u] :
    Function.Injective (fun P : Subobject X => (Subobject.map u).obj P) := by
  intro P Q h
  calc
    P = (Subobject.pullback u).obj ((Subobject.map u).obj P) :=
      (Subobject.pullback_map_self u P).symm
    _ = (Subobject.pullback u).obj ((Subobject.map u).obj Q) := congrArg _ h
    _ = Q := Subobject.pullback_map_self u Q

theorem map_pullback_eq_map_top_inf
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {X Y : C} (u : X ⟶ Y) [Mono u] (G : Subobject Y) :
    (Subobject.map u).obj ((Subobject.pullback u).obj G) =
      (Subobject.map u).obj (⊤ : Subobject X) ⊓ G := by
  rw [Subobject.map_top]
  change (Subobject.map u).obj ((Subobject.pullback u).obj G) =
    (Subobject.inf.obj (Quotient.mk'' (MonoOver.mk u))).obj G
  exact (Subobject.inf_eq_map_pullback' (MonoOver.mk u) G).symm

theorem strict_iff_isIso_of_hom_iso {C : Type u} [Category.{v} C]
    [Abelian C] {X Y : FilteredObject C} (u : X ⟶ Y) (hu : IsIso u.hom) :
    Strict u ↔ IsIso u := by
    constructor
    · intro hs
      let : IsIso u.hom := hu
      have hstrict' := (strict_iff_induced_filtration u (by
        change Mono u.hom
        infer_instance)).mp hs
      let ui : Y ⟶ X :=
        ⟨inv u.hom, by
          intro i
          rw [hstrict' i]
          apply (Subobject.factors_iff _ _).mpr
          let hpb := Subobject.isPullback u.hom (Y.filtration.obj i)
          refine ⟨hpb.lift (𝟙 _) ((Y.filtration.obj i).arrow ≫ inv u.hom)
            (by simp [Category.assoc]), ?_⟩
          exact hpb.lift_snd _ _ _⟩
      refine ⟨⟨ui, ?_, ?_⟩⟩
      · apply FilteredHom.ext _ _
        change u.hom ≫ inv u.hom = 𝟙 _
        simp
      · apply FilteredHom.ext _ _
        change inv u.hom ≫ u.hom = 𝟙 _
        simp
    · intro hu
      let : IsIso u := hu
      have hu_mono : Mono u.hom :=
        (filtered_mono_iff_underlying_mono u).1 (by infer_instance)
      let : Mono u.hom := hu_mono
      apply (strict_iff_induced_filtration u hu_mono).2
      intro i
      let Xᵢ := X.filtration.obj i
      let Yᵢ := Y.filtration.obj i
      let P := (Subobject.pullback u.hom).obj Yᵢ
      have hXP : Xᵢ ≤ P := by
        apply Subobject.le_of_factors
        exact (CategoryTheory.Limits.pullback_factors_iff u.hom Yᵢ
          Xᵢ.arrow).2 (u.map_filtration i)
      have hPX : P ≤ Xᵢ := by
        have hi : Xᵢ.Factors (Yᵢ.arrow ≫ (inv u).hom) :=
          (inv u).map_filtration i
        rcases (Subobject.factors_iff _ _).mp hi with ⟨s, hs⟩
        apply Subobject.le_of_factors
        apply (Subobject.factors_iff _ _).mpr
        refine ⟨Subobject.pullbackπ u.hom Yᵢ ≫ s, ?_⟩
        calc
          (Subobject.pullbackπ u.hom Yᵢ ≫ s) ≫
              (Subobject.representative.obj Xᵢ).arrow =
              Subobject.pullbackπ u.hom Yᵢ ≫
                (s ≫ (Subobject.representative.obj Xᵢ).arrow) :=
            Category.assoc _ _ _
          _ = Subobject.pullbackπ u.hom Yᵢ ≫
              (Yᵢ.arrow ≫ (inv u).hom) := by rw [hs]
          _ = (Subobject.pullbackπ u.hom Yᵢ ≫ Yᵢ.arrow) ≫
              (inv u).hom := by simp [Category.assoc]
          _ = (P.arrow ≫ u.hom) ≫ (inv u).hom := by
                rw [(Subobject.isPullback u.hom Yᵢ).w]
          _ = P.arrow := by
            have huinv : u.hom ≫ (inv u).hom = 𝟙 _ := by
              exact congrArg FilteredHom.hom (IsIso.hom_inv_id u)
            rw [Category.assoc, huinv, Category.comp_id]
      exact le_antisymm hXP hPX

private theorem coimageComparison_eq_of_factorisations
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasKernels C] [HasCokernels C]
    {A B Q I : C} (f : A ⟶ B) (q : A ⟶ Q) [Epi q]
    (c : Q ⟶ I) (l : A ⟶ I) (ι : I ⟶ B)
    (eQ : Q ⟶ Abelian.coimage f) (eI : I ⟶ Abelian.image f)
    (hqQ : q ≫ eQ = Abelian.coimage.π f) (hqc : q ≫ c = l)
    (hli : l ≫ ι = f) (heI : eI ≫ Abelian.image.ι f = ι) :
    eQ ≫ Abelian.coimageImageComparison f = c ≫ eI := by
  apply (cancel_epi q).mp
  apply (cancel_mono (Abelian.image.ι f)).mp
  calc
    (q ≫ eQ ≫ Abelian.coimageImageComparison f) ≫ Abelian.image.ι f =
        (q ≫ eQ) ≫ Abelian.coimageImageComparison f ≫
          Abelian.image.ι f := by simp [Category.assoc]
    _ = f := by rw [hqQ]; exact Abelian.coimage_image_factorisation f
    _ = l ≫ ι := hli.symm
    _ = (q ≫ c) ≫ ι := by rw [hqc]
    _ = (q ≫ c) ≫ (eI ≫ Abelian.image.ι f) := by rw [heI]
    _ = (q ≫ c ≫ eI) ≫ Abelian.image.ι f := by simp [Category.assoc]

theorem filtration_step_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B Q I : C} (q : A ⟶ Q) (c : Q ⟶ I) (ι : I ⟶ B) [Mono ι]
    (f : A ⟶ B) (P : Subobject A) (R : Subobject Q)
    (S : Subobject I) (T : Subobject B)
    (hcomp : q ≫ c ≫ ι = f)
    (hq : R = (Subobject.«exists» q).obj P)
    (hS : S = (Subobject.pullback ι).obj T)
    (htotal : (Subobject.«exists» f).obj (⊤ : Subobject A) =
      (Subobject.map ι).obj (⊤ : Subobject I)) :
    (Subobject.«exists» c).obj R = S ↔
      (Subobject.«exists» f).obj P =
        (Subobject.«exists» f).obj (⊤ : Subobject A) ⊓ T := by
  constructor
  · intro h
    calc
      (Subobject.«exists» f).obj P =
          (Subobject.«exists» (q ≫ c ≫ ι)).obj P := by rw [hcomp]
      _ = (Subobject.«exists» ι).obj
          ((Subobject.«exists» c).obj ((Subobject.«exists» q).obj P)) := by
        rw [← exists_comp, ← exists_comp]
      _ = (Subobject.map ι).obj ((Subobject.«exists» c).obj R) := by
        rw [Subobject.exists_iso_map ι, hq]
      _ = (Subobject.map ι).obj S := by rw [h]
      _ = (Subobject.map ι).obj ((Subobject.pullback ι).obj T) := by rw [hS]
      _ = (Subobject.map ι).obj (⊤ : Subobject I) ⊓ T :=
        map_pullback_eq_map_top_inf ι T
      _ = (Subobject.«exists» f).obj (⊤ : Subobject A) ⊓ T := by rw [htotal]
  · intro h
    apply subobjectMap_injective_of_mono ι
    calc
      (Subobject.map ι).obj ((Subobject.«exists» c).obj R) =
          (Subobject.map ι).obj
            ((Subobject.«exists» c).obj ((Subobject.«exists» q).obj P)) := by
        rw [hq]
      _ = (Subobject.«exists» f).obj P := by
        rw [← Subobject.exists_iso_map ι, ← exists_comp, ← exists_comp, hcomp]
      _ = (Subobject.«exists» f).obj (⊤ : Subobject A) ⊓ T := h
      _ = (Subobject.map ι).obj (⊤ : Subobject I) ⊓ T := by rw [htotal]
      _ = (Subobject.map ι).obj ((Subobject.pullback ι).obj T) :=
        (map_pullback_eq_map_top_inf ι T).symm
      _ = (Subobject.map ι).obj S := by rw [hS]

private theorem isIso_iff_of_iso_comp_eq_comp_iso
    {C : Type u} [Category.{v} C] {W X Y Z : C}
    (a : W ⟶ X) (f : X ⟶ Y) (b : W ⟶ Z) (c : Z ⟶ Y)
    (ha : IsIso a) (hc : IsIso c) (h : a ≫ f = b ≫ c) :
    IsIso f ↔ IsIso b := by
  let _ : IsIso a := ha
  let _ : IsIso c := hc
  constructor
  · intro hf
    let _ : IsIso f := hf
    have hcomp : IsIso (b ≫ c) := by rw [← h]; infer_instance
    exact IsIso.of_isIso_comp_right b c
  · intro hb
    let _ : IsIso b := hb
    have hcomp : IsIso (a ≫ f) := by rw [h]; infer_instance
    exact IsIso.of_isIso_comp_left a f

private def filteredFactorThruImage {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) :
    A ⟶ filteredKernel (filteredCokernelπ f) := by
  let n := filteredCokernelπ f
  let ι := filteredKernelι n
  let l₀ := kernel.lift n.hom f.hom (by
    change f.hom ≫ cokernel.π f.hom = 0
    exact cokernel.condition f.hom) ≫
    (Subobject.underlyingIso (kernel.ι n.hom)).inv
  refine ⟨l₀, ?_⟩
  intro i
  apply (Subobject.factors_iff _ _).mpr
  let X := A.filtration.obj i
  let Y := B.filtration.obj i
  let P := (Subobject.pullback ι.hom).obj Y
  let hP := Subobject.isPullback ι.hom Y
  let u := Y.factorThru (X.arrow ≫ f.hom) (f.map_filtration i)
  refine ⟨hP.lift u (X.arrow ≫ l₀) ?_, hP.lift_snd _ _ _⟩
  rw [Subobject.factorThru_arrow]
  change X.arrow ≫ f.hom =
    (X.arrow ≫ l₀) ≫ (Subobject.mk (kernel.ι n.hom)).arrow
  dsimp [l₀]
  simp only [Category.assoc]
  rw [Subobject.underlyingIso_arrow, kernel.lift_ι]

private theorem filteredFactorThruImage_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) :
    (filteredFactorThruImage f).hom ≫
      (filteredKernelι (filteredCokernelπ f)).hom = f.hom := by
  change (kernel.lift (cokernel.π f.hom) f.hom (cokernel.condition f.hom) ≫
      (Subobject.underlyingIso (kernel.ι (cokernel.π f.hom))).inv) ≫
    (Subobject.mk (kernel.ι (cokernel.π f.hom))).arrow = f.hom
  rw [Category.assoc, Subobject.underlyingIso_arrow, kernel.lift_ι]

private theorem filteredKernelι_comp_filteredFactorThruImage
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) :
    filteredKernelι f ≫ filteredFactorThruImage f = 0 := by
  apply FilteredHom.ext _ _
  let ι := filteredKernelι (filteredCokernelπ f)
  let _ : Mono ι.hom := by
    change Mono (Subobject.mk (kernel.ι (cokernel.π f.hom))).arrow
    infer_instance
  apply (cancel_mono ι.hom).mp
  rw [filteredHom_comp_hom]
  change ((filteredKernelι f).hom ≫ (filteredFactorThruImage f).hom) ≫ ι.hom =
    (0 : filteredHomAddSubgroup _ _).1 ≫ ι.hom
  rw [Category.assoc, filteredFactorThruImage_comp]
  change (filteredKernelι f).hom ≫ f.hom =
    (0 : (filteredKernel f).carrier ⟶ _ ) ≫ ι.hom
  rw [zero_comp]
  change (Subobject.mk (kernel.ι f.hom)).arrow ≫ f.hom = 0
  rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
    kernel.condition]
  simp

theorem strict_iff_coimage_image_isIso {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) :
    Strict f ↔ IsIso (Abelian.coimageImageComparison f) := by
  let n := filteredCokernelπ f
  let I := filteredKernel n
  let ι := filteredKernelι n
  let l : A ⟶ I := filteredFactorThruImage f
  let k := (filteredKernelFork f).π.app WalkingParallelPair.zero
  have hli : l.hom ≫ ι.hom = f.hom := filteredFactorThruImage_comp f
  have hkl : k ≫ l = 0 := filteredKernelι_comp_filteredFactorThruImage f
  let cc : CokernelCofork (show filteredKernel f ⟶ A from k) :=
    CokernelCofork.ofπ (f := (show filteredKernel f ⟶ A from k)) l hkl
  let c₀ := (filteredCokernelCofork_isColimit k).desc cc
  let q₀ := (filteredCokernelCofork k).π
  have hq₀c : q₀ ≫ c₀ = l := by
    exact (filteredCokernelCofork_isColimit k).fac cc WalkingParallelPair.one
  let eK := (filteredKernelFork_isLimit f).conePointUniqueUpToIso (limit.isLimit _)
  have hK : eK.hom ≫ kernel.ι f = k := by
    simpa [eK, k, filteredKernelFork] using
      IsLimit.conePointUniqueUpToIso_hom_comp
        (filteredKernelFork_isLimit f) (limit.isLimit _) WalkingParallelPair.zero
  let φQ : Arrow.mk k ≅ Arrow.mk (kernel.ι f) :=
    Arrow.isoMk' k (kernel.ι f) eK (Iso.refl _)
      (by simpa using hK)
  let cq : CokernelCofork (kernel.ι f) :=
    CokernelCofork.ofπ (Abelian.coimage.π f) (cokernel.condition _)
  let eQ₀ := CokernelCofork.mapIsoOfIsColimit
    (filteredCokernelCofork_isColimit k) (cokernelIsCokernel (kernel.ι f)) φQ
  let eN := (filteredCokernelCofork_isColimit f).coconePointUniqueUpToIso
    (colimit.isColimit _)
  have hN : n ≫ eN.hom = cokernel.π f := by
    change (filteredCokernelCofork f).π ≫ eN.hom = cokernel.π f
    simpa [eN] using
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (filteredCokernelCofork_isColimit f) (colimit.isColimit _) WalkingParallelPair.one
  let φI : Arrow.mk n ≅ Arrow.mk (cokernel.π f) :=
    Arrow.isoMk' n (cokernel.π f) (Iso.refl _) eN (by simpa using hN.symm)
  let eI₀ := KernelFork.mapIsoOfIsLimit
    (filteredKernelFork_isLimit n) (limit.isLimit _) φI
  have hI : eI₀.hom ≫ kernel.ι (cokernel.π f) =
      (filteredKernelFork n).π.app WalkingParallelPair.zero := by
    have hleft : φI.hom.left = 𝟙 B := by rfl
    simpa [eI₀, KernelFork.mapIsoOfIsLimit, φI, hleft] using
      KernelFork.mapOfIsLimit_ι (filteredKernelFork n) (limit.isLimit _)
        φI.hom
  have hfork : (filteredKernelFork n).π.app WalkingParallelPair.zero = ι := by
    rfl
  let : Epi q₀ := epi_of_isColimit_cofork
    (filteredCokernelCofork_isColimit k)
  have hqQ : q₀ ≫ eQ₀.hom = Abelian.coimage.π f := by
    simp [q₀, eQ₀, φQ]
  have hli' : l ≫ ι = f := by
    apply FilteredHom.ext _ _
    exact hli
  have hrel : eQ₀.hom ≫ Abelian.coimageImageComparison f =
      c₀ ≫ eI₀.hom := by
    apply coimageComparison_eq_of_factorisations f q₀ c₀ l ι
      eQ₀.hom eI₀.hom hqQ hq₀c hli'
    exact hI.trans hfork
  have hl0epi : Epi l.hom := by
    change Epi (Abelian.factorThruImage f.hom ≫
      (Subobject.underlyingIso (kernel.ι (cokernel.π f.hom))).inv)
    infer_instance
  let eKc : kernel f.hom ≅ (filteredKernel f).carrier :=
    (Subobject.underlyingIso (kernel.ι f.hom)).symm
  have hk : eKc.hom ≫ k.hom = kernel.ι f.hom := by
    change (Subobject.underlyingIso (kernel.ι f.hom)).inv ≫
      (Subobject.mk (kernel.ι f.hom)).arrow = kernel.ι f.hom
    simp
  let hck := cokernel.ofIsoComp (f := kernel.ι f.hom) k.hom eKc hk
  let eQ : (filteredCokernelCofork k).pt.carrier ≅
      cokernel (kernel.ι f.hom) := by
    change cokernel k.hom ≅ cokernel (kernel.ι f.hom)
    exact (cokernelIsCokernel k.hom).coconePointUniqueUpToIso hck
  have hqstd : q₀.hom ≫ eQ.hom = cokernel.π (kernel.ι f.hom) := by
    change cokernel.π k.hom ≫ eQ.hom = cokernel.π (kernel.ι f.hom)
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel k.hom) hck WalkingParallelPair.one
  let : Epi l.hom := hl0epi
  have hc0epi : Epi c₀.hom := by
    apply epi_of_epi_fac (f := q₀.hom) (g := c₀.hom) (h := l.hom)
    exact congrArg FilteredHom.hom hq₀c
  have Epi_q₀_hom : Epi q₀.hom := by
    change Epi (cokernel.π k.hom)
    infer_instance
  let d := eQ.hom ≫ Abelian.factorThruCoimage f.hom
  have hd : c₀.hom ≫ ι.hom = d := by
    apply (cancel_epi q₀.hom).mp
    calc
      q₀.hom ≫ c₀.hom ≫ ι.hom =
          (q₀ ≫ c₀).hom ≫ ι.hom := by simp [Category.assoc]
      _ = l.hom ≫ ι.hom := by rw [hq₀c]
      _ = f.hom := hli
      _ = cokernel.π (kernel.ι f.hom) ≫ Abelian.factorThruCoimage f.hom :=
        (Abelian.coimage.fac f.hom).symm
      _ = (q₀.hom ≫ eQ.hom) ≫ Abelian.factorThruCoimage f.hom := by
        rw [hqstd]
      _ = q₀.hom ≫ d := by
        dsimp [d]
        exact Category.assoc _ _ _
  have hdmono : Mono d := by
    dsimp [d]
    infer_instance
  let : Mono d := hdmono
  have hc0mono : Mono c₀.hom := by
    exact mono_of_mono_fac hd
  let : Epi c₀.hom := hc0epi
  let : Mono c₀.hom := hc0mono
  have hc0iso : IsIso c₀.hom := isIso_of_mono_of_epi c₀.hom
  have hqstrict : Strict q₀ := by
    apply (strict_iff_quotient_filtration q₀
      ((filtered_surjective_iff_epi q₀).2 inferInstance)).2
    intro i
    rfl
  let : Mono ι.hom := by
    change Mono (Subobject.mk (kernel.ι n.hom)).arrow
    infer_instance
  have histrict : Strict ι := by
    apply (strict_iff_induced_filtration ι (by
      change Mono ι.hom
      infer_instance)).2
    intro i
    rfl
  have htotal : (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) =
      (Subobject.map ι.hom).obj (⊤ : Subobject (filteredKernel n).carrier) := by
    rw [← Subobject.exists_iso_map ι.hom]
    rw [← hli]
    rw [exists_comp, exists_top_of_epi l.hom]
  have hc0strict_iff : Strict c₀ ↔
      ∀ i : ℤ,
        (Subobject.«exists» c₀.hom).obj
            ((filteredCokernelCofork k).pt.filtration.obj i) =
          cc.pt.filtration.obj i := by
    exact strict_iff_exists_eq_of_epi c₀
  have hq₀c' : q₀.hom ≫ c₀.hom = l.hom := by
    exact congrArg FilteredHom.hom hq₀c
  have hcomp : q₀.hom ≫ c₀.hom ≫ ι.hom = f.hom := by
    calc
      q₀.hom ≫ c₀.hom ≫ ι.hom =
          (q₀.hom ≫ c₀.hom) ≫ ι.hom := by simp [Category.assoc]
      _ = l.hom ≫ ι.hom := by rw [hq₀c']
      _ = f.hom := hli
  have hqfil (i : ℤ) :
      (filteredCokernelCofork k).pt.filtration.obj i =
        (Subobject.«exists» q₀.hom).obj (A.filtration.obj i) := by
    have hq := (strict_iff_quotient_filtration q₀
      ((filtered_surjective_iff_epi q₀).2 inferInstance)).mp hqstrict i
    simpa only [parallelPair_obj_zero] using hq
  have hstep (i : ℤ) :
      (Subobject.«exists» c₀.hom).obj
          ((filteredCokernelCofork k).pt.filtration.obj i) =
        cc.pt.filtration.obj i ↔
      (Subobject.«exists» f.hom).obj (A.filtration.obj i) =
        (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) ⊓
          B.filtration.obj i := by
    exact filtration_step_iff q₀.hom c₀.hom ι.hom f.hom
      (A.filtration.obj i) ((filteredCokernelCofork k).pt.filtration.obj i)
      (cc.pt.filtration.obj i) (B.filtration.obj i) hcomp (hqfil i) rfl htotal
  have hstrictc : Strict c₀ ↔ IsIso c₀ := by
    exact (strict_iff_isIso_of_hom_iso c₀ hc0iso)
  have hstep_iff : Strict c₀ ↔ Strict f := by
    constructor
    · intro hc i
      exact (hstep i).1 ((hc0strict_iff.mp hc) i)
    · intro hf
      apply hc0strict_iff.mpr
      intro i
      exact (hstep i).2 (hf i)
  have heQiso : IsIso eQ₀.hom := eQ₀.isIso_hom
  have heIiso : IsIso eI₀.hom := eI₀.isIso_hom
  have hiso : IsIso (Abelian.coimageImageComparison f) ↔ IsIso c₀ :=
    isIso_iff_of_iso_comp_eq_comp_iso eQ₀.hom
      (Abelian.coimageImageComparison f) c₀ eI₀.hom heQiso heIiso hrel
  constructor
  · intro hs
    exact hiso.mpr (hstrictc.mp (hstep_iff.mpr hs))
  · intro hi
    exact hstep_iff.mp (hstrictc.mpr (hiso.mp hi))

end Formalization.Books.Homology.Unit19
