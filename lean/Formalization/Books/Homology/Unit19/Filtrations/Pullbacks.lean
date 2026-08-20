import Formalization.Books.Homology.Unit19.Filtrations.Pushouts

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open scoped ZeroObject

universe v u

namespace Formalization.Books.Homology.Unit19

structure FilteredPullbackData {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A) where
  pullback : FilteredObject C
  fst : pullback ⟶ B
  snd : pullback ⟶ D
  comm : fst ≫ f = snd ≫ g
  isLimit : IsLimit (PullbackCone.mk fst snd comm)

private theorem image_pullback_projection_eq {C : Type u}
    [Category.{v} C] [Abelian C]
    {X Y Z W : C} (q : X ⟶ Y) (r : X ⟶ Z) (f : Y ⟶ W) (g : Z ⟶ W)
    (hcomm : q ≫ f = r ≫ g)
    (hpb : IsLimit (PullbackCone.mk q r hcomm)) (S : Subobject Y) :
    (Subobject.«exists» r).obj ((Subobject.pullback q).obj S) =
      (Subobject.pullback g).obj ((Subobject.«exists» f).obj S) := by
  let Q := (Subobject.pullback q).obj S
  let R := (Subobject.pullback g).obj
    ((Subobject.«exists» f).obj S)
  have hQq : S.Factors (Q.arrow ≫ q) := by
    apply (CategoryTheory.Limits.pullback_factors_iff q S Q.arrow).mp
    exact Subobject.factors_self Q
  have hSf : ((Subobject.«exists» f).obj S).Factors (S.arrow ≫ f) := by
    apply (CategoryTheory.Limits.pullback_factors_iff f
      ((Subobject.«exists» f).obj S) S.arrow).mp
    exact Subobject.factors_of_le _
      ((Subobject.existsPullbackAdj f).unit.app S).le
      (Subobject.factors_self S)
  have hQf : ((Subobject.«exists» f).obj S).Factors
      (Q.arrow ≫ q ≫ f) := by
    have h := Subobject.factors_of_factors_right
      (S.factorThru (Q.arrow ≫ q) hQq) hSf
    rw [← Category.assoc, Subobject.factorThru_arrow] at h
    simpa only [Category.assoc] using h
  have hQR : Q ≤ (Subobject.pullback r).obj R := by
    apply Subobject.le_of_factors
    apply (CategoryTheory.Limits.pullback_factors_iff r R Q.arrow).2
    apply (CategoryTheory.Limits.pullback_factors_iff g
      ((Subobject.«exists» f).obj S) (Q.arrow ≫ r)).2
    simpa only [Category.assoc, hcomm] using hQf
  have hle : (Subobject.«exists» r).obj Q ≤ R := by
    exact ((Subobject.existsPullbackAdj r).homEquiv Q R).symm
      (CategoryTheory.homOfLE hQR) |>.le

  let F := Subobject.imageFactorisation f S
  let M : Subobject W := Subobject.mk F.F.m
  have hM : M = (Subobject.«exists» f).obj S := by
    change Subobject.mk ((Subobject.«exists» f).obj S).arrow = _
    simp
  let R' := (Subobject.pullback g).obj M
  let f' : (R' : C) ⟶ F.F.I :=
    Subobject.pullbackπ g M ≫ (Subobject.underlyingIso F.F.m).hom
  have hf' : f' ≫ F.F.m = R'.arrow ≫ g := by
    dsimp [f', R', M]
    rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
    exact (Subobject.isPullback g (Subobject.mk F.F.m)).w
  let _ : Epi F.F.e := by
    exact (strongEpi_of_strongEpiMonoFactorisation
      (Abelian.imageStrongEpiMonoFactorisation (S.arrow ≫ f)) F.isImage).epi
  let _ : Mono F.F.m := inferInstance
  have hTepi : Epi (pullback.fst (R'.arrow ≫ g) (S.arrow ≫ f)) := by
    exact Abelian.epi_fst_of_factor_thru_epi_mono_factorization
      (g₁ := F.F.e) (g₂ := F.F.m) (hg := F.F.fac)
      (f' := f') (hf := hf')
      (t := PullbackCone.mk _ _ pullback.condition)
      (ht := pullbackIsPullback (R'.arrow ≫ g) (S.arrow ≫ f))
  let _ : Epi (pullback.fst (R'.arrow ≫ g) (S.arrow ≫ f)) := hTepi
  let T := pullback (R'.arrow ≫ g) (S.arrow ≫ f)
  let l : T ⟶ X :=
    hpb.lift (PullbackCone.mk
      (pullback.snd (R'.arrow ≫ g) (S.arrow ≫ f) ≫ S.arrow)
      (pullback.fst (R'.arrow ≫ g) (S.arrow ≫ f) ≫ R'.arrow)
      (by
        rw [Category.assoc, Category.assoc, pullback.condition]
        ))
  have hlq_eq : l ≫ q =
      pullback.snd (R'.arrow ≫ g) (S.arrow ≫ f) ≫ S.arrow := by
    dsimp [l]
    exact hpb.fac _ WalkingCospan.left
  have hlr : l ≫ r =
      pullback.fst (R'.arrow ≫ g) (S.arrow ≫ f) ≫ R'.arrow := by
    dsimp [l]
    exact hpb.fac _ WalkingCospan.right
  have hlq : S.Factors (l ≫ q) := by
    rw [hlq_eq]
    exact Subobject.factors_comp_arrow _
  have hQl : Q.Factors l := by
    apply (CategoryTheory.Limits.pullback_factors_iff q S l).2
    exact hlq
  let w : (T : C) ⟶ (Q : C) := Q.factorThru l hQl
  have hw : w ≫ Q.arrow = l := Q.factorThru_arrow l hQl
  have hQr : ((Subobject.«exists» r).obj Q).Factors
      (pullback.fst (R'.arrow ≫ g) (S.arrow ≫ f) ≫ R'.arrow) := by
    have hfac : ((Subobject.«exists» r).obj Q).Factors (Q.arrow ≫ r) := by
      apply (CategoryTheory.Limits.pullback_factors_iff r
        ((Subobject.«exists» r).obj Q) Q.arrow).mp
      exact Subobject.factors_of_le _
        ((Subobject.existsPullbackAdj r).unit.app Q).le
        (Subobject.factors_self Q)
    have h := Subobject.factors_of_factors_right w hfac
    rw [← Category.assoc, hw, hlr] at h
    exact h
  have himage :
      imageSubobject
          (pullback.fst (R'.arrow ≫ g) (S.arrow ≫ f) ≫ R'.arrow) ≤
        (Subobject.«exists» r).obj Q := by
    exact imageSubobject_le _
      (((Subobject.«exists» r).obj Q).factorThru _ hQr)
      (((Subobject.«exists» r).obj Q).factorThru_arrow _ hQr)
  have himage_eq : imageSubobject
      (pullback.fst (R'.arrow ≫ g) (S.arrow ≫ f) ≫ R'.arrow) = R' := by
    calc
      imageSubobject
          (pullback.fst (R'.arrow ≫ g) (S.arrow ≫ f) ≫ R'.arrow) =
          (Subobject.«exists» (pullback.fst (R'.arrow ≫ g)
            (S.arrow ≫ f) ≫ R'.arrow)).obj (⊤ : Subobject T) :=
        (exists_top_eq_imageSubobject _).symm
      _ = (Subobject.«exists» R'.arrow).obj
          ((Subobject.«exists» (pullback.fst (R'.arrow ≫ g)
            (S.arrow ≫ f))).obj (⊤ : Subobject T)) := by
        rw [exists_comp]
      _ = (Subobject.«exists» R'.arrow).obj
          (⊤ : Subobject (R' : C)) := by
        rw [exists_top_of_epi]
      _ = R' := by
        rw [exists_top_eq_imageSubobject]
        simpa using (imageSubobject_mono R'.arrow)
  have hR' : R' ≤ (Subobject.«exists» r).obj Q := by
    rw [← himage_eq]
    exact himage
  apply le_antisymm
  · exact hle
  · simpa [R', hM] using hR'
private def canonicalFilteredPullbackObject {C : Type u}
    [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A) :
    FilteredObject C :=
  { carrier := pullback f.hom g.hom
    filtration :=
      { obj := fun i =>
          (Subobject.pullback (pullback.fst f.hom g.hom)).obj
              (B.filtration.obj i) ⊓
            (Subobject.pullback (pullback.snd f.hom g.hom)).obj
              (D.filtration.obj i)
        antitone := by
          intro i j hij
          exact inf_le_inf
            ((Subobject.pullback (pullback.fst f.hom g.hom)).monotone
              (B.filtration.antitone hij))
            ((Subobject.pullback (pullback.snd f.hom g.hom)).monotone
              (D.filtration.antitone hij)) } }

private noncomputable def canonicalFilteredPullback {C : Type u}
    [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A) :
    FilteredPullbackData f g := by
  let p := pullback f.hom g.hom
  let Pfil : ℤ → Subobject p := fun i =>
    (Subobject.pullback (pullback.fst f.hom g.hom)).obj
        (B.filtration.obj i) ⊓
      (Subobject.pullback (pullback.snd f.hom g.hom)).obj
        (D.filtration.obj i)
  let P : FilteredObject C := canonicalFilteredPullbackObject f g
  let fst : P ⟶ B :=
    ⟨pullback.fst f.hom g.hom, by
      intro i
      apply (CategoryTheory.Limits.pullback_factors_iff
        (pullback.fst f.hom g.hom) (B.filtration.obj i) (Pfil i).arrow).mp
      exact Subobject.factors_of_le _ inf_le_left
        (Subobject.factors_self (Pfil i))⟩
  let snd : P ⟶ D :=
    ⟨pullback.snd f.hom g.hom, by
      intro i
      apply (CategoryTheory.Limits.pullback_factors_iff
        (pullback.snd f.hom g.hom) (D.filtration.obj i) (Pfil i).arrow).mp
      exact Subobject.factors_of_le _ inf_le_right
        (Subobject.factors_self (Pfil i))⟩
  have comm : fst ≫ f = snd ≫ g := by
    apply FilteredHom.ext
    change pullback.fst f.hom g.hom ≫ f.hom =
      pullback.snd f.hom g.hom ≫ g.hom
    exact pullback.condition
  let lift : ∀ s : PullbackCone f g, s.pt ⟶ P := by
    intro s
    let h : s.pt.carrier ⟶ p :=
      pullback.lift s.fst.hom s.snd.hom
        (congrArg FilteredHom.hom s.condition)
    refine ⟨h, ?_⟩
    intro i
    dsimp [P]
    apply (Subobject.inf_factors _).mpr
    constructor
    · apply (CategoryTheory.Limits.pullback_factors_iff
        (pullback.fst f.hom g.hom) (B.filtration.obj i)
        ((s.pt.filtration.obj i).arrow ≫ h)).mpr
      simpa only [Category.assoc, h, pullback.lift_fst] using
        s.fst.map_filtration i
    · apply (CategoryTheory.Limits.pullback_factors_iff
        (pullback.snd f.hom g.hom) (D.filtration.obj i)
        ((s.pt.filtration.obj i).arrow ≫ h)).mpr
      simpa only [Category.assoc, h, pullback.lift_snd] using
        s.snd.map_filtration i
  have hlim : IsLimit (PullbackCone.mk fst snd comm) := by
    refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
    · intro s
      apply FilteredHom.ext
      change pullback.lift s.fst.hom s.snd.hom _ ≫
          pullback.fst f.hom g.hom = s.fst.hom
      exact pullback.lift_fst _ _ _
    · intro s
      apply FilteredHom.ext
      change pullback.lift s.fst.hom s.snd.hom _ ≫
          pullback.snd f.hom g.hom = s.snd.hom
      exact pullback.lift_snd _ _ _
    · intro s m hm₁ hm₂
      apply FilteredHom.ext
      apply pullback.hom_ext
      · have h := congrArg FilteredHom.hom hm₁
        calc
          m.hom ≫ pullback.fst f.hom g.hom = s.fst.hom := by
            simpa [fst] using h
          _ = (lift s).hom ≫ pullback.fst f.hom g.hom := by
            change s.fst.hom =
              pullback.lift s.fst.hom s.snd.hom _ ≫
                pullback.fst f.hom g.hom
            exact (pullback.lift_fst _ _ _).symm
      · have h := congrArg FilteredHom.hom hm₂
        calc
          m.hom ≫ pullback.snd f.hom g.hom = s.snd.hom := by
            simpa [snd] using h
          _ = (lift s).hom ≫ pullback.snd f.hom g.hom := by
            change s.snd.hom =
              pullback.lift s.fst.hom s.snd.hom _ ≫
                pullback.snd f.hom g.hom
            exact (pullback.lift_snd _ _ _).symm
  exact ⟨P, fst, snd, comm, hlim⟩

private theorem canonicalFilteredPullback_snd_strict
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A)
    (hf : Strict f) :
    Strict (canonicalFilteredPullback f g).snd := by
  let q := pullback.fst f.hom g.hom
  let r := pullback.snd f.hom g.hom
  intro i
  change (Subobject.«exists» r).obj
      ((Subobject.pullback q).obj (B.filtration.obj i) ⊓
        (Subobject.pullback r).obj (D.filtration.obj i)) =
    (Subobject.«exists» r).obj (⊤ : Subobject (pullback f.hom g.hom)) ⊓
      D.filtration.obj i
  rw [exists_inf_pullback_eq_exists_inf_ab]
  rw [image_pullback_projection_eq q r f.hom g.hom
    pullback.condition (pullbackIsPullback f.hom g.hom)
    (B.filtration.obj i)]
  let U := (Subobject.«exists» r).obj
    (⊤ : Subobject (pullback f.hom g.hom))
  let V := (Subobject.«exists» f.hom).obj
    (⊤ : Subobject B.carrier)
  let R := (Subobject.pullback g.hom).obj V ⊓ D.filtration.obj i
  have htop :
      (Subobject.pullback g.hom).obj V = U := by
    change (Subobject.pullback g.hom).obj
        ((Subobject.«exists» f.hom).obj (⊤ : Subobject B.carrier)) =
      (Subobject.«exists» r).obj
        (⊤ : Subobject (pullback f.hom g.hom))
    rw [← image_pullback_projection_eq q r f.hom g.hom
      pullback.condition (pullbackIsPullback f.hom g.hom)
      (⊤ : Subobject B.carrier)]
    rw [Subobject.pullback_top]
  have hleft :
      ((Subobject.pullback g.hom).obj
        ((Subobject.«exists» f.hom).obj (B.filtration.obj i)) ⊓
        D.filtration.obj i) ≤ U ⊓ D.filtration.obj i := by
    apply le_inf
    · exact inf_le_left.trans (by
        rw [← htop]
        exact (Subobject.pullback g.hom).monotone
          ((Subobject.«exists» f.hom).monotone le_top))
    · exact inf_le_right
  have hRtop : V.Factors (R.arrow ≫ g.hom) := by
    apply (CategoryTheory.Limits.pullback_factors_iff g.hom V R.arrow).mp
    exact Subobject.factors_of_le _ inf_le_left
      (Subobject.factors_self R)
  have hRD : (A.filtration.obj i).Factors (R.arrow ≫ g.hom) := by
    have hD : (D.filtration.obj i).Factors R.arrow := by
      exact Subobject.inf_arrow_factors_right _ _
    have h := Subobject.factors_of_factors_right
      ((D.filtration.obj i).factorThru R.arrow hD)
      (g := (D.filtration.obj i).arrow ≫ g.hom)
      (g.map_filtration i)
    rw [← Category.assoc, Subobject.factorThru_arrow] at h
    exact h
  have hRpre : R ≤
      (Subobject.pullback g.hom).obj
        ((Subobject.«exists» f.hom).obj (B.filtration.obj i)) := by
    apply Subobject.le_of_factors
    apply (CategoryTheory.Limits.pullback_factors_iff g.hom
      ((Subobject.«exists» f.hom).obj (B.filtration.obj i)) R.arrow).2
    rw [hf i]
    exact (Subobject.inf_factors _).2 ⟨hRtop, hRD⟩
  have hright : U ⊓ D.filtration.obj i ≤
      (Subobject.pullback g.hom).obj
        ((Subobject.«exists» f.hom).obj (B.filtration.obj i)) ⊓
        D.filtration.obj i := by
    rw [← htop]
    exact le_inf hRpre inf_le_right
  exact le_antisymm hleft hright

theorem filtered_pullback_exists {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A) :
    Nonempty (FilteredPullbackData f g) := by
  exact ⟨canonicalFilteredPullback f g⟩

theorem filtered_pullback_preserves_strict {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A)
    (hf : Strict f) (P : FilteredPullbackData f g) :
    Strict P.snd := by
  let Q := canonicalFilteredPullback f g
  have hQ : Strict Q.snd :=
    canonicalFilteredPullback_snd_strict f g hf
  let e : P.pullback ⟶ Q.pullback :=
    Q.isLimit.lift (PullbackCone.mk P.fst P.snd P.comm)
  let d : Q.pullback ⟶ P.pullback :=
    P.isLimit.lift (PullbackCone.mk Q.fst Q.snd Q.comm)
  have he_fst : e ≫ Q.fst = P.fst :=
    Q.isLimit.fac (PullbackCone.mk P.fst P.snd P.comm)
      WalkingCospan.left
  have he_snd : e ≫ Q.snd = P.snd :=
    Q.isLimit.fac (PullbackCone.mk P.fst P.snd P.comm)
      WalkingCospan.right
  have hd_fst : d ≫ P.fst = Q.fst :=
    P.isLimit.fac (PullbackCone.mk Q.fst Q.snd Q.comm)
      WalkingCospan.left
  have hd_snd : d ≫ P.snd = Q.snd :=
    P.isLimit.fac (PullbackCone.mk Q.fst Q.snd Q.comm)
      WalkingCospan.right
  have hed : e ≫ d = 𝟙 P.pullback := by
    apply PullbackCone.IsLimit.hom_ext P.isLimit
    · change (e ≫ d) ≫ P.fst = (𝟙 P.pullback) ≫ P.fst
      calc
        (e ≫ d) ≫ P.fst = e ≫ (d ≫ P.fst) := Category.assoc _ _ _
        _ = e ≫ Q.fst := by rw [hd_fst]
        _ = P.fst := he_fst
        _ = (𝟙 P.pullback) ≫ P.fst := (Category.id_comp _).symm
    · change (e ≫ d) ≫ P.snd = (𝟙 P.pullback) ≫ P.snd
      calc
        (e ≫ d) ≫ P.snd = e ≫ (d ≫ P.snd) := Category.assoc _ _ _
        _ = e ≫ Q.snd := by rw [hd_snd]
        _ = P.snd := he_snd
        _ = (𝟙 P.pullback) ≫ P.snd := (Category.id_comp _).symm
  have hde : d ≫ e = 𝟙 Q.pullback := by
    apply PullbackCone.IsLimit.hom_ext Q.isLimit
    · change (d ≫ e) ≫ Q.fst = (𝟙 Q.pullback) ≫ Q.fst
      calc
        (d ≫ e) ≫ Q.fst = d ≫ (e ≫ Q.fst) := Category.assoc _ _ _
        _ = d ≫ P.fst := by rw [he_fst]
        _ = Q.fst := hd_fst
        _ = (𝟙 Q.pullback) ≫ Q.fst := (Category.id_comp _).symm
    · change (d ≫ e) ≫ Q.snd = (𝟙 Q.pullback) ≫ Q.snd
      calc
        (d ≫ e) ≫ Q.snd = d ≫ (e ≫ Q.snd) := Category.assoc _ _ _
        _ = d ≫ P.snd := by rw [he_snd]
        _ = Q.snd := hd_snd
        _ = (𝟙 Q.pullback) ≫ Q.snd := (Category.id_comp _).symm
  let : IsIso e := ⟨⟨d, hed, hde⟩⟩
  let : IsIso e.hom :=
    ⟨⟨d.hom, congrArg FilteredHom.hom hed,
      congrArg FilteredHom.hom hde⟩⟩
  have he : Strict e := by
    apply (strict_iff_isIso_of_hom_iso e (by infer_instance)).2
    infer_instance
  rw [← he_snd]
  exact strict_composition_of_strict_of_epi e Q.snd he hQ (by
    change Epi e.hom
    infer_instance)

end Formalization.Books.Homology.Unit19
