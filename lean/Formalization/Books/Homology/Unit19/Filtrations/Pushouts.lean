import Formalization.Books.Homology.Unit19.Filtrations.Subquotients

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open scoped ZeroObject

universe v u

namespace Formalization.Books.Homology.Unit19

/-! ### Pushouts and pullbacks -/

structure FilteredPushoutData {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : A ⟶ D) where
  pushout : FilteredObject C
  inl : B ⟶ pushout
  inr : D ⟶ pushout
  comm : f ≫ inl = g ≫ inr
  isColimit : IsColimit (PushoutCocone.mk inl inr comm)

theorem filtered_pushout_exists {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : A ⟶ D) :
    Nonempty (FilteredPushoutData f g) := by
  let h := filteredBiproductLift f (-g)
  let inlF := filteredBiproductLift (𝟙 B) (0 : B ⟶ D)
  let inrF := filteredBiproductLift (0 : D ⟶ B) (𝟙 D)
  let π := filteredCokernelπ h
  let inl := inlF ≫ π
  let inr := inrF ≫ π
  have hinl_eq : inlF.hom = biprod.inl := by
    change biprod.lift (𝟙 B.carrier) 0 = biprod.inl
    apply biprod.hom_ext <;> simp
  have hinr_eq : inrF.hom = biprod.inr := by
    change biprod.lift 0 (𝟙 D.carrier) = biprod.inr
    apply biprod.hom_ext <;> simp
  have hcomm : f ≫ inl = g ≫ inr := by
    let q := cokernel.π (biprod.lift f.hom (-g).hom)
    have hrel : f.hom ≫ biprod.inl ≫ q =
        g.hom ≫ biprod.inr ≫ q := by
      apply sub_eq_zero.mp
      have hz : biprod.lift f.hom (-g).hom ≫ q = 0 := by
        dsimp [q]
        exact cokernel.condition _
      have hz' : f.hom ≫ biprod.inl ≫ q +
          (-g).hom ≫ biprod.inr ≫ q = 0 := by
        have hl := congrArg (fun t => t ≫ q)
          (biprod.lift_eq (f := f.hom) (g := (-g).hom))
        calc
          f.hom ≫ biprod.inl ≫ q +
              (-g).hom ≫ biprod.inr ≫ q =
              (f.hom ≫ biprod.inl + (-g).hom ≫ biprod.inr) ≫ q := by
                rw [Preadditive.add_comp]
                simp only [Category.assoc]
          _ = (biprod.lift f.hom (-g).hom) ≫ q := hl.symm
          _ = 0 := hz
      have hneg : (-g).hom = -g.hom := by
        have hzero := congrArg FilteredHom.hom (add_neg_cancel g)
        change g.hom + (-g).hom =
          (0 : filteredHomAddSubgroup A D).1 at hzero
        exact eq_neg_of_add_eq_zero_right hzero
      have hnegcomp : (-g).hom ≫ biprod.inr ≫ q =
          -(g.hom ≫ biprod.inr ≫ q) := by
        have hh := congrArg (fun t => t ≫ biprod.inr ≫ q) hneg
        simpa only [neg_comp] using hh
      rw [hnegcomp] at hz'
      simpa [sub_eq_add_neg] using hz'
    apply FilteredHom.ext
    change f.hom ≫ inlF.hom ≫ π.hom =
      g.hom ≫ inrF.hom ≫ π.hom
    rw [hinl_eq, hinr_eq]
    exact hrel
  let desc : ∀ s : PushoutCocone f g, filteredCokernel h ⟶ s.pt := by
    intro s
    let d := filteredBiproductDesc s.inl s.inr
    have hd : h ≫ d = 0 := by
      apply FilteredHom.ext
      change biprod.lift f.hom (-g).hom ≫
          biprod.desc s.inl.hom s.inr.hom = 0
      rw [biprod.lift_desc]
      have hneg : (-g).hom = -g.hom := by
        have hzero := congrArg FilteredHom.hom (add_neg_cancel g)
        change g.hom + (-g).hom =
          (0 : filteredHomAddSubgroup A D).1 at hzero
        exact eq_neg_of_add_eq_zero_right hzero
      rw [hneg]
      change f.hom ≫ s.inl.hom + (-g.hom) ≫ s.inr.hom = 0
      have hscond := congrArg FilteredHom.hom s.condition
      change f.hom ≫ s.inl.hom = g.hom ≫ s.inr.hom at hscond
      rw [neg_comp, ← hscond]
      simp
    exact (filteredCokernelCofork_isColimit h).desc
      (CokernelCofork.ofπ d hd)
  have hcolim : IsColimit (PushoutCocone.mk inl inr hcomm) := by
    refine PushoutCocone.IsColimit.mk hcomm desc ?_ ?_ ?_
    · intro s
      have hfac : π ≫ desc s = filteredBiproductDesc s.inl s.inr := by
        dsimp [desc]
        exact (filteredCokernelCofork_isColimit h).fac _ WalkingParallelPair.one
      change (inlF ≫ π) ≫ desc s = s.inl
      rw [Category.assoc, hfac]
      apply FilteredHom.ext
      change biprod.lift (𝟙 B.carrier) 0 ≫
          biprod.desc s.inl.hom s.inr.hom = s.inl.hom
      simp
    · intro s
      have hfac : π ≫ desc s = filteredBiproductDesc s.inl s.inr := by
        dsimp [desc]
        exact (filteredCokernelCofork_isColimit h).fac _ WalkingParallelPair.one
      change (inrF ≫ π) ≫ desc s = s.inr
      rw [Category.assoc, hfac]
      apply FilteredHom.ext
      change biprod.lift 0 (𝟙 D.carrier) ≫
          biprod.desc s.inl.hom s.inr.hom = s.inr.hom
      simp
    · intro s m hm₁ hm₂
      apply Cofork.IsColimit.hom_ext (filteredCokernelCofork_isColimit h)
      have hfac : π ≫ desc s = filteredBiproductDesc s.inl s.inr := by
        dsimp [desc]
        exact (filteredCokernelCofork_isColimit h).fac _ WalkingParallelPair.one
      change π ≫ m = π ≫ desc s
      rw [hfac]
      apply FilteredHom.ext
      apply biprod.hom_ext'
      · have hm := congrArg FilteredHom.hom hm₁
        dsimp [inl] at hm
        rw [Category.assoc] at hm
        change inlF.hom ≫ π.hom ≫ m.hom = s.inl.hom at hm
        rw [hinl_eq] at hm
        have hd_inl : biprod.inl ≫
            (filteredBiproductDesc s.inl s.inr).hom = s.inl.hom := by
          change biprod.inl ≫ biprod.desc s.inl.hom s.inr.hom = _
          simp
        exact hm.trans hd_inl.symm
      · have hm := congrArg FilteredHom.hom hm₂
        dsimp [inr] at hm
        rw [Category.assoc] at hm
        change inrF.hom ≫ π.hom ≫ m.hom = s.inr.hom at hm
        rw [hinr_eq] at hm
        have hd_inr : biprod.inr ≫
            (filteredBiproductDesc s.inl s.inr).hom = s.inr.hom := by
          change biprod.inr ≫ biprod.desc s.inl.hom s.inr.hom = _
          simp
        exact hm.trans hd_inr.symm
  exact ⟨⟨filteredCokernel h, inl, inr, hcomm, hcolim⟩⟩

private theorem exists_sup_le_of_le {C : Type u} [Category.{v} C]
    [Abelian C] {X Y : C} (q : X ⟶ Y)
    (P Q : Subobject X) (R : Subobject Y)
    (hP : (Subobject.«exists» q).obj P ≤ R)
    (hQ : (Subobject.«exists» q).obj Q ≤ R) :
    (Subobject.«exists» q).obj (P ⊔ Q) ≤ R := by
  have hP' := ((Subobject.existsPullbackAdj q).homEquiv P R)
    (CategoryTheory.homOfLE hP)
  have hQ' := ((Subobject.existsPullbackAdj q).homEquiv Q R)
    (CategoryTheory.homOfLE hQ)
  exact ((Subobject.existsPullbackAdj q).homEquiv (P ⊔ Q) R).symm
    (CategoryTheory.homOfLE (sup_le hP'.le hQ'.le)) |>.le

private theorem image_eq_kernel_cokernel {C : Type u} [Category.{v} C]
    [Abelian C] {X Y : C} (a : X ⟶ Y) :
    imageSubobject a = kernelSubobject (cokernel.π a) := by
  let S : ShortComplex C :=
    ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
  have hExact : S.Exact := by
    apply (ShortComplex.exact_iff_of_forks (S := S)
      (kernelIsKernel (cokernel.π a))
      (cokernelIsCokernel a)).2
    exact kernel.condition (cokernel.π a)
  exact (ShortComplex.exact_iff_image_eq_kernel (S := S)).mp hExact

private theorem pushout_subobject_lattice_bound {C : Type u}
    [Category.{v} C] [Abelian C] {X : C}
    (T J K : Subobject X)
    (hKL : K ⊓ (T ⊔ J) ≤ (K ⊓ T) ⊔ (K ⊓ J)) :
    J ⊓ (T ⊔ K) ≤ (J ⊓ T) ⊔ K := by
  let L := T ⊔ J
  have hmod₁ : (T ⊔ K) ⊓ L = T ⊔ (K ⊓ L) :=
    sup_inf_assoc_of_le K le_sup_left
  have hmid : J ⊓ (T ⊔ K) ≤ T ⊔ (K ⊓ J) := by
    have h₁ : J ⊓ (T ⊔ K) ≤ (T ⊔ K) ⊓ L :=
      le_inf inf_le_right (inf_le_left.trans le_sup_right)
    rw [hmod₁] at h₁
    have h₂ : T ⊔ (K ⊓ L) ≤ T ⊔ ((K ⊓ T) ⊔ (K ⊓ J)) :=
      sup_le_sup_left hKL T
    have h₃ : T ⊔ ((K ⊓ T) ⊔ (K ⊓ J)) = T ⊔ (K ⊓ J) := by
      calc
        T ⊔ ((K ⊓ T) ⊔ (K ⊓ J)) =
            (T ⊔ (K ⊓ T)) ⊔ (K ⊓ J) := (sup_assoc _ _ _).symm
        _ = T ⊔ (K ⊓ J) := by
          exact congrArg (fun R => R ⊔ (K ⊓ J))
            (sup_eq_left.mpr inf_le_right)
    exact h₁.trans (h₂.trans_eq h₃)
  have hmod₂ :
      J ⊓ (T ⊔ (K ⊓ J)) = (J ⊓ T) ⊔ (K ⊓ J) :=
    (inf_sup_assoc_of_le (x := J) (y := T)
      (z := K ⊓ J) inf_le_right).symm
  have hmid' : J ⊓ (T ⊔ K) ≤ J ⊓ (T ⊔ (K ⊓ J)) :=
    le_inf inf_le_left hmid
  exact (hmid'.trans_eq hmod₂).trans
    (sup_le_sup_left inf_le_left (J ⊓ T))

private theorem canonicalFilteredPushout_inr_strict {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : A ⟶ D)
    (hfg : Strict f) :
    Strict (filteredBiproductLift (0 : D ⟶ B) (𝟙 D) ≫
      filteredCokernelπ (filteredBiproductLift f (-g))) := by
  let h := filteredBiproductLift f (-g)
  let inrF := filteredBiproductLift (0 : D ⟶ B) (𝟙 D)
  let π := filteredCokernelπ h
  let r := inrF ≫ π
  have hinrF_strict : Strict inrF := by
    have hm : FilteredInjective inrF := by
      change Mono (biprod.lift (0 : D.carrier ⟶ B.carrier)
        (𝟙 D.carrier))
      constructor
      intro Z a b hab
      have hs := congrArg
        (fun k => k ≫ (biprod.snd : B.carrier ⊞ D.carrier ⟶ D.carrier)) hab
      simpa using hs
    apply (strict_iff_induced_filtration inrF hm).2
    intro i
    have h₁ : D.filtration.obj i ≤
        (Subobject.pullback inrF.hom).obj
          ((filteredBiproduct B D).filtration.obj i) := by
      apply Subobject.le_of_factors
      apply (CategoryTheory.Limits.pullback_factors_iff
        inrF.hom ((filteredBiproduct B D).filtration.obj i)
        (D.filtration.obj i).arrow).2
      exact (inrF.map_filtration i)
    have h₂ : (Subobject.pullback inrF.hom).obj
          ((filteredBiproduct B D).filtration.obj i) ≤
        D.filtration.obj i := by
      let T : Subobject (B.carrier ⊞ D.carrier) :=
        (filteredBiproduct B D).filtration.obj i
      let P := (Subobject.pullback inrF.hom).obj T
      apply Subobject.le_of_factors
      apply (Subobject.factors_iff _ _).mpr
      let hpb := Subobject.isPullback inrF.hom T
      have hPfac : T.Factors (P.arrow ≫ inrF.hom) :=
        (CategoryTheory.Limits.pullback_factors_iff inrF.hom T P.arrow).1
          (Subobject.factors_self P)
      have hTsnd : (D.filtration.obj i).Factors
          (T.arrow ≫ biprod.snd) := by
        have hfac := Subobject.factors_comp_arrow
          ((Subobject.underlyingIso
            (biprod.map (B.filtration.obj i).arrow
              (D.filtration.obj i).arrow)).hom ≫ biprod.snd)
        rw [Category.assoc, ← biprod.map_snd
          (B.filtration.obj i).arrow (D.filtration.obj i).arrow,
          ← Category.assoc,
          Subobject.underlyingIso_hom_comp_eq_mk] at hfac
        exact hfac
      have hcomp := Subobject.factors_of_factors_right
        (T.factorThru (P.arrow ≫ inrF.hom) hPfac)
        (g := T.arrow ≫ biprod.snd) hTsnd
      have heq : T.factorThru (P.arrow ≫ inrF.hom) hPfac ≫
          (T.arrow ≫ biprod.snd) =
          (P.arrow ≫ inrF.hom) ≫ biprod.snd := by
        calc
          T.factorThru (P.arrow ≫ inrF.hom) hPfac ≫
                (T.arrow ≫ biprod.snd) =
              (T.factorThru (P.arrow ≫ inrF.hom) hPfac ≫ T.arrow) ≫
                biprod.snd := (Category.assoc _ _ _).symm
          _ = (P.arrow ≫ inrF.hom) ≫ biprod.snd := by
            rw [Subobject.factorThru_arrow]
            rfl
      have heq' : (P.arrow ≫ inrF.hom) ≫ biprod.snd = P.arrow := by
        change (P.arrow ≫
          biprod.lift (0 : D.carrier ⟶ B.carrier) (𝟙 D.carrier)) ≫
            biprod.snd = P.arrow
        simp [Category.assoc]
      rw [heq, heq'] at hcomp
      exact (Subobject.factors_iff _ _).mp hcomp
    exact le_antisymm h₁ h₂
  have hr : Strict r := by
    intro i
    let j : D.carrier ⟶ (filteredBiproduct B D).carrier := biprod.inr
    have hinrF : inrF.hom = j := by
      change biprod.lift 0 (𝟙 D.carrier) = j
      apply biprod.hom_ext <;> simp [j]
    have hr_hom : r.hom = j ≫ π.hom := by
      change (inrF ≫ π).hom = _
      change inrF.hom ≫ π.hom = _
      rw [hinrF]
    rw [hr_hom]
    change (Subobject.«exists»
        (j ≫ π.hom)).obj (D.filtration.obj i) =
      (Subobject.«exists»
        (j ≫ π.hom)).obj (⊤ : Subobject D.carrier) ⊓
        (Subobject.«exists» π.hom).obj
          ((filteredBiproduct B D).filtration.obj i)
    let T : Subobject (filteredBiproduct B D).carrier :=
      (filteredBiproduct B D).filtration.obj i
    let fstE : (filteredBiproduct B D).carrier ⟶ B.carrier := by
      change B.carrier ⊞ D.carrier ⟶ B.carrier
      exact biprod.fst
    let sndE : (filteredBiproduct B D).carrier ⟶ D.carrier := by
      change B.carrier ⊞ D.carrier ⟶ D.carrier
      exact biprod.snd
    let : Mono j :=
      (inferInstance : Mono (biprod.inr : D.carrier ⟶ B.carrier ⊞ D.carrier))
    let J : Subobject (filteredBiproduct B D).carrier := Subobject.mk j
    let K : Subobject (filteredBiproduct B D).carrier :=
      Subobject.mk (kernel.ι (cokernel.π h.hom))
    let L : Subobject (filteredBiproduct B D).carrier := T ⊔ J
    let U : Subobject A.carrier :=
      (Subobject.pullback f.hom).obj (B.filtration.obj i)
    let Kf : Subobject A.carrier := Subobject.mk (kernel.ι f.hom)
    have hJarrow :
        (Subobject.underlyingIso j).inv ≫ J.arrow = j := by
      dsimp [J]
      apply (cancel_epi (Subobject.underlyingIso j).hom).mp
      simp
    have hJarrow' : J.arrow =
        (Subobject.underlyingIso j).hom ≫ j := by
      dsimp [J]
      exact (Subobject.underlyingIso_hom_comp_eq_mk _).symm
    have hfst : h.hom ≫ fstE = f.hom := by
      change biprod.lift f.hom (-g).hom ≫ biprod.fst = f.hom
      simp
    have hTfst : (B.filtration.obj i).Factors
        (T.arrow ≫ fstE) := by
      have hfac := Subobject.factors_comp_arrow
        ((Subobject.underlyingIso
          (biprod.map (B.filtration.obj i).arrow
            (D.filtration.obj i).arrow)).hom ≫ biprod.fst)
      rw [Category.assoc, ← biprod.map_fst
        (B.filtration.obj i).arrow (D.filtration.obj i).arrow,
        ← Category.assoc,
        Subobject.underlyingIso_hom_comp_eq_mk] at hfac
      exact hfac
    have hJfst : (B.filtration.obj i).Factors
        (J.arrow ≫ fstE) := by
      have hjfst : j ≫ fstE = 0 := by
        dsimp [j, fstE]
        change (biprod.inr : D.carrier ⟶ B.carrier ⊞ D.carrier) ≫
          (biprod.fst : B.carrier ⊞ D.carrier ⟶ B.carrier) = 0
        simp
      rw [hJarrow', Category.assoc, hjfst, comp_zero]
      exact Subobject.factors_zero
    have hTpre : T ≤
        (Subobject.pullback fstE).obj
          (B.filtration.obj i) := by
      apply Subobject.le_of_factors
      exact (CategoryTheory.Limits.pullback_factors_iff
        fstE
        (B.filtration.obj i) T.arrow).2 hTfst
    have hJpre : J ≤
        (Subobject.pullback fstE).obj
          (B.filtration.obj i) := by
      apply Subobject.le_of_factors
      exact (CategoryTheory.Limits.pullback_factors_iff
        fstE
        (B.filtration.obj i) J.arrow).2 hJfst
    have hLpre : L ≤
        (Subobject.pullback fstE).obj
          (B.filtration.obj i) := by
      exact sup_le hTpre hJpre
    have hpre : (Subobject.pullback h.hom).obj L ≤ U := by
      calc
        (Subobject.pullback h.hom).obj L ≤
            (Subobject.pullback h.hom).obj
              ((Subobject.pullback fstE).obj
                (B.filtration.obj i)) :=
          (Subobject.pullback h.hom).monotone hLpre
        _ = (Subobject.pullback (h.hom ≫ fstE)).obj
              (B.filtration.obj i) := by
          rw [← Subobject.pullback_comp]
        _ = U := by rw [hfst]
    have hK0 :
        (Subobject.«exists» h.hom).obj (⊤ : Subobject A.carrier) = K := by
      rw [exists_top_eq_imageSubobject h.hom]
      simpa [K] using
        image_eq_kernel_cokernel h.hom
    have hJfac_of_fst_zero {X : C}
        (z : X ⟶ (filteredBiproduct B D).carrier)
        (hz : z ≫ fstE = 0) : J.Factors z := by
      change X ⟶ B.carrier ⊞ D.carrier at z
      change B.carrier ⊞ D.carrier ⟶ B.carrier at fstE
      change B.carrier ⊞ D.carrier ⟶ D.carrier at sndE
      dsimp [J]
      apply (Subobject.factors_iff (Subobject.mk j) z).mpr
      let w : D.carrier ⟶ (Subobject.mk j : C) :=
        (Subobject.underlyingIso j).inv
      refine ⟨z ≫ sndE ≫ w, ?_⟩
      dsimp [w]
      rw [← Subobject.underlyingIso_hom_comp_eq_mk]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      dsimp [fstE, sndE] at hz ⊢
      change z ≫ biprod.fst = 0 at hz
      apply biprod.hom_ext
      · change (z ≫ biprod.snd ≫ biprod.inr) ≫ biprod.fst =
          z ≫ biprod.fst
        calc
          (z ≫ biprod.snd ≫ biprod.inr) ≫ biprod.fst =
              z ≫ ((biprod.snd ≫ biprod.inr) ≫ biprod.fst) :=
            Category.assoc _ _ _
          _ = z ≫ (biprod.snd ≫ (biprod.inr ≫ biprod.fst)) := by
            rw [Category.assoc]
          _ = 0 := by rw [biprod.inr_fst, comp_zero, comp_zero]
          _ = z ≫ biprod.fst := hz.symm
      · change (z ≫ biprod.snd ≫ biprod.inr) ≫ biprod.snd =
          z ≫ biprod.snd
        calc
          (z ≫ biprod.snd ≫ biprod.inr) ≫ biprod.snd =
              z ≫ ((biprod.snd ≫ biprod.inr) ≫ biprod.snd) :=
            Category.assoc _ _ _
          _ = z ≫ (biprod.snd ≫ (biprod.inr ≫ biprod.snd)) := by
            rw [Category.assoc]
          _ = z ≫ biprod.snd ≫ 𝟙 D.carrier := by
            rw [biprod.inr_snd]
          _ = z ≫ biprod.snd := by simp
    have hKfJ :
        (Subobject.«exists» h.hom).obj Kf ≤ K ⊓ J := by
      have hz : (Kf.arrow ≫ h.hom) ≫ fstE = 0 := by
        rw [Category.assoc, hfst]
        rw [← Subobject.underlyingIso_hom_comp_eq_mk,
          Category.assoc, kernel.condition]
        simp
      have hfac : J.Factors (Kf.arrow ≫ h.hom) :=
        hJfac_of_fst_zero (Kf.arrow ≫ h.hom) hz
      have hKfK :
          (Subobject.«exists» h.hom).obj Kf ≤ K := by
        calc
          (Subobject.«exists» h.hom).obj Kf ≤
              (Subobject.«exists» h.hom).obj (⊤ : Subobject A.carrier) :=
            (Subobject.«exists» h.hom).monotone le_top
          _ = K := hK0
      have hKfJ' :
          (Subobject.«exists» h.hom).obj Kf ≤ J := by
        have hp : Kf ≤ (Subobject.pullback h.hom).obj J := by
          apply Subobject.le_of_factors
          exact (CategoryTheory.Limits.pullback_factors_iff
            h.hom J Kf.arrow).2 hfac
        exact ((Subobject.existsPullbackAdj h.hom).homEquiv Kf J).symm
          (CategoryTheory.homOfLE hp) |>.le
      exact le_inf hKfK hKfJ'
    have hAi :
        (Subobject.«exists» h.hom).obj (A.filtration.obj i) ≤ K ⊓ T := by
      have hAiK :
          (Subobject.«exists» h.hom).obj (A.filtration.obj i) ≤ K := by
        calc
          (Subobject.«exists» h.hom).obj (A.filtration.obj i) ≤
              (Subobject.«exists» h.hom).obj (⊤ : Subobject A.carrier) :=
            (Subobject.«exists» h.hom).monotone le_top
          _ = K := hK0
      have hAiT :
          (Subobject.«exists» h.hom).obj (A.filtration.obj i) ≤ T := by
        have hp : A.filtration.obj i ≤
            (Subobject.pullback h.hom).obj T := by
          apply Subobject.le_of_factors
          exact (CategoryTheory.Limits.pullback_factors_iff
            h.hom T (A.filtration.obj i).arrow).2
            (by simpa [T] using h.map_filtration i)
        exact ((Subobject.existsPullbackAdj h.hom).homEquiv
          (A.filtration.obj i) T).symm
          (CategoryTheory.homOfLE hp) |>.le
      exact le_inf hAiK hAiT
    have hU : U = A.filtration.obj i ⊔ Kf :=
      (strict_iff_preimage_eq_sup_kernel f).1 hfg i
    have hExistsU :
        (Subobject.«exists» h.hom).obj U ≤
          (K ⊓ T) ⊔ (K ⊓ J) := by
      rw [hU]
      exact exists_sup_le_of_le h.hom
        (A.filtration.obj i) Kf ((K ⊓ T) ⊔ (K ⊓ J))
        (hAi.trans le_sup_left) (hKfJ.trans le_sup_right)
    have hKL : K ⊓ L ≤ (K ⊓ T) ⊔ (K ⊓ J) := by
      calc
        K ⊓ L =
            (Subobject.«exists» h.hom).obj
              ((⊤ : Subobject A.carrier) ⊓
                (Subobject.pullback h.hom).obj L) := by
          rw [exists_inf_pullback_eq_exists_inf_ab]
          rw [hK0]
        _ ≤ (Subobject.«exists» h.hom).obj U := by
          apply (Subobject.«exists» h.hom).monotone
          simpa only [top_inf_eq] using hpre
        _ ≤ (K ⊓ T) ⊔ (K ⊓ J) := hExistsU
    have hJR :
        J ⊓ (Subobject.pullback π.hom).obj
            ((Subobject.«exists» π.hom).obj T) ≤
          (J ⊓ T) ⊔ K := by
      have hR :
          (Subobject.pullback π.hom).obj
              ((Subobject.«exists» π.hom).obj T) = T ⊔ K := by
        change (Subobject.pullback π.hom).obj
            ((Subobject.«exists» π.hom).obj T) =
          T ⊔ Subobject.mk (kernel.ι π.hom)
        exact pullback_exists_eq_sup_kernel π T
      rw [hR]
      exact pushout_subobject_lattice_bound T J K hKL
    rw [exists_comp, exists_comp]
    have hD : D.filtration.obj i =
        (Subobject.pullback j).obj T := by
      have hm : FilteredInjective inrF := by
        change Mono inrF.hom
        constructor
        intro Z a b hab
        change a ≫ biprod.lift (0 : D.carrier ⟶ B.carrier)
            (𝟙 D.carrier) =
          b ≫ biprod.lift (0 : D.carrier ⟶ B.carrier)
            (𝟙 D.carrier) at hab
        have hs := congrArg
          (fun k => k ≫ (biprod.snd : B.carrier ⊞ D.carrier ⟶ D.carrier)) hab
        change (a ≫ biprod.lift (0 : D.carrier ⟶ B.carrier)
            (𝟙 D.carrier)) ≫ biprod.snd =
          (b ≫ biprod.lift (0 : D.carrier ⟶ B.carrier)
            (𝟙 D.carrier)) ≫ biprod.snd at hs
        simpa [Category.assoc] using hs
      simpa [hinrF, T] using
        ((strict_iff_induced_filtration inrF hm).1 hinrF_strict i)
    have hJDi :
        (Subobject.«exists» j).obj (D.filtration.obj i) = J ⊓ T := by
      rw [hD, Subobject.exists_iso_map j]
      simpa [J] using map_pullback_eq_map_top_inf j T
    have hJtop :
        (Subobject.«exists» j).obj (⊤ : Subobject D.carrier) = J := by
      rw [Subobject.exists_iso_map j, Subobject.map_top]
    rw [hJDi, hJtop]
    rw [← exists_inf_pullback_eq_exists_inf_ab π.hom J
      ((Subobject.«exists» π.hom).obj T)]
    apply le_antisymm
    · apply (Subobject.«exists» π.hom).monotone
      exact le_inf inf_le_left
        (inf_le_right.trans
          ((Subobject.existsPullbackAdj π.hom).unit.app T).le)
    · have hKimage :
          (Subobject.«exists» π.hom).obj K ≤
            (Subobject.«exists» π.hom).obj (J ⊓ T) := by
        exact ((Subobject.existsPullbackAdj π.hom).homEquiv K
          ((Subobject.«exists» π.hom).obj (J ⊓ T))).symm
          (CategoryTheory.homOfLE (kernel_le_pullback π
            ((Subobject.«exists» π.hom).obj (J ⊓ T)))) |>.le
      have hsup :
          (Subobject.«exists» π.hom).obj (J ⊓ T) ≤
            (Subobject.«exists» π.hom).obj (J ⊓ T) := le_rfl
      have hsum := exists_sup_le_of_le π.hom (J ⊓ T) K
        ((Subobject.«exists» π.hom).obj (J ⊓ T)) hsup hKimage
      exact ((Subobject.«exists» π.hom).monotone hJR).trans hsum
  exact hr

private structure FilteredPushoutComparisonData {C : Type u}
    [Category.{v} C] [Abelian C] {A B D : FilteredObject C}
    (f : A ⟶ B) (g : A ⟶ D) (P : FilteredPushoutData f g) where
  comparison :
    filteredCokernel (filteredBiproductLift f (-g)) ⟶ P.pushout
  inr_comparison :
    (filteredBiproductLift (0 : D ⟶ B) (𝟙 D) ≫
        filteredCokernelπ (filteredBiproductLift f (-g))) ≫ comparison = P.inr
  comparison_strict : Strict comparison
  comparison_mono : Mono comparison.hom

private theorem filteredPushoutComparison_exists {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : A ⟶ D)
    (P : FilteredPushoutData f g) :
    Nonempty (FilteredPushoutComparisonData f g P) := by
  let h := filteredBiproductLift f (-g)
  let inrF := filteredBiproductLift (0 : D ⟶ B) (𝟙 D)
  let π := filteredCokernelπ h
  let r := inrF ≫ π
  let inlF := filteredBiproductLift (𝟙 B) (0 : B ⟶ D)
  let inl := inlF ≫ π
  have hinl_eq : inlF.hom = biprod.inl := by
    change biprod.lift (𝟙 B.carrier) 0 = biprod.inl
    apply biprod.hom_ext <;> simp
  have hinr_eq : inrF.hom = biprod.inr := by
    change biprod.lift 0 (𝟙 D.carrier) = biprod.inr
    apply biprod.hom_ext <;> simp
  have hcomm : f ≫ inl = g ≫ r := by
    let q := cokernel.π (biprod.lift f.hom (-g).hom)
    have hrel : f.hom ≫ biprod.inl ≫ q =
        g.hom ≫ biprod.inr ≫ q := by
      apply sub_eq_zero.mp
      have hz : biprod.lift f.hom (-g).hom ≫ q = 0 := by
        dsimp [q]
        exact cokernel.condition _
      have hz' : f.hom ≫ biprod.inl ≫ q +
          (-g).hom ≫ biprod.inr ≫ q = 0 := by
        have hl := congrArg (fun t => t ≫ q)
          (biprod.lift_eq (f := f.hom) (g := (-g).hom))
        calc
          f.hom ≫ biprod.inl ≫ q +
                (-g).hom ≫ biprod.inr ≫ q =
              (f.hom ≫ biprod.inl + (-g).hom ≫ biprod.inr) ≫ q := by
                rw [Preadditive.add_comp]
                simp only [Category.assoc]
          _ = (biprod.lift f.hom (-g).hom) ≫ q := hl.symm
          _ = 0 := hz
      have hneg : (-g).hom = -g.hom := by
        have hzero := congrArg FilteredHom.hom (add_neg_cancel g)
        change g.hom + (-g).hom =
          (0 : filteredHomAddSubgroup A D).1 at hzero
        exact eq_neg_of_add_eq_zero_right hzero
      have hnegcomp : (-g).hom ≫ biprod.inr ≫ q =
          -(g.hom ≫ biprod.inr ≫ q) := by
        have hh := congrArg (fun t => t ≫ biprod.inr ≫ q) hneg
        simpa only [neg_comp] using hh
      rw [hnegcomp] at hz'
      simpa [sub_eq_add_neg] using hz'
    apply FilteredHom.ext
    change f.hom ≫ inlF.hom ≫ π.hom =
      g.hom ≫ inrF.hom ≫ π.hom
    rw [hinl_eq, hinr_eq]
    exact hrel
  let dP := filteredBiproductDesc P.inl P.inr
  have hdP : h ≫ dP = 0 := by
    apply FilteredHom.ext
    change biprod.lift f.hom (-g).hom ≫
        biprod.desc P.inl.hom P.inr.hom = 0
    rw [biprod.lift_desc]
    have hneg : (-g).hom = -g.hom := by
      have hzero := congrArg FilteredHom.hom (add_neg_cancel g)
      change g.hom + (-g).hom =
        (0 : filteredHomAddSubgroup A D).1 at hzero
      exact eq_neg_of_add_eq_zero_right hzero
    rw [hneg]
    change f.hom ≫ P.inl.hom + (-g.hom) ≫ P.inr.hom = 0
    have hscond := congrArg FilteredHom.hom P.comm
    change f.hom ≫ P.inl.hom = g.hom ≫ P.inr.hom at hscond
    rw [neg_comp, ← hscond]
    simp
  let e : filteredCokernel h ⟶ P.pushout :=
    (filteredCokernelCofork_isColimit h).desc
      (CokernelCofork.ofπ dP hdP)
  have hefac : π ≫ e = dP := by
    dsimp [e]
    exact (filteredCokernelCofork_isColimit h).fac _ WalkingParallelPair.one
  have hinl_e : inl ≫ e = P.inl := by
    dsimp [inl]
    rw [Category.assoc, hefac]
    apply FilteredHom.ext
    change biprod.lift (𝟙 B.carrier) 0 ≫
        biprod.desc P.inl.hom P.inr.hom = P.inl.hom
    simp
  have hinr_e : r ≫ e = P.inr := by
    dsimp [r]
    rw [Category.assoc, hefac]
    apply FilteredHom.ext
    change biprod.lift 0 (𝟙 D.carrier) ≫
        biprod.desc P.inl.hom P.inr.hom = P.inr.hom
    simp
  let S : PushoutCocone f g := PushoutCocone.mk inl r hcomm
  let d : P.pushout ⟶ filteredCokernel h := P.isColimit.desc S
  have hd_inl : P.inl ≫ d = inl := by
    exact P.isColimit.fac S WalkingCospan.left
  have hd_inr : P.inr ≫ d = r := by
    exact P.isColimit.fac S WalkingCospan.right
  have hde : d ≫ e = 𝟙 P.pushout := by
    apply PushoutCocone.IsColimit.hom_ext P.isColimit
    · change P.inl ≫ (d ≫ e) = P.inl ≫ 𝟙 P.pushout
      rw [← Category.assoc, hd_inl, hinl_e]
      simp
    · change P.inr ≫ (d ≫ e) = P.inr ≫ 𝟙 P.pushout
      rw [← Category.assoc, hd_inr, hinr_e]
      simp
  have hed : e ≫ d = 𝟙 (filteredCokernel h) := by
    apply Cofork.IsColimit.hom_ext (filteredCokernelCofork_isColimit h)
    dsimp [filteredCokernelCofork, π]
    rw [← Category.assoc]
    rw [hefac]
    simp only [Category.comp_id]
    apply FilteredHom.ext
    apply biprod.hom_ext'
    · change biprod.inl ≫
        biprod.desc P.inl.hom P.inr.hom ≫ d.hom =
        biprod.inl ≫ π.hom
      rw [← Category.assoc]
      simp only [biprod.inl_desc]
      have hd_inl_hom := congrArg FilteredHom.hom hd_inl
      dsimp at hd_inl_hom
      change P.inl.hom ≫ d.hom = inl.hom at hd_inl_hom
      rw [← hinl_eq]
      rw [hd_inl_hom]
      change inlF.hom ≫ π.hom = inlF.hom ≫ π.hom
      simp
    · change biprod.inr ≫
        biprod.desc P.inl.hom P.inr.hom ≫ d.hom =
        biprod.inr ≫ π.hom
      rw [← Category.assoc]
      simp only [biprod.inr_desc]
      have hd_inr_hom := congrArg FilteredHom.hom hd_inr
      dsimp at hd_inr_hom
      change P.inr.hom ≫ d.hom = r.hom at hd_inr_hom
      rw [← hinr_eq, hd_inr_hom]
      change inrF.hom ≫ π.hom = inrF.hom ≫ π.hom
      simp
  let : IsIso e := ⟨⟨d, hed, hde⟩⟩
  let : IsIso e.hom :=
    ⟨⟨d.hom, congrArg FilteredHom.hom hed, congrArg FilteredHom.hom hde⟩⟩
  have he_strict : Strict e := by
    apply (strict_iff_isIso_of_hom_iso e (by infer_instance)).2
    infer_instance
  exact ⟨{
    comparison := e
    inr_comparison := hinr_e
    comparison_strict := he_strict
    comparison_mono := by infer_instance }⟩

theorem filtered_pushout_preserves_strict {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : A ⟶ D)
    (hfg : Strict f) (P : FilteredPushoutData f g) :
    Strict P.inr := by
  let r := filteredBiproductLift (0 : D ⟶ B) (𝟙 D) ≫
    filteredCokernelπ (filteredBiproductLift f (-g))
  have hr : Strict r := canonicalFilteredPushout_inr_strict f g hfg
  let Q := Classical.choice (filteredPushoutComparison_exists f g P)
  rw [← Q.inr_comparison]
  exact strict_composition_of_strict_of_mono r Q.comparison hr
    Q.comparison_strict Q.comparison_mono

end Formalization.Books.Homology.Unit19
