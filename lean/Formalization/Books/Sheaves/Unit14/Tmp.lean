import Formalization.Books.Sheaves.Unit14.StalksOfPresheavesOfModules

namespace Formalization.Books.Sheaves.Unit14

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit06
open scoped ChangeOfRings

universe u
noncomputable section

#check colimit.cocone
#check colimit.isColimit
#check PresheafOfModules.ModuleColimit.homEquiv
#check BinaryFan.mk_fst
#check BinaryFan.mk_snd
#check Types.binaryProductCone
#check Types.binaryProductLimitCone
#check Limits.limit.π
#check PresheafOfModules.ModuleColimit.ιR
#check PresheafOfModules.ModuleColimit.ιM
#check ModuleCat.smul
#check AddCommGrpCat.Hom.hom
#check PresheafOfModules.ModuleColimit.homEquiv_symm_apply
#check PresheafOfModules.colimitAdjunction
#check PresheafOfModules.colimitAdjunction_homEquiv
#check PresheafOfModules.colimitAdjunction_homEquiv_symm_apply
#check TopCat.Presheaf.stalkFunctor_map_germ_apply
#check ModuleCat.ExtendScalars.hom_ext
#check ModuleCat.extendRestrictScalarsAdj
#check ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
#check ModuleCat.isoMk
#check ModuleCat.homMk
#check Cocone.tensor_ι_app
#check CategoryTheory.Limits.Cocone.tensor_ι_app

example {X : TopCat.{u}} {O : CommRingPresheaf X}
    (F : CommRingPresheafModule O) (x : X) : True := by
  letI : InitiallySmall (OpenNhds x) := initiallySmall_of_essentiallySmall _
  let R₀ : (OpenNhds x)ᵒᵖ ⥤ CommRingCat :=
    (OpenNhds.inclusion x).op ⋙ O
  let cR₀ : Cocone R₀ := colimit.cocone R₀
  let hcR₀ : IsColimit cR₀ := colimit.isColimit R₀
  let R : (OpenNhds x)ᵒᵖ ⥤ RingCat := R₀ ⋙ forget₂ CommRingCat RingCat
  let cR : Cocone R := (forget₂ CommRingCat RingCat).mapCocone cR₀
  let hcR : IsColimit cR := isColimitOfPreserves (forget₂ CommRingCat RingCat) hcR₀
  let M : PresheafOfModules R :=
    (PresheafOfModules.pushforward₀ (OpenNhds.inclusion x) (O ⋙ forget₂ CommRingCat RingCat)).obj F
  let cM : Cocone M.presheaf := colimit.cocone M.presheaf
  let hcM : IsColimit cM := colimit.isColimit M.presheaf
  let e := PresheafOfModules.ModuleColimit.homEquiv
    (N := ModuleCat.of cR.pt (PresheafOfModules.ModuleColimit hcR hcM)) hcR hcM
  letI : Module (O.stalk x) (↑(TopCat.Presheaf.stalk F.presheaf x)) :=
    stalkModule O F x
  have hcolF : ModuleCat.of cR.pt (PresheafOfModules.ModuleColimit hcR hcM) ≅
      ModuleCat.of (O.stalk x) (↑(TopCat.Presheaf.stalk F.presheaf x)) := by
    dsimp [cR, cR₀, R₀]
    refine ModuleCat.isoMk
      (M := ModuleCat.of cR.pt (PresheafOfModules.ModuleColimit hcR hcM))
      (N := ModuleCat.of (O.stalk x) (↑(TopCat.Presheaf.stalk F.presheaf x)))
      (Iso.refl _) ?_
    intro r₀
    ext m₀
    obtain ⟨U, ⟨r, m⟩, h⟩ := Types.jointly_surjective_of_isColimit
      ((isColimitOfPreserves (forget RingCat) hcR).tensor
        (isColimitOfPreserves (forget Ab) hcM)) ⟨r₀, m₀⟩
    dsimp only [Functor.const_obj_obj] at h
    simp only [Cocone.tensor_ι_app] at h
    have hr := congrArg Prod.fst h
    have hm := congrArg Prod.snd h
    change _ = r₀ at hr
    change _ = m₀ at hm
    have hR :
        ((ConcreteCategory.hom
            (MonoidalCategoryStruct.tensorHom (((forget RingCat).mapCocone cR).ι.app U)
              (((forget Ab).mapCocone cM).ι.app U))) (r, m)).1 =
          (ConcreteCategory.hom (((forget RingCat).mapCocone cR).ι.app U)) r := by
      rfl
    have hM :
        ((ConcreteCategory.hom
            (MonoidalCategoryStruct.tensorHom (((forget RingCat).mapCocone cR).ι.app U)
              (((forget Ab).mapCocone cM).ι.app U))) (r, m)).2 =
          (ConcreteCategory.hom (((forget Ab).mapCocone cM).ι.app U)) m := by
      rfl
    rw [← hr, ← hm]
    let r' : R.obj U := r
    let m' : M.obj U := m
    convert (Limits.IsColimit.ι_smul R M.presheaf
      (fun f r m => M.map_smul f r m) hcR hcM U r' m').symm using 1
    · rfl
    · rfl
    · simpa only [hR, hM, Iso.refl_hom, Category.id_comp, Category.comp_id]
  exact True.intro

end
end Formalization.Books.Sheaves.Unit14
