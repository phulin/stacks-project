import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.CategoryTheory.Limits.Final

namespace DecompScratch

open CategoryTheory
open CategoryTheory.Limits

universe u v v' w

noncomputable section

variable {R : Type u} [CommRing R]

abbrev D (J : Type v) [Category.{v'} J] := Decomposed J

def componentColim {J : Type v} [Category.{v'} J]
    (F : D J ⥤ ModuleCat.{max v v' w} R) (j : ConnectedComponents J) :
    ModuleCat.{max v v' w} R :=
  colimit (inclusion j ⋙ F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
def decompCocone {J : Type v} [Category.{v'} J]
    (F : D J ⥤ ModuleCat.{max v v' w} R) :
    Cocone F := by
  let G : ConnectedComponents J → ModuleCat.{max v v' w} R := componentColim F
  let O := colimit (Discrete.functor G)
  refine { pt := O, ι := ?_ }
  refine Sigma.natTrans (fun j => ?_)
  refine { app := fun x => colimit.ι (inclusion j ⋙ F) x ≫
      colimit.ι (Discrete.functor G) (Discrete.mk j), naturality := ?_ }
  intro X Y f
  simpa [O, Category.assoc] using congrArg (fun q =>
      q ≫ colimit.ι (Discrete.functor G) (Discrete.mk j))
    (colimit.w (inclusion j ⋙ F) f)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
def decompIsColimit {J : Type v} [Category.{v'} J]
    (F : D J ⥤ ModuleCat.{max v v' w} R) :
    IsColimit (decompCocone F) := by
  let G : ConnectedComponents J → ModuleCat.{max v v' w} R := componentColim F
  let O := colimit (Discrete.functor G)
  let desc (s : Cocone F) : (decompCocone F).pt ⟶ s.pt := by
    let cG : Cocone (Discrete.functor G) :=
      Cocone.mk s.pt (Discrete.natTrans (fun j => by
        let c : Cocone (inclusion j.as ⋙ F) :=
          s.whisker (inclusion j.as)
        exact colimit.desc (inclusion j.as ⋙ F) c))
    exact colimit.desc (Discrete.functor G) cG
  refine { desc := desc, fac := ?_, uniq := ?_ }
  · intro s
    rintro ⟨j, X⟩
    dsimp [decompCocone, desc, G]
    change _ = s.ι.app ((inclusion j).obj X)
    simp [Category.assoc, Discrete.natTrans_app, colimit.ι_desc]
  · intro s m hm
    dsimp [decompCocone] at m hm ⊢
    apply colimit.hom_ext
    rintro ⟨j⟩
    apply colimit.hom_ext
    intro X
    have h := hm ⟨j, X⟩
    dsimp [desc, G]
    simpa [Sigma.natTrans_app, Cocone.whisker_ι, NatTrans.comp_app,
      Discrete.natTrans_app, Category.assoc, colimit.ι_desc] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
example {J : Type v} [Category.{v'} J]
    (F : J ⥤ ModuleCat.{max v v' w} R) :
    Nonempty (colimit F ≅ (decompCocone ((decomposedEquiv (J := J)).functor ⋙ F)).pt) := by
  let e := (decomposedEquiv (J := J)).inverse
  let ef := (decomposedEquiv (J := J)).functor
  let H : ∀ j : ConnectedComponents J,
      j.Component ⥤ ModuleCat.{max v v' w} R :=
    fun j => inclusion j ⋙ ef ⋙ F
  let i₁ : ef ⋙ F ≅ CategoryTheory.Sigma.desc H :=
    Sigma.descUniq H (ef ⋙ F) (fun _ => Iso.refl _)
  let cH : Cocone (CategoryTheory.Sigma.desc H) :=
    (Cocone.precompose i₁.symm.hom).obj (decompCocone (ef ⋙ F))
  let hH : IsColimit cH :=
    (IsColimit.precomposeHomEquiv i₁.symm (decompCocone (ef ⋙ F))).symm
      (decompIsColimit (ef ⋙ F))
  let i₀ : e ⋙ ef ⋙ F ≅ e ⋙ CategoryTheory.Sigma.desc H :=
    Functor.isoWhiskerLeft e i₁
  let i : e ⋙ CategoryTheory.Sigma.desc H ≅ F :=
    i₀.symm ≪≫ Functor.isoWhiskerRight
      (decomposedEquiv (J := J)).counitIso F
  let k := (HasColimit.isoOfNatIso i).symm ≪≫
    Functor.Final.colimitIso e (CategoryTheory.Sigma.desc H) ≪≫
      (colimit.isColimit (CategoryTheory.Sigma.desc H)).coconePointUniqueUpToIso
        hH
  exact ⟨k⟩

end

end DecompScratch
