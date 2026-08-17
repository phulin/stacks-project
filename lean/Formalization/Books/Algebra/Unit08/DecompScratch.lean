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

def decompCocone {J : Type v} [Category.{v'} J]
    (F : D J ⥤ ModuleCat.{max v v' w} R) :
    Cocone F := by
  let G : ConnectedComponents J → ModuleCat.{max v v' w} R := componentColim F
  let O := colimit (Discrete.functor G)
  let ι : F ⟶ (Functor.const (D J)).obj O :=
    Sigma.natTrans (fun j => {
      app := fun x => colimit.ι (inclusion j ⋙ F) x ≫
        colimit.ι (Discrete.functor G) (Discrete.mk j)
      naturality := by
        intro X Y f
        change F.map (Sigma.SigmaHom.mk f) ≫
            (colimit.ι (inclusion j ⋙ F) Y ≫
              colimit.ι (Discrete.functor G) (Discrete.mk j)) =
          (colimit.ι (inclusion j ⋙ F) X ≫
            colimit.ι (Discrete.functor G) (Discrete.mk j)) ≫ 𝟙 _
        simp only [Functor.comp_map, Category.assoc, colimit.w, Category.comp_id] })
  exact { pt := O, ι := ι }

def decompIsColimit {J : Type v} [Category.{v'} J]
    (F : D J ⥤ ModuleCat.{max v v' w} R) :
    IsColimit (decompCocone F) := by
  let G : ConnectedComponents J → ModuleCat.{max v v' w} R := componentColim F
  let O := colimit (Discrete.functor G)
  refine { desc := ?_, fac := ?_, uniq := ?_ }
  · intro s
    exact Sigma.desc (fun j =>
        colimit.desc (inclusion j ⋙ F) {
          pt := s.pt,
          ι := { app := fun x => s.ι.app ⟨j, x⟩,
            naturality := fun X Y f => s.ι.naturality (Sigma.SigmaHom.mk f) } })
  · rintro ⟨j, X⟩
    change (colimit.ι (inclusion j ⋙ F) X ≫
      colimit.ι (Discrete.functor G) (Discrete.mk j)) ≫
      Sigma.desc (fun j => colimit.desc (inclusion j ⋙ F) {
        pt := s.pt,
        ι := { app := fun x => s.ι.app ⟨j, x⟩,
          naturality := fun X Y f => s.ι.naturality (Sigma.SigmaHom.mk f) } }) =
      s.ι.app ⟨j, X⟩
    rw [Category.assoc, Sigma.ι_desc, colimit.ι_desc]
  · intro s m hm
    apply Sigma.hom_ext
    intro j
    apply colimit.hom_ext
    intro X
    have h := congrArg (fun q =>
      (colimit.ι (Discrete.functor G) (Discrete.mk j)) ≫ q)
      (hm ⟨j, X⟩)
    exact h

example {J : Type v} [Category.{v'} J]
    (F : J ⥤ ModuleCat.{max v v' w} R) :
    Nonempty (colimit F ≅ (decompCocone ((decomposedEquiv (J := J)).functor ⋙ F)).pt) := by
  let e := (decomposedEquiv (J := J)).functor
  let c := decompCocone (e ⋙ F)
  let hc := decompIsColimit (e ⋙ F)
  exact ⟨(Functor.Final.colimitIso e F).symm ≪≫
    (colimit.isColimit (e ⋙ F)).coconePointUniqueUpToIso (by
      exact (Functor.Final.isColimitWhiskerEquiv e F).symm hc)⟩

end

end DecompScratch
