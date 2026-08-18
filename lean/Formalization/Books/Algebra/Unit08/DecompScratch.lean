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
      naturality := by sorry })
  exact { pt := O, ι := ι }

def decompIsColimit {J : Type v} [Category.{v'} J]
    (F : D J ⥤ ModuleCat.{max v v' w} R) :
    IsColimit (decompCocone F) := by sorry

example {J : Type v} [Category.{v'} J]
    (F : J ⥤ ModuleCat.{max v v' w} R) :
    Nonempty (colimit F ≅ (decompCocone ((decomposedEquiv (J := J)).functor ⋙ F)).pt) := by
  sorry

end

end DecompScratch
