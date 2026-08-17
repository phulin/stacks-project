import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

namespace FilteredScratch

open CategoryTheory
open CategoryTheory.Limits

universe u v v' w

noncomputable section

variable {R : Type u} [CommRing R]

def firstMap {J : Type v} [Category.{v'} J]
    (S : J ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    (S ⋙ ShortComplex.π₁) ⟶ (S ⋙ ShortComplex.π₂) where
  app i := (S.obj i).f
  naturality _ _ f := (S.map f).comm₁₂

def secondMap {J : Type v} [Category.{v'} J]
    (S : J ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    (S ⋙ ShortComplex.π₂) ⟶ (S ⋙ ShortComplex.π₃) where
  app i := (S.obj i).g
  naturality _ _ f := (S.map f).comm₂₃

def colimShort {J : Type v} [Category.{v'} J]
    (S : J ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    ShortComplex (ModuleCat.{max v v' w} R) :=
  ShortComplex.mk (colim.map (firstMap S)) (colim.map (secondMap S)) (by
    apply colimit.hom_ext
    intro i
    rw [← Category.assoc, colimit.ι_map, Category.assoc, colimit.ι_map]
    have hi : (firstMap S).app i ≫ (secondMap S).app i = 0 := by
      change (S.obj i).f ≫ (S.obj i).g = 0
      exact (S.obj i).zero
    rw [← Category.assoc, hi, zero_comp, comp_zero])

def homologySystem {J : Type v} [Category.{v'} J]
    (S : J ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    J ⥤ ModuleCat.{max v v' w} R :=
  S ⋙ ShortComplex.homologyFunctor (ModuleCat.{max v v' w} R)

example {J : Type v} [Category.{v'} J] [IsFiltered J]
    (S : J ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    Nonempty ((colimShort S).homology ≅ colimit (homologySystem S)) := by
  letI : AB5OfSize.{v', v} (AddCommGrpCat.{max v v' w}) :=
    AB5OfSize_of_univLE (AddCommGrpCat.{max v v' w})
  letI : HasExactColimitsOfShape J (ModuleCat.{max v v' w} R) :=
    HasExactColimitsOfShape.domain_of_functor J
      (forget₂ (ModuleCat.{max v v' w} R) AddCommGrpCat)
  have hF : (colim : (J ⥤ ModuleCat.{max v v' w} R) ⥤
      ModuleCat.{max v v' w} R).PreservesHomology := by infer_instance
  let T := ShortComplex.FunctorEquivalence.inverse J
    (ModuleCat.{max v v' w} R)
  let ST := T.obj S
  have hfirst : S.whiskerLeft ShortComplex.π₁Toπ₂ = firstMap S := by
    apply NatTrans.ext
    funext i
    rfl
  have hsecond : S.whiskerLeft ShortComplex.π₂Toπ₃ = secondMap S := by
    apply NatTrans.ext
    funext i
    rfl
  have hff : colim.map ST.f = colim.map (firstMap S) := by
    simpa [T, ST, ShortComplex.FunctorEquivalence.inverse] using
      congrArg (fun q => colim.map q) hfirst
  have hgg : colim.map ST.g = colim.map (secondMap S) := by
    simpa [T, ST, ShortComplex.FunctorEquivalence.inverse] using
      congrArg (fun q => colim.map q) hsecond
  let q : ST.map colim ≅ colimShort S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
        exact hff.symm)
      (by
        simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
        exact hgg.symm)
  let E := ShortComplex.FunctorEquivalence.functor J
    (ModuleCat.{max v v' w} R)
  let HST := E.obj ST ⋙ ShortComplex.homologyFunctor (ModuleCat.{max v v' w} R)
  let p₀ : ST.homology ≅ HST :=
    NatIso.ofComponents (fun i => by
      simpa [HST, E, T, ST, ShortComplex.FunctorEquivalence.functor,
        ShortComplex.FunctorEquivalence.inverse] using
        (ST.mapHomologyIso ((evaluation J (ModuleCat.{max v v' w} R)).obj i)).symm) (by
      intro i j h
      let eᵢ := ST.mapHomologyIso ((evaluation J (ModuleCat.{max v v' w} R)).obj i)
      let eⱼ := ST.mapHomologyIso ((evaluation J (ModuleCat.{max v v' w} R)).obj j)
      change ST.homology.map h ≫ eⱼ.inv =
        eᵢ.inv ≫ ShortComplex.homologyMap (ST.mapNatTrans
          ((evaluation J (ModuleCat.{max v v' w} R)).map h))
      rw [ShortComplex.homologyMap_mapNatTrans]
      change ST.homology.map h ≫ eⱼ.inv =
        eᵢ.inv ≫ eᵢ.hom ≫
          ((evaluation J (ModuleCat.{max v v' w} R)).map h).app ST.homology ≫ eⱼ.inv
      simp)
  let p : ST.homology ≅ homologySystem S :=
    p₀ ≪≫ Functor.isoWhiskerRight
      ((ShortComplex.FunctorEquivalence.counitIso J
        (ModuleCat.{max v v' w} R)).app S)
      (ShortComplex.homologyFunctor (ModuleCat.{max v v' w} R))
  refine ⟨((ShortComplex.homologyFunctor (ModuleCat.{max v v' w} R)).mapIso q).symm ≪≫
    ST.mapHomologyIso colim ≪≫ colim.mapIso p⟩

end

end FilteredScratch
