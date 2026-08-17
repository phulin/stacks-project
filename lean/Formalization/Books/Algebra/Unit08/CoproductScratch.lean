import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

namespace CoproductScratch

open CategoryTheory
open CategoryTheory.Limits

universe u v w

noncomputable section

variable {R : Type u} [CommRing R]

def firstMap {J : Type v} (S : J → ShortComplex (ModuleCat.{max v w} R)) :
    (Discrete.functor S ⋙ ShortComplex.π₁) ⟶
      (Discrete.functor S ⋙ ShortComplex.π₂) :=
  Discrete.natTrans (fun i => (S i.as).f)

def secondMap {J : Type v} (S : J → ShortComplex (ModuleCat.{max v w} R)) :
    (Discrete.functor S ⋙ ShortComplex.π₂) ⟶
      (Discrete.functor S ⋙ ShortComplex.π₃) :=
  Discrete.natTrans (fun i => (S i.as).g)

def colimShort {J : Type v} (S : J → ShortComplex (ModuleCat.{max v w} R)) :
    ShortComplex (ModuleCat.{max v w} R) :=
  ShortComplex.mk (colim.map (firstMap S)) (colim.map (secondMap S)) (by
    apply colimit.hom_ext
    intro i
    rw [← Category.assoc, colimit.ι_map, Category.assoc, colimit.ι_map]
    have hi : (firstMap S).app i ≫ (secondMap S).app i = 0 := by
      change (S i.as).f ≫ (S i.as).g = 0
      exact (S i.as).zero
    rw [← Category.assoc, hi, zero_comp, comp_zero])

def homologySystem {J : Type v} (S : J → ShortComplex (ModuleCat.{max v w} R)) :
    Discrete J ⥤ ModuleCat.{max v w} R :=
  Discrete.functor S ⋙ ShortComplex.homologyFunctor (ModuleCat.{max v w} R)

example {J : Type v} (S : J → ShortComplex (ModuleCat.{max v w} R)) :
    Nonempty ((colimShort S).homology ≅ colimit (homologySystem S)) := by
  letI : AB5OfSize.{v, v} (AddCommGrpCat.{max v w}) :=
    AB5OfSize_of_univLE (AddCommGrpCat.{max v w})
  letI : AB4OfSize.{max v w} (AddCommGrpCat.{max v w}) :=
    AB4.of_AB5 (AddCommGrpCat.{max v w})
  letI : AB4OfSize.{v} (AddCommGrpCat.{max v w}) :=
    AB4OfSize_shrink (AddCommGrpCat.{max v w})
  letI : HasExactColimitsOfShape (Discrete J) (ModuleCat.{max v w} R) :=
    HasExactColimitsOfShape.domain_of_functor (Discrete J)
      (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat)
  have hF : (colim : (Discrete J ⥤ ModuleCat.{max v w} R) ⥤
      ModuleCat.{max v w} R).PreservesHomology := by infer_instance
  let SD := Discrete.functor S
  let T := ShortComplex.FunctorEquivalence.inverse (Discrete J)
    (ModuleCat.{max v w} R)
  let ST := T.obj SD
  have hfirst : SD.whiskerLeft ShortComplex.π₁Toπ₂ = firstMap S := by
    apply NatTrans.ext
    funext i
    rfl
  have hsecond : SD.whiskerLeft ShortComplex.π₂Toπ₃ = secondMap S := by
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
  let E := ShortComplex.FunctorEquivalence.functor (Discrete J)
    (ModuleCat.{max v w} R)
  let HST := E.obj ST ⋙ ShortComplex.homologyFunctor (ModuleCat.{max v w} R)
  let p₀ : ST.homology ≅ HST :=
    NatIso.ofComponents (fun i => by
      simpa [HST, E, T, ST, ShortComplex.FunctorEquivalence.functor,
        ShortComplex.FunctorEquivalence.inverse] using
        (ST.mapHomologyIso ((evaluation (Discrete J) (ModuleCat.{max v w} R)).obj i)).symm) (by
      intro i j h
      let eᵢ := ST.mapHomologyIso ((evaluation (Discrete J) (ModuleCat.{max v w} R)).obj i)
      let eⱼ := ST.mapHomologyIso ((evaluation (Discrete J) (ModuleCat.{max v w} R)).obj j)
      change ST.homology.map h ≫ eⱼ.inv =
        eᵢ.inv ≫ ShortComplex.homologyMap (ST.mapNatTrans
          ((evaluation (Discrete J) (ModuleCat.{max v w} R)).map h))
      rw [ShortComplex.homologyMap_mapNatTrans]
      change ST.homology.map h ≫ eⱼ.inv =
        eᵢ.inv ≫ eᵢ.hom ≫
          ((evaluation (Discrete J) (ModuleCat.{max v w} R)).map h).app ST.homology ≫ eⱼ.inv
      simp)
  let p : ST.homology ≅ homologySystem S :=
    p₀ ≪≫ Functor.isoWhiskerRight
      ((ShortComplex.FunctorEquivalence.counitIso (Discrete J)
        (ModuleCat.{max v w} R)).app SD)
      (ShortComplex.homologyFunctor (ModuleCat.{max v w} R))
  refine ⟨((ShortComplex.homologyFunctor (ModuleCat.{max v w} R)).mapIso q).symm ≪≫
    ST.mapHomologyIso colim ≪≫ colim.mapIso p⟩

end

end CoproductScratch
