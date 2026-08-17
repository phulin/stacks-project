import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

namespace DirectSumScratch

open CategoryTheory
open CategoryTheory.Limits

universe u v w

noncomputable section

def firstMap {R : Type u} [CommRing R] {J : Type v}
    (S : J → ShortComplex (ModuleCat.{max v w} R)) :
    (Discrete.functor S ⋙ ShortComplex.π₁) ⟶
      (Discrete.functor S ⋙ ShortComplex.π₂) :=
  Discrete.natTrans (fun i => (S i.as).f)

def secondMap {R : Type u} [CommRing R] {J : Type v}
    (S : J → ShortComplex (ModuleCat.{max v w} R)) :
    (Discrete.functor S ⋙ ShortComplex.π₂) ⟶
      (Discrete.functor S ⋙ ShortComplex.π₃) :=
  Discrete.natTrans (fun i => (S i.as).g)

def colimShort {R : Type u} [CommRing R] {J : Type v}
    (S : J → ShortComplex (ModuleCat.{max v w} R)) :
    ShortComplex (ModuleCat.{max v w} R) :=
  ShortComplex.mk (colim.map (firstMap S)) (colim.map (secondMap S)) (by
    apply colimit.hom_ext
    intro i
    rw [← Category.assoc, colimit.ι_map, Category.assoc, colimit.ι_map]
    have hi : (firstMap S).app i ≫ (secondMap S).app i = 0 := by
      change (S i.as).f ≫ (S i.as).g = 0
      exact (S i.as).zero
    rw [← Category.assoc, hi, zero_comp, comp_zero])

example {R : Type u} [CommRing R] {J : Type v}
    (S : J → ShortComplex (ModuleCat.{max v w} R))
    (hS : ∀ j : J, (S j).Exact) :
    (colimShort S).Exact := by
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
  have hST : ST.Exact := by
    apply (ST.exact_iff_isZero_homology).2
    refine { unique_to := ?_, unique_from := ?_ }
    · intro X
      refine ⟨⟨⟨0⟩, ?_⟩⟩
      intro q
      apply NatTrans.ext
      funext i
      change q.app i = ((0 : ST.homology ⟶ X).app i)
      have hi : IsZero (ST.homology.obj i) := by
        let e := (ShortComplex.homologyFunctorIso
          ((evaluation (Discrete J) (ModuleCat.{max v w} R)).obj i)).app ST
        apply IsZero.of_iso
          ((ST.map ((evaluation (Discrete J) (ModuleCat.{max v w} R)).obj i)).exact_iff_isZero_homology.1
            (hS i.as)) e.symm
      exact hi.eq_of_src (q.app i) ((0 : ST.homology ⟶ X).app i)
    · intro X
      refine ⟨⟨⟨0⟩, ?_⟩⟩
      intro q
      apply NatTrans.ext
      funext i
      change q.app i = ((0 : X ⟶ ST.homology).app i)
      have hi : IsZero (ST.homology.obj i) := by
        let e := (ShortComplex.homologyFunctorIso
          ((evaluation (Discrete J) (ModuleCat.{max v w} R)).obj i)).app ST
        apply IsZero.of_iso
          ((ST.map ((evaluation (Discrete J) (ModuleCat.{max v w} R)).obj i)).exact_iff_isZero_homology.1
            (hS i.as)) e.symm
      exact hi.eq_of_tgt (q.app i) ((0 : X ⟶ ST.homology).app i)
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
  have hcol := colim.exact_mapShortComplex (S := ST) hST
    (c₁ := colimit.cocone ST.X₁)
    (hc₁ := colimit.isColimit ST.X₁)
    (c₂ := colimit.cocone ST.X₂)
    (hc₂ := colimit.isColimit ST.X₂)
    (c₃ := colimit.cocone ST.X₃)
    (hc₃ := colimit.isColimit ST.X₃)
    (f := colim.map ST.f) (g := colim.map ST.g) (hf := by
      intro i
      exact colimit.ι_map ST.f i) (hg := by
      intro i
      exact colimit.ι_map ST.g i)
  change (ShortComplex.mk (colim.map ST.f) (colim.map ST.g) _).Exact at hcol
  apply ShortComplex.exact_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_) hcol
  · simpa [colimShort] using hff.symm
  · simpa [colimShort] using hgg.symm

end

end DirectSumScratch
