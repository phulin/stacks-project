import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets

namespace ExactScratch

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21

universe u v w

noncomputable section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I]

def firstMap (S : I ⥤ ShortComplex (ModuleCat.{max v w} R)) :
    (S ⋙ ShortComplex.π₁) ⟶ (S ⋙ ShortComplex.π₂) where
  app i := (S.obj i).f
  naturality _ _ f := (S.map f).comm₁₂

def secondMap (S : I ⥤ ShortComplex (ModuleCat.{max v w} R)) :
    (S ⋙ ShortComplex.π₂) ⟶ (S ⋙ ShortComplex.π₃) where
  app i := (S.obj i).g
  naturality _ _ f := (S.map f).comm₂₃

def colimShort (S : I ⥤ ShortComplex (ModuleCat.{max v w} R)) :
    ShortComplex (ModuleCat.{max v w} R) :=
  ShortComplex.mk (colim.map (firstMap S)) (colim.map (secondMap S)) (by
    apply colimit.hom_ext
    intro i
    rw [← Category.assoc, colimit.ι_map, Category.assoc, colimit.ι_map]
    have hi : (firstMap S).app i ≫ (secondMap S).app i = 0 := by
      change (S.obj i).f ≫ (S.obj i).g = 0
      exact (S.obj i).zero
    rw [← Category.assoc, hi, zero_comp, comp_zero])

def homologySystem (S : I ⥤ ShortComplex (ModuleCat.{max v w} R)) :
    I ⥤ ModuleCat.{max v w} R :=
  S ⋙ ShortComplex.homologyFunctor (ModuleCat.{max v w} R)

example (S : I ⥤ ShortComplex (ModuleCat.{max v w} R)) (hI : IsDirectedSet I)
    (hS : ∀ i : I, (S.obj i).Exact) : (colimShort S).Exact := by
  letI : IsDirectedOrder I := hI.2
  letI : Nonempty I := hI.1
  letI : IsFiltered I := inferInstance
  letI : AB5OfSize.{v, v} (AddCommGrpCat.{max v w}) :=
    AB5OfSize_of_univLE (AddCommGrpCat.{max v w})
  letI : HasExactColimitsOfShape I (ModuleCat.{max v w} R) :=
    HasExactColimitsOfShape.domain_of_functor I
      (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat)
  have hF : (colim : (I ⥤ ModuleCat.{max v w} R) ⥤
      ModuleCat.{max v w} R).PreservesHomology := by infer_instance
  let T := ShortComplex.FunctorEquivalence.inverse I (ModuleCat.{max v w} R)
  let ST := T.obj S
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
          ((evaluation I (ModuleCat.{max v w} R)).obj i)).app ST
        apply IsZero.of_iso ((ST.map ((evaluation I (ModuleCat.{max v w} R)).obj i)).exact_iff_isZero_homology.1
          (hS i)) e.symm
      exact hi.eq_of_src (q.app i) ((0 : ST.homology ⟶ X).app i)
    · intro X
      refine ⟨⟨⟨0⟩, ?_⟩⟩
      intro q
      apply NatTrans.ext
      funext i
      change q.app i = ((0 : X ⟶ ST.homology).app i)
      have hi : IsZero (ST.homology.obj i) := by
        let e := (ShortComplex.homologyFunctorIso
          ((evaluation I (ModuleCat.{max v w} R)).obj i)).app ST
        apply IsZero.of_iso ((ST.map ((evaluation I (ModuleCat.{max v w} R)).obj i)).exact_iff_isZero_homology.1
          (hS i)) e.symm
      exact hi.eq_of_tgt (q.app i) ((0 : X ⟶ ST.homology).app i)
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

end ExactScratch
