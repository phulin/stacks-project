import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Formalization.Books.Algebra.Unit153
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 154: Filtered colimits of étale ring maps

This file formalizes the definitions and theorem interfaces in the source
section `Filtered colimits of étale ring maps`.  Filtered colimits are
represented by a filtered diagram in `Under (CommRingCat.of R)`, a cocone,
its colimit proof, and an identification of the colimit object with the
specified target algebra.
-/

namespace Formalization.Books.Algebra.Unit154

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit127
open Formalization.Books.Algebra.Unit153
open scoped TensorProduct

universe u v

noncomputable section

/-! ## Filtered colimits of étale algebras -/

/-- The data that a ring map is a filtered colimit of `R`-algebras. -/
structure FilteredColimitData {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) where
  index : Type u
  [indexCategory : Category.{u} index]
  [indexFiltered : IsFiltered index]
  diagram : index ⥤ Under (CommRingCat.of R)
  cocone : Cocone diagram
  isColimit : IsColimit cocone
  targetIso : cocone.pt ≅ underRingHom f

/-- The source's phrase “filtered colimit of étale `R`-algebras”. -/
structure FilteredEtaleColimit {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) extends FilteredColimitData f where
  etale : ∀ i, RingHom.Etale (diagram.obj i).hom.hom

/-- A ring map is a filtered colimit of étale algebras. -/
def IsFilteredColimitOfEtale {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : Prop :=
  Nonempty (FilteredEtaleColimit f)

/-! ## Lemma `base-change-colimit-etale` -/

/-- Filtered colimits of étale algebras are preserved by base change. -/
theorem base_change_colimit_etale
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    (hA : IsFilteredColimitOfEtale (algebraMap R A)) :
    IsFilteredColimitOfEtale
      (Algebra.TensorProduct.includeLeftRingHom :
        R' →+* R' ⊗[R] A) := by
  sorry

/-! ## Lemma `composition-colimit-etale` -/

/-- A composition of two filtered colimits of étale algebras is again one. -/
theorem composition_colimit_etale
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hB : IsFilteredColimitOfEtale f)
    (hC : IsFilteredColimitOfEtale g) :
    IsFilteredColimitOfEtale (g.comp f) := by
  sorry

/-! ## Lemma `colimit-colimit-etale` -/

/-- An outer filtered colimit whose stages are themselves filtered colimits of
étale algebras is a filtered colimit of étale algebras. -/
structure FilteredEtaleStagesColimit {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) extends FilteredColimitData f where
  stage : ∀ i, IsFilteredColimitOfEtale (diagram.obj i).hom.hom

theorem colimit_colimit_etale
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A)
    (h : Nonempty (FilteredEtaleStagesColimit f)) :
    IsFilteredColimitOfEtale f := by
  sorry

/-! ## Lemma `colimit-colimit-etale-better` -/

/-- A filtered system of ring maps with étale-colimit stages has an
étale-colimit map after taking colimits in source and target. -/
structure FilteredEtaleRingMapSystem (I : Type u) [Category.{u} I]
    [IsFiltered I] where
  baseDiagram : I ⥤ CommRingCat.{u}
  targetDiagram : I ⥤ CommRingCat.{u}
  map : baseDiagram ⟶ targetDiagram
  baseCocone : Cocone baseDiagram
  targetCocone : Cocone targetDiagram
  baseIsColimit : IsColimit baseCocone
  targetIsColimit : IsColimit targetCocone
  colimitMap : baseCocone.pt ⟶ targetCocone.pt
  colimitMap_comm : ∀ i,
    map.app i ≫ targetCocone.ι.app i = baseCocone.ι.app i ≫ colimitMap
  stage : ∀ i, IsFilteredColimitOfEtale (map.app i).hom

theorem colimit_colimit_etale_better
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (D : FilteredEtaleRingMapSystem I) :
    IsFilteredColimitOfEtale D.colimitMap.hom := by
  sorry

/-! ## Lemma `colimits-of-etale` -/

/-- If two `R`-algebras are filtered colimits of étale `R`-algebras, the
second is a filtered colimit of étale algebras over the first. -/
theorem colimits_of_etale
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (f : A →+* B)
    (hf : f.comp (algebraMap R A) = algebraMap R B)
    (hA : IsFilteredColimitOfEtale (algebraMap R A))
    (hB : IsFilteredColimitOfEtale (algebraMap R B)) :
    IsFilteredColimitOfEtale f := by
  sorry

/-! ## Lemma `map-into-henselian-colimit` -/

/-- The source's map-into-henselian-colimit assertion, using the residue-field
compatibility data already introduced in Chapter 153. -/
theorem map_into_henselian_colimit
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [HenselianLocalRing S]
    (hA : IsFilteredColimitOfEtale (algebraMap R A))
    (q : PrimeSpectrum A)
    (hq : q.asIdeal.comap (algebraMap R A) =
      (IsLocalRing.maximalIdeal S).comap (algebraMap R S))
    (τ : ResidueFieldMapData q hq) :
    ∃! f : A →ₐ[R] S,
      PrimeSpectrum.comap f.toRingHom (maximalPrime S) = q ∧
        ∀ a : A,
          τ.map (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField
            (Ideal.Quotient.mk q.asIdeal a)) =
            IsLocalRing.residue S (f a) := by
  sorry

/-! ## Lemma `uniqueness-henselian` -/

/-- Two henselian filtered étale-colimit `R`-algebras with the same residue
field are uniquely isomorphic over `R`. -/
theorem uniqueness_henselian
    {R S S' K : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Field K] [Algebra R S] [Algebra R S']
    [HenselianLocalRing S] [HenselianLocalRing S']
    (hS : IsFilteredColimitOfEtale (algebraMap R S))
    (hS' : IsFilteredColimitOfEtale (algebraMap R S'))
    (s : S →+* K) (s' : S' →+* K)
    (hcomm : s.comp (algebraMap R S) = s'.comp (algebraMap R S'))
    (hker : RingHom.ker s = IsLocalRing.maximalIdeal S)
    (hker' : RingHom.ker s' = IsLocalRing.maximalIdeal S')
    (hsurj : Function.Surjective s)
    (hsurj' : Function.Surjective s') :
    ∃! e : S ≃ₐ[R] S',
      s'.comp e.toRingEquiv.toRingHom = s := by
  sorry

/-! ## Lemma `colimit-henselian` -/

/-- The data of a filtered colimit of commutative rings along local maps. -/
structure FilteredLocalRingColimitData (I : Type u) [Category.{u} I]
    [IsFiltered I] (A : Type u) [CommRing A] where
  diagram : I ⥤ CommRingCat.{u}
  cocone : Cocone diagram
  isColimit : IsColimit cocone
  targetIso : cocone.pt ≅ CommRingCat.of A
  localHom : ∀ {i j : I} (f : i ⟶ j), IsLocalHom (diagram.map f).hom

/-- A filtered colimit of henselian local rings along local maps is
henselian. -/
theorem colimit_henselian
    {I A : Type u} [Category.{u} I] [IsFiltered I] [CommRing A]
    (D : FilteredLocalRingColimitData I A)
    (hH : ∀ i, HenselianLocalRing (D.diagram.obj i)) :
    HenselianLocalRing A := by
  sorry

/-- A filtered colimit of strictly henselian local rings along local maps is
strictly henselian. -/
theorem colimit_strictly_henselian
    {I A : Type u} [Category.{u} I] [IsFiltered I] [CommRing A]
    (D : FilteredLocalRingColimitData I A)
    (hH : ∀ i, StrictlyHenselianLocalRing (D.diagram.obj i)) :
    StrictlyHenselianLocalRing A := by
  sorry

end

end Formalization.Books.Algebra.Unit154
