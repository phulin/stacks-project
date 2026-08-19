import Formalization.Books.MoreAlgebra.Unit75.PerfectComplexes
import Formalization.Books.Derived.Unit33.DerivedColimits
import Formalization.Books.Derived.Unit37.CompactObjects

/-!
# More on Algebra, Chapter 79: characterizing perfect complexes

This file records the source-facing interfaces for the characterization of
perfect complexes by generation, compactness, and quotient descent.  The
perfect predicate, derived colimits, compactness, and quotient base-change
functors are reused from the preceding chapters.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit33
open Formalization.Books.Derived.Unit36
open Formalization.Books.Derived.Unit37
open Formalization.Books.MoreAlgebra.Unit75
open scoped CategoryTheory.Preadditive CategoryTheory.Pretriangulated.Opposite

universe w u

namespace Formalization.Books.MoreAlgebra.Unit79

/-! ## The perfect subcategory and countable colimits -/

def PerfectObjects
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Unit75.Mod R)] : ObjectProperty (Unit75.D R) :=
  fun K => Perfect R K

def IsClassicalGeneratorForPerfect
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Unit75.Mod R)] (G : Unit75.D R) : Prop :=
  Perfect R G ∧ ∀ K : Unit75.D R, Perfect R K → generatedSubcategory G K

def componentDiagram
    (R : Type u) [CommRing R]
    (F : SequentialSystem (Unit75.Comp R)) (i : ℤ) :
    ℕ ⥤ Unit75.Mod R where
  obj n := (F.obj n).X i
  map f := (F.map f).f i
  map_id n := by simp
  map_comp f g := by simp

def IsTermwiseColimitComplex
    (R : Type u) [CommRing R] (F : SequentialSystem (Unit75.Comp R))
    (L : Unit75.Comp R) : Prop :=
  ∀ i : ℤ, Nonempty (colimit (componentDiagram R F i) ≅ L.X i)

def homDiagram
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Unit75.Mod R)]
    (K : Unit75.D R) (F : SequentialSystem (Unit75.D R)) : ℕ ⥤ Type w where
  obj n := K ⟶ F.obj n
  map f := TypeCat.ofHom (fun h => h ≫ F.map f)
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro h
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro h
    simp [Category.assoc]

def SequentialHomColimitComparison
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Unit75.Mod R)]
    (K : Unit75.D R) (F : SequentialSystem (Unit75.D R)) (L : Unit75.D R)
    (ι : ∀ n : ℕ, F.obj n ⟶ L)
    (hι : ∀ {n m : ℕ} (f : n ⟶ m),
      F.map f ≫ ι m = ι n) : Prop :=
  let c : Cocone (homDiagram R K F) :=
    Cocone.mk (K ⟶ L) {
      app := fun n => TypeCat.ofHom (fun h => h ≫ ι n)
      naturality := by
        intro n m f
        apply ConcreteCategory.hom_ext
        intro h
        change (((h : K ⟶ F.obj n) ≫ F.map f) ≫ ι m) =
          (h : K ⟶ F.obj n) ≫ ι n
        calc
          ((h : K ⟶ F.obj n) ≫ F.map f) ≫ ι m =
              (h : K ⟶ F.obj n) ≫ (F.map f ≫ ι m) := Category.assoc _ _ _
          _ = (h : K ⟶ F.obj n) ≫ ι n :=
            congrArg (fun q => (h : K ⟶ F.obj n) ≫ q) (hι f) }
  IsIso (colimit.desc (homDiagram R K F) c)

theorem perfect_ring_classical_generator
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Unit75.Mod R)] :
    (PerfectObjects R =
      generatedSubcategory (moduleInDerived R (ModuleCat.of R R))) ∧
    IsClassicalGeneratorForPerfect R
      (moduleInDerived R (ModuleCat.of R R)) := by
  sorry

theorem commutes_with_countable_sums
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Unit75.Mod R)]
    [HasCoproducts (Unit75.D R)] (K : Unit75.D R)
    (hK : IsCountablyCompact K)
    (F : SequentialSystem (Unit75.Comp R)) (L : Unit75.Comp R)
    (hL : IsTermwiseColimitComplex R F L)
    (ι : ∀ n : ℕ, (derivedQuotient R).obj (F.obj n) ⟶
      (derivedQuotient R).obj L)
    (hι : ∀ {n m : ℕ} (f : n ⟶ m),
      (F ⋙ derivedQuotient R).map f ≫ ι m = ι n) :
    SequentialHomColimitComparison R K (F ⋙ derivedQuotient R)
      ((derivedQuotient R).obj L) ι hι := by
  sorry

/-! ## Compactness -/

theorem perfect_is_compact
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Unit75.Mod R)]
    [HasCoproducts (Unit75.D R)] (K : Unit75.D R) :
    Perfect R K ↔ IsCompactObject K := by
  sorry

/-! ## Quotient descent -/

theorem perfect_modulo_nilpotent_ideal
    (R : Type u) [CommRing R] (I : Ideal R)
    [HasDerivedCategory.{w} (Unit75.Mod R)]
    [HasDerivedCategory.{w} (Unit75.Mod (R ⧸ I))]
    (K : Unit75.D R)
    (hK : Perfect (R ⧸ I)
      ((derivedBaseChange (Ideal.Quotient.mk I)).obj K))
    (hI : ∃ n : ℕ, I ^ n = ⊥) :
    Perfect R K := by
  sorry

theorem perfect_modulo_two_ideals
    (R : Type u) [CommRing R] (I J : Ideal R)
    [HasDerivedCategory.{w} (Unit75.Mod R)]
    [HasDerivedCategory.{w} (Unit75.Mod (R ⧸ (I * J)))]
    [HasDerivedCategory.{w} (Unit75.Mod (R ⧸ I))]
    [HasDerivedCategory.{w} (Unit75.Mod (R ⧸ J))]
    (K : Unit75.D R)
    (hI : Perfect (R ⧸ I)
      ((derivedBaseChange (Ideal.Quotient.mk I)).obj K))
    (hJ : Perfect (R ⧸ J)
      ((derivedBaseChange (Ideal.Quotient.mk J)).obj K)) :
    Perfect (R ⧸ (I * J))
      ((derivedBaseChange (Ideal.Quotient.mk (I * J))).obj K) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit79
