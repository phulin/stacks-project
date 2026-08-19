import Formalization.Books.MoreAlgebra.Unit75.RecognizingPerfectComplexes
import Formalization.Books.Derived.Unit33.DerivedColimits
import Formalization.Books.Derived.Unit37.CompactObjects

/-!
# More on Algebra, Chapter 75: characterizing perfect complexes

The compactness statements use the derived-category coproduct comparison
already exposed by Chapter 37.  Quotient and nilpotent descent retain the
actual ring maps from the source rather than introducing parallel tensor
constructions.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit33
open Formalization.Books.Derived.Unit36
open Formalization.Books.Derived.Unit37
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit75
open scoped CategoryTheory.Preadditive CategoryTheory.Pretriangulated.Opposite

universe w u

namespace Formalization.Books.MoreAlgebra.Unit75

def PerfectObjects
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] : ObjectProperty (D R) :=
  fun K => Perfect R K

def IsClassicalGeneratorForPerfect
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (G : D R) : Prop :=
  Perfect R G ∧ ∀ K : D R, Perfect R K →
    generatedSubcategory G K

def PreservesCountableCoproductHom
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] [HasCoproducts (D R)] (K : D R) : Prop :=
  ∀ (E : ℕ → D R),
    IsIso (sigmaComparison (preadditiveCoyoneda.obj (Opposite.op K)) E)

def componentDiagram
    (R : Type u) [CommRing R] (F : SequentialSystem (Comp R)) (i : ℤ) :
    ℕ ⥤ Mod R where
  obj n := (F.obj n).X i
  map f := (F.map f).f i
  map_id n := by simp
  map_comp f g := by simp

def IsTermwiseColimitComplex
    (R : Type u) [CommRing R] (F : SequentialSystem (Comp R))
    (L : Comp R) : Prop :=
  ∀ i : ℤ, Nonempty (colimit (componentDiagram R F i) ≅ L.X i)

def homDiagram
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (F : SequentialSystem (D R)) : ℕ ⥤ Type w where
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
    [HasDerivedCategory.{w} (Mod R)]
    (K : D R) (F : SequentialSystem (D R)) (L : D R)
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
    [HasDerivedCategory.{w} (Mod R)] :
    (∀ K : D R, Perfect R K ↔
      generatedSubcategory (moduleInDerived R (ModuleCat.of R R)) K) ∧
    IsClassicalGeneratorForPerfect R
      (moduleInDerived R (ModuleCat.of R R)) := by
  sorry

theorem commutes_with_countable_sums
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] [HasCoproducts (D R)] (K : D R)
    (hK : PreservesCountableCoproductHom R K)
    (F : SequentialSystem (Comp R)) (L : Comp R)
    (hL : IsTermwiseColimitComplex R F L)
    (ι : ∀ n : ℕ, (derivedQuotient R).obj (F.obj n) ⟶
      (derivedQuotient R).obj L)
    (hι : ∀ {n m : ℕ} (f : n ⟶ m),
      (F ⋙ derivedQuotient R).map f ≫ ι m = ι n) :
    SequentialHomColimitComparison R K (F ⋙ derivedQuotient R)
      ((derivedQuotient R).obj L) ι hι := by
  sorry

theorem perfect_is_compact
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] [HasCoproducts (D R)] (K : D R) :
    Perfect R K ↔ IsCompactObject K := by
  sorry

theorem perfect_modulo_nilpotent_ideal
    (R : Type u) [CommRing R] (I : Ideal R)
    [HasDerivedCategory.{w} (Mod R)]
    (hquotDC : HasDerivedCategory.{w} (Mod (R ⧸ I)))
    (K : D R)
    (hK : Perfect (R ⧸ I)
      ((derivedBaseChange (Ideal.Quotient.mk I)).obj K))
    (hI : ∃ n : ℕ, I ^ n = ⊥) :
    Perfect R K := by
  sorry

theorem perfect_modulo_two_ideals
    (R : Type u) [CommRing R] (I J : Ideal R)
    [HasDerivedCategory.{w} (Mod R)]
    (hIJDC : HasDerivedCategory.{w} (Mod (R ⧸ (I * J))))
    (hIDC : HasDerivedCategory.{w} (Mod (R ⧸ I)))
    (hJDC : HasDerivedCategory.{w} (Mod (R ⧸ J)))
    (K : D R)
    (hI : Perfect (R ⧸ I)
      ((derivedBaseChange (Ideal.Quotient.mk I)).obj K))
    (hJ : Perfect (R ⧸ J)
      ((derivedBaseChange (Ideal.Quotient.mk J)).obj K)) :
    Perfect (R ⧸ (I * J))
      ((derivedBaseChange (Ideal.Quotient.mk (I * J))).obj K) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit75
