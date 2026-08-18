import Formalization.Books.Simplicial.Unit27.HomotopiesInAbelianCategories
import Formalization.Books.Simplicial.Unit28.HomotopiesAndCosimplicialObjects
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Simplicial Methods, Chapter 29: More homotopies in abelian categories

This file records the backwards direction of the simplicial/chain-complex
homotopy comparison.  The explicit representing complex is indexed by `ℤ`,
as in the source's category `Ch(𝒜)`; the normalized complexes occurring in
the final theorem retain the earlier chapter's nonnegative indexing.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit29

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Simplicial.Unit23
open Formalization.Books.Simplicial.Unit26
open Opposite

universe v u

/-! ## The representing complex `◇ A` -/

/-- The degree-`n` object of the source's representing complex `◇ A`. -/
def diamondObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (n : ℤ) : C :=
  biprod (biprod (A.X n) (A.X n)) (A.X (n - 1))

/-- The matrix differential from the source, expressed using biproduct maps.
The third summand is the shifted copy of `A`. -/
def diamondBoundary
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (n : ℤ) :
    diamondObject A n ⟶ diamondObject A (n - 1) :=
  biprod.lift
    (biprod.desc
      (biprod.lift
        (biprod.desc
          (A.d n (n - 1))
          0)
        (biprod.desc 0
          (A.d n (n - 1))))
      (biprod.lift (𝟙 _) 0))
    (biprod.desc 0
      ((-A.d (n - 1) (n - 2)) ≫ eqToHom (by congr 1 <;> omega)))

/-- The differential with the zero maps away from the immediate predecessor. -/
def diamondDifferential
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (i j : ℤ) :
    diamondObject A i ⟶ diamondObject A j :=
  if h : j = i - 1 then
    diamondBoundary A i ≫ eqToHom (by subst j; rfl)
  else 0

/-- The chain complex `◇ A` from the source. -/
def diamond
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) : ChainComplex C ℤ where
  X := diamondObject A
  d := diamondDifferential A
  shape := by sorry
  d_comp_d' := by
    intro i j k hij hjk
    sorry

@[simp]
theorem diamond_X
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (n : ℤ) :
    (diamond A).X n = diamondObject A n :=
  rfl

@[simp]
theorem diamond_d_pred
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (n : ℤ) :
    (diamond A).d n (n - 1) = diamondBoundary A n := by
  simp [diamond, diamondDifferential]

def diamondThirdInclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (n : ℤ) :
    A.X (n - 1) ⟶ diamondObject A n := by
  dsimp [diamondObject]
  exact biprod.inr

def diamondThirdInclusionChain
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (n : ℤ) :
    A.X (n - 1) ⟶ (diamond A).X n := by
  change A.X (n - 1) ⟶ diamondObject A n
  exact diamondThirdInclusion A n

/-- The two endpoint maps into `◇ A`. -/
def diamondLeft
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) : A ⟶ diamond A where
  f n := biprod.inl ≫ biprod.inl
  comm' := by
    intro i j hij
    sorry

def diamondRight
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) : A ⟶ diamond A where
  f n := biprod.inl ≫ biprod.snd
  comm' := by
    intro i j hij
    sorry

/-- The canonical chain homotopy between the endpoint maps. -/
def diamondHomotopy
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) :
    _root_.Homotopy (diamondLeft A) (diamondRight A) where
  hom i j :=
    by
      by_cases h : j = i + 1
      · subst j
        change A.X i ⟶ diamondObject A (i + 1)
        exact eqToHom (by simp) ≫ diamondThirdInclusion A (i + 1)
      · exact 0
  zero i j hij := by sorry
  comm := by
    intro i
    sorry

/-! ## Representability and functoriality -/

/-- A triple represented by a map out of `◇ A`. -/
structure ChainHomotopyTriple
    {C : Type u} [Category.{v} C] [Abelian C]
    (A B : ChainComplex C ℤ) where
  a : A ⟶ B
  b : A ⟶ B
  h : _root_.Homotopy a b

def diamondToTriple
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : ChainComplex C ℤ} (f : diamond A ⟶ B) :
    ChainHomotopyTriple A B where
  a := diamondLeft A ≫ f
  b := diamondRight A ≫ f
  h := Homotopy.compRight (diamondHomotopy A) f

def tripleToDiamond
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : ChainComplex C ℤ} (t : ChainHomotopyTriple A B) :
    diamond A ⟶ B where
  f n :=
    biprod.desc
      (biprod.desc (t.a.f n) (t.b.f n))
      (t.h.hom (n - 1) n)
  comm' := by
    intro i j hij
    sorry

/-- The universal property of `◇ A`: maps out of it are exactly homotopy
triples `(a,b,h)`. -/
theorem diamond_represents_homotopy
    {C : Type u} [Category.{v} C] [Abelian C]
    (A B : ChainComplex C ℤ) :
    Nonempty ((diamond A ⟶ B) ≃ ChainHomotopyTriple A B) := by
  sorry

/-- The map on representing complexes induced by a chain map. -/
def diamondMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : ChainComplex C ℤ} (f : A ⟶ B) : diamond A ⟶ diamond B where
  f n := biprod.lift
    (biprod.desc
      (biprod.lift
        ((biprod.fst : biprod (A.X n) (A.X n) ⟶ A.X n) ≫ f.f n)
        ((biprod.snd : biprod (A.X n) (A.X n) ⟶ A.X n) ≫ f.f n))
      0)
    (biprod.desc 0 (f.f (n - 1)))
  comm' := by
    intro i j hij
    sorry

/-- The construction `A ↦ ◇ A` is functorial. -/
def diamondFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    ChainComplex C ℤ ⥤ ChainComplex C ℤ where
  obj A := diamond A
  map f := diamondMap f
  map_id := by
    intro A
    ext n
    sorry
  map_comp := by
    intro A B D f g
    ext n
    sorry
/-! ## The split extension and its connecting morphism -/

/-- The copy `A[-1]` used in the short exact sequence. -/
def diamondShift
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) : ChainComplex C ℤ where
  X n := A.X (n - 1)
  d i j := if h : j = i - 1 then
      (-A.d (i - 1) (i - 2)) ≫ eqToHom (by subst j; congr 1 <;> omega)
    else 0
  shape := by sorry
  d_comp_d' := by
    intro i j k hij hjk
    sorry

/-- The shifted copy is definitionally `A_(n-1)` in degree `n`. -/
def diamondShiftComponent
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (n : ℤ) :
  A.X (n - 1) ≅ (diamondShift A).X n :=
  by
    dsimp [diamondShift]
    exact Iso.refl _

def diamondShiftMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : ChainComplex C ℤ} (f : A ⟶ B) :
  diamondShift A ⟶ diamondShift B where
  f n := by
    dsimp [diamondShift]
    exact f.f (n - 1)
  comm' := by
    intro i j hij
    sorry

/-- Projection `◇ A → A[-1]`. -/
def diamondProjection
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) : diamond A ⟶ diamondShift A where
  f n := biprod.snd ≫ (diamondShiftComponent A n).hom
  comm' := by
    intro i j hij
    sorry

/-- The canonical section of the projection in every degree. -/
def diamondSection
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (n : ℤ) :
    (diamondShift A).X n ⟶ (diamond A).X n :=
  (diamondShiftComponent A n).inv ≫ biprod.inr

/-- The map `(1,-1) : A[-1] → (A ⊕ A)[-1]`. -/
def diamondConnecting
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) :
    diamondShift A ⟶ diamondShift (A ⊞ A) :=
  diamondShiftMap (biprod.lift (𝟙 A) (-𝟙 A))

/-- The inclusion of the first two summands. -/
def diamondPairInclusion
    {C : Type u} [Category.{v} C] [Abelian C]
  (A : ChainComplex C ℤ) : (A ⊞ A) ⟶ diamond A where
  f n :=
    (biprod.lift
      ((biprod.fst : A ⊞ A ⟶ A).f n)
      ((biprod.snd : A ⊞ A ⟶ A).f n)) ≫ biprod.inl
  comm' := by
    intro i j hij
    sorry

def diamondShortComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) : ShortComplex (ChainComplex C ℤ) :=
  ShortComplex.mk (diamondPairInclusion A) (diamondProjection A) (by
    ext n
    sorry)

/-- Degreewise splittings of a short complex of chain complexes. -/
structure DegreewiseSplitting
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (ChainComplex C ℤ)} where
  section_ : ∀ n : ℤ, S.X₃.X n ⟶ S.X₂.X n
  retraction : ∀ n : ℤ, S.g.f n ≫ section_ n = 𝟙 _

def diamondDegreewiseSplitting
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) :
    DegreewiseSplitting (S := diamondShortComplex A) where
  section_ := diamondSection A
  retraction := by
    intro n
    sorry

structure DiamondExtensionData
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) where
  splitting : DegreewiseSplitting (S := diamondShortComplex A)
  connecting : diamondShift A ⟶ diamondShift (A ⊞ A)
  connecting_eq : connecting = diamondConnecting A

def diamondExtensionData
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) : DiamondExtensionData A where
  splitting := diamondDegreewiseSplitting A
  connecting := diamondConnecting A
  connecting_eq := rfl

/-- The split short exact sequence and the source's connecting-map value. -/
theorem diamond_short_exact_and_connecting
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) :
    (diamondShortComplex A).ShortExact ∧
      Nonempty (DiamondExtensionData A) := by
  refine ⟨?_, ⟨diamondExtensionData A⟩⟩
  sorry

/-! ## Maps into `◇ A` -/

/-- The compatibility condition for the unique map in the source's second
lemma.  The field `δ` is the connecting morphism attached to the chosen
degreewise splittings. -/
def DiamondLiftProperty
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : ChainComplex C ℤ}
    (i : (A ⊞ A) ⟶ B) (p : B ⟶ D)
    (s : ∀ n : ℤ, D.X n ⟶ B.X n)
    (δ : D ⟶ diamondShift (A ⊞ A))
    (φ : D ⟶ diamondShift A) (ψ : B ⟶ diamond A) : Prop :=
  i ≫ ψ = diamondPairInclusion A ∧
    ψ ≫ diamondProjection A = p ≫ φ ∧
    δ = φ ≫ diamondConnecting A ∧
    ∀ n : ℤ, s n ≫ ψ.f n = φ.f n ≫ diamondSection A n

/-- A connecting morphism factoring through `(1,-1)` gives a unique compatible
map into `◇ A`. -/
theorem map_into_diamond
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : ChainComplex C ℤ}
    (i : (A ⊞ A) ⟶ B) (p : B ⟶ D) (hp : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hp).ShortExact)
    (s : ∀ n : ℤ, D.X n ⟶ B.X n)
    (hs : ∀ n : ℤ, p.f n ≫ s n = 𝟙 _)
    (δ : D ⟶ diamondShift (A ⊞ A))
    (φ : D ⟶ diamondShift A)
    (hδ : δ = φ ≫ diamondConnecting A) :
    ∃! ψ : B ⟶ diamond A,
      DiamondLiftProperty i p s δ φ ψ := by
  sorry

/-! ## The backwards homotopy theorem -/

/-- A normalized chain homotopy lifts to a simplicial cylinder homotopy, with
the same degree-`n` homotopy components. -/
theorem backwards_homotopy
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : _root_.Homotopy
      (normalizedChainComplexMap a)
      (normalizedChainComplexMap b)) :
    ∃ h : CylinderHomotopy a b,
      ∃ K : _root_.Homotopy
        (normalizedChainComplexMap a)
        (normalizedChainComplexMap b),
        ∀ n : ℕ, K.hom n (n + 1) = H.hom n (n + 1) := by
  sorry

end Formalization.Books.Simplicial.Unit29
