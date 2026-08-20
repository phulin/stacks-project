import Formalization.Books.Simplicial.Unit27.HomotopiesInAbelianCategories
import Formalization.Books.Homology.Unit14.HomotopyAndShift
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Yoneda
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
      ((-A.d (n - 1) (n - 2)) ≫ eqToHom (by congr 1; omega)))

private def diamondBoundary_explicit
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (n : ℤ) :
    ((A.X n ⊞ A.X n) ⊞ A.X (n - 1)) ⟶
      ((A.X (n - 1) ⊞ A.X (n - 1)) ⊞ A.X (n - 1 - 1)) :=
  biprod.lift
    (biprod.desc
      (biprod.lift
        (biprod.desc (A.d n (n - 1)) 0)
        (biprod.desc 0 (A.d n (n - 1))))
      (biprod.lift (𝟙 _) 0))
    (biprod.desc 0
      ((-A.d (n - 1) (n - 2)) ≫ eqToHom (by congr 1; omega)))

private lemma diamondBoundary_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (n : ℤ) :
    diamondBoundary A n ≫ diamondBoundary A (n - 1) = 0 := by
  change diamondBoundary_explicit A n ≫ diamondBoundary_explicit A (n - 1) = 0
  simp [diamondBoundary_explicit]
  apply biprod.hom_ext
  · apply biprod.hom_ext'
    · apply biprod.hom_ext
      · apply biprod.hom_ext'
        · simp [Category.assoc]
        · simp [Category.assoc]
      · apply biprod.hom_ext'
        · simp [Category.assoc]
        · simp [Category.assoc]
    · apply biprod.hom_ext
      · have h : n - 1 - 1 = n - 2 := by omega
        simp [h, Category.assoc]
      · simp [Category.assoc]
  · apply biprod.hom_ext'
    · simp [Category.assoc]
    · simp [Category.assoc]
      have h₁ : n - 1 - 1 = n - 2 := by omega
      have h₂ : n - 1 - 2 = n - 1 - 1 - 1 := by omega
      simp [h₁, h₂]

/-- The differential with the zero maps away from the immediate predecessor. -/
def diamondDifferential
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (i j : ℤ) :
    diamondObject A i ⟶ diamondObject A j :=
  if h : j = i - 1 then
    diamondBoundary A i ≫ eqToHom (by subst j; rfl)
  else 0

private lemma diamondDifferential_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) {i j k : ℤ}
    (hij : j = i - 1) (hjk : k = j - 1) :
    diamondDifferential A i j ≫ diamondDifferential A j k = 0 := by
  subst j
  subst k
  simp [diamondDifferential]
  exact diamondBoundary_comp A i

/-- The chain complex `◇ A` from the source. -/
def diamond
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) : ChainComplex C ℤ where
  X := diamondObject A
  d := diamondDifferential A
  shape := by
    intro i j hij
    simp only [ComplexShape.down_Rel] at hij
    simp only [diamondDifferential]
    rw [dif_neg]
    intro h
    apply hij
    simp [h]
  d_comp_d' := by
    intro i j k hij hjk
    simp only [ComplexShape.down_Rel] at hij hjk
    have hij' : j = i - 1 := by omega
    have hjk' : k = j - 1 := by omega
    exact diamondDifferential_comp A hij' hjk'

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

private lemma diamond_endpoint_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (q : ℤ) :
    ((biprod.inl ≫ biprod.inl) :
      A.X (q - 1) ⟶ ((A.X (q - 1) ⊞ A.X (q - 1)) ⊞ A.X (q - 1 - 1))) =
      A.d (q - 1) (q - 1 - 1) ≫ (biprod.inr :
        A.X (q - 1 - 1) ⟶
          ((A.X (q - 1) ⊞ A.X (q - 1)) ⊞ A.X (q - 1 - 1))) +
        (biprod.inr : A.X (q - 1) ⟶
          ((A.X q ⊞ A.X q) ⊞ A.X (q - 1))) ≫
          diamondBoundary_explicit A q +
        (biprod.inl ≫ biprod.snd :
          A.X (q - 1) ⟶
            ((A.X (q - 1) ⊞ A.X (q - 1)) ⊞ A.X (q - 1 - 1))) := by
  simp [diamondBoundary_explicit]
  apply biprod.hom_ext
  · rw [Preadditive.add_comp]
    simp [Category.assoc]
    apply biprod.hom_ext
    · simp
    · simp
  · rw [Preadditive.add_comp]
    simp [Category.assoc]
    have h : q - 1 - 1 = q - 2 := by omega
    simp [h]

private lemma diamond_endpoint_formula_transport
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) {i q : ℤ} (h : q - 1 = i) :
    ((biprod.inl ≫ biprod.inl) :
      A.X i ⟶ ((A.X i ⊞ A.X i) ⊞ A.X (i - 1))) =
      A.d i (i - 1) ≫ (biprod.inr :
        A.X (i - 1) ⟶ ((A.X i ⊞ A.X i) ⊞ A.X (i - 1))) +
        ((eqToHom (by subst i; rfl) ≫ (biprod.inr :
          A.X (q - 1) ⟶ ((A.X q ⊞ A.X q) ⊞ A.X (q - 1)))) ≫
          diamondBoundary_explicit A q ≫ eqToHom (by subst i; rfl)) +
        (0 : A.X i ⟶ ((A.X i ⊞ A.X i) ⊞ A.X (i - 1))) := by
  subst i
  simpa [Category.assoc, eqToHom_trans, eqToHom_refl] using
    (diamond_endpoint_formula A q)

/-- The two endpoint maps into `◇ A`. -/
def diamondLeft
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) : A ⟶ diamond A where
  f n := biprod.inl ≫ biprod.inl
  comm' := by
    intro i j hij
    simp only [ComplexShape.down_Rel] at hij
    have hj : j = i - 1 := by
      calc
        j = (j + 1) - 1 := by
          simp
        _ = i - 1 := by rw [hij]
    subst j
    change (biprod.inl ≫ biprod.inl) ≫ diamondDifferential A i (i - 1) =
      A.d i (i - 1) ≫ biprod.inl ≫ biprod.inl
    simp only [diamondDifferential]
    simp
    apply biprod.hom_ext
    · simp only [diamondBoundary]
      erw [Category.assoc, biprod.lift_fst]
      simp [Category.assoc]
      apply biprod.hom_ext
      · simp [Category.assoc]
      · simp [Category.assoc]
    · simp only [diamondBoundary]
      erw [Category.assoc, biprod.lift_snd]
      simp [Category.assoc]

def diamondRight
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) : A ⟶ diamond A where
  f n := biprod.inl ≫ biprod.snd
  comm' := by
    intro i j hij
    simp only [ComplexShape.down_Rel] at hij
    subst i
    simp [diamond, diamondDifferential, diamondBoundary]

private def diamondHomComponent
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (i j : ℤ) :
    A.X i ⟶ (diamond A).X j := by
  by_cases h : j = i + 1
  · exact eqToHom (by congr 1; omega) ≫ diamondThirdInclusionChain A j
  · exact 0

/-- The canonical chain homotopy between the endpoint maps. -/
def diamondHomotopy
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) :
    _root_.Homotopy (diamondLeft A) (diamondRight A) where
  hom i j := diamondHomComponent A i j
  zero i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    have h : ¬j = i + 1 := by
      intro h'
      apply hij
      exact h'.symm
    simp [diamondHomComponent, h]
    rfl
  comm := by
    intro i
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel i (i - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (i + 1) i by simp)]
    convert (diamond_endpoint_formula_transport A (i := i) (q := i + 1) (by omega)) using 1 <;>
      simp [diamondLeft, diamondRight, diamondHomComponent, diamond,
        diamondDifferential, diamondBoundary,
        diamondBoundary_explicit, diamondThirdInclusionChain,
        diamondThirdInclusion, diamondObject, Category.assoc, eqToHom_refl,
        Category.id_comp]
    all_goals
      abel_nf

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
    sorry

def chainHomotopyTripleMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) {B D : ChainComplex C ℤ} (g : B ⟶ D) :
    ChainHomotopyTriple A B → ChainHomotopyTriple A D := fun t =>
  { a := t.a ≫ g
    b := t.b ≫ g
    h := _root_.Homotopy.compRight t.h g }

def chainHomotopyTripleFunctor
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) : ChainComplex C ℤ ⥤ Type v where
  obj B := ChainHomotopyTriple A B
  map g := TypeCat.homEquiv.symm (chainHomotopyTripleMap A g)
  map_id := by
    sorry
  map_comp := by
    sorry

/-- The universal property of `◇ A`: maps out of it are exactly homotopy
triples `(a,b,h)`. -/
theorem diamond_represents_homotopy
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) :
    Nonempty ((chainHomotopyTripleFunctor A).CorepresentableBy (diamond A)) := by
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

/-- Projection `◇ A → A[-1]`. -/
def diamondProjection
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) : diamond A ⟶
      (Formalization.Books.Homology.Unit14.ChainComplex.shiftFunctor C (-1 : ℤ)).obj A where
  f n :=
    biprod.snd ≫
      (Formalization.Books.Homology.Unit14.ChainComplex.shiftFunctorObjXIso
        A (-1 : ℤ) n (n - 1) (by omega)).inv
  comm' := by
    intro i j hij
    sorry

/-- The canonical section of the projection in every degree. -/
def diamondSection
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (n : ℤ) :
    ((Formalization.Books.Homology.Unit14.ChainComplex.shiftFunctor C (-1 : ℤ)).obj A).X n ⟶
      (diamond A).X n :=
  (Formalization.Books.Homology.Unit14.ChainComplex.shiftFunctorObjXIso
      A (-1 : ℤ) n (n - 1) (by omega)).hom ≫ biprod.inr

/-- The map `(1,-1) : A[-1] → (A ⊕ A)[-1]`. -/
def diamondConnecting
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) :
    (Formalization.Books.Homology.Unit14.ChainComplex.shiftFunctor C (-1 : ℤ)).obj A ⟶
      (Formalization.Books.Homology.Unit14.ChainComplex.shiftFunctor C (-1 : ℤ)).obj (A ⊞ A) :=
  (Formalization.Books.Homology.Unit14.ChainComplex.shiftFunctor C (-1 : ℤ)).map
    (biprod.lift (𝟙 A) (-𝟙 A))

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
    /-
    Prior attempt: `ext n; sorry`.  After exposing the established
    homological-complex biproduct API, extensionality leaves an additional
    component goal, so this proof is retained as a single placeholder until
    the chain-map calculation is completed.
    -/
    sorry)

/-- The canonical termwise splitting of the projection.  This uses the
established splitting API for short complexes rather than a local wrapper. -/
noncomputable def diamondTermwiseSplitting
    {C : Type u} [Category.{v} C] [Abelian C]
  (A : ChainComplex C ℤ) :
    Formalization.Books.Homology.Unit14.ChainComplex.TermwiseSplitting
    (diamondShortComplex A) := fun n =>
  { r := by
      change diamondObject A n ⟶ (A ⊞ A).X n
      exact biprod.fst ≫ (HomologicalComplex.biprodXIso A A n).inv
    s := diamondSection A n
    f_r := by sorry
    s_g := by sorry
    id := by sorry }

/-- The connecting map associated to the canonical termwise splitting. -/
noncomputable def diamondTermwiseConnectingMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) :
    Formalization.Books.Homology.Unit14.ChainComplex.TermwiseSplitConnectingMap
      (diamondTermwiseSplitting A) :=
  (Formalization.Books.Homology.Unit14.ChainComplex.termwiseSplitConnectingMap_exists
    (diamondTermwiseSplitting A)).some

theorem diamondTermwiseSplitting_section
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) (n : ℤ) :
    (diamondTermwiseSplitting A n).s = diamondSection A n := by
  sorry

/-- The split short exact sequence and the source's connecting-map value. -/
theorem diamond_short_exact_and_connecting
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : ChainComplex C ℤ) :
    (diamondShortComplex A).ShortExact ∧
      (diamondTermwiseConnectingMap A).hom = diamondConnecting A := by
  sorry

/-! ## The termwise split extension and maps into `◇ A` -/

/-- The compatibility condition for the unique map in the source's second
lemma.  The field `δ` is the connecting morphism attached to the chosen
termwise splittings. -/
def DiamondLiftProperty
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : ChainComplex C ℤ}
    (i : (A ⊞ A) ⟶ B) (p : B ⟶ D)
    (hp : i ≫ p = 0)
    (s : Formalization.Books.Homology.Unit14.ChainComplex.TermwiseSplitting
      (ShortComplex.mk i p hp))
    (δ : Formalization.Books.Homology.Unit14.ChainComplex.TermwiseSplitConnectingMap s)
    (φ : D ⟶
      (Formalization.Books.Homology.Unit14.ChainComplex.shiftFunctor C (-1 : ℤ)).obj A)
    (ψ : B ⟶ diamond A) : Prop :=
  i ≫ ψ = diamondPairInclusion A ∧
    ψ ≫ diamondProjection A = p ≫ φ ∧
    δ.hom = φ ≫ diamondConnecting A ∧
    ∀ n : ℤ, (s n).s ≫ ψ.f n = φ.f n ≫ diamondSection A n

/-- A connecting morphism factoring through `(1,-1)` gives a unique compatible
map into `◇ A`. -/
theorem map_into_diamond
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : ChainComplex C ℤ}
    (i : (A ⊞ A) ⟶ B) (p : B ⟶ D) (hp : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hp).ShortExact)
    (s : Formalization.Books.Homology.Unit14.ChainComplex.TermwiseSplitting
      (ShortComplex.mk i p hp))
    (δ : Formalization.Books.Homology.Unit14.ChainComplex.TermwiseSplitConnectingMap s)
    (φ : D ⟶
      (Formalization.Books.Homology.Unit14.ChainComplex.shiftFunctor C (-1 : ℤ)).obj A)
    (hδ : δ.hom = φ ≫ diamondConnecting A) :
    ∃! ψ : B ⟶ diamond A,
      DiamondLiftProperty i p hp s δ φ ψ := by
  sorry

/-! ## The backwards homotopy theorem -/

/-- The normalized chain homotopy canonically associated to a cylinder
homotopy.  Its degree-`n` component is the normalized version of the chain
homotopy attached directly to that cylinder map, as in Chapter 27. -/
noncomputable def normalizedChainHomotopyOfCylinder
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (h : CylinderHomotopy a b) :
    _root_.Homotopy
      (normalizedChainComplexMap a)
      (normalizedChainComplexMap b) := by
  /-
  Prior attempt: choosing an arbitrary witness from
  `normalizedChainMap_homotopic` proves only that the endpoint maps are
  homotopic.  It does not identify the chosen witness with the componentwise
  normalized homotopy attached to this particular cylinder map, which is the
  datum required by the source theorem:

    exact (Formalization.Books.Simplicial.Unit27.normalizedChainMap_homotopic
      (Relation.EqvGen.rel a b
        (Formalization.Books.Simplicial.Unit26.homotopy_iff_degreewise.1 ⟨h⟩))).some
  -/
  sorry

/-- A normalized chain homotopy lifts to a simplicial cylinder homotopy, with
the same degree-`n` homotopy components. -/
theorem backwards_homotopy
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} {a b : U ⟶ V}
    (H : _root_.Homotopy
      (normalizedChainComplexMap a)
      (normalizedChainComplexMap b)) :
    ∃ h : CylinderHomotopy a b,
      ∀ n : ℕ,
        (normalizedChainHomotopyOfCylinder h).hom n (n + 1) = H.hom n (n + 1) := by
  sorry

end Formalization.Books.Simplicial.Unit29
