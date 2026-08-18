import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Formalization.Books.Homology.Unit14.HomotopyAndShift
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Products.Basic

/-!
# Homological Algebra, Chapter 18: Double complexes and associated total complexes

The source uses cochain-indexed double complexes.  A double complex is kept as
its two-indexed object-and-differential data, while rows and columns are
presented through Mathlib's `CochainComplex`.  Total complexes use Mathlib's
`Sigma` coproducts and the standard cochain-complex shift.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open HomologicalComplex
open ComplexShape

universe v u

namespace Formalization.Books.Homology.Unit18

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ## Double complexes -/

/-- A cochain double complex with commuting, rather than anticommuting,
    squares.  The first differential raises the first index and the second
    differential raises the second index. -/
structure DoubleComplex (C : Type u) [Category.{v} C] [Preadditive C] where
  obj : ℤ → ℤ → C
  d1 : ∀ p q, obj p q ⟶ obj (p + 1) q
  d2 : ∀ p q, obj p q ⟶ obj p (q + 1)
  d1_sq : ∀ p q, d1 p q ≫ d1 (p + 1) q = 0
  d2_sq : ∀ p q, d2 p q ≫ d2 p (q + 1) = 0
  comm : ∀ p q, d2 p q ≫ d1 p (q + 1) = d1 p q ≫ d2 (p + 1) q

/-- The horizontal cochain complex in a fixed second degree. -/
def row (A : DoubleComplex C) (q : ℤ) : CochainComplex C ℤ where
  X p := A.obj p q
  d p r := if h : p + 1 = r then h ▸ A.d1 p q else 0
  shape p r hpr := by
    classical
    split_ifs with h
    · exact (hpr h).elim
    · rfl
  d_comp_d' p r s hpr hrs := by
    classical
    have hpr' : p + 1 = r := by
      simpa only [ComplexShape.up_Rel] using hpr
    have hrs' : r + 1 = s := by
      simpa only [ComplexShape.up_Rel] using hrs
    rw [dif_pos hpr', dif_pos hrs']
    subst r
    subst s
    exact A.d1_sq p q

/-- The vertical cochain complex in a fixed first degree. -/
def column (A : DoubleComplex C) (p : ℤ) : CochainComplex C ℤ where
  X q := A.obj p q
  d q r := if h : q + 1 = r then h ▸ A.d2 p q else 0
  shape q r hqr := by
    classical
    split_ifs with h
    · exact (hqr h).elim
    · rfl
  d_comp_d' q r s hqr hrs := by
    classical
    have hqr' : q + 1 = r := by
      simpa only [ComplexShape.up_Rel] using hqr
    have hrs' : r + 1 = s := by
      simpa only [ComplexShape.up_Rel] using hrs
    rw [dif_pos hqr', dif_pos hrs']
    subst r
    subst s
    exact A.d2_sq p q

/-- The map between horizontal rows induced by the second differential. -/
def rowMap (A : DoubleComplex C) (q : ℤ) : row A q ⟶ row A (q + 1) where
  f p := by
    change A.obj p q ⟶ A.obj p (q + 1)
    exact A.d2 p q
  comm' p r hpr := by
    classical
    have hpr' : p + 1 = r := by
      simpa only [ComplexShape.up_Rel] using hpr
    subst r
    simpa [row] using A.comm p q

/-- The map between vertical columns induced by the first differential. -/
def columnMap (A : DoubleComplex C) (p : ℤ) : column A p ⟶ column A (p + 1) where
  f q := by
    change A.obj p q ⟶ A.obj (p + 1) q
    exact A.d1 p q
  comm' q r hqr := by
    classical
    have hqr' : q + 1 = r := by
      simpa only [ComplexShape.up_Rel] using hqr
    subst r
    simpa [column] using (A.comm p q).symm

theorem rowMap_comp_zero (A : DoubleComplex C) (p : ℤ) :
    rowMap A p ≫ rowMap A (p + 1) = 0 := by
  apply HomologicalComplex.Hom.ext
  ext r
  change A.d2 r p ≫ A.d2 r (p + 1) = 0
  exact A.d2_sq r p

theorem columnMap_comp_zero (A : DoubleComplex C) (q : ℤ) :
    columnMap A q ≫ columnMap A (q + 1) = 0 := by
  apply HomologicalComplex.Hom.ext
  ext r
  change A.d1 q r ≫ A.d1 (q + 1) r = 0
  exact A.d1_sq q r

/- The source's observation that a double complex is a complex of complexes
   is made explicit by the following two HomologicalComplex objects. -/
def rowsAsComplex (A : DoubleComplex C) :
    CochainComplex (CochainComplex C ℤ) ℤ where
  X p := row A p
  d p r := if h : p + 1 = r then h ▸ rowMap A p else 0
  shape p r hpr := by
    classical
    split_ifs with h
    · exact (hpr h).elim
    · rfl
  d_comp_d' p r s hpr hrs := by
    classical
    have hpr' : p + 1 = r := by
      simpa only [ComplexShape.up_Rel] using hpr
    have hrs' : r + 1 = s := by
      simpa only [ComplexShape.up_Rel] using hrs
    rw [dif_pos hpr', dif_pos hrs']
    subst r
    subst s
    exact rowMap_comp_zero A p

def columnsAsComplex (A : DoubleComplex C) :
    CochainComplex (CochainComplex C ℤ) ℤ where
  X q := column A q
  d q r := if h : q + 1 = r then h ▸ columnMap A q else 0
  shape q r hqr := by
    classical
    split_ifs with h
    · exact (hqr h).elim
    · rfl
  d_comp_d' q r s hqr hrs := by
    classical
    have hqr' : q + 1 = r := by
      simpa only [ComplexShape.up_Rel] using hqr
    have hrs' : r + 1 = s := by
      simpa only [ComplexShape.up_Rel] using hrs
    rw [dif_pos hqr', dif_pos hrs']
    subst r
    subst s
    exact columnMap_comp_zero A q

/-! ## Maps and the tensor-product example -/

/-- A morphism of double complexes. -/
structure DoubleComplexMap {C : Type u} [Category.{v} C] [Preadditive C]
    (A B : DoubleComplex C) where
  f : ∀ p q, A.obj p q ⟶ B.obj p q
  comm1 : ∀ p q, A.d1 p q ≫ f (p + 1) q = f p q ≫ B.d1 p q
  comm2 : ∀ p q, A.d2 p q ≫ f p (q + 1) = f p q ≫ B.d2 p q

@[ext]
theorem DoubleComplexMap.ext {A B : DoubleComplex C}
    (f g : DoubleComplexMap A B) (h : ∀ p q, f.f p q = g.f p q) : f = g := by
  cases f
  cases g
  simp only [DoubleComplexMap.mk.injEq]
  exact funext fun p => funext fun q => h p q

instance doubleComplexCategory {C : Type u} [Category.{v} C] [Preadditive C] :
    Category (DoubleComplex C) where
  Hom A B := DoubleComplexMap A B
  id A :=
    { f := fun p q => 𝟙 (A.obj p q)
      comm1 := by simp
      comm2 := by simp }
  comp {A B D} f g :=
    { f := fun p q => f.f p q ≫ g.f p q
      comm1 := by
        intro p q
        calc
          A.d1 p q ≫ (f.f (p + 1) q ≫ g.f (p + 1) q) =
              (A.d1 p q ≫ f.f (p + 1) q) ≫ g.f (p + 1) q :=
            (Category.assoc _ _ _).symm
          _ = (f.f p q ≫ B.d1 p q) ≫ g.f (p + 1) q := by rw [f.comm1]
          _ = f.f p q ≫ (B.d1 p q ≫ g.f (p + 1) q) :=
            Category.assoc _ _ _
          _ = f.f p q ≫ (g.f p q ≫ D.d1 p q) := by rw [g.comm1]
          _ = (f.f p q ≫ g.f p q) ≫ D.d1 p q :=
            (Category.assoc _ _ _).symm
      comm2 := by
        intro p q
        calc
          A.d2 p q ≫ (f.f p (q + 1) ≫ g.f p (q + 1)) =
              (A.d2 p q ≫ f.f p (q + 1)) ≫ g.f p (q + 1) :=
            (Category.assoc _ _ _).symm
          _ = (f.f p q ≫ B.d2 p q) ≫ g.f p (q + 1) := by rw [f.comm2]
          _ = f.f p q ≫ (B.d2 p q ≫ g.f p (q + 1)) :=
            Category.assoc _ _ _
          _ = f.f p q ≫ (g.f p q ≫ D.d2 p q) := by rw [g.comm2]
          _ = (f.f p q ≫ g.f p q) ≫ D.d2 p q :=
            (Category.assoc _ _ _).symm }
  id_comp := by
    intro A B f
    apply DoubleComplexMap.ext _ _
    intro p q
    simp
  comp_id := by
    intro A B f
    apply DoubleComplexMap.ext _ _
    intro p q
    simp
  assoc := by
    intro A B D E f g h
    apply DoubleComplexMap.ext _ _
    intro p q
    simp [Category.assoc]

/- A bifunctor that is additive in each variable.  This is the exact
   bilinearity hypothesis used by the tensor-product example; it avoids
   imposing a joint additive structure on the product category. -/
structure BilinearFunctor
    (A B C : Type u) [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [Preadditive A] [Preadditive B] [Preadditive C] where
  functor : (A × B) ⥤ C
  map_add_left : ∀ {X X' : A} (Y : B) (f g : X ⟶ X'),
    functor.map (Prod.mkHom (f + g) (𝟙 Y)) =
      functor.map (Prod.mkHom f (𝟙 Y)) + functor.map (Prod.mkHom g (𝟙 Y))
  map_add_right : ∀ (X : A) {Y Y' : B} (f g : Y ⟶ Y'),
    functor.map (Prod.mkHom (𝟙 X) (f + g)) =
      functor.map (Prod.mkHom (𝟙 X) f) + functor.map (Prod.mkHom (𝟙 X) g)

theorem tensor_d1_sq
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (T : BilinearFunctor A B C)
    (X : CochainComplex A ℤ) (Y : CochainComplex B ℤ) (p q : ℤ) :
    T.functor.map (Prod.mkHom (X.d p (p + 1)) (𝟙 (Y.X q))) ≫
    T.functor.map (Prod.mkHom (X.d (p + 1) ((p + 1) + 1)) (𝟙 (Y.X q))) = 0 := by
  have hzero :
      ∀ {U V : A} (Z : B),
        T.functor.map (Prod.mkHom (0 : U ⟶ V) (𝟙 Z)) = 0 := by
    intro U V Z
    have h := T.map_add_left Z (0 : U ⟶ V) 0
    have h' :
        T.functor.map (Prod.mkHom (0 : U ⟶ V) (𝟙 Z)) + 0 =
          T.functor.map (Prod.mkHom (0 : U ⟶ V) (𝟙 Z)) +
            T.functor.map (Prod.mkHom (0 : U ⟶ V) (𝟙 Z)) := by
      simpa only [zero_add, add_zero] using h
    exact (add_left_cancel h').symm
  rw [← T.functor.map_comp]
  rw [show
    Prod.mkHom (X.d p (p + 1)) (𝟙 (Y.X q)) ≫
        Prod.mkHom (X.d (p + 1) ((p + 1) + 1)) (𝟙 (Y.X q)) =
      Prod.mkHom (X.d p (p + 1) ≫ X.d (p + 1) ((p + 1) + 1)) (𝟙 (Y.X q)) by
    ext <;> simp]
  rw [X.d_comp_d]
  exact @hzero (X.X p) (X.X ((p + 1) + 1)) (Y.X q)

theorem tensor_d2_sq
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (T : BilinearFunctor A B C)
    (X : CochainComplex A ℤ) (Y : CochainComplex B ℤ) (p q : ℤ) :
    T.functor.map (Prod.mkHom (𝟙 (X.X p)) (Y.d q (q + 1))) ≫
        T.functor.map (Prod.mkHom (𝟙 (X.X p)) (Y.d (q + 1) ((q + 1) + 1))) = 0 := by
  have hzero :
      ∀ (U : A) {V W : B},
        T.functor.map (Prod.mkHom (𝟙 U) (0 : V ⟶ W)) = 0 := by
    intro U V W
    have h := T.map_add_right U (0 : V ⟶ W) 0
    have h' :
        T.functor.map (Prod.mkHom (𝟙 U) (0 : V ⟶ W)) + 0 =
          T.functor.map (Prod.mkHom (𝟙 U) (0 : V ⟶ W)) +
            T.functor.map (Prod.mkHom (𝟙 U) (0 : V ⟶ W)) := by
      simpa only [zero_add, add_zero] using h
    exact (add_left_cancel h').symm
  rw [← T.functor.map_comp]
  rw [show
    Prod.mkHom (𝟙 (X.X p)) (Y.d q (q + 1)) ≫
        Prod.mkHom (𝟙 (X.X p)) (Y.d (q + 1) ((q + 1) + 1)) =
      Prod.mkHom (𝟙 (X.X p))
        (Y.d q (q + 1) ≫ Y.d (q + 1) ((q + 1) + 1)) by
    ext <;> simp]
  rw [Y.d_comp_d]
  exact @hzero (X.X p) (Y.X q) (Y.X ((q + 1) + 1))

theorem tensor_differentials_commute
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (T : BilinearFunctor A B C)
    (X : CochainComplex A ℤ) (Y : CochainComplex B ℤ) (p q : ℤ) :
    T.functor.map (Prod.mkHom (𝟙 (X.X p)) (Y.d q (q + 1))) ≫
        T.functor.map (Prod.mkHom (X.d p (p + 1)) (𝟙 (Y.X (q + 1)))) =
        T.functor.map (Prod.mkHom (X.d p (p + 1)) (𝟙 (Y.X q))) ≫
        T.functor.map (Prod.mkHom (𝟙 (X.X (p + 1))) (Y.d q (q + 1))) := by
  rw [← T.functor.map_comp, ← T.functor.map_comp]
  congr 1
  ext <;> simp

/-- The tensor-product double complex from the source example. -/
def tensorProductDoubleComplex
    {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (T : BilinearFunctor A B C)
    (X : CochainComplex A ℤ) (Y : CochainComplex B ℤ) : DoubleComplex C where
  obj p q := T.functor.obj (X.X p, Y.X q)
  d1 p q := T.functor.map (Prod.mkHom (X.d p (p + 1)) (𝟙 (Y.X q)))
  d2 p q := T.functor.map (Prod.mkHom (𝟙 (X.X p)) (Y.d q (q + 1)))
  d1_sq p q := tensor_d1_sq T X Y p q
  d2_sq p q := tensor_d2_sq T X Y p q
  comm p q := tensor_differentials_commute T X Y p q

/-! ## Associated total complexes -/

def totalD1Component (A : DoubleComplex C) (n p : ℤ) :
    A.obj p (n - p) ⟶ A.obj (p + 1) (n + 1 - (p + 1)) :=
  A.d1 p (n - p) ≫ eqToHom (by congr 1; lia)

def totalD2Component (A : DoubleComplex C) (n p : ℤ) :
    A.obj p (n - p) ⟶ A.obj p (n + 1 - p) :=
  A.d2 p (n - p) ≫ eqToHom (by congr 1; lia)

def totalDifferential [HasCountableCoproducts C]
    (A : DoubleComplex C) (n : ℤ) :
    (∐ fun p : ℤ => A.obj p (n - p)) ⟶
      ∐ fun p : ℤ => A.obj p (n + 1 - p) :=
  Sigma.desc fun p =>
    totalD1Component A n p ≫
        Sigma.ι (fun r : ℤ => A.obj r (n + 1 - r)) (p + 1) +
      p.negOnePow •
        (totalD2Component A n p ≫
          Sigma.ι (fun r : ℤ => A.obj r (n + 1 - r)) p)

theorem totalDifferential_comp_zero [HasCountableCoproducts C]
    (A : DoubleComplex C) (n : ℤ) :
    totalDifferential A n ≫ totalDifferential A (n + 1) = 0 := by
  apply Sigma.hom_ext
  intro p
  have h11 :
      totalD1Component A n p ≫ totalD1Component A (n + 1) (p + 1) = 0 := by
    dsimp [totalD1Component]
    simp [Category.assoc]
    exact A.d1_sq p (n + 1 + 1 - (p + 1 + 1))
  have h22 :
      totalD2Component A n p ≫ totalD2Component A (n + 1) p = 0 := by
    dsimp [totalD2Component]
    simp only [Category.assoc]
    rw [← eqToHom_naturality_assoc (fun q : ℤ => A.d2 p q)
      (show n - p + 1 = n + 1 - p by ring)]
    simpa [Category.assoc] using
      congrArg (fun f => f ≫ eqToHom (by congr 1; ring))
        (A.d2_sq p (n - p))
  have hcomm :
      totalD1Component A n p ≫ totalD2Component A (n + 1) (p + 1) =
        totalD2Component A n p ≫ totalD1Component A (n + 1) p := by
    dsimp [totalD1Component, totalD2Component]
    simp only [Category.assoc]
    rw [← eqToHom_naturality_assoc (fun q : ℤ => A.d2 (p + 1) q)
      (show n - p = n + 1 - (p + 1) by ring)]
    rw [← eqToHom_naturality_assoc (fun q : ℤ => A.d1 p q)
      (show n - p + 1 = n + 1 - p by ring)]
    simpa [Category.assoc] using
      congrArg (fun f => f ≫ eqToHom (by congr 1; ring))
        (A.comm p (n - p)).symm
  have h11' :
      totalD1Component A n p ≫ totalD1Component A (n + 1) (p + 1) ≫
          Sigma.ι (fun r : ℤ => A.obj r (n + 1 + 1 - r)) (p + 1 + 1) = 0 := by
    rw [← Category.assoc, h11, zero_comp]
  have h22' :
      totalD2Component A n p ≫ totalD2Component A (n + 1) p ≫
          Sigma.ι (fun r : ℤ => A.obj r (n + 1 + 1 - r)) p = 0 := by
    rw [← Category.assoc, h22, zero_comp]
  have hcomm' :
      totalD1Component A n p ≫ totalD2Component A (n + 1) (p + 1) ≫
          Sigma.ι (fun r : ℤ => A.obj r (n + 1 + 1 - r)) (p + 1) =
        totalD2Component A n p ≫ totalD1Component A (n + 1) p ≫
          Sigma.ι (fun r : ℤ => A.obj r (n + 1 + 1 - r)) (p + 1) := by
    rw [← Category.assoc, ← Category.assoc, hcomm]
  simp [totalDifferential, Category.assoc, Int.negOnePow_succ, h11', h22', hcomm']

/-- The associated simple/total cochain complex. -/
def totalComplex [HasCountableCoproducts C]
    (A : DoubleComplex C) : CochainComplex C ℤ where
  X n := ∐ fun p : ℤ => A.obj p (n - p)
  d n m := if h : n + 1 = m then h ▸ totalDifferential A n else 0
  shape n m hnm := by
    classical
    split_ifs with h
    · exact (hnm h).elim
    · rfl
  d_comp_d' n m k hnm hmk := by
    classical
    have hnm' : n + 1 = m := by
      simpa only [ComplexShape.up_Rel] using hnm
    have hmk' : m + 1 = k := by
      simpa only [ComplexShape.up_Rel] using hmk
    rw [dif_pos hnm', dif_pos hmk']
    subst m
    subst k
    exact totalDifferential_comp_zero A n

theorem totalComplex_component_formula [HasCountableCoproducts C]
    (A : DoubleComplex C) (n p : ℤ) :
    Sigma.ι (fun r : ℤ => A.obj r (n - r)) p ≫
        (totalComplex A).d n (n + 1) =
      totalD1Component A n p ≫
          Sigma.ι (fun r : ℤ => A.obj r (n + 1 - r)) (p + 1) +
        p.negOnePow •
          (totalD2Component A n p ≫
            Sigma.ι (fun r : ℤ => A.obj r (n + 1 - r)) p) := by
  classical
  simp [totalComplex, totalDifferential]

/-- Existence of all diagonal coproducts, without committing to a typeclass. -/
def HasDiagonalCoproducts (A : DoubleComplex C) : Prop :=
  ∀ n : ℤ, Nonempty (ColimitCocone
    (Discrete.functor (fun p : ℤ => A.obj p (n - p))))

/-- The finite-support condition in the source's criterion for totalization. -/
def HasFiniteDiagonalSupport (A : DoubleComplex C) : Prop :=
  ∀ n : ℤ, {p : ℤ | ¬ IsZero (A.obj p (n - p))}.Finite

/-- A total complex presentation records chosen diagonal coproducts, the
    resulting cochain complex, and the displayed differential on each
    summand. -/
structure TotalComplexPresentation (A : DoubleComplex C) where
  diagonal : ∀ n : ℤ, ColimitCocone
    (Discrete.functor (fun p : ℤ => A.obj p (n - p)))
  complex : CochainComplex C ℤ
  term_iso : ∀ n : ℤ, complex.X n ≅ (diagonal n).cocone.pt
  differential_formula : ∀ (n p : ℤ),
    (diagonal n).cocone.ι.app (Discrete.mk p) ≫
        (term_iso n).inv ≫ complex.d n (n + 1) ≫ (term_iso (n + 1)).hom =
      totalD1Component A n p ≫
          (diagonal (n + 1)).cocone.ι.app (Discrete.mk (p + 1)) ≫
            eqToHom (by dsimp) +
        p.negOnePow •
          (totalD2Component A n p ≫
              (diagonal (n + 1)).cocone.ι.app (Discrete.mk p) ≫
              eqToHom (by dsimp))

theorem totalComplexPresentation_exists_of_diagonal_coproducts
    (A : DoubleComplex C) (hA : HasDiagonalCoproducts A) :
    Nonempty (TotalComplexPresentation A) := by
  classical
  let diag : ∀ n : ℤ, ColimitCocone
      (Discrete.functor (fun p : ℤ => A.obj p (n - p))) :=
    fun n => Classical.choice (hA n)
  let rawC : ∀ n : ℤ, Cocone (Discrete.functor (fun p : ℤ => A.obj p (n - p))) :=
    fun n =>
      { pt := (diag (n + 1)).cocone.pt
        ι := Discrete.natTrans (fun p : Discrete ℤ => by
          let i1 : A.obj p.as (n - p.as) ⟶ (diag (n + 1)).cocone.pt :=
            totalD1Component A n p.as ≫
              (diag (n + 1)).cocone.ι.app (Discrete.mk (p.as + 1))
          let i2 : A.obj p.as (n - p.as) ⟶ (diag (n + 1)).cocone.pt :=
            totalD2Component A n p.as ≫
              (diag (n + 1)).cocone.ι.app (Discrete.mk p.as)
          exact i1 + p.as.negOnePow • i2) }
  let rawD : ∀ n : ℤ, (diag n).cocone.pt ⟶ (diag (n + 1)).cocone.pt :=
    fun n => (diag n).isColimit.desc (rawC n)
  let K : CochainComplex C ℤ := {
    X := fun n => (diag n).cocone.pt,
    d := fun n m => if h : n + 1 = m then h ▸ rawD n else 0,
    shape := by
      intro n m hnm
      split_ifs with h
      · exact (hnm h).elim
      · rfl,
    d_comp_d' := by
      intro n m k hnm hmk
      have hnm' : n + 1 = m := by
        simpa only [ComplexShape.up_Rel] using hnm
      have hmk' : m + 1 = k := by
        simpa only [ComplexShape.up_Rel] using hmk
      rw [dif_pos hnm', dif_pos hmk']
      subst m
      subst k
      apply (diag n).isColimit.hom_ext
      intro p
      have h11 :
          totalD1Component A n p.as ≫
              totalD1Component A (n + 1) (p.as + 1) = 0 := by
        dsimp [totalD1Component]
        simp [Category.assoc]
        exact A.d1_sq p.as (n + 1 + 1 - (p.as + 1 + 1))
      have h22 :
          totalD2Component A n p.as ≫
              totalD2Component A (n + 1) p.as = 0 := by
        dsimp [totalD2Component]
        simp only [Category.assoc]
        rw [← eqToHom_naturality_assoc (fun q : ℤ => A.d2 p.as q)
          (show n - p.as + 1 = n + 1 - p.as by ring)]
        simpa [Category.assoc] using
          congrArg (fun f => f ≫ eqToHom (by congr 1; ring))
            (A.d2_sq p.as (n - p.as))
      have hcomm :
          totalD1Component A n p.as ≫
              totalD2Component A (n + 1) (p.as + 1) =
            totalD2Component A n p.as ≫
              totalD1Component A (n + 1) p.as := by
        dsimp [totalD1Component, totalD2Component]
        simp only [Category.assoc]
        rw [← eqToHom_naturality_assoc (fun q : ℤ => A.d2 (p.as + 1) q)
          (show n - p.as = n + 1 - (p.as + 1) by ring)]
        rw [← eqToHom_naturality_assoc (fun q : ℤ => A.d1 p.as q)
          (show n - p.as + 1 = n + 1 - p.as by ring)]
        simpa [Category.assoc] using
          congrArg (fun f => f ≫ eqToHom (by congr 1; ring))
            (A.comm p.as (n - p.as)).symm
      have h11' :
          totalD1Component A n p.as ≫
              totalD1Component A (n + 1) (p.as + 1) ≫
              (diag (n + 1 + 1)).cocone.ι.app
                (Discrete.mk (p.as + 1 + 1)) = 0 := by
        rw [← Category.assoc, h11, zero_comp]
      have h22' :
          totalD2Component A n p.as ≫
              totalD2Component A (n + 1) p.as ≫
              (diag (n + 1 + 1)).cocone.ι.app
                (Discrete.mk p.as) = 0 := by
        rw [← Category.assoc, h22, zero_comp]
      have hcomm' :
          totalD1Component A n p.as ≫
              totalD2Component A (n + 1) (p.as + 1) ≫
              (diag (n + 1 + 1)).cocone.ι.app
                (Discrete.mk (p.as + 1)) =
            totalD2Component A n p.as ≫
              totalD1Component A (n + 1) p.as ≫
              (diag (n + 1 + 1)).cocone.ι.app
                (Discrete.mk (p.as + 1)) := by
        rw [← Category.assoc, ← Category.assoc, hcomm]
      simp [rawD, rawC, Int.negOnePow_succ, h11', h22', hcomm']
  }
  let iso : ∀ n : ℤ, K.X n ≅ (diag n).cocone.pt := fun n => Iso.refl _
  refine ⟨{ diagonal := diag, complex := K, term_iso := iso, differential_formula := ?_ }⟩
  intro n p
  simp [iso, K, rawD, rawC]

theorem totalComplexPresentation_exists_of_countable
    [HasCountableCoproducts C] (A : DoubleComplex C) :
    Nonempty (TotalComplexPresentation A) := by
  apply totalComplexPresentation_exists_of_diagonal_coproducts A
  intro n
  exact ⟨getColimitCocone (Discrete.functor (fun p : ℤ => A.obj p (n - p)))⟩

theorem totalComplexPresentation_exists_of_finite_support
    [HasFiniteBiproducts C]
    (A : DoubleComplex C) (hA : HasFiniteDiagonalSupport A) :
    Nonempty (TotalComplexPresentation A) := by
  apply totalComplexPresentation_exists_of_diagonal_coproducts A
  intro n
  let S : Finset ℤ := (hA n).toFinset
  let f : S → C := fun p => A.obj p.1 (n - p.1)
  let c : Cofan (fun p : ℤ => A.obj p (n - p)) :=
    Cofan.mk (⨁ f) (fun p =>
      if hp : p ∈ S then biproduct.ι f ⟨p, hp⟩ else 0)
  refine ⟨{ cocone := c, isColimit := ?_ }⟩
  refine Cofan.IsColimit.mk c (fun t => biproduct.desc (fun p => t.inj p.1)) ?_ ?_
  · intro t p
    by_cases hp : p ∈ S
    · simp [c, hp, f]
    · have hz : IsZero (A.obj p (n - p)) := by
        apply not_not.mp
        intro hne
        apply hp
        exact (hA n).mem_toFinset.mpr hne
      simp [c, hp]
      exact hz.eq_of_src _ _
  · intro t m hm
    apply biproduct.hom_ext' _ _
    intro p
    have hm' := hm p.1
    simpa [c, f, p.2] using hm'

/-! ## Triple complexes and reassociation -/

/-- A three-direction cochain complex with commuting coordinate squares. -/
structure TripleComplex (C : Type u) [Category.{v} C] [Preadditive C] where
  obj : ℤ → ℤ → ℤ → C
  d1 : ∀ p q r, obj p q r ⟶ obj (p + 1) q r
  d2 : ∀ p q r, obj p q r ⟶ obj p (q + 1) r
  d3 : ∀ p q r, obj p q r ⟶ obj p q (r + 1)
  d1_sq : ∀ p q r, d1 p q r ≫ d1 (p + 1) q r = 0
  d2_sq : ∀ p q r, d2 p q r ≫ d2 p (q + 1) r = 0
  d3_sq : ∀ p q r, d3 p q r ≫ d3 p q (r + 1) = 0
  comm12 : ∀ p q r, d2 p q r ≫ d1 p (q + 1) r = d1 p q r ≫ d2 (p + 1) q r
  comm13 : ∀ p q r, d3 p q r ≫ d1 p q (r + 1) = d1 p q r ≫ d3 (p + 1) q r
  comm23 : ∀ p q r, d3 p q r ≫ d2 p q (r + 1) = d2 p q r ≫ d3 p (q + 1) r

def tripleTotalTerm [HasCountableCoproducts C]
    (A : TripleComplex C) (n : ℤ) : C :=
  ∐ fun p : ℤ => ∐ fun q : ℤ => A.obj p q (n - p - q)

def tripleTotalSign₁ (p _q : ℤ) : ℤˣ := p.negOnePow

def tripleTotalSign₂ (p q : ℤ) : ℤˣ := (p + q).negOnePow

def tripleD1Component
    (A : TripleComplex C) (n p q : ℤ) :
    A.obj p q (n - p - q) ⟶
      A.obj (p + 1) q (n + 1 - (p + 1) - q) :=
  A.d1 p q (n - p - q) ≫ eqToHom (by congr 1; lia)

def tripleD2Component
    (A : TripleComplex C) (n p q : ℤ) :
    A.obj p q (n - p - q) ⟶
      A.obj p (q + 1) (n + 1 - p - (q + 1)) :=
  A.d2 p q (n - p - q) ≫ eqToHom (by congr 1; lia)

def tripleD3Component
    (A : TripleComplex C) (n p q : ℤ) :
    A.obj p q (n - p - q) ⟶
      A.obj p q (n + 1 - p - q) :=
  A.d3 p q (n - p - q) ≫ eqToHom (by congr 1; lia)

def tripleTotalDifferential [HasCountableCoproducts C]
    (A : TripleComplex C) (n : ℤ) :
    tripleTotalTerm A n ⟶ tripleTotalTerm A (n + 1) :=
  Sigma.desc fun p =>
    Sigma.desc fun q =>
      (tripleD1Component A n p q ≫
          Sigma.ι (fun s : ℤ => A.obj (p + 1) s (n + 1 - (p + 1) - s)) q ≫
          Sigma.ι (fun r : ℤ => ∐ fun s : ℤ => A.obj r s (n + 1 - r - s)) (p + 1)) +
        tripleTotalSign₁ p q •
          (tripleD2Component A n p q ≫
            Sigma.ι (fun s : ℤ => A.obj p s (n + 1 - p - s)) (q + 1) ≫
            Sigma.ι (fun r : ℤ => ∐ fun s : ℤ => A.obj r s (n + 1 - r - s)) p) +
        tripleTotalSign₂ p q •
          (tripleD3Component A n p q ≫
            Sigma.ι (fun s : ℤ => A.obj p s (n + 1 - p - s)) q ≫
            Sigma.ι (fun r : ℤ => ∐ fun s : ℤ => A.obj r s (n + 1 - r - s)) p)

theorem tripleTotalDifferential_comp_zero [HasCountableCoproducts C]
    (A : TripleComplex C) (n : ℤ) :
    tripleTotalDifferential A n ≫ tripleTotalDifferential A (n + 1) = 0 := by
  apply Sigma.hom_ext
  intro p
  apply Sigma.hom_ext
  intro q
  let g : ∀ s : ℤ, A.obj p s (n - p - s) ⟶ tripleTotalTerm A (n + 1) :=
    fun s =>
      tripleD1Component A n p s ≫
          Sigma.ι (fun t : ℤ => A.obj (p + 1) t
            (n + 1 - (p + 1) - t)) s ≫
          Sigma.ι (fun r : ℤ => ∐ fun t : ℤ => A.obj r t
            (n + 1 - r - t)) (p + 1) +
        tripleTotalSign₁ p s •
          (tripleD2Component A n p s ≫
            Sigma.ι (fun t : ℤ => A.obj p t (n + 1 - p - t)) (s + 1) ≫
            Sigma.ι (fun r : ℤ => ∐ fun t : ℤ => A.obj r t
              (n + 1 - r - t)) p) +
        tripleTotalSign₂ p s •
          (tripleD3Component A n p s ≫
            Sigma.ι (fun t : ℤ => A.obj p t (n + 1 - p - t)) s ≫
            Sigma.ι (fun r : ℤ => ∐ fun t : ℤ => A.obj r t
              (n + 1 - r - t)) p)
  have hp :
      Sigma.ι (fun r : ℤ => ∐ fun s : ℤ => A.obj r s (n - r - s)) p ≫
          tripleTotalDifferential A n =
        Sigma.desc g := by
    apply Sigma.hom_ext
    intro s
    dsimp [g, tripleTotalDifferential]
    rw [Sigma.ι_desc]
  have hpq := congrArg
    (fun f => Sigma.ι (fun s : ℤ => A.obj p s (n - p - s)) q ≫ f) hp
  have hnext (r s : ℤ) :
      Sigma.ι (fun t : ℤ => A.obj r t (n + 1 - r - t)) s ≫
          Sigma.ι (fun r' : ℤ => ∐ fun t : ℤ => A.obj r' t
            (n + 1 - r' - t)) r ≫ tripleTotalDifferential A (n + 1) =
        tripleD1Component A (n + 1) r s ≫
            Sigma.ι (fun t : ℤ => A.obj (r + 1) t
              (n + 1 + 1 - (r + 1) - t)) s ≫
            Sigma.ι (fun r' : ℤ => ∐ fun t : ℤ => A.obj r' t
              (n + 1 + 1 - r' - t)) (r + 1) +
          tripleTotalSign₁ r s •
            (tripleD2Component A (n + 1) r s ≫
              Sigma.ι (fun t : ℤ => A.obj r t
                (n + 1 + 1 - r - t)) (s + 1) ≫
              Sigma.ι (fun r' : ℤ => ∐ fun t : ℤ => A.obj r' t
                (n + 1 + 1 - r' - t)) r) +
          tripleTotalSign₂ r s •
            (tripleD3Component A (n + 1) r s ≫
              Sigma.ι (fun t : ℤ => A.obj r t
                (n + 1 + 1 - r - t)) s ≫
              Sigma.ι (fun r' : ℤ => ∐ fun t : ℤ => A.obj r' t
                (n + 1 + 1 - r' - t)) r) := by
    dsimp [tripleTotalDifferential]
    rw [Sigma.ι_desc]
    dsimp [tripleTotalTerm]
    rw [Sigma.ι_desc]
  have h11 :
      tripleD1Component A n p q ≫
          tripleD1Component A (n + 1) (p + 1) q = 0 := by
    dsimp [tripleD1Component]
    simp [Category.assoc]
    exact A.d1_sq p q (n + 1 + 1 - (p + 1 + 1) - q)
  have h22 :
      tripleD2Component A n p q ≫
          tripleD2Component A (n + 1) p (q + 1) = 0 := by
    dsimp [tripleD2Component]
    simp only [Category.assoc]
    rw [← eqToHom_naturality_assoc (fun r : ℤ => A.d2 p (q + 1) r)
      (show n - p - q = n + 1 - p - (q + 1) by ring)]
    simpa [Category.assoc] using
      congrArg (fun f => f ≫ eqToHom (by congr 1; ring))
        (A.d2_sq p q (n - p - q))
  have h33 :
      tripleD3Component A n p q ≫
          tripleD3Component A (n + 1) p q = 0 := by
    dsimp [tripleD3Component]
    simp only [Category.assoc]
    rw [← eqToHom_naturality_assoc (fun r : ℤ => A.d3 p q r)
      (show n - p - q + 1 = n + 1 - p - q by ring)]
    simpa [Category.assoc] using
      congrArg (fun f => f ≫ eqToHom (by congr 1; ring))
        (A.d3_sq p q (n - p - q))
  have h12 :
      tripleD1Component A n p q ≫
          tripleD2Component A (n + 1) (p + 1) q =
        tripleD2Component A n p q ≫
          tripleD1Component A (n + 1) p (q + 1) := by
    dsimp [tripleD1Component, tripleD2Component]
    simp only [Category.assoc]
    rw [← eqToHom_naturality_assoc (fun r : ℤ => A.d2 (p + 1) q r)
      (show n - p - q = n + 1 - (p + 1) - q by ring)]
    rw [← eqToHom_naturality_assoc (fun r : ℤ => A.d1 p (q + 1) r)
      (show n - p - q = n + 1 - p - (q + 1) by ring)]
    simpa [Category.assoc] using
      congrArg (fun f => f ≫ eqToHom (by congr 1; ring))
        (A.comm12 p q (n - p - q)).symm
  have h13 :
      tripleD1Component A n p q ≫
          tripleD3Component A (n + 1) (p + 1) q =
        tripleD3Component A n p q ≫
          tripleD1Component A (n + 1) p q := by
    dsimp [tripleD1Component, tripleD3Component]
    simp only [Category.assoc]
    rw [← eqToHom_naturality_assoc (fun r : ℤ => A.d3 (p + 1) q r)
      (show n - p - q = n + 1 - (p + 1) - q by ring)]
    rw [← eqToHom_naturality_assoc (fun r : ℤ => A.d1 p q r)
      (show n - p - q + 1 = n + 1 - p - q by ring)]
    simpa [Category.assoc] using
      congrArg (fun f => f ≫ eqToHom (by congr 1; ring))
        (A.comm13 p q (n - p - q)).symm
  have h23 :
      tripleD2Component A n p q ≫
          tripleD3Component A (n + 1) p (q + 1) =
        tripleD3Component A n p q ≫
          tripleD2Component A (n + 1) p q := by
    dsimp [tripleD2Component, tripleD3Component]
    simp only [Category.assoc]
    rw [← eqToHom_naturality_assoc (fun r : ℤ => A.d3 p (q + 1) r)
      (show n - p - q = n + 1 - p - (q + 1) by ring)]
    rw [← eqToHom_naturality_assoc (fun r : ℤ => A.d2 p q r)
      (show n - p - q + 1 = n + 1 - p - q by ring)]
    simpa [Category.assoc] using
      congrArg (fun f => f ≫ eqToHom (by congr 1; ring))
        (A.comm23 p q (n - p - q)).symm
  have h11' :
      tripleD1Component A n p q ≫
          tripleD1Component A (n + 1) (p + 1) q ≫
          Sigma.ι (fun t : ℤ => A.obj (p + 1 + 1) t
            (n + 1 + 1 - (p + 1 + 1) - t)) q ≫
          Sigma.ι (fun r : ℤ => ∐ fun t : ℤ => A.obj r t
            (n + 1 + 1 - r - t)) (p + 1 + 1) = 0 := by
    rw [← Category.assoc, h11, zero_comp]
  have h22' :
      tripleD2Component A n p q ≫
          tripleD2Component A (n + 1) p (q + 1) ≫
          Sigma.ι (fun t : ℤ => A.obj p t
            (n + 1 + 1 - p - t)) (q + 1 + 1) ≫
          Sigma.ι (fun r : ℤ => ∐ fun t : ℤ => A.obj r t
            (n + 1 + 1 - r - t)) p = 0 := by
    rw [← Category.assoc, h22, zero_comp]
  have h33' :
      tripleD3Component A n p q ≫
          tripleD3Component A (n + 1) p q ≫
          Sigma.ι (fun t : ℤ => A.obj p t
            (n + 1 + 1 - p - t)) q ≫
          Sigma.ι (fun r : ℤ => ∐ fun t : ℤ => A.obj r t
            (n + 1 + 1 - r - t)) p = 0 := by
    rw [← Category.assoc, h33, zero_comp]
  have h12' :
      tripleD1Component A n p q ≫
          tripleD2Component A (n + 1) (p + 1) q ≫
          Sigma.ι (fun t : ℤ => A.obj (p + 1) t
            (n + 1 + 1 - (p + 1) - t)) (q + 1) ≫
          Sigma.ι (fun r : ℤ => ∐ fun t : ℤ => A.obj r t
            (n + 1 + 1 - r - t)) (p + 1) =
        tripleD2Component A n p q ≫
          tripleD1Component A (n + 1) p (q + 1) ≫
          Sigma.ι (fun t : ℤ => A.obj (p + 1) t
            (n + 1 + 1 - (p + 1) - t)) (q + 1) ≫
          Sigma.ι (fun r : ℤ => ∐ fun t : ℤ => A.obj r t
            (n + 1 + 1 - r - t)) (p + 1) := by
    rw [← Category.assoc, h12]
    simp only [Category.assoc]
  have h13' :
      tripleD1Component A n p q ≫
          tripleD3Component A (n + 1) (p + 1) q ≫
          Sigma.ι (fun t : ℤ => A.obj (p + 1) t
            (n + 1 + 1 - (p + 1) - t)) q ≫
          Sigma.ι (fun r : ℤ => ∐ fun t : ℤ => A.obj r t
            (n + 1 + 1 - r - t)) (p + 1) =
        tripleD3Component A n p q ≫
          tripleD1Component A (n + 1) p q ≫
          Sigma.ι (fun t : ℤ => A.obj (p + 1) t
            (n + 1 + 1 - (p + 1) - t)) q ≫
          Sigma.ι (fun r : ℤ => ∐ fun t : ℤ => A.obj r t
            (n + 1 + 1 - r - t)) (p + 1) := by
    rw [← Category.assoc, h13]
    simp only [Category.assoc]
  have h23' :
      tripleD2Component A n p q ≫
          tripleD3Component A (n + 1) p (q + 1) ≫
          Sigma.ι (fun t : ℤ => A.obj p t
            (n + 1 + 1 - p - t)) (q + 1) ≫
          Sigma.ι (fun r : ℤ => ∐ fun t : ℤ => A.obj r t
            (n + 1 + 1 - r - t)) p =
        tripleD3Component A n p q ≫
          tripleD2Component A (n + 1) p q ≫
          Sigma.ι (fun t : ℤ => A.obj p t
            (n + 1 + 1 - p - t)) (q + 1) ≫
          Sigma.ι (fun r : ℤ => ∐ fun t : ℤ => A.obj r t
            (n + 1 + 1 - r - t)) p := by
    rw [← Category.assoc, h23]
    simp only [Category.assoc]
  have hs2p :
      tripleTotalSign₂ (p + 1) q = -tripleTotalSign₂ p q := by
    dsimp [tripleTotalSign₂]
    rw [show p + 1 + q = (p + q) + 1 by ring]
    simp [Int.negOnePow_succ]
  have hs2q :
      tripleTotalSign₂ p (q + 1) = -tripleTotalSign₂ p q := by
    dsimp [tripleTotalSign₂]
    rw [show p + (q + 1) = (p + q) + 1 by ring]
    simp [Int.negOnePow_succ]
  have hs2p_raw :
      (p + 1 + q).negOnePow = -(p + q).negOnePow := by
    rw [show p + 1 + q = (p + q) + 1 by ring]
    simp [Int.negOnePow_succ]
  have hs2q_raw :
      (p + (q + 1)).negOnePow = -(p + q).negOnePow := by
    rw [show p + (q + 1) = (p + q) + 1 by ring]
    simp [Int.negOnePow_succ]
  have hzero : g q ≫ tripleTotalDifferential A (n + 1) =
      (0 : A.obj p q (n - p - q) ⟶
        ∐ fun r : ℤ => ∐ fun s : ℤ => A.obj r s (n + 1 + 1 - r - s)) := by
    let g' : ∀ s : ℤ, A.obj p s (n - p - s) ⟶
        ∐ fun r : ℤ => ∐ fun t : ℤ => A.obj r t (n + 1 - r - t) :=
      fun s => g s
    let d' :
        (∐ fun r : ℤ => ∐ fun s : ℤ => A.obj r s (n + 1 - r - s)) ⟶
          ∐ fun r : ℤ => ∐ fun s : ℤ => A.obj r s (n + 1 + 1 - r - s) :=
      tripleTotalDifferential A (n + 1)
    have hnext' (r s : ℤ) :
        Sigma.ι (fun t : ℤ => A.obj r t (n + 1 - r - t)) s ≫
            Sigma.ι (fun r' : ℤ => ∐ fun t : ℤ => A.obj r' t
              (n + 1 - r' - t)) r ≫ d' =
          tripleD1Component A (n + 1) r s ≫
              Sigma.ι (fun t : ℤ => A.obj (r + 1) t
                (n + 1 + 1 - (r + 1) - t)) s ≫
              Sigma.ι (fun r' : ℤ => ∐ fun t : ℤ => A.obj r' t
                (n + 1 + 1 - r' - t)) (r + 1) +
            tripleTotalSign₁ r s •
              (tripleD2Component A (n + 1) r s ≫
                Sigma.ι (fun t : ℤ => A.obj r t
                  (n + 1 + 1 - r - t)) (s + 1) ≫
                Sigma.ι (fun r' : ℤ => ∐ fun t : ℤ => A.obj r' t
                  (n + 1 + 1 - r' - t)) r) +
            tripleTotalSign₂ r s •
              (tripleD3Component A (n + 1) r s ≫
                Sigma.ι (fun t : ℤ => A.obj r t
                  (n + 1 + 1 - r - t)) s ≫
                Sigma.ι (fun r' : ℤ => ∐ fun t : ℤ => A.obj r' t
                  (n + 1 + 1 - r' - t)) r) := by
      simpa only [d', tripleTotalTerm] using hnext r s
    change g' q ≫ d' = 0
    simp only [g', g]
    rw [Preadditive.add_comp, Preadditive.add_comp]
    simp only [Linear.units_smul_comp, Category.assoc]
    rw [hnext' (p + 1) q, hnext' p (q + 1), hnext' p q]
    simp [tripleTotalSign₁, tripleTotalSign₂, Int.negOnePow_succ,
      hs2p, hs2q, h11', h22', h33', h12', h13', h23', Category.assoc,
      Linear.units_smul_comp, Linear.comp_units_smul]
    rw [hs2p_raw, hs2q_raw]
    simp only [Units.neg_smul, neg_smul, neg_one_smul, one_smul, smul_smul,
      Int.units_mul_self, mul_comm]
    rw [← smul_smul]
    simp only [smul_neg]
    abel
  have hcomp := congrArg
    (fun f => f ≫ tripleTotalDifferential A (n + 1)) hpq
  rw [Sigma.ι_desc] at hcomp
  erw [comp_zero, comp_zero]
  dsimp [tripleTotalTerm] at hcomp hzero
  have hassoc :
      (Sigma.ι (fun s : ℤ => A.obj p s (n - p - s)) q ≫
          (Sigma.ι (fun r : ℤ => ∐ fun s : ℤ => A.obj r s
            (n - r - s)) p ≫ tripleTotalDifferential A n)) ≫
          tripleTotalDifferential A (n + 1) =
        Sigma.ι (fun s : ℤ => A.obj p s (n - p - s)) q ≫
            (Sigma.ι (fun r : ℤ => ∐ fun s : ℤ => A.obj r s
            (n - r - s)) p ≫
            (tripleTotalDifferential A n ≫ tripleTotalDifferential A (n + 1))) := by
    exact (Category.assoc
      (Sigma.ι (fun s : ℤ => A.obj p s (n - p - s)) q)
      (Sigma.ι (fun r : ℤ => ∐ fun s : ℤ => A.obj r s
        (n - r - s)) p ≫ tripleTotalDifferential A n)
      (tripleTotalDifferential A (n + 1))).trans
      (congrArg
        (fun f => Sigma.ι (fun s : ℤ => A.obj p s (n - p - s)) q ≫ f)
        (Category.assoc
          (Sigma.ι (fun r : ℤ => ∐ fun s : ℤ => A.obj r s
            (n - r - s)) p)
          (tripleTotalDifferential A n)
          (tripleTotalDifferential A (n + 1))))
  exact hassoc.symm.trans (hcomp.trans hzero)

def tripleTotalComplex [HasCountableCoproducts C]
    (A : TripleComplex C) : CochainComplex C ℤ where
  X n := tripleTotalTerm A n
  d n m := if h : n + 1 = m then h ▸ tripleTotalDifferential A n else 0
  shape n m hnm := by
    classical
    split_ifs with h
    · exact (hnm h).elim
    · rfl
  d_comp_d' n m k hnm hmk := by
    classical
    have hnm' : n + 1 = m := by
      simpa only [ComplexShape.up_Rel] using hnm
    have hmk' : m + 1 = k := by
      simpa only [ComplexShape.up_Rel] using hmk
    rw [dif_pos hnm', dif_pos hmk']
    subst m
    subst k
    exact tripleTotalDifferential_comp_zero A n

theorem tripleTotalComplex_component_formula [HasCountableCoproducts C]
    (A : TripleComplex C) (n p q : ℤ) :
    Sigma.ι (fun s : ℤ => A.obj p s (n - p - s)) q ≫
        Sigma.ι (fun r : ℤ => ∐ fun s : ℤ => A.obj r s (n - r - s)) p ≫
        (tripleTotalComplex A).d n (n + 1) =
      (tripleD1Component A n p q ≫
          Sigma.ι (fun s : ℤ => A.obj (p + 1) s (n + 1 - (p + 1) - s)) q ≫
          Sigma.ι (fun r : ℤ => ∐ fun s : ℤ => A.obj r s (n + 1 - r - s)) (p + 1)) +
        tripleTotalSign₁ p q •
          (tripleD2Component A n p q ≫
            Sigma.ι (fun s : ℤ => A.obj p s (n + 1 - p - s)) (q + 1) ≫
            Sigma.ι (fun r : ℤ => ∐ fun s : ℤ => A.obj r s (n + 1 - r - s)) p) +
        tripleTotalSign₂ p q •
          (tripleD3Component A n p q ≫
            Sigma.ι (fun s : ℤ => A.obj p s (n + 1 - p - s)) q ≫
            Sigma.ι (fun r : ℤ => ∐ fun s : ℤ => A.obj r s (n + 1 - r - s)) p) := by
  classical
  simp [tripleTotalComplex, tripleTotalDifferential, Cofan.mk_ι_app,
    Discrete.functor_obj]
  rfl

def tripleTotalization [HasCountableCoproducts C]
    (A : TripleComplex C) : CochainComplex C ℤ :=
  tripleTotalComplex A

theorem tripleTotalization_exists [HasCountableCoproducts C]
    (A : TripleComplex C) : Nonempty (CochainComplex C ℤ) :=
  ⟨tripleTotalization A⟩

/- The first iterated totalization groups the first two indices before taking
   the final coproduct, while the second has the direct `(p,q)` presentation.
   Their canonical comparison is recorded as an isomorphism rather than as a
   definitional equality. -/
def tripleTotalizationOrder12Term [HasCountableCoproducts C]
    (A : TripleComplex C) (n : ℤ) : C :=
  ∐ fun s : ℤ => ∐ fun p : ℤ => A.obj p (s - p) (n - s)

def tripleTotalizationOrder23Term [HasCountableCoproducts C]
    (A : TripleComplex C) (n : ℤ) : C :=
  ∐ fun p : ℤ => ∐ fun q : ℤ => A.obj p q (n - p - q)

def tripleOrder12D1Component (A : TripleComplex C) (n s p : ℤ) :
    A.obj p (s - p) (n - s) ⟶
      A.obj (p + 1) ((s + 1) - (p + 1)) ((n + 1) - (s + 1)) :=
  A.d1 p (s - p) (n - s) ≫ eqToHom (by
    congr 1
    all_goals omega)

def tripleOrder12D2Component (A : TripleComplex C) (n s p : ℤ) :
    A.obj p (s - p) (n - s) ⟶
      A.obj p ((s + 1) - p) ((n + 1) - (s + 1)) :=
  A.d2 p (s - p) (n - s) ≫ eqToHom (by
    congr 1
    all_goals omega)

def tripleOrder12D3Component (A : TripleComplex C) (n s p : ℤ) :
    A.obj p (s - p) (n - s) ⟶
      A.obj p ((s) - p) ((n + 1) - s) :=
  A.d3 p (s - p) (n - s) ≫ eqToHom (by
    congr 1
    all_goals omega)

def tripleOrder12Differential [HasCountableCoproducts C]
    (A : TripleComplex C) (n : ℤ) :
    tripleTotalizationOrder12Term A n ⟶ tripleTotalizationOrder12Term A (n + 1) :=
  Sigma.desc fun s =>
    Sigma.desc fun p =>
      (tripleOrder12D1Component A n s p ≫
          Sigma.ι (fun r : ℤ =>
            A.obj r ((s + 1) - r) ((n + 1) - (s + 1))) (p + 1) ≫
          Sigma.ι (fun t : ℤ => ∐ fun r : ℤ =>
            A.obj r (t - r) ((n + 1) - t)) (s + 1)) +
        tripleTotalSign₁ p (s - p) •
          (tripleOrder12D2Component A n s p ≫
            Sigma.ι (fun r : ℤ =>
              A.obj r ((s + 1) - r) ((n + 1) - (s + 1))) p ≫
            Sigma.ι (fun t : ℤ => ∐ fun r : ℤ =>
              A.obj r (t - r) ((n + 1) - t)) (s + 1)) +
        tripleTotalSign₂ p (s - p) •
          (tripleOrder12D3Component A n s p ≫
            Sigma.ι (fun r : ℤ => A.obj r (s - r) ((n + 1) - s)) p ≫
            Sigma.ι (fun t : ℤ => ∐ fun r : ℤ =>
              A.obj r (t - r) ((n + 1) - t)) s)

theorem tripleOrder12Differential_comp_zero [HasCountableCoproducts C]
    (A : TripleComplex C) (n : ℤ) :
    tripleOrder12Differential A n ≫ tripleOrder12Differential A (n + 1) = 0 := by
  sorry

def tripleTotalizationOrder12Complex [HasCountableCoproducts C]
    (A : TripleComplex C) : CochainComplex C ℤ where
  X n := tripleTotalizationOrder12Term A n
  d n m := if h : n + 1 = m then h ▸ tripleOrder12Differential A n else 0
  shape n m hnm := by
    classical
    split_ifs with h
    · exact (hnm h).elim
    · rfl
  d_comp_d' n m k hnm hmk := by
    classical
    have hnm' : n + 1 = m := by
      simpa only [ComplexShape.up_Rel] using hnm
    have hmk' : m + 1 = k := by
      simpa only [ComplexShape.up_Rel] using hmk
    rw [dif_pos hnm', dif_pos hmk']
    subst m
    subst k
    exact tripleOrder12Differential_comp_zero A n

theorem tripleTotalization_associative [HasCountableCoproducts C]
    (A : TripleComplex C) (n : ℤ) :
    Nonempty (tripleTotalizationOrder12Term A n ≅ tripleTotalTerm A n) ∧
      Nonempty (tripleTotalizationOrder23Term A n ≅ tripleTotalTerm A n) := by
  sorry

theorem tripleTotalization_associative_complex [HasCountableCoproducts C]
    (A : TripleComplex C) :
    Nonempty (tripleTotalizationOrder12Complex A ≅ tripleTotalization A) := by
  sorry

/-! ## Shifts -/

def shiftedD1Component (A : DoubleComplex C) (a b p q : ℤ) :
    A.obj (p + a) (q + b) ⟶ A.obj ((p + 1) + a) (q + b) :=
  (a.negOnePow • A.d1 (p + a) (q + b)) ≫ eqToHom (by congr 1; lia)

def shiftedD2Component (A : DoubleComplex C) (a b p q : ℤ) :
    A.obj (p + a) (q + b) ⟶ A.obj (p + a) ((q + 1) + b) :=
  (b.negOnePow • A.d2 (p + a) (q + b)) ≫ eqToHom (by congr 1; lia)

theorem shifted_d1_sq (A : DoubleComplex C) (a b p q : ℤ) :
    shiftedD1Component A a b p q ≫ shiftedD1Component A a b (p + 1) q = 0 := by
  sorry

theorem shifted_d2_sq (A : DoubleComplex C) (a b p q : ℤ) :
    shiftedD2Component A a b p q ≫ shiftedD2Component A a b p (q + 1) = 0 := by
  sorry

theorem shifted_comm (A : DoubleComplex C) (a b p q : ℤ) :
    shiftedD2Component A a b p q ≫ shiftedD1Component A a b p (q + 1) =
      shiftedD1Component A a b p q ≫ shiftedD2Component A a b (p + 1) q := by
  sorry

/-- The shifted double complex from the source. -/
def doubleComplexShift (A : DoubleComplex C) (a b : ℤ) : DoubleComplex C where
  obj p q := A.obj (p + a) (q + b)
  d1 p q := shiftedD1Component A a b p q
  d2 p q := shiftedD2Component A a b p q
  d1_sq p q := shifted_d1_sq A a b p q
  d2_sq p q := shifted_d2_sq A a b p q
  comm p q := shifted_comm A a b p q

/-- The sign multiplying the summand `A^{p,q}` in the totalization shift
    comparison. -/
def totalizationShiftSign (p _q _a b : ℤ) : ℤˣ := (p * b).negOnePow

theorem totalizationShiftSign_first (p _q _a b : ℤ) :
    totalizationShiftSign (p + 1) q a b =
      b.negOnePow * totalizationShiftSign p q a b := by
  sorry

theorem totalizationShiftSign_second (p _q _a _b : ℤ) :
    totalizationShiftSign p (q + 1) a b =
      totalizationShiftSign p q a b := by
  sorry

structure TotalComplexShiftData [HasCountableCoproducts C]
    (A : DoubleComplex C) (a b : ℤ) where
  iso :
      (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (a + b)).obj
          (totalComplex A) ≅
        totalComplex (doubleComplexShift A a b)
  component_formula : ∀ n p : ℤ,
    Sigma.ι (fun r : ℤ => A.obj r (n + (a + b) - r)) p ≫ iso.hom.f n =
      totalizationShiftSign p (n + (a + b) - p) a b •
        (eqToHom (by
          dsimp [doubleComplexShift]
          congr 1 <;> ring) ≫
          Sigma.ι (fun r : ℤ =>
            (doubleComplexShift A a b).obj r (n - r)) (p - a))

theorem totalComplex_shift_data_exists [HasCountableCoproducts C]
    (A : DoubleComplex C) (a b : ℤ) :
    Nonempty (TotalComplexShiftData A a b) := by
  sorry

noncomputable def totalComplexShiftData [HasCountableCoproducts C]
    (A : DoubleComplex C) (a b : ℤ) : TotalComplexShiftData A a b :=
  Classical.choice (totalComplex_shift_data_exists A a b)

theorem totalComplex_shift_iso_exists [HasCountableCoproducts C]
    (A : DoubleComplex C) (a b : ℤ) :
    Nonempty (
      (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (a + b)).obj
          (totalComplex A) ≅
        totalComplex (doubleComplexShift A a b)) := by
  exact ⟨(totalComplexShiftData A a b).iso⟩

theorem totalComplex_shift_component_formula [HasCountableCoproducts C]
    (A : DoubleComplex C) (a b n p : ℤ) :
    ∃ γ :
        (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (a + b)).obj
            (totalComplex A) ≅
          totalComplex (doubleComplexShift A a b),
      Sigma.ι (fun r : ℤ => A.obj r (n + (a + b) - r)) p ≫ γ.hom.f n =
        totalizationShiftSign p (n + (a + b) - p) a b •
          (eqToHom (by
            dsimp [doubleComplexShift]
            congr 1 <;> ring) ≫
            Sigma.ι (fun r : ℤ =>
              (doubleComplexShift A a b).obj r (n - r)) (p - a)) := by
  exact ⟨(totalComplexShiftData A a b).iso,
    (totalComplexShiftData A a b).component_formula n p⟩

/-! ## Totalization of maps and homotopies -/

def totalMapComponent [HasCountableCoproducts C]
    {A B : DoubleComplex C} (f : DoubleComplexMap A B) (n : ℤ) :
    (totalComplex A).X n ⟶ (totalComplex B).X n :=
  Sigma.desc fun p =>
    f.f p (n - p) ≫ Sigma.ι (fun r : ℤ => B.obj r (n - r)) p

theorem totalMapComponent_comm [HasCountableCoproducts C]
    {A B : DoubleComplex C} (f : DoubleComplexMap A B) (n m : ℤ)
    (hnm : ComplexShape.Rel (ComplexShape.up ℤ) n m) :
    totalMapComponent f n ≫ (totalComplex B).d n m =
      (totalComplex A).d n m ≫ totalMapComponent f m := by
  sorry

def totalMap [HasCountableCoproducts C]
    {A B : DoubleComplex C} (f : DoubleComplexMap A B) :
    totalComplex A ⟶ totalComplex B where
  f n := totalMapComponent f n
  comm' n m hnm := totalMapComponent_comm f n m hnm

theorem totalMap_id [HasCountableCoproducts C] (A : DoubleComplex C) :
    totalMap (𝟙 A) = 𝟙 (totalComplex A) := by
  sorry

theorem totalMap_comp [HasCountableCoproducts C]
    {A B D : DoubleComplex C} (f : A ⟶ B) (g : B ⟶ D) :
    totalMap (f ≫ g) = totalMap f ≫ totalMap g := by
  sorry

/-- Totalization is a functor on double complexes whenever the required
    countable coproducts exist. -/
def totalizationFunctor [HasCountableCoproducts C] :
    DoubleComplex C ⥤ CochainComplex C ℤ where
  obj := totalComplex
  map := fun {_A _B} f => totalMap f
  map_id := totalMap_id
  map_comp := totalMap_comp

def verticalTotalHomotopyComponent [HasCountableCoproducts C]
    {A B : DoubleComplex C} (h : ∀ p q, A.obj p q ⟶ B.obj p (q - 1)) (n : ℤ) :
    (totalComplex A).X n ⟶ (totalComplex B).X (n - 1) :=
  Sigma.desc fun p =>
    p.negOnePow •
      (h p (n - p) ≫
        eqToHom (by congr 1; lia) ≫
        Sigma.ι (fun r : ℤ => B.obj r ((n - 1) - r)) p)

def horizontalTotalHomotopyComponent [HasCountableCoproducts C]
    {A B : DoubleComplex C} (h : ∀ p q, A.obj p q ⟶ B.obj (p - 1) q) (n : ℤ) :
    (totalComplex A).X n ⟶ (totalComplex B).X (n - 1) :=
  Sigma.desc fun p =>
    h p (n - p) ≫
      eqToHom (by congr 1; lia) ≫
      Sigma.ι (fun r : ℤ => B.obj r ((n - 1) - r)) (p - 1)

structure VerticalHomotopy {A B : DoubleComplex C}
    (f g : DoubleComplexMap A B) where
  h : ∀ p q, A.obj p q ⟶ B.obj p (q - 1)
  homotopy : ∀ p q,
    f.f p q - g.f p q =
      h p q ≫ B.d2 p (q - 1) ≫ eqToHom (by congr 1; lia) +
        A.d2 p q ≫ h p (q + 1) ≫ eqToHom (by congr 1; lia)
  map : ∀ p q,
    h p q ≫ B.d1 p (q - 1) = A.d1 p q ≫ h (p + 1) q

structure HorizontalHomotopy {A B : DoubleComplex C}
    (f g : DoubleComplexMap A B) where
  h : ∀ p q, A.obj p q ⟶ B.obj (p - 1) q
  homotopy : ∀ p q,
    f.f p q - g.f p q =
      h p q ≫ B.d1 (p - 1) q ≫ eqToHom (by congr 1; lia) +
        A.d1 p q ≫ h (p + 1) q ≫ eqToHom (by congr 1; lia)
  map : ∀ p q,
    h p q ≫ B.d2 (p - 1) q = A.d2 p q ≫ h p (q + 1)

theorem totalMap_homotopic_of_vertical [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f g : DoubleComplexMap A B}
    (h : VerticalHomotopy f g) :
    Nonempty (Homotopy (totalMap f) (totalMap g)) := by
  sorry

theorem totalMap_homotopic_of_horizontal [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f g : DoubleComplexMap A B}
    (h : HorizontalHomotopy f g) :
    Nonempty (Homotopy (totalMap f) (totalMap g)) := by
  sorry

theorem vertical_total_homotopy_components [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f g : DoubleComplexMap A B}
    (h : VerticalHomotopy f g) :
    ∃ H : Homotopy (totalMap f) (totalMap g),
      ∀ n : ℤ,
        H.hom n (n + (-1 : ℤ)) =
          verticalTotalHomotopyComponent h.h n := by
  sorry

theorem horizontal_total_homotopy_components [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f g : DoubleComplexMap A B}
    (h : HorizontalHomotopy f g) :
    ∃ H : Homotopy (totalMap f) (totalMap g),
      ∀ n : ℤ,
        H.hom n (n + (-1 : ℤ)) =
          horizontalTotalHomotopyComponent h.h n := by
  sorry

theorem verticalTotalShiftedHomotopy_comm [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f : DoubleComplexMap A B}
    (h : VerticalHomotopy f f) (n m : ℤ)
    (hnm : ComplexShape.Rel (ComplexShape.up ℤ) n m) :
    verticalTotalHomotopyComponent h.h n ≫
          ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).obj
            (totalComplex B)).d n m =
      (totalComplex A).d n m ≫ verticalTotalHomotopyComponent h.h m := by
  sorry

def verticalTotalShiftedHomotopy [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f : DoubleComplexMap A B}
    (h : VerticalHomotopy f f) :
    totalComplex A ⟶
      (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).obj
        (totalComplex B) where
  f n := verticalTotalHomotopyComponent h.h n
  comm' n m hnm := verticalTotalShiftedHomotopy_comm h n m hnm

theorem horizontalTotalShiftedHomotopy_comm [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f : DoubleComplexMap A B}
    (h : HorizontalHomotopy f f) (n m : ℤ)
    (hnm : ComplexShape.Rel (ComplexShape.up ℤ) n m) :
    horizontalTotalHomotopyComponent h.h n ≫
          ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).obj
            (totalComplex B)).d n m =
      (totalComplex A).d n m ≫ horizontalTotalHomotopyComponent h.h m := by
  sorry

def horizontalTotalShiftedHomotopy [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f : DoubleComplexMap A B}
    (h : HorizontalHomotopy f f) :
    totalComplex A ⟶
      (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).obj
        (totalComplex B) where
  f n := horizontalTotalHomotopyComponent h.h n
  comm' n m hnm := horizontalTotalShiftedHomotopy_comm h n m hnm

theorem vertical_homotopy_shift_compatibility [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f : DoubleComplexMap A B}
    (h : VerticalHomotopy f f) :
    ∃ k : DoubleComplexMap A (doubleComplexShift B 0 (-1)),
      (∀ p q,
        k.f p q = h.h p q ≫ eqToHom (by
          dsimp [doubleComplexShift]
          congr 1; ring)) ∧
      ∃ γ :
          (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).obj
              (totalComplex B) ≅
            totalComplex (doubleComplexShift B 0 (-1)),
        totalMap k ≫ γ.inv = verticalTotalShiftedHomotopy h := by
  sorry

theorem horizontal_homotopy_shift_compatibility [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f : DoubleComplexMap A B}
    (h : HorizontalHomotopy f f) :
    ∃ k : DoubleComplexMap A (doubleComplexShift B (-1) 0),
      (∀ p q,
        k.f p q = h.h p q ≫ eqToHom (by
          dsimp [doubleComplexShift]
          congr 1; ring)) ∧
      ∃ γ :
          (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).obj
              (totalComplex B) ≅
            totalComplex (doubleComplexShift B (-1) 0),
        totalMap k ≫ γ.inv = horizontalTotalShiftedHomotopy h := by
  sorry

/-! ## Termwise split short exact sequences -/

structure DoubleComplexShortExact (A B D : DoubleComplex C) where
  inclusion : A ⟶ B
  projection : B ⟶ D
  zero : ∀ p q, inclusion.f p q ≫ projection.f p q = 0
  component_shortExact : ∀ p q,
    (ShortComplex.mk (inclusion.f p q) (projection.f p q)
      (zero p q)).Exact

theorem totalizedShortComplex_zero [HasCountableCoproducts C]
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D) :
    totalMap S.inclusion ≫ totalMap S.projection = 0 := by
  sorry

def totalizedShortComplex [HasCountableCoproducts C]
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (totalMap S.inclusion) (totalMap S.projection)
    (totalizedShortComplex_zero S)

structure FirstDirectionSplitting
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D) where
  sectionMap : ∀ q p, D.obj p q ⟶ B.obj p q
  projectionMap : ∀ q p, B.obj p q ⟶ A.obj p q
  section_right_inverse : ∀ q p,
    sectionMap q p ≫ S.projection.f p q = 𝟙 _
  projection_left_inverse : ∀ q p,
    S.inclusion.f p q ≫ projectionMap q p = 𝟙 _
  splitting_id : ∀ q p,
    projectionMap q p ≫ S.inclusion.f p q +
        S.projection.f p q ≫ sectionMap q p = 𝟙 _
  section_horizontal : ∀ q p,
    sectionMap q p ≫ B.d1 p q = D.d1 p q ≫ sectionMap q (p + 1)
  projection_horizontal : ∀ q p,
    B.d1 p q ≫ projectionMap q (p + 1) = projectionMap q p ≫ A.d1 p q

structure SecondDirectionSplitting
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D) where
  sectionMap : ∀ p q, D.obj p q ⟶ B.obj p q
  projectionMap : ∀ p q, B.obj p q ⟶ A.obj p q
  section_right_inverse : ∀ p q,
    sectionMap p q ≫ S.projection.f p q = 𝟙 _
  projection_left_inverse : ∀ p q,
    S.inclusion.f p q ≫ projectionMap p q = 𝟙 _
  splitting_id : ∀ p q,
    projectionMap p q ≫ S.inclusion.f p q +
        S.projection.f p q ≫ sectionMap p q = 𝟙 _
  section_vertical : ∀ p q,
    sectionMap p q ≫ B.d2 p q = D.d2 p q ≫ sectionMap p (q + 1)
  projection_vertical : ∀ p q,
    B.d2 p q ≫ projectionMap p (q + 1) = projectionMap p q ≫ A.d2 p q

def firstTotalSection [HasCountableCoproducts C]
    {A B D : DoubleComplex C} {S : DoubleComplexShortExact A B D}
    (s : FirstDirectionSplitting S) (n : ℤ) :
    (totalComplex D).X n ⟶ (totalComplex B).X n :=
  Sigma.desc fun p =>
    s.sectionMap (n - p) p ≫
      Sigma.ι (fun r : ℤ => B.obj r (n - r)) p

def firstTotalProjection [HasCountableCoproducts C]
    {A B D : DoubleComplex C} {S : DoubleComplexShortExact A B D}
    (s : FirstDirectionSplitting S) (n : ℤ) :
    (totalComplex B).X n ⟶ (totalComplex A).X n :=
  Sigma.desc fun p =>
    s.projectionMap (n - p) p ≫
      Sigma.ι (fun r : ℤ => A.obj r (n - r)) p

def secondTotalSection [HasCountableCoproducts C]
    {A B D : DoubleComplex C} {S : DoubleComplexShortExact A B D}
    (s : SecondDirectionSplitting S) (n : ℤ) :
    (totalComplex D).X n ⟶ (totalComplex B).X n :=
  Sigma.desc fun p =>
    s.sectionMap p (n - p) ≫
      Sigma.ι (fun r : ℤ => B.obj r (n - r)) p

def secondTotalProjection [HasCountableCoproducts C]
    {A B D : DoubleComplex C} {S : DoubleComplexShortExact A B D}
    (s : SecondDirectionSplitting S) (n : ℤ) :
    (totalComplex B).X n ⟶ (totalComplex A).X n :=
  Sigma.desc fun p =>
    s.projectionMap p (n - p) ≫
      Sigma.ι (fun r : ℤ => A.obj r (n - r)) p

theorem firstTotalSection_projection_id [HasCountableCoproducts C]
    {A B D : DoubleComplex C} {S : DoubleComplexShortExact A B D}
    (s : FirstDirectionSplitting S) (n : ℤ) :
    firstTotalSection s n ≫ (totalMap S.projection).f n = 𝟙 _ := by
  sorry

theorem firstTotalInclusion_projection [HasCountableCoproducts C]
    {A B D : DoubleComplex C} {S : DoubleComplexShortExact A B D}
    (s : FirstDirectionSplitting S) (n : ℤ) :
    (totalMap S.inclusion).f n ≫ firstTotalProjection s n = 𝟙 _ := by
  sorry

theorem secondTotalSection_projection_id [HasCountableCoproducts C]
    {A B D : DoubleComplex C} {S : DoubleComplexShortExact A B D}
    (s : SecondDirectionSplitting S) (n : ℤ) :
    secondTotalSection s n ≫ (totalMap S.projection).f n = 𝟙 _ := by
  sorry

theorem secondTotalInclusion_projection [HasCountableCoproducts C]
    {A B D : DoubleComplex C} {S : DoubleComplexShortExact A B D}
    (s : SecondDirectionSplitting S) (n : ℤ) :
    (totalMap S.inclusion).f n ≫ secondTotalProjection s n = 𝟙 _ := by
  sorry

def firstConnectingComponent
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : FirstDirectionSplitting S) (p q : ℤ) :
    D.obj p q ⟶ A.obj p (q + 1) :=
  s.sectionMap q p ≫ B.d2 p q ≫ s.projectionMap (q + 1) p

def secondConnectingComponent
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : SecondDirectionSplitting S) (p q : ℤ) :
    D.obj p q ⟶ A.obj (p + 1) q :=
  s.sectionMap p q ≫ B.d1 p q ≫ s.projectionMap (p + 1) q

theorem first_totalized_splitting_formula
    [HasCountableCoproducts C]
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : FirstDirectionSplitting S) (n p : ℤ) :
    Sigma.ι (fun r : ℤ => D.obj r (n - r)) p ≫
        firstTotalSection s n ≫ (totalComplex B).d n (n + 1) ≫
        firstTotalProjection s (n + 1) =
      p.negOnePow •
        (firstConnectingComponent S s p (n - p) ≫
          eqToHom (by congr 1; lia) ≫
          Sigma.ι (fun r : ℤ => A.obj r (n + 1 - r)) p) := by
  sorry

theorem second_totalized_splitting_formula
    [HasCountableCoproducts C]
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : SecondDirectionSplitting S) (n p : ℤ) :
    Sigma.ι (fun r : ℤ => D.obj r (n - r)) p ≫
        secondTotalSection s n ≫ (totalComplex B).d n (n + 1) ≫
        secondTotalProjection s (n + 1) =
      secondConnectingComponent S s p (n - p) ≫
        eqToHom (by congr 1; lia) ≫
        Sigma.ι (fun r : ℤ => A.obj r (n + 1 - r)) (p + 1) := by
  sorry

structure FirstConnectingMapData
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : FirstDirectionSplitting S) where
  map : DoubleComplexMap D (doubleComplexShift A 0 1)
  component_formula : ∀ p q : ℤ,
    map.f p q = firstConnectingComponent S s p q ≫ eqToHom (by
      dsimp [doubleComplexShift]
      congr 1; ring)

theorem firstConnectingMap_data_exists
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : FirstDirectionSplitting S) :
    Nonempty (FirstConnectingMapData S s) := by
  sorry

noncomputable def firstConnectingMapData
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : FirstDirectionSplitting S) : FirstConnectingMapData S s :=
  Classical.choice (firstConnectingMap_data_exists S s)

theorem firstConnectingMap_component
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : FirstDirectionSplitting S) (p q : ℤ) :
    (firstConnectingMapData S s).map.f p q =
      firstConnectingComponent S s p q ≫ eqToHom (by
        dsimp [doubleComplexShift]
        congr 1; ring) :=
  (firstConnectingMapData S s).component_formula p q

theorem firstConnectingMap_exists
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : FirstDirectionSplitting S) :
    Nonempty (DoubleComplexMap D (doubleComplexShift A 0 1)) :=
  ⟨(firstConnectingMapData S s).map⟩

noncomputable def firstConnectingMap
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : FirstDirectionSplitting S) :
    DoubleComplexMap D (doubleComplexShift A 0 1) :=
  (firstConnectingMapData S s).map

theorem firstConnectingMap_formula
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : FirstDirectionSplitting S) (p q : ℤ) :
    (firstConnectingMap S s).f p q =
      firstConnectingComponent S s p q ≫ eqToHom (by
        dsimp [doubleComplexShift]
        congr 1; ring) := by
  exact firstConnectingMap_component S s p q

structure SecondConnectingMapData
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : SecondDirectionSplitting S) where
  map : DoubleComplexMap D (doubleComplexShift A 1 0)
  component_formula : ∀ p q : ℤ,
    map.f p q = secondConnectingComponent S s p q ≫ eqToHom (by
      dsimp [doubleComplexShift]
      congr 1; ring)

theorem secondConnectingMap_data_exists
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : SecondDirectionSplitting S) :
    Nonempty (SecondConnectingMapData S s) := by
  sorry

noncomputable def secondConnectingMapData
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : SecondDirectionSplitting S) : SecondConnectingMapData S s :=
  Classical.choice (secondConnectingMap_data_exists S s)

theorem secondConnectingMap_component
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : SecondDirectionSplitting S) (p q : ℤ) :
    (secondConnectingMapData S s).map.f p q =
      secondConnectingComponent S s p q ≫ eqToHom (by
        dsimp [doubleComplexShift]
        congr 1; ring) :=
  (secondConnectingMapData S s).component_formula p q

theorem secondConnectingMap_exists
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : SecondDirectionSplitting S) :
    Nonempty (DoubleComplexMap D (doubleComplexShift A 1 0)) :=
  ⟨(secondConnectingMapData S s).map⟩

noncomputable def secondConnectingMap
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : SecondDirectionSplitting S) :
    DoubleComplexMap D (doubleComplexShift A 1 0) :=
  (secondConnectingMapData S s).map

theorem secondConnectingMap_formula
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : SecondDirectionSplitting S) (p q : ℤ) :
    (secondConnectingMap S s).f p q =
      secondConnectingComponent S s p q ≫ eqToHom (by
        dsimp [doubleComplexShift]
        congr 1; ring) := by
  exact secondConnectingMap_component S s p q

noncomputable def totalShiftIso [HasCountableCoproducts C]
    (A : DoubleComplex C) (a b : ℤ) :
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (a + b)).obj
        (totalComplex A) ≅ totalComplex (doubleComplexShift A a b) :=
  (totalComplexShiftData A a b).iso

theorem totalShiftIso_component_formula [HasCountableCoproducts C]
    (A : DoubleComplex C) (a b n p : ℤ) :
    Sigma.ι (fun r : ℤ => A.obj r (n + (a + b) - r)) p ≫
        (totalShiftIso A a b).hom.f n =
      totalizationShiftSign p (n + (a + b) - p) a b •
        (eqToHom (by
          dsimp [doubleComplexShift]
          congr 1 <;> ring) ≫
          Sigma.ι (fun r : ℤ =>
            (doubleComplexShift A a b).obj r (n - r)) (p - a)) := by
  exact (totalComplexShiftData A a b).component_formula n p

noncomputable def totalFirstConnectingMap
    [HasCountableCoproducts C]
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : FirstDirectionSplitting S) :
    totalComplex D ⟶
      (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).obj
        (totalComplex A) :=
  totalMap (firstConnectingMap S s) ≫ (totalShiftIso A 0 1).inv

theorem total_first_connecting_formula
    [HasCountableCoproducts C]
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : FirstDirectionSplitting S) (n p : ℤ) :
    Sigma.ι (fun r : ℤ => D.obj r (n - r)) p ≫
        (totalFirstConnectingMap S s).f n =
      firstConnectingComponent S s p (n - p) ≫
        eqToHom (by congr 1; lia) ≫
        Sigma.ι (fun r : ℤ => A.obj r (n + 1 - r)) p := by
  sorry

noncomputable def totalSecondConnectingMap
    [HasCountableCoproducts C]
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : SecondDirectionSplitting S) :
    totalComplex D ⟶
      (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).obj
        (totalComplex A) :=
  totalMap (secondConnectingMap S s) ≫ (totalShiftIso A 1 0).inv

theorem total_second_connecting_formula
    [HasCountableCoproducts C]
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s : SecondDirectionSplitting S) (n p : ℤ) :
    Sigma.ι (fun r : ℤ => D.obj r (n - r)) p ≫
        (totalSecondConnectingMap S s).f n =
      secondConnectingComponent S s p (n - p) ≫
        eqToHom (by congr 1; lia) ≫
        Sigma.ι (fun r : ℤ => A.obj r (n + 1 - r)) (p + 1) := by
  sorry

theorem total_first_connecting_independent_up_to_homotopy
    [HasCountableCoproducts C]
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s s' : FirstDirectionSplitting S) :
    Nonempty (Homotopy (totalFirstConnectingMap S s)
      (totalFirstConnectingMap S s')) := by
  sorry

theorem total_second_connecting_independent_up_to_homotopy
    [HasCountableCoproducts C]
    {A B D : DoubleComplex C} (S : DoubleComplexShortExact A B D)
    (s s' : SecondDirectionSplitting S) :
    Nonempty (Homotopy (totalSecondConnectingMap S s)
      (totalSecondConnectingMap S s')) := by
  sorry

end Formalization.Books.Homology.Unit18
