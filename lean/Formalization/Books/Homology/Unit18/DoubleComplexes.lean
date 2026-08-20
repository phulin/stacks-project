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
  A.d1 p (n - p) ≫ eqToHom (by congr 1; ring)

def totalD2Component (A : DoubleComplex C) (n p : ℤ) :
    A.obj p (n - p) ⟶ A.obj p (n + 1 - p) :=
  A.d2 p (n - p) ≫ eqToHom (by congr 1; ring)

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
  A.d1 p q (n - p - q) ≫ eqToHom (by congr 1; ring)

def tripleD2Component
    (A : TripleComplex C) (n p q : ℤ) :
    A.obj p q (n - p - q) ⟶
      A.obj p (q + 1) (n + 1 - p - (q + 1)) :=
  A.d2 p q (n - p - q) ≫ eqToHom (by congr 1; ring)

def tripleD3Component
    (A : TripleComplex C) (n p q : ℤ) :
    A.obj p q (n - p - q) ⟶
      A.obj p q (n + 1 - p - q) :=
  A.d3 p q (n - p - q) ≫ eqToHom (by congr 1; ring)

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
      h11', h22', h33', h12', h13', h23',
      Linear.comp_units_smul]
    rw [hs2p_raw, hs2q_raw]
    simp only [Units.neg_smul, smul_smul, mul_comm]
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
  simp [tripleTotalComplex, tripleTotalDifferential, Cofan.mk_ι_app]
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
    all_goals ring)

def tripleOrder12D2Component (A : TripleComplex C) (n s p : ℤ) :
    A.obj p (s - p) (n - s) ⟶
      A.obj p ((s + 1) - p) ((n + 1) - (s + 1)) :=
  A.d2 p (s - p) (n - s) ≫ eqToHom (by
    congr 1
    all_goals ring)

def tripleOrder12D3Component (A : TripleComplex C) (n s p : ℤ) :
    A.obj p (s - p) (n - s) ⟶
      A.obj p ((s) - p) ((n + 1) - s) :=
  A.d3 p (s - p) (n - s) ≫ eqToHom (by
    congr 1
    all_goals ring)

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

private def tripleOrder12TermIso [HasCountableCoproducts C]
    (A : TripleComplex C) (n : ℤ) :
    tripleTotalizationOrder12Term A n ≅ tripleTotalTerm A n := by
  let hom : tripleTotalizationOrder12Term A n ⟶ tripleTotalTerm A n :=
    Sigma.desc (fun s =>
      Sigma.desc (fun p =>
        eqToHom (by congr 1; ring) ≫
          Sigma.ι (fun q : ℤ => A.obj p q (n - p - q)) (s - p) ≫
          Sigma.ι (fun r : ℤ => ∐ fun q : ℤ => A.obj r q (n - r - q)) p))
  let inv : tripleTotalTerm A n ⟶ tripleTotalizationOrder12Term A n :=
    Sigma.desc (fun p =>
      Sigma.desc (fun q =>
        eqToHom (by congr 1 <;> ring) ≫
          Sigma.ι (fun r : ℤ => A.obj r ((p + q) - r) (n - (p + q))) p ≫
          Sigma.ι (fun s : ℤ => ∐ fun r : ℤ => A.obj r (s - r) (n - s)) (p + q)))
  refine { hom := hom, inv := inv, hom_inv_id := ?_, inv_hom_id := ?_ }
  ·
    apply Sigma.hom_ext
    intro s
    apply Sigma.hom_ext
    intro p
    dsimp [hom, inv, tripleTotalizationOrder12Term, tripleTotalTerm]
    simp [Cofan.mk_ι_app, Category.assoc]
    rw [← eqToHom_naturality_assoc
      (fun t : ℤ => Sigma.ι (fun r : ℤ => A.obj r (t - r) (n - t)) p)
      (show s = p + (s - p) by ring)]
    rw [← eqToHom_naturality
      (fun t : ℤ =>
        Sigma.ι (fun s : ℤ => ∐ fun r : ℤ => A.obj r (s - r) (n - s)) t)
      (show s = p + (s - p) by ring)]
    simp
  · apply Sigma.hom_ext
    intro p
    apply Sigma.hom_ext
    intro q
    dsimp [hom, inv, tripleTotalizationOrder12Term, tripleTotalTerm]
    simp [Cofan.mk_ι_app, Category.assoc]
    rw [← eqToHom_naturality_assoc
      (fun t : ℤ => Sigma.ι (fun r : ℤ => A.obj p r (n - p - r)) t)
      (show q = p + q - p by ring)]
    simp

private theorem tripleOrder12Differential_comp_termIso [HasCountableCoproducts C]
    (A : TripleComplex C) (n : ℤ) :
    tripleOrder12Differential A n ≫ (tripleOrder12TermIso A (n + 1)).hom =
      (tripleOrder12TermIso A n).hom ≫ tripleTotalDifferential A n := by
  classical
  apply Sigma.hom_ext
  intro s
  apply Sigma.hom_ext
  intro p
  dsimp [tripleOrder12TermIso, tripleTotalizationOrder12Term,
    tripleOrder12Differential, tripleTotalTerm, tripleTotalDifferential]
  simp
  have h1 :
      eqToHom (by congr 1; ring) ≫
          tripleD1Component A n p (s - p) ≫
            Sigma.ι (fun q : ℤ => A.obj (p + 1) q
              (n + 1 - (p + 1) - q)) (s - p) ≫
            Sigma.ι (fun r : ℤ => ∐ fun q : ℤ => A.obj r q
              (n + 1 - r - q)) (p + 1) =
        tripleOrder12D1Component A n s p ≫
          eqToHom (by congr 1; ring_nf) ≫
            Sigma.ι (fun q : ℤ => A.obj (p + 1) q
              (n + 1 - (p + 1) - q)) (s + 1 - (p + 1)) ≫
            Sigma.ι (fun r : ℤ => ∐ fun q : ℤ => A.obj r q
              (n + 1 - r - q)) (p + 1) := by
    dsimp [tripleD1Component, tripleOrder12D1Component]
    simp only [Category.assoc]
    convert (eqToHom_naturality_assoc
      (fun r : ℤ => A.d1 p (s - p) r)
      (show n - s = n - p - (s - p) by ring)
      (eqToHom (by congr 1; ring) ≫
        Sigma.ι (fun q : ℤ => A.obj (p + 1) q
          (n + 1 - (p + 1) - q)) (s - p) ≫
            Sigma.ι (fun r : ℤ => ∐ fun q => A.obj r q
          (n + 1 - r - q)) (p + 1))).symm using 1;
      simp
    have hq :
        eqToHom (show A.obj (p + 1) (s - p) (n - s) =
          A.obj (p + 1) (s + 1 - (p + 1))
            (n + 1 - (p + 1) - (s + 1 - (p + 1))) by
          congr 1
          all_goals ring) ≫
            Sigma.ι (fun q : ℤ => A.obj (p + 1) q
              (n + 1 - (p + 1) - q)) (s + 1 - (p + 1)) ≫
            Sigma.ι (fun r : ℤ => ∐ fun q => A.obj r q
              (n + 1 - r - q)) (p + 1) =
          eqToHom (show A.obj (p + 1) (s - p) (n - s) =
            A.obj (p + 1) (s - p)
              (n + 1 - (p + 1) - (s - p)) by
            congr 1; ring) ≫
          Sigma.ι (fun q : ℤ => A.obj (p + 1) q
            (n + 1 - (p + 1) - q)) (s - p) ≫
            Sigma.ι (fun r : ℤ => ∐ fun q => A.obj r q
              (n + 1 - r - q)) (p + 1) := by
      have hnat :=
        eqToHom_naturality_assoc
          (fun q : ℤ => Sigma.ι (fun q : ℤ => A.obj (p + 1) q
            (n + 1 - (p + 1) - q)) q)
          (show s - p = s + 1 - (p + 1) by ring)
          (Sigma.ι (fun r : ℤ => ∐ fun q => A.obj r q
            (n + 1 - r - q)) (p + 1))
      convert (congrArg
        (fun f =>
          eqToHom (show A.obj (p + 1) (s - p) (n - s) =
            A.obj (p + 1) (s - p)
              (n + 1 - (p + 1) - (s - p)) by
            congr 1
            ring) ≫ f) hnat).symm using 1
      all_goals simp
    calc
      _ = A.d1 p (s - p) (n - s) ≫
          eqToHom (by congr 1; ring_nf) ≫
          Sigma.ι (fun q : ℤ => A.obj (p + 1) q
            (n + 1 - (p + 1) - q)) (s - p) ≫
          Sigma.ι (fun r : ℤ => ∐ fun q => A.obj r q
            (n + 1 - r - q)) (p + 1) := by
        simpa [Category.assoc] using
          congrArg (fun f => A.d1 p (s - p) (n - s) ≫ f) hq
      _ = _ := by
        convert (eqToHom_naturality_assoc
          (fun r : ℤ => A.d1 p (s - p) r)
          (show n - s = n - p - (s - p) by ring)
          (eqToHom (by congr 1; ring) ≫
            Sigma.ι (fun q : ℤ => A.obj (p + 1) q
              (n + 1 - (p + 1) - q)) (s - p) ≫
            Sigma.ι (fun r : ℤ => ∐ fun q => A.obj r q
              (n + 1 - r - q)) (p + 1))) using 1
        all_goals simp
  have h2 :
      eqToHom (by congr 1; ring) ≫
          tripleD2Component A n p (s - p) ≫
            Sigma.ι (fun q : ℤ => A.obj p q
              (n + 1 - p - q)) ((s - p) + 1) ≫
            Sigma.ι (fun r : ℤ => ∐ fun q : ℤ => A.obj r q
              (n + 1 - r - q)) p =
        tripleOrder12D2Component A n s p ≫
          eqToHom (by congr 1; ring) ≫
            Sigma.ι (fun q : ℤ => A.obj p q
              (n + 1 - p - q)) ((s + 1) - p) ≫
            Sigma.ι (fun r : ℤ => ∐ fun q : ℤ => A.obj r q
              (n + 1 - r - q)) p := by
    dsimp [tripleD2Component, tripleOrder12D2Component]
    simp only [Category.assoc]
    rw [← eqToHom_naturality_assoc
      (fun r : ℤ => A.d2 p (s - p) r)
      (show n - s = n - p - (s - p) by ring)]
    have hq :
        eqToHom (show A.obj p ((s - p) + 1) (n - s) =
          A.obj p ((s + 1) - p)
            (n + 1 - p - ((s + 1) - p)) by
          congr 1
          all_goals ring) ≫
            Sigma.ι (fun q : ℤ => A.obj p q
              (n + 1 - p - q)) ((s + 1) - p) ≫
            Sigma.ι (fun r : ℤ => ∐ fun q => A.obj r q
              (n + 1 - r - q)) p =
          eqToHom (show A.obj p ((s - p) + 1) (n - s) =
            A.obj p ((s - p) + 1)
              (n + 1 - p - ((s - p) + 1)) by
            congr 1; ring) ≫
            Sigma.ι (fun q : ℤ => A.obj p q
              (n + 1 - p - q)) ((s - p) + 1) ≫
            Sigma.ι (fun r : ℤ => ∐ fun q => A.obj r q
              (n + 1 - r - q)) p := by
      have hnat :=
        eqToHom_naturality_assoc
          (fun q : ℤ => Sigma.ι (fun q : ℤ => A.obj p q
            (n + 1 - p - q)) q)
          (show (s - p) + 1 = (s + 1) - p by ring)
          (Sigma.ι (fun r : ℤ => ∐ fun q => A.obj r q
            (n + 1 - r - q)) p)
      convert (congrArg
        (fun f =>
          eqToHom (show A.obj p ((s - p) + 1) (n - s) =
            A.obj p ((s - p) + 1)
              (n + 1 - p - ((s - p) + 1)) by
            congr 1; ring) ≫ f) hnat.symm) using 1
      all_goals simp
    simpa [Category.assoc] using
      (congrArg (fun f => A.d2 p (s - p) (n - s) ≫ f) hq).symm
  have h3 :
      eqToHom (by congr 1; ring) ≫
          tripleD3Component A n p (s - p) ≫
            Sigma.ι (fun q : ℤ => A.obj p q
              (n + 1 - p - q)) (s - p) ≫
            Sigma.ι (fun r : ℤ => ∐ fun q : ℤ => A.obj r q
              (n + 1 - r - q)) p =
        tripleOrder12D3Component A n s p ≫
          eqToHom (by congr 1; ring) ≫
            Sigma.ι (fun q : ℤ => A.obj p q
              (n + 1 - p - q)) (s - p) ≫
            Sigma.ι (fun r : ℤ => ∐ fun q : ℤ => A.obj r q
              (n + 1 - r - q)) p := by
    dsimp [tripleD3Component, tripleOrder12D3Component]
    simp only [Category.assoc]
    rw [← eqToHom_naturality_assoc
      (fun r : ℤ => A.d3 p (s - p) r)
      (show n - s = n - p - (s - p) by ring)]
    simp
  rw [h1, h2, h3]

theorem tripleOrder12Differential_comp_zero [HasCountableCoproducts C]
    (A : TripleComplex C) (n : ℤ) :
    tripleOrder12Differential A n ≫ tripleOrder12Differential A (n + 1) = 0 := by
  classical
  apply (cancel_mono (tripleOrder12TermIso A (n + 1 + 1)).hom).mp
  rw [zero_comp, Category.assoc, tripleOrder12Differential_comp_termIso]
  rw [← Category.assoc, tripleOrder12Differential_comp_termIso]
  rw [Category.assoc, tripleTotalDifferential_comp_zero, comp_zero]

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

def tripleTotalizationOrder12TermIso [HasCountableCoproducts C]
    (A : TripleComplex C) (n : ℤ) :
    tripleTotalizationOrder12Term A n ≅ tripleTotalTerm A n := by
  exact tripleOrder12TermIso A n

theorem tripleTotalization_associative [HasCountableCoproducts C]
    (A : TripleComplex C) (n : ℤ) :
    Nonempty (tripleTotalizationOrder12Term A n ≅ tripleTotalTerm A n) ∧
      Nonempty (tripleTotalizationOrder23Term A n ≅ tripleTotalTerm A n) := by
  constructor
  · exact ⟨tripleTotalizationOrder12TermIso A n⟩
  · exact ⟨Iso.refl _⟩

theorem tripleTotalization_associative_complex [HasCountableCoproducts C]
    (A : TripleComplex C) :
    Nonempty (tripleTotalizationOrder12Complex A ≅ tripleTotalization A) := by
  classical
  let e : ∀ n : ℤ,
      (tripleTotalizationOrder12Complex A).X n ≅ (tripleTotalization A).X n :=
    fun n => tripleTotalizationOrder12TermIso A n
  refine ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩
  intro n m hnm
  have hnm' : n + 1 = m := by
    simpa only [ComplexShape.up_Rel] using hnm
  subst m
  dsimp only [tripleTotalization, tripleTotalComplex, tripleTotalizationOrder12Complex]
  rw [dif_pos rfl, dif_pos rfl]
  simpa [e, tripleTotalizationOrder12TermIso] using
    (tripleOrder12Differential_comp_termIso A n).symm
/-! ## Shifts -/

def shiftedD1Component (A : DoubleComplex C) (a b p q : ℤ) :
    A.obj (p + a) (q + b) ⟶ A.obj ((p + 1) + a) (q + b) :=
  (a.negOnePow • A.d1 (p + a) (q + b)) ≫ eqToHom (by congr 1; ring)

def shiftedD2Component (A : DoubleComplex C) (a b p q : ℤ) :
    A.obj (p + a) (q + b) ⟶ A.obj (p + a) ((q + 1) + b) :=
  (b.negOnePow • A.d2 (p + a) (q + b)) ≫ eqToHom (by congr 1; ring)

theorem shifted_d1_sq (A : DoubleComplex C) (a b p q : ℤ) :
    shiftedD1Component A a b p q ≫ shiftedD1Component A a b (p + 1) q = 0 := by
  dsimp [shiftedD1Component]
  simp only [Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul]
  rw [← eqToHom_naturality_assoc (fun r : ℤ => A.d1 r (q + b))
    (show p + a + 1 = p + 1 + a by ring)]
  simpa [Category.assoc, smul_smul, Int.units_mul_self] using
    congrArg (fun f => f ≫ eqToHom (by congr 1; ring)) (A.d1_sq (p + a) (q + b))

theorem shifted_d2_sq (A : DoubleComplex C) (a b p q : ℤ) :
    shiftedD2Component A a b p q ≫ shiftedD2Component A a b p (q + 1) = 0 := by
  dsimp [shiftedD2Component]
  simp only [Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul]
  rw [← eqToHom_naturality_assoc (fun r : ℤ => A.d2 (p + a) r)
    (show q + b + 1 = q + 1 + b by ring)]
  simpa [Category.assoc, smul_smul, Int.units_mul_self] using
    congrArg (fun f => f ≫ eqToHom (by congr 1; ring)) (A.d2_sq (p + a) (q + b))

theorem shifted_comm (A : DoubleComplex C) (a b p q : ℤ) :
    shiftedD2Component A a b p q ≫ shiftedD1Component A a b p (q + 1) =
      shiftedD1Component A a b p q ≫ shiftedD2Component A a b (p + 1) q := by
  dsimp [shiftedD1Component, shiftedD2Component]
  simp only [Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul]
  rw [← eqToHom_naturality_assoc (fun r : ℤ => A.d1 (p + a) r)
    (show q + b + 1 = q + 1 + b by ring)]
  rw [← eqToHom_naturality_assoc (fun r : ℤ => A.d2 r (q + b))
    (show p + a + 1 = p + 1 + a by ring)]
  simpa [Category.assoc, smul_smul, mul_comm] using
    congrArg (fun f => f ≫ eqToHom (by ring_nf)) (A.comm (p + a) (q + b))

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
  dsimp [totalizationShiftSign]
  rw [show (p + 1) * b = p * b + b by ring, Int.negOnePow_add, mul_comm]

theorem totalizationShiftSign_second (p _q _a _b : ℤ) :
    totalizationShiftSign p (q + 1) a b =
      totalizationShiftSign p q a b := by
  rfl

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
  classical
  have e_hom_obj (n p : ℤ) :
      A.obj p (n + (a + b) - p) =
        (doubleComplexShift A a b).obj (p - a) (n - (p - a)) := by
    dsimp [doubleComplexShift]
    congr 1 <;> ring
  have e_inv_obj (n r : ℤ) :
      (doubleComplexShift A a b).obj r (n - r) =
        A.obj (r + a) (n + (a + b) - (r + a)) := by
    dsimp [doubleComplexShift]
    congr 1; ring
  let e : ∀ n : ℤ,
      (∐ fun p : ℤ => A.obj p (n + (a + b) - p)) ≅
        (∐ fun r : ℤ => (doubleComplexShift A a b).obj r (n - r)) :=
    fun n =>
      { hom := Sigma.desc (fun p =>
          totalizationShiftSign p (n + (a + b) - p) a b •
            (eqToHom (e_hom_obj n p) ≫
              Sigma.ι (fun r : ℤ =>
                (doubleComplexShift A a b).obj r (n - r)) (p - a)))
        inv := Sigma.desc (fun r =>
            totalizationShiftSign (r + a) (n + (a + b) - (r + a)) a b •
            (eqToHom (e_inv_obj n r) ≫
              Sigma.ι (fun p : ℤ => A.obj p (n + (a + b) - p)) (r + a)))
        hom_inv_id := by
          apply Sigma.hom_ext
          intro p
          rw [← Category.assoc, Sigma.ι_desc]
          rw [Linear.units_smul_comp]
          rw [Category.assoc, Sigma.ι_desc]
          rw [Linear.comp_units_smul]
          simp only [smul_smul]
          simp
          rw [← eqToHom_naturality
            (fun t : ℤ => Sigma.ι (fun p : ℤ => A.obj p (n + (a + b) - p)) t)
            (show p = p - a + a by ring_nf)]
          simp
        inv_hom_id := by
          apply Sigma.hom_ext
          intro r
          rw [← Category.assoc, Sigma.ι_desc]
          rw [Linear.units_smul_comp]
          rw [Category.assoc, Sigma.ι_desc]
          rw [Linear.comp_units_smul]
          simp only [smul_smul]
          simp
          rw [← eqToHom_naturality
            (fun t : ℤ => Sigma.ι
              (fun r : ℤ => (doubleComplexShift A a b).obj r (n - r)) t)
            (show r = r + a - a by ring_nf)]
          simp }
  have e_component_shift (k r : ℤ) :
      Sigma.ι (fun p : ℤ => A.obj p (k + (a + b) + 1 - p)) r ≫
          eqToHom (by congr 1; ring_nf) ≫
          (e (k + 1)).hom =
        totalizationShiftSign r (k + 1 + (a + b) - r) a b •
          (eqToHom (by congr 1; ring) ≫
            eqToHom (e_hom_obj (k + 1) r) ≫
            Sigma.ι (fun p : ℤ =>
              (doubleComplexShift A a b).obj p (k + 1 - p)) (r - a)) := by
    ring_nf
    dsimp [e]
    rw [eqToHom_naturality_assoc
      (fun d : ℤ => Sigma.ι (fun p : ℤ => A.obj p (d - p)) r)
      (show k + (a + b) + 1 = k + 1 + (a + b) by ring_nf)]
    rw [Sigma.ι_desc]
    rw [Linear.comp_units_smul]
    simp [totalizationShiftSign]
  have e_component_shift_expanded (k r : ℤ) :
      Sigma.ι (fun p : ℤ => A.obj p (k + (a + b) + 1 - p)) r ≫
          eqToHom (by congr 1; ring_nf) ≫
          Sigma.desc (fun p : ℤ =>
            totalizationShiftSign p (1 + k + a + b - p) a b •
              (eqToHom (e_hom_obj (k + 1) p) ≫
                Sigma.ι (fun r : ℤ =>
                  (doubleComplexShift A a b).obj r (k + 1 - r)) (p - a))) =
        totalizationShiftSign r (1 + k + a + b - r) a b •
          (eqToHom (by congr 1; ring) ≫
            eqToHom (e_hom_obj (k + 1) r) ≫
            Sigma.ι (fun p : ℤ =>
              (doubleComplexShift A a b).obj p (k + 1 - p)) (r - a)) := by
    convert e_component_shift k r using 1 <;> simp [e] <;> ring_nf

  let iso :
      (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (a + b)).obj
          (totalComplex A) ≅
        totalComplex (doubleComplexShift A a b) :=
    HomologicalComplex.Hom.isoOfComponents e (by
      intro n m hnm
      have hnm' : n + 1 = m := by
        simpa only [ComplexShape.up_Rel] using hnm
      subst m
      apply Sigma.hom_ext
      intro p
      have htransport_total {i j : ℤ} (h : i + 1 = j) :
          ((h ▸ (totalDifferential A i :
              (∐ fun p : ℤ => A.obj p (i - p)) ⟶
                ∐ fun p : ℤ => A.obj p (i + 1 - p))) :
            (∐ fun p : ℤ => A.obj p (i - p)) ⟶
              ∐ fun p : ℤ => A.obj p (j - p)) =
            totalDifferential A i ≫
              eqToHom (by
                congr 1; simp [h]) := by
        subst j; simp
      dsimp [e, totalComplex, CochainComplex.shiftFunctor]
      ring_nf
      simp only [if_pos, dif_pos]
      simp only [htransport_total]
      dsimp [totalDifferential]
      rw [← Category.assoc, Sigma.ι_desc]
      rw [Linear.units_smul_comp]
      rw [Category.assoc, Sigma.ι_desc]
      conv_rhs =>
        rw [← Category.assoc]
        congr
        rw [← Linear.comp_units_smul]
      simp only [Linear.comp_units_smul]
      conv_rhs =>
        rw [← Linear.units_smul_comp]
      conv_rhs =>
        rw [Linear.units_smul_comp]
        rw [← Category.assoc]
        rw [Sigma.ι_desc]
      simp only [Category.assoc, Linear.units_smul_comp, Preadditive.add_comp]
      conv_rhs =>
        rw [e_component_shift_expanded n (p + 1), e_component_shift_expanded n p]
      simp only [Category.assoc, totalD1Component, totalD2Component]
      simp [totalizationShiftSign, Int.negOnePow_add, smul_smul,
        mul_comm]
      ring_nf
      have hshift_d1_left :
          A.obj p (n + (a + b) - p) =
            (doubleComplexShift A a b).obj (p - a)
              (n + 1 - (p - a + 1)) := by
        calc
          A.obj p (n + (a + b) - p) =
              (doubleComplexShift A a b).obj (p - a) (n - (p - a)) :=
            e_hom_obj n p
          _ = (doubleComplexShift A a b).obj (p - a)
              (n + 1 - (p - a + 1)) := by
            congr 1; ring
      have hshift_d1_right :
          A.obj (p + 1) (n + (a + b) - p) =
            (doubleComplexShift A a b).obj (p + 1 - a)
              (n + 1 - (p + 1 - a)) := by
        calc
          A.obj (p + 1) (n + (a + b) - p) =
              A.obj (p + 1) ((n + 1) + (a + b) - (p + 1)) := by
            congr 1; ring
          _ = (doubleComplexShift A a b).obj (p + 1 - a)
              (n + 1 - (p + 1 - a)) := e_hom_obj (n + 1) (p + 1)
      have hshift_d1_left_unfolded :
          A.obj p (n + (a + b) - p) =
            A.obj (p - a + a) (n + 1 - (p - a + 1) + b) := by
        congr 1 <;> ring
      have hshift_d1_right_unfolded :
          A.obj (p + 1) (n + (a + b) - p) =
            A.obj (p + 1 - a + a) (n + 1 - (p + 1 - a) + b) := by
        congr 1 <;> ring
      have h1 :
          (b * p).negOnePow •
              ((eqToHom hshift_d1_left ≫
                (doubleComplexShift A a b).d1 (p - a)
                    (n + 1 - (p - a + 1))) ≫
                Sigma.ι (fun r : ℤ =>
                  (doubleComplexShift A a b).obj r (n + 1 - r))
                  (p - a + 1)) =
            (a.negOnePow * b.negOnePow * (b * (p + 1)).negOnePow) •
              ((A.d1 p (n + (a + b) - p) ≫
                eqToHom hshift_d1_right) ≫
                Sigma.ι (fun p : ℤ =>
                  (doubleComplexShift A a b).obj p (n + 1 - p))
                  (p + 1 - a)) := by
        change
          (b * p).negOnePow •
              ((eqToHom hshift_d1_left_unfolded ≫
                shiftedD1Component A a b (p - a)
                    (n + 1 - (p - a + 1))) ≫
                Sigma.ι (fun r : ℤ =>
                  A.obj (r + a) (n + 1 - r + b))
                  (p - a + 1)) =
            (a.negOnePow * b.negOnePow * (b * (p + 1)).negOnePow) •
              ((A.d1 p (n + (a + b) - p) ≫
                eqToHom hshift_d1_right_unfolded) ≫
                Sigma.ι (fun r : ℤ => A.obj (r + a) (n + 1 - r + b))
                  (p + 1 - a))
        unfold shiftedD1Component
        rw [← Category.assoc]
        rw [Linear.comp_units_smul]
        simp only [Linear.units_smul_comp, smul_smul]
        have hsign1 :
            (b * p).negOnePow * a.negOnePow =
              a.negOnePow * b.negOnePow * (b * (p + 1)).negOnePow := by
          rw [show b * (p + 1) = b * p + b by ring_nf, Int.negOnePow_add]
          have hb : b.negOnePow * b.negOnePow = (1 : ℤˣ) :=
            Int.units_mul_self b.negOnePow
          calc
            (b * p).negOnePow * a.negOnePow =
                a.negOnePow * (b * p).negOnePow := by ac_rfl
            _ = a.negOnePow * (b * p).negOnePow * 1 := by rw [mul_one]
            _ = a.negOnePow * (b * p).negOnePow *
                (b.negOnePow * b.negOnePow) := by rw [hb]
            _ = a.negOnePow * b.negOnePow *
                ((b * p).negOnePow * b.negOnePow) := by ac_rfl
        have hsign1' :
            (b * p).negOnePow * a.negOnePow =
              a.negOnePow * b.negOnePow * (b + b * p).negOnePow := by
          rw [show b + b * p = b * (p + 1) by ring_nf]
          exact hsign1
        rw [hsign1']
        rw [show b * (p + 1) = b + b * p by ring_nf]
        have hshift_d1_g :
            A.obj (p - a + a + 1)
                (n + 1 - (p - a + 1) + b) =
              (doubleComplexShift A a b).obj (p - a + 1)
                (n + 1 - (p - a + 1)) := by
          calc
            A.obj (p - a + a + 1)
                (n + 1 - (p - a + 1) + b) =
                A.obj (p + 1) ((n + 1) + (a + b) - (p + 1)) := by
              congr 1 <;> ring
            _ = (doubleComplexShift A a b).obj (p + 1 - a)
                (n + 1 - (p + 1 - a)) := e_hom_obj (n + 1) (p + 1)
            _ = (doubleComplexShift A a b).obj (p - a + 1)
                (n + 1 - (p - a + 1)) := by
              congr 1 <;> ring
        have hnat :=
          eqToHom_naturality_assoc
            (fun t : ℤ × ℤ => A.d1 t.1 t.2)
            (show (p, n + (a + b) - p) =
                (p - a + a, n + 1 - (p - a + 1) + b) by
              congr 1 <;> ring)
            (eqToHom hshift_d1_g ≫
              Sigma.ι (fun r : ℤ =>
                (doubleComplexShift A a b).obj r (n + 1 - r))
                (p - a + 1))
        have hι :=
          eqToHom_naturality
            (fun r : ℤ =>
              Sigma.ι (fun s : ℤ =>
                (doubleComplexShift A a b).obj s (n + 1 - s)) r)
            (show p + 1 - a = p - a + 1 by ring_nf)
        have hshift_d1_hq :
            A.obj (p + 1) (n + (a + b) - p) =
              (doubleComplexShift A a b).obj (p - a + 1)
                (n + 1 - (p - a + 1)) := by
          calc
            A.obj (p + 1) (n + (a + b) - p) =
                (doubleComplexShift A a b).obj (p + 1 - a)
                  (n + 1 - (p + 1 - a)) := hshift_d1_right
            _ = (doubleComplexShift A a b).obj (p - a + 1)
                  (n + 1 - (p - a + 1)) := by
              congr 1 <;> ring
        have hq :
            eqToHom (show A.obj (p + 1) (n + (a + b) - p) =
                (doubleComplexShift A a b).obj (p + 1 - a)
                  (n + 1 - (p + 1 - a)) by
              congr 1) ≫
                Sigma.ι (fun r : ℤ =>
                  (doubleComplexShift A a b).obj r (n + 1 - r))
                  (p + 1 - a) =
              eqToHom hshift_d1_hq ≫
                Sigma.ι (fun r : ℤ =>
                  (doubleComplexShift A a b).obj r (n + 1 - r))
                  (p - a + 1) := by
          have e1 : A.obj (p + 1) (n + (a + b) - p) =
              (doubleComplexShift A a b).obj (p + 1 - a)
                (n + 1 - (p + 1 - a)) := by
            congr 1
          simpa [Category.assoc, eqToHom_trans] using
            (congrArg
              (fun f =>
                eqToHom e1 ≫ f)
              hι)
        apply congrArg (fun f =>
          (a.negOnePow * b.negOnePow * (b + b * p).negOnePow) • f)
        convert hnat.symm using 1
        case e'_1 => simp [doubleComplexShift]
        case e'_2 => simp [Category.assoc, doubleComplexShift]
        case e'_3 =>
          simp only [Category.assoc]
          apply CategoryTheory.heq_comp (eq1 := rfl) (eq2 := rfl)
          case eq3 => rfl
          case H1 => rfl
          case H2 =>
            have hi :
                Sigma.ι (fun r : ℤ =>
                  (doubleComplexShift A a b).obj r (n + 1 - r)) (p + 1 - a) ≍
                  Sigma.ι (fun r : ℤ =>
                    (doubleComplexShift A a b).obj r (n + 1 - r)) (p - a + 1) := by
              have hq' := heq_of_eq hq
              simpa only [CategoryTheory.eqToHom_comp_heq_iff,
                CategoryTheory.heq_eqToHom_comp_iff] using hq'
            rw [CategoryTheory.eqToHom_comp_heq_iff]
            rw [← Category.assoc, eqToHom_trans]
            rw [CategoryTheory.heq_eqToHom_comp_iff]
            simpa [doubleComplexShift] using hi
      have hshift_d2_left_unfolded :
          A.obj p (n + (a + b) - p) =
            A.obj (p - a + a) (n - (p - a) + b) := by
        congr 1 <;> ring
      have hshift_d2_right_unfolded :
          A.obj (p - a + a) ((n - (p - a) + 1) + b) =
            A.obj (p - a + a) (n + 1 - (p - a) + b) := by
        congr 1; ring
      have hshift_d2_mid :
          (doubleComplexShift A a b).obj (p - a) (n - (p - a) + 1) =
            (doubleComplexShift A a b).obj (p - a) (n + 1 - (p - a)) := by
        congr 1; ring
      have hshift_d2_right :
          A.obj p ((n + (a + b) - p) + 1) =
            (doubleComplexShift A a b).obj (p - a) (n + 1 - (p - a)) := by
        calc
          A.obj p ((n + (a + b) - p) + 1) =
              A.obj p ((n + 1) + (a + b) - p) := by
            congr 1; ring
          _ = (doubleComplexShift A a b).obj (p - a)
              (n + 1 - (p - a)) := e_hom_obj (n + 1) p
      have hshift_d2_outer_unfolded :
          A.obj p ((n + (a + b) - p) + 1) =
            A.obj (p - a + a) (n + 1 - (p - a) + b) := by
        congr 1 <;> ring
      have hshift_d2_g :
          A.obj (p - a + a) ((n - (p - a) + b) + 1) =
            A.obj (p - a + a) (n + 1 - (p - a) + b) := by
        congr 1; ring
      have h2 :
          ((b * p).negOnePow * (p - a).negOnePow) •
              ((eqToHom (e_hom_obj n p) ≫
                (doubleComplexShift A a b).d2 (p - a)
                    (n - (p - a))) ≫
                eqToHom hshift_d2_mid ≫
                Sigma.ι (fun r : ℤ =>
                  (doubleComplexShift A a b).obj r (n + 1 - r))
                  (p - a)) =
            (a.negOnePow * b.negOnePow *
                (p.negOnePow * (b * p).negOnePow)) •
              ((A.d2 p (n + (a + b) - p) ≫
                eqToHom hshift_d2_right) ≫
                Sigma.ι (fun p : ℤ =>
                  (doubleComplexShift A a b).obj p (n + 1 - p))
                  (p - a)) := by
        change
          ((b * p).negOnePow * (p - a).negOnePow) •
              ((eqToHom hshift_d2_left_unfolded ≫
                shiftedD2Component A a b (p - a)
                    (n - (p - a))) ≫
                eqToHom hshift_d2_right_unfolded ≫
                Sigma.ι (fun r : ℤ => A.obj (r + a) (n + 1 - r + b))
                  (p - a)) =
            (a.negOnePow * b.negOnePow *
                (p.negOnePow * (b * p).negOnePow)) •
              ((A.d2 p (n + (a + b) - p) ≫
                eqToHom hshift_d2_outer_unfolded) ≫
                Sigma.ι (fun r : ℤ => A.obj (r + a) (n + 1 - r + b))
                  (p - a))
        unfold shiftedD2Component
        simp only [Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul]
        simp only [smul_smul]
        have hpa :
            (p - a).negOnePow = p.negOnePow * a.negOnePow := by
          rw [show p - a = p + (-a) by ring_nf, Int.negOnePow_add]
          simp
        have hsign2 :
            (b * p).negOnePow * (p - a).negOnePow * b.negOnePow =
              a.negOnePow * b.negOnePow *
                (p.negOnePow * (b * p).negOnePow) := by
          rw [hpa]
          calc
            (b * p).negOnePow *
                (p.negOnePow * a.negOnePow) * b.negOnePow =
                (b * p + (p + a) + b).negOnePow := by
              simp only [Int.negOnePow_add, mul_assoc]
            _ = (a + b + (p + b * p)).negOnePow := by
              congr 1; ring_nf
            _ = a.negOnePow * b.negOnePow *
                (p.negOnePow * (b * p).negOnePow) := by
              simp only [Int.negOnePow_add, mul_assoc]
        rw [hsign2]
        apply congrArg (fun f =>
          (a.negOnePow * b.negOnePow *
            (p.negOnePow * (b * p).negOnePow)) • f)
        have hnat :=
          eqToHom_naturality_assoc
            (fun t : ℤ × ℤ => A.d2 t.1 t.2)
            (show (p, n + (a + b) - p) =
                (p - a + a, n - (p - a) + b) by
              congr 1 <;> ring)
            (eqToHom hshift_d2_g ≫
                Sigma.ι (fun r : ℤ => A.obj (r + a) (n + 1 - r + b))
                (p - a))
        simpa [Category.assoc, eqToHom_trans] using hnat.symm
      have h1' := h1
      simp only [Category.assoc] at h1'
      have h2' := h2
      simp only [Category.assoc] at h2'
      rw [h1', h2']
      rw [show b * (p + 1) = b + b * p by ring_nf]
      )
  refine ⟨{ iso := iso, component_formula := ?_ }⟩
  intro n p
  dsimp [iso, e, HomologicalComplex.Hom.isoOfComponents, totalComplex,
    CochainComplex.shiftFunctor]
  rw [Sigma.ι_desc]


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
  have hnm' : n + 1 = m := by
    simpa only [ComplexShape.up_Rel] using hnm
  subst m
  apply Sigma.hom_ext
  intro p
  simp [totalComplex, totalMapComponent, totalDifferential, Category.assoc]
  have h1 :
      f.f p (n - p) ≫ totalD1Component B n p ≫
          Sigma.ι (fun r : ℤ => B.obj r (n + 1 - r)) (p + 1) =
        totalD1Component A n p ≫ f.f (p + 1) (n + 1 - (p + 1)) ≫
          Sigma.ι (fun r : ℤ => B.obj r (n + 1 - r)) (p + 1) := by
    dsimp [totalD1Component]
    simp only [Category.assoc]
    conv_rhs =>
      rw [← eqToHom_naturality_assoc
        (fun q : ℤ => f.f (p + 1) q)
        (show n - p = n + 1 - (p + 1) by ring)]
    simpa [Category.assoc] using
      congrArg (fun k => k ≫ eqToHom (by congr 1; ring) ≫
        Sigma.ι (fun r : ℤ => B.obj r (n + 1 - r)) (p + 1))
        (f.comm1 p (n - p)).symm
  have h2core :
      f.f p (n - p) ≫ totalD2Component B n p ≫
          Sigma.ι (fun r : ℤ => B.obj r (n + 1 - r)) p =
        totalD2Component A n p ≫ f.f p (n + 1 - p) ≫
          Sigma.ι (fun r : ℤ => B.obj r (n + 1 - r)) p := by
    dsimp [totalD2Component]
    simp only [Category.assoc]
    conv_rhs =>
      rw [← eqToHom_naturality_assoc
        (fun q : ℤ => f.f p q)
        (show n - p + 1 = n + 1 - p by ring)]
    simpa [Category.assoc] using
      congrArg (fun k => k ≫ eqToHom (by congr 1; ring) ≫
        Sigma.ι (fun r : ℤ => B.obj r (n + 1 - r)) p)
        (f.comm2 p (n - p)).symm
  have h2 := congrArg (fun k => p.negOnePow • k) h2core
  rw [h1]
  simpa [Category.assoc, Linear.units_smul_comp] using h2

def totalMap [HasCountableCoproducts C]
    {A B : DoubleComplex C} (f : DoubleComplexMap A B) :
    totalComplex A ⟶ totalComplex B where
  f n := totalMapComponent f n
  comm' n m hnm := totalMapComponent_comm f n m hnm

theorem totalMap_id [HasCountableCoproducts C] (A : DoubleComplex C) :
    totalMap (𝟙 A) = 𝟙 (totalComplex A) := by
  apply HomologicalComplex.Hom.ext
  ext n
  apply Sigma.hom_ext
  intro p
  simp only [totalMap, totalMapComponent, Sigma.ι_desc]
  dsimp [totalComplex]
  have h_id : (𝟙 A : DoubleComplexMap A A).f p (n - p) = 𝟙 _ := rfl
  rw [h_id]
  simp

theorem totalMap_comp [HasCountableCoproducts C]
    {A B D : DoubleComplex C} (f : A ⟶ B) (g : B ⟶ D) :
    totalMap (f ≫ g) = totalMap f ≫ totalMap g := by
  apply HomologicalComplex.Hom.ext
  ext n
  apply Sigma.hom_ext
  intro p
  simp [totalMap, totalMapComponent, totalComplex,
    HomologicalComplex.comp_f, Category.assoc]
  have hcomp :
      (f ≫ g : DoubleComplexMap A D).f p (n - p) =
        f.f p (n - p) ≫ g.f p (n - p) := rfl
  rw [hcomp]
  simp [Category.assoc]

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

private theorem vertical_total_homotopy_data [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f g : DoubleComplexMap A B}
    (h : VerticalHomotopy f g) :
    ∃ H : Homotopy (totalMap f) (totalMap g),
      ∀ n : ℤ,
        H.hom n (n + (-1 : ℤ)) =
          verticalTotalHomotopyComponent h.h n := by
  let shiftEq : ∀ n m : ℤ, m = n - 1 →
      (totalComplex B).X (n - 1) = (totalComplex B).X m :=
    fun n m hm => by
      subst m
      rfl
  let H : ∀ n m : ℤ, (totalComplex A).X n ⟶ (totalComplex B).X m :=
    fun n m => dite (m = n - 1)
      (fun hm => verticalTotalHomotopyComponent h.h n ≫
        eqToHom (shiftEq n m hm))
      (fun _ => 0)
  refine ⟨{ hom := H, zero := ?_, comm := ?_ }, ?_⟩
  · intro i j hij
    dsimp [H]
    split_ifs with h'
    · exfalso
      apply hij
      change j + 1 = i
      omega
    · rfl
  · intro i
    change totalMapComponent f i = dNext i H + prevD i H + totalMapComponent g i
    have hd :
        dNext i H =
          (totalComplex A).d i (i + 1) ≫ H (i + 1) i :=
      dNext_eq H (by simp [ComplexShape.up])
    have hp :
        prevD i H =
          H i (i - 1) ≫ (totalComplex B).d (i - 1) i :=
      prevD_eq H (by simp [ComplexShape.up])
    rw [hd, hp]
    have hnextEq :
        (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) =
          ∐ fun r : ℤ => B.obj r (i - r) := by
      congr 1
      funext r
      ring
    have hnext :
        H (i + 1) i =
          verticalTotalHomotopyComponent h.h (i + 1) ≫
            (eqToHom hnextEq :
              (totalComplex B).X (i + 1 - 1) ⟶ (totalComplex B).X i) := by
      dsimp [H]
      split_ifs with hi
      · rfl
      · exfalso
        apply hi
        ring
    have hprev :
        H i (i - 1) =
          verticalTotalHomotopyComponent h.h i ≫
            (eqToHom (shiftEq i (i - 1) (by ring)) :
              (totalComplex B).X (i - 1) ⟶ (totalComplex B).X (i - 1)) := by
      dsimp [H]
      split_ifs with hi
      · rfl
      · exact (hi rfl).elim
    rw [hnext, hprev]
    simp
    rw [← sub_eq_iff_eq_add]
    apply Sigma.hom_ext
    intro p
    have hsub :=
      Preadditive.comp_sub (Sigma.ι (fun r : ℤ => A.obj r (i - r)) p)
        (totalMapComponent f i) (totalMapComponent g i)
    calc
      _ = Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫ totalMapComponent f i -
          Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫ totalMapComponent g i := hsub
      _ = _ := by
        have hadd :
            Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                ((totalComplex A).d i (i + 1) ≫
                    verticalTotalHomotopyComponent h.h (i + 1) ≫
                    (eqToHom hnextEq :
                      (totalComplex B).X (i + 1 - 1) ⟶ (totalComplex B).X i) +
                  verticalTotalHomotopyComponent h.h i ≫
                    (totalComplex B).d (i - 1) i) =
              Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                  ((totalComplex A).d i (i + 1) ≫
                    verticalTotalHomotopyComponent h.h (i + 1) ≫
                    (eqToHom hnextEq :
                      (totalComplex B).X (i + 1 - 1) ⟶ (totalComplex B).X i)) +
                Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                  (verticalTotalHomotopyComponent h.h i ≫
                    (totalComplex B).d (i - 1) i) := by
          apply Preadditive.comp_add
        have hfirst :
            (Sigma.ι (fun r : ℤ => A.obj r (i - r)) p :
                A.obj p (i - p) ⟶ (totalComplex A).X i) ≫ totalMapComponent f i -
                (Sigma.ι (fun r : ℤ => A.obj r (i - r)) p :
                  A.obj p (i - p) ⟶ (totalComplex A).X i) ≫ totalMapComponent g i =
              (Sigma.ι (fun r : ℤ => A.obj r (i - r)) p :
                A.obj p (i - p) ⟶ (totalComplex A).X i) ≫
                  ((totalComplex A).d i (i + 1) ≫
                    verticalTotalHomotopyComponent h.h (i + 1) ≫
                    (eqToHom hnextEq :
                      (totalComplex B).X (i + 1 - 1) ⟶ (totalComplex B).X i)) +
                (Sigma.ι (fun r : ℤ => A.obj r (i - r)) p :
                  A.obj p (i - p) ⟶ (totalComplex A).X i) ≫
                  (verticalTotalHomotopyComponent h.h i ≫
                    (totalComplex B).d (i - 1) i) := by
          simp [totalMapComponent,
            verticalTotalHomotopyComponent]
          have hhom :
              f.f p (i - p) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) p -
                  g.f p (i - p) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) p =
                h.h p (i - p) ≫ B.d2 p (i - p - 1) ≫
                    eqToHom (by congr 1; lia) ≫
                    (Sigma.ι (fun r : ℤ => B.obj r (i - r)) p :
                      B.obj p (i - p) ⟶ (totalComplex B).X i) +
                  A.d2 p (i - p) ≫ h.h p (i - p + 1) ≫
                    eqToHom (by congr 1; lia) ≫
                    (Sigma.ι (fun r : ℤ => B.obj r (i - r)) p :
                      B.obj p (i - p) ⟶ (totalComplex B).X i) := by
            simpa [Category.assoc, totalComplex] using
              congrArg (fun k =>
                k ≫ Sigma.ι (fun r : ℤ => B.obj r (i - r)) p)
                (h.homotopy p (i - p))
          have hmap :
              h.h p (i - p) ≫ eqToHom (by congr 1; ring) ≫
                  totalD1Component B (i - 1) p ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                  (eqToHom (by congr 1; funext r; ring) :
                    (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                      (totalComplex B).X i) =
                totalD1Component A i p ≫
                  h.h (p + 1) (i + 1 - (p + 1)) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                  (eqToHom (by congr 1; funext r; ring) :
                    (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                      (totalComplex B).X i) := by
            dsimp [totalD1Component]
            simp only [Category.assoc]
            rw [← eqToHom_naturality_assoc (fun q : ℤ => B.d1 p q)
              (show i - p - 1 = i - 1 - p by ring)]
            conv_rhs =>
              rw [← eqToHom_naturality_assoc
                (fun q : ℤ => h.h (p + 1) q)
                (show i - p = i + 1 - (p + 1) by ring)]
            simpa [Category.assoc, eqToHom_trans] using congrArg (fun k =>
                k ≫ eqToHom (by congr 1; ring) ≫
                Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                (eqToHom (by congr 1; funext r; ring) :
                  (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                    (totalComplex B).X i))
              (h.map p (i - p))
          have e1 :
              (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) =
                (totalComplex B).X i := by
            change (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) =
              ∐ fun r : ℤ => B.obj r (i - r)
            congr 1
          have e2 :
              (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) =
                (totalComplex B).X i := by
            change (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) =
              ∐ fun r : ℤ => B.obj r (i - r)
            congr 1
            funext r
            ring
          have hι :
              eqToHom (show B.obj (p + 1) (i - 1 + 1 - (p + 1)) =
                B.obj (p + 1) (i + 1 - 1 - (p + 1)) by congr 1; ring) ≫
                Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1) ≫
                (eqToHom (by
                  dsimp [totalComplex]
                  congr 1
                  ) :
                  (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) ⟶
                    (totalComplex B).X i) =
              Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                (eqToHom (by
                  dsimp [totalComplex]
                  congr 1
                  funext r
                  ring) :
                  (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                    (totalComplex B).X i) := by
            have e1 :
                (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) =
                  (totalComplex B).X i := by
              change (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) =
                ∐ fun r : ℤ => B.obj r (i - r)
              congr 1
            have e2 :
                (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) =
                  (totalComplex B).X i := by
              change (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) =
                ∐ fun r : ℤ => B.obj r (i - r)
              congr 1
              funext r
              ring
            change
              eqToHom (show B.obj (p + 1) (i - 1 + 1 - (p + 1)) =
                B.obj (p + 1) (i + 1 - 1 - (p + 1)) by congr 1; ring) ≫
                Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1) ≫
                  eqToHom e1 =
                Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                  eqToHom e2
            have hfamily :
                (fun r : ℤ => B.obj r (i - 1 + 1 - r)) =
                  (fun r : ℤ => B.obj r (i + 1 - 1 - r)) := by
              funext r
              congr 1
              ring
            have hcoprod :
                (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) =
                  (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) :=
              congrArg (fun F : ℤ → C => ∐ F) hfamily
            have hι0 :
                Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                    eqToHom hcoprod =
                  eqToHom (congrFun hfamily (p + 1)) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1) := by
              have hι0' := eqToHom_naturality
                (fun F : ℤ → C => Sigma.ι F (p + 1)) hfamily
              simpa only [CategoryTheory.eqToHom_comp_heq_iff,
                CategoryTheory.heq_eqToHom_comp_iff] using hι0'
            calc
              _ = Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                    eqToHom hcoprod ≫
                    eqToHom e1 := by
                simpa only [Category.assoc] using
                  (congrArg (fun k => k ≫ eqToHom e1) hι0).symm
              _ = _ := by
                congr 1
                rw [eqToHom_trans]
          have eA :
              B.obj (p + 1) (i + 1 - (p + 1) - 1) =
                B.obj (p + 1) (i + 1 - 1 - (p + 1)) := by
            congr 1
            ring
          have eB :
              B.obj (p + 1) (i + 1 - (p + 1) - 1) =
                B.obj (p + 1) (i - 1 + 1 - (p + 1)) := by
            congr 1
            ring
          have eC :
              B.obj (p + 1) (i - 1 + 1 - (p + 1)) =
                B.obj (p + 1) (i + 1 - 1 - (p + 1)) := by
            congr 1
            ring
          have eL :
              B.obj p (i - p - 1) = B.obj p (i - 1 - p) := by
            congr 1
            ring
          have hι_named :
              eqToHom eC ≫
                Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1) ≫
                  eqToHom e1 =
              Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                eqToHom e2 := by
            exact hι
          have hmap' :
              h.h p (i - p) ≫ eqToHom eL ≫
                  totalD1Component B (i - 1) p ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                  eqToHom e2 =
                totalD1Component A i p ≫
                  h.h (p + 1) (i + 1 - (p + 1)) ≫
                  eqToHom eA ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1) ≫
                  eqToHom e1 := by
            have htransport : eqToHom eB ≫ eqToHom eC = eqToHom eA := by
              rw [eqToHom_trans]
            have hleft :
                totalD1Component A i p ≫
                    h.h (p + 1) (i + 1 - (p + 1)) ≫
                    eqToHom eA ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1) ≫
                    eqToHom e1 =
                  totalD1Component A i p ≫
                    h.h (p + 1) (i + 1 - (p + 1)) ≫
                    eqToHom eB ≫ eqToHom eC ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1) ≫
                    eqToHom e1 := by
              simpa only [Category.assoc] using
                congrArg (fun k =>
                  totalD1Component A i p ≫
                    h.h (p + 1) (i + 1 - (p + 1)) ≫ k ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1) ≫
                    eqToHom e1) htransport.symm
            have hright :
                totalD1Component A i p ≫
                    h.h (p + 1) (i + 1 - (p + 1)) ≫
                    eqToHom eA ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1) ≫
                    eqToHom e1 =
                  totalD1Component A i p ≫
                    h.h (p + 1) (i + 1 - (p + 1)) ≫
                    eqToHom eB ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                    eqToHom e2 := by
              calc
                _ = totalD1Component A i p ≫
                    h.h (p + 1) (i + 1 - (p + 1)) ≫
                    eqToHom eB ≫ eqToHom eC ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1) ≫
                    eqToHom e1 := hleft
                _ = _ := by
                  simpa only [Category.assoc] using
                    congrArg (fun k : B.obj (p + 1) (i - 1 + 1 - (p + 1)) ⟶
                      (totalComplex B).X i =>
                      totalD1Component A i p ≫
                        h.h (p + 1) (i + 1 - (p + 1)) ≫ eqToHom eB ≫ k)
                      hι_named
            calc
              _ = totalD1Component A i p ≫
                  h.h (p + 1) (i + 1 - (p + 1)) ≫
                  eqToHom eB ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                  eqToHom e2 := by simpa only [Category.assoc] using hmap
              _ = _ := hright.symm
          have hprevEq :
              (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) =
                ∐ fun r : ℤ => B.obj r (i - r) := by
            congr 1
            funext r
            ring
          have hmapRaw :
              h.h p (i - p) ≫ eqToHom eL ≫
                  totalD1Component B (i - 1) p ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                  (eqToHom hprevEq :
                    (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                      ∐ fun r : ℤ => B.obj r (i - r)) =
                totalD1Component A i p ≫
                  h.h (p + 1) (i + 1 - (p + 1)) ≫ eqToHom eA ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1) ≫
                  (eqToHom hnextEq :
                    (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) ⟶
                      ∐ fun r : ℤ => B.obj r (i - r)) := by
            simpa only [totalComplex] using hmap'
          have hmapRaw_smul :=
            congrArg (fun k => (-p.negOnePow) • k) hmapRaw
          have hi : i - 1 + 1 = i := by omega
          have hmapRaw_smul' :
              -p.negOnePow •
                  h.h p (i - p) ≫ eqToHom eL ≫
                    totalD1Component B (i - 1) p ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                    (eqToHom (by congr 1) :
                      (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                        ∐ fun r : ℤ => B.obj r (i - r)) =
                -p.negOnePow •
                  totalD1Component A i p ≫
                    h.h (p + 1) (i + 1 - (p + 1)) ≫ eqToHom eA ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1) ≫
                    (eqToHom hnextEq :
                      (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) ⟶
                        ∐ fun r : ℤ => B.obj r (i - r)) := by
            simpa only using hmapRaw_smul
          have htransport_prev {j : ℤ} (hij : i - 1 + 1 = j) :
              ((hij ▸ (Sigma.desc (fun p : ℤ =>
                totalD1Component B (i - 1) p ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) +
                p.negOnePow •
                  (totalD2Component B (i - 1) p ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) p)) :
                (∐ fun r : ℤ => B.obj r (i - 1 - r)) ⟶
                  ∐ fun r : ℤ => B.obj r (i - 1 + 1 - r))) :
                (∐ fun r : ℤ => B.obj r (i - 1 - r)) ⟶
                  ∐ fun r : ℤ => B.obj r (j - r)) =
                (Sigma.desc fun p : ℤ =>
                  totalD1Component B (i - 1) p ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) +
                  p.negOnePow •
                    (totalD2Component B (i - 1) p ≫
                      Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) p)) ≫
                  eqToHom (by congr 1; simp [hij]) := by
            subst j
            simp
          have hprev_desc :
              (Sigma.ι (fun r : ℤ => B.obj r (i - 1 - r)) p :
                B.obj p (i - 1 - p) ⟶ (totalComplex B).X (i - 1)) ≫
                  (totalComplex B).d (i - 1) i =
                totalD1Component B (i - 1) p ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                      (eqToHom hprevEq :
                        (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                          ∐ fun r : ℤ => B.obj r (i - r)) +
                  p.negOnePow •
                    (totalD2Component B (i - 1) p ≫
                      Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) p ≫
                        (eqToHom hprevEq :
                          (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                            ∐ fun r : ℤ => B.obj r (i - r))) := by
            have htransport_total {j : ℤ} (hij : i - 1 + 1 = j) :
                ((hij ▸ (totalDifferential B (i - 1) :
                    (∐ fun r : ℤ => B.obj r (i - 1 - r)) ⟶
                      ∐ fun r : ℤ => B.obj r (i - 1 + 1 - r))) :
                  (∐ fun r : ℤ => B.obj r (i - 1 - r)) ⟶
                    ∐ fun r : ℤ => B.obj r (j - r)) =
                  totalDifferential B (i - 1) ≫
                    eqToHom (by congr 1; simp [hij]) := by
              subst j
              simp
            dsimp [totalComplex]
            rw [dif_pos (by omega)]
            rw [htransport_total (by omega)]
            dsimp [totalDifferential]
            rw [← Category.assoc, Sigma.ι_desc]
            simp only [Category.assoc, Preadditive.add_comp,
              Linear.units_smul_comp]
          change
            (f.f p (i - p) ≫
                (Sigma.ι (fun r : ℤ => B.obj r (i - r)) p :
                  B.obj p (i - p) ⟶ ∐ fun r : ℤ => B.obj r (i - r)) -
              g.f p (i - p) ≫
                (Sigma.ι (fun r : ℤ => B.obj r (i - r)) p :
                  B.obj p (i - p) ⟶ ∐ fun r : ℤ => B.obj r (i - r))) = _
          dsimp [totalComplex]
          rw [if_pos (by ring), dif_pos (by ring)]
          dsimp [totalDifferential]
          conv_rhs =>
            lhs
            rw [← Category.assoc
              (Sigma.ι (fun r : ℤ => A.obj r (i - r)) p) _ _]
            rw [Sigma.ι_desc]
          rw [hhom]
          simp only [Category.assoc, Preadditive.add_comp,
            Linear.units_smul_comp]
          conv_rhs =>
            lhs
            lhs
            rw [← Category.assoc
              (Sigma.ι (fun r : ℤ => A.obj r (i + 1 - r)) (p + 1)) _ _]
            rw [Sigma.ι_desc]
            simp only [Int.negOnePow_succ, Linear.units_smul_comp,
              Linear.comp_units_smul, Category.assoc]
            rw [← hmapRaw_smul']
          have htransport_prev' := htransport_prev (j := i) hi
          have heq_prev :
              eqToHom (by congr 1) =
                (eqToHom hprevEq :
                  (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                    ∐ fun r : ℤ => B.obj r (i - r)) := by
            congr 1
          rw [heq_prev] at htransport_prev'
          conv_rhs =>
            rhs
            rhs
            rw [htransport_prev']
            simp only [Category.assoc]
            rw [← Category.assoc
              (Sigma.ι (fun r : ℤ => B.obj r (i - 1 - r)) p) _ _]
            rw [Sigma.ι_desc]
            simp only [Category.assoc, Preadditive.add_comp,
              Linear.units_smul_comp]
          simp only [Preadditive.comp_add, smul_add, smul_smul,
            Linear.comp_units_smul, one_smul,
            Int.units_mul_self]
          have hA2 :
              A.d2 p (i - p) ≫ h.h p (i - p + 1) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - r)) p =
                totalD2Component A i p ≫ h.h p (i + 1 - p) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) p ≫
                  (eqToHom hnextEq :
                    (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) ⟶
                      ∐ fun r : ℤ => B.obj r (i - r)) := by
            dsimp [totalD2Component]
            simp only [Category.assoc]
            conv_rhs =>
              rw [← eqToHom_naturality_assoc (fun q : ℤ => h.h p q)
                (show i - p + 1 = i + 1 - p by ring)]
            change
              A.d2 p (i - p) ≫ h.h p (i - p + 1) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - r)) p =
                A.d2 p (i - p) ≫ h.h p (i - p + 1) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) p ≫
                    eqToHom hnextEq
            have hnat := eqToHom_naturality_assoc
              (fun q : ℤ => Sigma.ι (fun r : ℤ => B.obj r (q - r)) p)
              (show i = i + 1 - 1 by ring)
              (eqToHom hnextEq)
            have hcoprod :
                (∐ fun r : ℤ => B.obj r (i - r)) =
                  ∐ fun r : ℤ => B.obj r (i + 1 - 1 - r) := by
              congr 1
              funext r
              ring
            have hcomp : eqToHom hcoprod ≫ eqToHom hnextEq =
                eqToHom (show
                  (∐ fun r : ℤ => B.obj r (i - r)) =
                    ∐ fun r : ℤ => B.obj r (i - r) by rfl) := by
              rw [eqToHom_trans]
            simpa [Category.assoc, hcomp, eqToHom_refl, Category.comp_id] using
              congrArg (fun k =>
                A.d2 p (i - p) ≫ h.h p (i - p + 1) ≫
                  eqToHom (by congr 1 <;> ring) ≫ k) hnat
          have hB2 :
              h.h p (i - p) ≫ B.d2 p (i - p - 1) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - r)) p =
                h.h p (i - p) ≫ eqToHom eL ≫
                  totalD2Component B (i - 1) p ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) p ≫
                  (eqToHom hprevEq :
                    (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                      ∐ fun r : ℤ => B.obj r (i - r)) := by
            dsimp [totalD2Component]
            simp only [Category.assoc]
            rw [← eqToHom_naturality_assoc (fun q : ℤ => B.d2 p q)
              (show i - p - 1 = i - 1 - p by ring)]
            have hnat := eqToHom_naturality_assoc
              (fun q : ℤ => Sigma.ι (fun r : ℤ => B.obj r (q - r)) p)
              (show i = i - 1 + 1 by ring)
              (eqToHom hprevEq)
            have hcoprod :
                (∐ fun r : ℤ => B.obj r (i - r)) =
                  ∐ fun r : ℤ => B.obj r (i - 1 + 1 - r) := by
              congr 1
              funext r
              ring
            have hcomp : eqToHom hcoprod ≫ eqToHom hprevEq =
                eqToHom (show
                  (∐ fun r : ℤ => B.obj r (i - r)) =
                    ∐ fun r : ℤ => B.obj r (i - r) by rfl) := by
              rw [eqToHom_trans]
            simpa [Category.assoc, hcomp, eqToHom_refl, Category.comp_id] using
              congrArg (fun k =>
                h.h p (i - p) ≫ B.d2 p (i - p - 1) ≫
                  eqToHom (by congr 1 <;> ring) ≫ k) hnat
          change @Eq (A.obj p (i - p) ⟶ ∐ fun r : ℤ => B.obj r (i - r)) _ _
          rw [hA2, hB2]
          conv_rhs =>
            lhs
            rhs
            rw [← Category.assoc
              (Sigma.ι (fun r : ℤ => A.obj r (i + 1 - r)) p) _ _]
            rw [Sigma.ι_desc]
            rw [← Category.assoc]
            rw [Linear.comp_units_smul]
            rw [Linear.units_smul_comp]
          simp only [smul_smul, Int.units_mul_self, one_smul]
          simp only [Category.assoc]
          have heq_eL :
              (eqToHom (by congr 1) :
                B.obj p (i - p - 1) ⟶ B.obj p (i - 1 - p)) =
                (eqToHom eL : B.obj p (i - p - 1) ⟶ B.obj p (i - 1 - p)) := by
            congr 1
          rw [heq_eL]
          change @Eq (A.obj p (i - p) ⟶ ∐ fun r : ℤ => B.obj r (i - r)) _ _
          have hneg :
              (-p.negOnePow) •
                  (h.h p (i - p) ≫ eqToHom eL ≫
                    totalD1Component B (i - 1) p ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                    (eqToHom hprevEq :
                      (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                        ∐ fun r : ℤ => B.obj r (i - r))) =
                -(p.negOnePow •
                  (h.h p (i - p) ≫ eqToHom eL ≫
                    totalD1Component B (i - 1) p ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p + 1) ≫
                    (eqToHom hprevEq :
                      (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                        ∐ fun r : ℤ => B.obj r (i - r)))) := by
            exact Units.neg_smul (R := ℤ) p.negOnePow _
          rw [hneg]
          abel
        exact hfirst.trans hadd.symm
  · intro n
    change H n (n - 1) = verticalTotalHomotopyComponent h.h n
    dsimp [H]
    rw [if_pos (by ring)]
    simp
/-
  let H : ∀ n m : ℤ, (totalComplex A).X n ⟶ (totalComplex B).X m :=
    fun n m => dite (m = n - 1)
      (fun hm => verticalTotalHomotopyComponent h.h n ≫
        eqToHom (by subst m; rfl))
      (fun _ => 0)
  refine ⟨{ hom := H, zero := ?_, comm := ?_ }, ?_⟩
  · intro i j hij
    dsimp [H]
    split_ifs with h'
    · exfalso
      apply hij
      change j + 1 = i
      omega
    · rfl
  · intro i
    change totalMapComponent f i = dNext i H + prevD i H + totalMapComponent g i
    have hd :
        dNext i H =
          (totalComplex A).d i (i + 1) ≫ H (i + 1) i :=
      dNext_eq H (by simp [ComplexShape.up])
    have hp :
        prevD i H =
          H i (i - 1) ≫ (totalComplex B).d (i - 1) i :=
      prevD_eq H (by simp [ComplexShape.up])
    rw [hd, hp]
    simp [H]
    rw [← sub_eq_iff_eq_add]
    apply Sigma.hom_ext
    intro p
    have hsub :=
      Preadditive.comp_sub (Sigma.ι (fun r : ℤ => A.obj r (i - r)) p)
        (totalMapComponent f i) (totalMapComponent g i)
    calc
      _ = Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫ totalMapComponent f i -
          Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫ totalMapComponent g i := hsub
      _ = _ := by
        have hadd :
            Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                ((totalComplex A).d i (i + 1) ≫
                    verticalTotalHomotopyComponent h.h (i + 1) ≫
                    eqToHom (by congr 1; lia) +
                  verticalTotalHomotopyComponent h.h i ≫
                    (totalComplex B).d (i - 1) i) =
              Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                  ((totalComplex A).d i (i + 1) ≫
                    verticalTotalHomotopyComponent h.h (i + 1) ≫
                    eqToHom (by congr 1; lia)) +
                Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                  (verticalTotalHomotopyComponent h.h i ≫
                    (totalComplex B).d (i - 1) i) := by
          apply Preadditive.comp_add
        have hfirst :
            Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫ totalMapComponent f i -
                Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫ totalMapComponent g i =
              Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                  ((totalComplex A).d i (i + 1) ≫
                    verticalTotalHomotopyComponent h.h (i + 1) ≫
                    eqToHom (by congr 1; lia)) +
                Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                  (verticalTotalHomotopyComponent h.h i ≫
                    (totalComplex B).d (i - 1) i) := by
          simp [totalMapComponent, totalDifferential,
            verticalTotalHomotopyComponent, totalD1Component, totalD2Component]
          have hhom :
              f.f p (i - p) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) p -
                  g.f p (i - p) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) p =
                h.h p (i - p) ≫ B.d2 p (i - p - 1) ≫
                    eqToHom (by congr 1; lia) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) p +
                  A.d2 p (i - p) ≫ h.h p (i - p + 1) ≫
                    eqToHom (by congr 1; lia) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) p := by
            simpa [Category.assoc] using
              congrArg (fun k =>
                k ≫ Sigma.ι (fun r : ℤ => B.obj r (i - r)) p)
                (h.homotopy p (i - p))
          have hmap := congrArg (fun k =>
            k ≫ eqToHom (by congr 1; ring) ≫
              Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p + 1))
            (h.map p (i - p))
          rw [hhom]
          simp only [sub_eq_add_neg, Category.assoc, smul_add, smul_smul,
            Int.negOnePow_succ, Linear.units_smul_comp]
          rw [← hmap]
          simp [add_assoc, add_comm, add_left_comm]
        refine hfirst.trans ?_
        convert hadd.symm using 1
        congr 1
  · intro n
    dsimp [H]
    rw [if_pos (by ring)]
    simp
-/

theorem totalMap_homotopic_of_vertical [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f g : DoubleComplexMap A B}
    (h : VerticalHomotopy f g) :
    Nonempty (Homotopy (totalMap f) (totalMap g)) := by
  exact ⟨(vertical_total_homotopy_data h).choose⟩

private theorem horizontal_total_homotopy_data [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f g : DoubleComplexMap A B}
    (h : HorizontalHomotopy f g) :
    ∃ H : Homotopy (totalMap f) (totalMap g),
      ∀ n : ℤ,
        H.hom n (n + (-1 : ℤ)) =
          horizontalTotalHomotopyComponent h.h n := by
  let H : ∀ n m : ℤ, (totalComplex A).X n ⟶ (totalComplex B).X m :=
    fun n m => dite (m = n - 1)
      (fun hm => horizontalTotalHomotopyComponent h.h n ≫
        eqToHom (by subst m; rfl))
      (fun _ => 0)
  refine ⟨{ hom := H, zero := ?_, comm := ?_ }, ?_⟩
  · intro i j hij
    dsimp [H]
    split_ifs with h'
    · exfalso
      apply hij
      change j + 1 = i
      omega
    · rfl
  · intro i
    change totalMapComponent f i = dNext i H + prevD i H + totalMapComponent g i
    have hd :
        dNext i H =
          (totalComplex A).d i (i + 1) ≫ H (i + 1) i :=
      dNext_eq H (by simp [ComplexShape.up])
    have hp :
        prevD i H =
          H i (i - 1) ≫ (totalComplex B).d (i - 1) i :=
      prevD_eq H (by simp [ComplexShape.up])
    rw [hd, hp]
    simp [H]
    rw [← sub_eq_iff_eq_add]
    apply Sigma.hom_ext
    intro p
    have hsub :=
      Preadditive.comp_sub (Sigma.ι (fun r : ℤ => A.obj r (i - r)) p)
        (totalMapComponent f i) (totalMapComponent g i)
    calc
      _ = Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫ totalMapComponent f i -
          Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫ totalMapComponent g i := hsub
      _ = _ := by
        have hnextEq :
            (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) =
              ∐ fun r : ℤ => B.obj r (i - r) := by
          congr 1
          funext r
          ring
        have hadd :
            Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                ((totalComplex A).d i (i + 1) ≫
                    horizontalTotalHomotopyComponent h.h (i + 1) ≫
                    (eqToHom hnextEq :
                      (totalComplex B).X (i + 1 - 1) ⟶ (totalComplex B).X i) +
                  horizontalTotalHomotopyComponent h.h i ≫
                    (totalComplex B).d (i - 1) i) =
              Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                  ((totalComplex A).d i (i + 1) ≫
                    horizontalTotalHomotopyComponent h.h (i + 1) ≫
                    (eqToHom hnextEq :
                      (totalComplex B).X (i + 1 - 1) ⟶ (totalComplex B).X i)) +
                Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                  (horizontalTotalHomotopyComponent h.h i ≫
                    (totalComplex B).d (i - 1) i) := by
          apply Preadditive.comp_add
        have hfirst :
            (Sigma.ι (fun r : ℤ => A.obj r (i - r)) p :
                A.obj p (i - p) ⟶ (totalComplex A).X i) ≫ totalMapComponent f i -
                (Sigma.ι (fun r : ℤ => A.obj r (i - r)) p :
                  A.obj p (i - p) ⟶ (totalComplex A).X i) ≫ totalMapComponent g i =
              (Sigma.ι (fun r : ℤ => A.obj r (i - r)) p :
                A.obj p (i - p) ⟶ (totalComplex A).X i) ≫
                  ((totalComplex A).d i (i + 1) ≫
                    horizontalTotalHomotopyComponent h.h (i + 1) ≫
                    (eqToHom hnextEq :
                      (totalComplex B).X (i + 1 - 1) ⟶ (totalComplex B).X i)) +
                (Sigma.ι (fun r : ℤ => A.obj r (i - r)) p :
                  A.obj p (i - p) ⟶ (totalComplex A).X i) ≫
                  (horizontalTotalHomotopyComponent h.h i ≫
                    (totalComplex B).d (i - 1) i) := by
          simp [totalMapComponent, totalComplex, totalDifferential,
            horizontalTotalHomotopyComponent, totalD1Component, totalD2Component]
          have eRaw :
              (∐ fun r : ℤ => B.obj r (i - r)) = (totalComplex B).X i := by
            rfl
          have hhom :
              f.f p (i - p) ≫ Sigma.ι (fun r : ℤ => B.obj r (i - r)) p -
                  g.f p (i - p) ≫ Sigma.ι (fun r : ℤ => B.obj r (i - r)) p =
                h.h p (i - p) ≫ B.d1 (p - 1) (i - p) ≫
                    eqToHom (by congr 1; lia) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) p +
                  A.d1 p (i - p) ≫ h.h (p + 1) (i - p) ≫
                    eqToHom (by congr 1; lia) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) p := by
            simpa [Category.assoc, totalComplex] using
              congrArg (fun k =>
                k ≫ Sigma.ι (fun r : ℤ => B.obj r (i - r)) p)
                (h.homotopy p (i - p))
          have hmap := congrArg (fun k =>
            k ≫ eqToHom (by congr 1; ring) ≫
              Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p - 1))
            (h.map p (i - p))
          have hsign : (p - 1).negOnePow = -p.negOnePow := by
            simpa using (Int.negOnePow_sub p 1)
          have hnextEq :
              (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) =
                ∐ fun r : ℤ => B.obj r (i - r) := by
            congr 1
          have hA2 :
              A.d2 p (i - p) ≫ h.h p (i - p + 1) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  (Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p - 1)) =
                totalD2Component A i p ≫ h.h p (i + 1 - p) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p - 1) ≫
                  (eqToHom hnextEq :
                    (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) ⟶
                      ∐ fun r : ℤ => B.obj r (i - r)) := by
            dsimp [totalD2Component]
            simp only [Category.assoc]
            conv_rhs =>
              rw [← eqToHom_naturality_assoc (fun q : ℤ => h.h p q)
                (show i - p + 1 = i + 1 - p by ring)]
            change
              A.d2 p (i - p) ≫ h.h p (i - p + 1) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p - 1) =
                A.d2 p (i - p) ≫ h.h p (i - p + 1) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p - 1) ≫
                    eqToHom hnextEq
            have hnat := eqToHom_naturality_assoc
              (fun q : ℤ => Sigma.ι (fun r : ℤ => B.obj r (q - r)) (p - 1))
              (show i = i + 1 - 1 by ring)
              (eqToHom hnextEq)
            have hcoprod :
                (∐ fun r : ℤ => B.obj r (i - r)) =
                  ∐ fun r : ℤ => B.obj r (i + 1 - 1 - r) := by
              congr 1
              funext r
              ring
            have hcomp : eqToHom hcoprod ≫ eqToHom hnextEq =
                eqToHom (show
                  (∐ fun r : ℤ => B.obj r (i - r)) =
                    ∐ fun r : ℤ => B.obj r (i - r) by rfl) := by
              rw [eqToHom_trans]
            simpa [Category.assoc, hcomp, eqToHom_refl, Category.comp_id] using
              congrArg (fun k =>
                A.d2 p (i - p) ≫ h.h p (i - p + 1) ≫
                  eqToHom (by congr 1 <;> ring) ≫ k) hnat
          have hmapTarget :
              h.h p (i - p) ≫ B.d2 (p - 1) (i - p) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p - 1) ≫
                  (eqToHom hnextEq :
                    (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) ⟶
                      ∐ fun r : ℤ => B.obj r (i - r)) =
                A.d2 p (i - p) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  h.h p (i + 1 - p) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p - 1) ≫
                  (eqToHom hnextEq :
                    (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) ⟶
                      ∐ fun r : ℤ => B.obj r (i - r)) := by
            conv_rhs =>
              rw [← eqToHom_naturality_assoc (fun q : ℤ => h.h p q)
                (show i - p + 1 = i + 1 - p by ring)]
            simpa [Category.assoc] using
              congrArg (fun k =>
                k ≫ eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p - 1) ≫
                  (eqToHom hnextEq :
                    (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) ⟶
                      ∐ fun r : ℤ => B.obj r (i - r)))
                (h.map p (i - p))
          have hmapTarget_smul :=
            congrArg (fun k => p.negOnePow • k) hmapTarget
          have hA1 :
              A.d1 p (i - p) ≫ h.h (p + 1) (i - p) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - r)) p =
                eqToHom (by congr 1 <;> ring) ≫
                  A.d1 p (i + 1 - 1 - (p + 1 - 1)) ≫
                    h.h (p + 1) (i + 1 - 1 - (p + 1 - 1)) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1 - 1) ≫
                    (eqToHom hnextEq :
                      (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) ⟶
                        ∐ fun r : ℤ => B.obj r (i - r)) := by
            have hcoprod :
                (∐ fun r : ℤ => B.obj r (i - r)) =
                  ∐ fun r : ℤ => B.obj r (i + 1 - 1 - r) := by
              congr 1
              funext r
              ring
            have hcomp : eqToHom hcoprod ≫ eqToHom hnextEq =
                eqToHom (show
                  (∐ fun r : ℤ => B.obj r (i - r)) =
                    ∐ fun r : ℤ => B.obj r (i - r) by rfl) := by
              rw [eqToHom_trans]
            have hι0 :
                Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p + 1 - 1) ≫
                    eqToHom hcoprod =
                  eqToHom (by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1 - 1) := by
              have hι0' := eqToHom_naturality
                (fun F : ℤ → C => Sigma.ι F (p + 1 - 1))
                (show (fun r : ℤ => B.obj r (i - r)) =
                  (fun r : ℤ => B.obj r (i + 1 - 1 - r)) by
                    funext r
                    congr 1
                    ring)
              simpa only [CategoryTheory.eqToHom_comp_heq_iff,
                CategoryTheory.heq_eqToHom_comp_iff] using hι0'
            have hιL :
                eqToHom (show B.obj (p + 1 - 1) (i - p) = B.obj p (i - p) by
                    congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) p =
                  eqToHom (show B.obj (p + 1 - 1) (i - p) =
                    B.obj (p + 1 - 1) (i - (p + 1 - 1)) by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p + 1 - 1) := by
              have sigma_ι_transport {a b : ℤ} {F : ℤ → C} (hab : a = b) :
                  eqToHom (show F a = F b by subst b; rfl) ≫ Sigma.ι F b =
                    Sigma.ι F a := by
                subst b
                simp
              have hι := sigma_ι_transport
                (F := fun r : ℤ => B.obj r (i - r))
                (a := p + 1 - 1) (b := p) (by ring)
              have htransport :
                  eqToHom (show B.obj (p + 1 - 1) (i - p) =
                    B.obj (p + 1 - 1) (i - (p + 1 - 1)) by congr 1 <;> ring) ≫
                      eqToHom (show B.obj (p + 1 - 1) (i - (p + 1 - 1)) =
                        B.obj p (i - p) by congr 1 <;> ring) =
                    eqToHom (show B.obj (p + 1 - 1) (i - p) =
                      B.obj p (i - p) by congr 1 <;> ring) := by
                rw [eqToHom_trans]
              have hidx :
                  eqToHom (show B.obj (p + 1 - 1) (i - (p + 1 - 1)) =
                    B.obj p (i - p) by congr 1 <;> ring) ≫
                      Sigma.ι (fun r : ℤ => B.obj r (i - r)) p =
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p + 1 - 1) := by
                exact hι
              calc
                _ = eqToHom (show B.obj (p + 1 - 1) (i - p) =
                      B.obj (p + 1 - 1) (i - (p + 1 - 1)) by congr 1 <;> ring) ≫
                    eqToHom (show B.obj (p + 1 - 1) (i - (p + 1 - 1)) =
                      B.obj p (i - p) by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) p := by
                  simpa only [Category.assoc] using
                    congrArg (fun k => k ≫ Sigma.ι (fun r : ℤ => B.obj r (i - r)) p)
                      htransport.symm
                _ = _ := by
                  simpa only [Category.assoc] using
                    congrArg (fun k =>
                      eqToHom (show B.obj (p + 1 - 1) (i - p) =
                        B.obj (p + 1 - 1) (i - (p + 1 - 1)) by congr 1 <;> ring) ≫ k) hidx
            have hbase :
                eqToHom (show B.obj (p + 1 - 1) (i - p) = B.obj p (i - p) by
                    congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) p =
                  eqToHom (show B.obj (p + 1 - 1) (i - p) =
                    B.obj (p + 1 - 1) (i + 1 - 1 - (p + 1 - 1)) by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1 - 1) ≫
                    eqToHom hnextEq := by
              calc
                _ = eqToHom (show B.obj (p + 1 - 1) (i - p) =
                      B.obj (p + 1 - 1) (i - (p + 1 - 1)) by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p + 1 - 1) := hιL
                _ = eqToHom (show B.obj (p + 1 - 1) (i - p) =
                      B.obj (p + 1 - 1) (i - (p + 1 - 1)) by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p + 1 - 1) ≫
                    eqToHom hcoprod ≫ eqToHom hnextEq := by
                  rw [hcomp]
                  simp
                _ = eqToHom (show B.obj (p + 1 - 1) (i - p) =
                      B.obj (p + 1 - 1) (i - (p + 1 - 1)) by congr 1 <;> ring) ≫
                    eqToHom (by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1 - 1) ≫
                    eqToHom hnextEq := by
                  simpa only [Category.assoc] using
                    congrArg (fun k =>
                      eqToHom (show B.obj (p + 1 - 1) (i - p) =
                        B.obj (p + 1 - 1) (i - (p + 1 - 1)) by congr 1 <;> ring) ≫
                        k ≫ eqToHom hnextEq) hι0
                _ = _ := by
                  rw [← Category.assoc]
                  rw [eqToHom_trans]
            have hnat := eqToHom_naturality_assoc
              (fun q : ℤ => A.d1 p q ≫ h.h (p + 1) q)
              (show i - p = i + 1 - 1 - (p + 1 - 1) by ring)
              (Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1 - 1) ≫
                (eqToHom hnextEq :
                  (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) ⟶
                    ∐ fun r : ℤ => B.obj r (i - r)))
            calc
              _ = (A.d1 p (i - p) ≫ h.h (p + 1) (i - p)) ≫
                    eqToHom (by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p + 1 - 1) ≫
                    (eqToHom hnextEq :
                      (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) ⟶
                        ∐ fun r : ℤ => B.obj r (i - r)) := by
                simpa only [Category.assoc] using
                  congrArg (fun k => A.d1 p (i - p) ≫ h.h (p + 1) (i - p) ≫ k) hbase
              _ = _ := by
                simpa only [Category.assoc] using hnat
          have hprevEqH :
              (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) =
                ∐ fun r : ℤ => B.obj r (i - r) := by
            congr 1
            funext r
            ring
          have htransport_desc {j : ℤ} (hij : i - 1 + 1 = j) :
              ((hij ▸ (Sigma.desc (fun q : ℤ =>
                B.d1 q (i - 1 - q) ≫
                    eqToHom (by congr 1; ring) ≫
                      Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (q + 1) +
                  q.negOnePow •
                    (B.d2 q (i - 1 - q) ≫
                      eqToHom (by congr 1; ring) ≫
                        Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) q)) :
                (∐ fun r : ℤ => B.obj r (i - 1 - r)) ⟶
                  ∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) :
                (∐ fun r : ℤ => B.obj r (i - 1 - r)) ⟶
                  ∐ fun r : ℤ => B.obj r (j - r))) =
                (Sigma.desc fun q : ℤ =>
                  B.d1 q (i - 1 - q) ≫
                      eqToHom (by congr 1; ring) ≫
                        Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (q + 1) +
                    q.negOnePow •
                      (B.d2 q (i - 1 - q) ≫
                        eqToHom (by congr 1; ring) ≫
                          Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) q)) ≫
                  (eqToHom (by congr 1; simp [hij]) :
                    (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                      ∐ fun r : ℤ => B.obj r (j - r)) := by
            subst j
            simp
          have htransport_desc' := htransport_desc (j := i) (by ring)
          have heq_prev :
              eqToHom (by congr 1) =
                (eqToHom hprevEqH :
                  (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                    ∐ fun r : ℤ => B.obj r (i - r)) := by
            congr 1
          rw [heq_prev] at htransport_desc'
          change @Eq ((∐ fun r : ℤ => B.obj r (i - 1 - r)) ⟶ (totalComplex B).X i) _ _ at htransport_desc'
          have hcoprod_prev :
              (∐ fun r : ℤ => B.obj r (i - r)) =
                ∐ fun r : ℤ => B.obj r (i - 1 + 1 - r) := by
            congr 1
            funext r
            ring
          have hcomp_prev : eqToHom hcoprod_prev ≫ eqToHom hprevEqH =
              eqToHom (show
                (∐ fun r : ℤ => B.obj r (i - r)) =
                  ∐ fun r : ℤ => B.obj r (i - r) by rfl) := by
            rw [eqToHom_trans]
          have hcoprod_next :
              (∐ fun r : ℤ => B.obj r (i - r)) =
                ∐ fun r : ℤ => B.obj r (i + 1 - 1 - r) := by
            congr 1
            funext r
            ring
          have hcomp_next : eqToHom hcoprod_next ≫ eqToHom hnextEq =
              eqToHom (show
                (∐ fun r : ℤ => B.obj r (i - r)) =
                  ∐ fun r : ℤ => B.obj r (i - r) by rfl) := by
            rw [eqToHom_trans]
          have hι_next :
              Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p - 1) ≫
                  eqToHom hcoprod_next =
                eqToHom (show B.obj (p - 1) (i - (p - 1)) =
                  B.obj (p - 1) (i + 1 - 1 - (p - 1)) by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p - 1) := by
            have hnat := eqToHom_naturality
              (fun F : ℤ → C => Sigma.ι F (p - 1))
              (show (fun r : ℤ => B.obj r (i - r)) =
                (fun r : ℤ => B.obj r (i + 1 - 1 - r)) by
                  funext r
                  congr 1
                  ring)
            simpa only [CategoryTheory.eqToHom_comp_heq_iff,
              CategoryTheory.heq_eqToHom_comp_iff] using hnat
          have htransEq :
              eqToHom (show B.obj (p - 1) (i - p + 1) =
                B.obj (p - 1) (i - (p - 1)) by congr 1 <;> ring) ≫
                eqToHom (show B.obj (p - 1) (i - (p - 1)) =
                  B.obj (p - 1) (i + 1 - 1 - (p - 1)) by congr 1 <;> ring) =
              eqToHom (show B.obj (p - 1) (i - p + 1) =
                B.obj (p - 1) (i + 1 - 1 - (p - 1)) by congr 1 <;> ring) := by
            rw [eqToHom_trans]
          have htransport2 :
              eqToHom (show B.obj (p - 1) (i - p + 1) =
                B.obj (p - 1) (i + 1 - 1 - (p - 1)) by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p - 1) ≫
                    (eqToHom hnextEq :
                      (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) ⟶
                        ∐ fun r : ℤ => B.obj r (i - r)) =
                eqToHom (show B.obj (p - 1) (i - p + 1) =
                  B.obj (p - 1) (i - (p - 1)) by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p - 1) := by
            calc
              _ = eqToHom (show B.obj (p - 1) (i - p + 1) =
                    B.obj (p - 1) (i - (p - 1)) by congr 1 <;> ring) ≫
                    eqToHom (show B.obj (p - 1) (i - (p - 1)) =
                      B.obj (p - 1) (i + 1 - 1 - (p - 1)) by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p - 1) ≫
                      (eqToHom hnextEq :
                        (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) ⟶
                          ∐ fun r : ℤ => B.obj r (i - r)) := by
                simpa only [Category.assoc] using
                  congrArg
                    (fun k => k ≫
                      Sigma.ι (fun r : ℤ => B.obj r (i + 1 - 1 - r)) (p - 1) ≫
                        (eqToHom hnextEq :
                          (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) ⟶
                            ∐ fun r : ℤ => B.obj r (i - r)))
                    htransEq.symm
              _ = eqToHom (show B.obj (p - 1) (i - p + 1) =
                    B.obj (p - 1) (i - (p - 1)) by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p - 1) ≫
                      eqToHom hcoprod_next ≫ eqToHom hnextEq := by
                simpa only [Category.assoc] using
                  congrArg
                    (fun k =>
                      eqToHom (show B.obj (p - 1) (i - p + 1) =
                        B.obj (p - 1) (i - (p - 1)) by congr 1 <;> ring) ≫
                        k ≫ (eqToHom hnextEq :
                          (∐ fun r : ℤ => B.obj r (i + 1 - 1 - r)) ⟶
                            ∐ fun r : ℤ => B.obj r (i - r)))
                    hι_next.symm
              _ = _ := by
                rw [hcomp_next]
                simp
          have hprev1 :
              h.h p (i - p) ≫ B.d1 (p - 1) (i - p) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - r)) p =
                eqToHom (by congr 1 <;> ring) ≫
                  h.h p (i - 1 + 1 - p) ≫
                    B.d1 (p - 1) (i - 1 + 1 - p) ≫
                    eqToHom (by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) p ≫
                    (eqToHom hprevEqH :
                      (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                        ∐ fun r : ℤ => B.obj r (i - r)) := by
            have hnat := eqToHom_naturality_assoc
              (fun n : ℤ =>
                h.h p (n - p) ≫ B.d1 (p - 1) (n - p) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (n - r)) p)
              (show i = i - 1 + 1 by ring)
              (eqToHom hprevEqH)
            simpa [Category.assoc, hcomp_prev, eqToHom_refl, Category.comp_id]
              using hnat
          have hprev2 :
              h.h p (i - p) ≫ B.d2 (p - 1) (i - p) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p - 1) =
                eqToHom (by congr 1 <;> ring) ≫
                  h.h p (i - 1 + 1 - p) ≫
                    B.d2 (p - 1) (i - 1 + 1 - p) ≫
                    eqToHom (by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p - 1) ≫
                    (eqToHom hprevEqH :
                      (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                        ∐ fun r : ℤ => B.obj r (i - r)) := by
            have hnat := eqToHom_naturality_assoc
              (fun n : ℤ =>
                h.h p (n - p) ≫ B.d2 (p - 1) (n - p) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (n - r)) (p - 1))
              (show i = i - 1 + 1 by ring)
              (eqToHom hprevEqH)
            simpa [Category.assoc, hcomp_prev, eqToHom_refl, Category.comp_id]
              using hnat
          have hindex1 :
              eqToHom (show B.obj (p - 1 + 1) (i - 1 + 1 - p) =
                B.obj p (i - 1 + 1 - p) by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) p =
                eqToHom (show B.obj (p - 1 + 1) (i - 1 + 1 - p) =
                  B.obj (p - 1 + 1) (i - 1 + 1 - (p - 1 + 1)) by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p - 1 + 1) := by
            have sigma_ι_transport {a b : ℤ} {F : ℤ → C} (hab : a = b) :
                eqToHom (show F a = F b by subst b; rfl) ≫ Sigma.ι F b =
                  Sigma.ι F a := by
              subst b
              simp
            have hι := sigma_ι_transport
              (F := fun r : ℤ => B.obj r (i - 1 + 1 - r))
              (a := p - 1 + 1) (b := p) (by ring)
            have htransport :
                eqToHom (show B.obj (p - 1 + 1) (i - 1 + 1 - p) =
                  B.obj (p - 1 + 1) (i - 1 + 1 - (p - 1 + 1)) by congr 1 <;> ring) ≫
                    eqToHom (show B.obj (p - 1 + 1) (i - 1 + 1 - (p - 1 + 1)) =
                      B.obj p (i - 1 + 1 - p) by congr 1 <;> ring) =
                  eqToHom (show B.obj (p - 1 + 1) (i - 1 + 1 - p) =
                    B.obj p (i - 1 + 1 - p) by congr 1 <;> ring) := by
              rw [eqToHom_trans]
            have hidx :
                eqToHom (show B.obj (p - 1 + 1) (i - 1 + 1 - (p - 1 + 1)) =
                  B.obj p (i - 1 + 1 - p) by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) p =
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p - 1 + 1) := hι
            calc
              _ = eqToHom (show B.obj (p - 1 + 1) (i - 1 + 1 - p) =
                    B.obj (p - 1 + 1) (i - 1 + 1 - (p - 1 + 1)) by congr 1 <;> ring) ≫
                    eqToHom (show B.obj (p - 1 + 1) (i - 1 + 1 - (p - 1 + 1)) =
                      B.obj p (i - 1 + 1 - p) by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) p := by
                simpa only [Category.assoc] using
                  congrArg (fun k => k ≫ Sigma.ι
                    (fun r : ℤ => B.obj r (i - 1 + 1 - r)) p)
                    htransport.symm
              _ = _ := by
                simpa only [Category.assoc] using
                  congrArg (fun k => eqToHom (show B.obj (p - 1 + 1) (i - 1 + 1 - p) =
                    B.obj (p - 1 + 1) (i - 1 + 1 - (p - 1 + 1)) by congr 1 <;> ring) ≫ k)
                    hidx
          have hprev1_transport :
              (eqToHom (by congr 1 <;> ring) ≫
                h.h p (i - 1 + 1 - p) ≫
                  B.d1 (p - 1) (i - 1 + 1 - p) ≫
                  eqToHom (show B.obj (p - 1 + 1) (i - 1 + 1 - p) =
                    B.obj p (i - 1 + 1 - p) by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) p ≫
                  (eqToHom hprevEqH :
                    (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                      ∐ fun r : ℤ => B.obj r (i - r))) =
                eqToHom (by congr 1 <;> ring) ≫
                  h.h p (i - 1 + 1 - p) ≫
                    B.d1 (p - 1) (i - 1 + 1 - p) ≫
                    eqToHom (show B.obj (p - 1 + 1) (i - 1 + 1 - p) =
                      B.obj (p - 1 + 1) (i - 1 + 1 - (p - 1 + 1)) by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p - 1 + 1) ≫
                    (eqToHom hprevEqH :
                      (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                        ∐ fun r : ℤ => B.obj r (i - r)) := by
            simpa only [Category.assoc] using
              congrArg (fun k =>
                eqToHom (by congr 1 <;> ring) ≫
                  h.h p (i - 1 + 1 - p) ≫
                  B.d1 (p - 1) (i - 1 + 1 - p) ≫ k ≫
                  (eqToHom hprevEqH :
                      (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                        ∐ fun r : ℤ => B.obj r (i - r))) hindex1
          have hindex1_q :
              eqToHom (show B.obj (p - 1 + 1) (i - 1 - (p - 1)) =
                B.obj p (i - 1 + 1 - p) by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) p =
                eqToHom (show B.obj (p - 1 + 1) (i - 1 - (p - 1)) =
                  B.obj (p - 1 + 1) (i - 1 + 1 - (p - 1 + 1)) by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p - 1 + 1) := by
            convert hindex1 using 1 <;> subst_vars <;> simp
          have hprev1_transport_q :
              (eqToHom (by congr 1 <;> ring) ≫
                h.h p (i - 1 - (p - 1)) ≫
                  B.d1 (p - 1) (i - 1 - (p - 1)) ≫
                  eqToHom (show B.obj (p - 1 + 1) (i - 1 - (p - 1)) =
                    B.obj p (i - 1 + 1 - p) by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) p ≫
                  (eqToHom hprevEqH :
                    (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                      ∐ fun r : ℤ => B.obj r (i - r))) =
                eqToHom (by congr 1 <;> ring) ≫
                  h.h p (i - 1 - (p - 1)) ≫
                    B.d1 (p - 1) (i - 1 - (p - 1)) ≫
                    eqToHom (show B.obj (p - 1 + 1) (i - 1 - (p - 1)) =
                      B.obj (p - 1 + 1) (i - 1 + 1 - (p - 1 + 1)) by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p - 1 + 1) ≫
                    (eqToHom hprevEqH :
                      (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                        ∐ fun r : ℤ => B.obj r (i - r)) := by
            simpa only [Category.assoc] using
              congrArg (fun k =>
                eqToHom (by congr 1 <;> ring) ≫
                  h.h p (i - 1 - (p - 1)) ≫
                  B.d1 (p - 1) (i - 1 - (p - 1)) ≫ k ≫
                  (eqToHom hprevEqH :
                      (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                        ∐ fun r : ℤ => B.obj r (i - r))) hindex1_q
          have hprev1_transport_q' :
              (eqToHom (by congr 1 <;> ring) ≫
                h.h p (i - 1 - (p - 1)) ≫
                  B.d1 (p - 1) (i - 1 - (p - 1)) ≫
                  eqToHom (show B.obj (p - 1) (i - 1 - (p - 1) + 1) =
                    B.obj (p - 1) (i - 1 + 1 - (p - 1)) by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p - 1 + 1) ≫
                  (eqToHom hprevEqH :
                    (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                      ∐ fun r : ℤ => B.obj r (i - r))) =
                eqToHom (by congr 1 <;> ring) ≫
                  h.h p (i - 1 - (p - 1)) ≫
                    B.d1 (p - 1) (i - 1 - (p - 1)) ≫
                    eqToHom (show B.obj (p - 1 + 1) (i - 1 - (p - 1)) =
                      B.obj p (i - 1 + 1 - p) by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) p ≫
                    (eqToHom hprevEqH :
                      (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                        ∐ fun r : ℤ => B.obj r (i - r)) := by
            simpa only [Category.assoc] using hprev1_transport_q.symm
          have hprev1_transport_target :
              (eqToHom (show A.obj p (i - p) = A.obj p (i - 1 - (p - 1)) by
                  congr 1 <;> ring) ≫
                h.h p (i - 1 - (p - 1)) ≫
                  B.d1 (p - 1) (i - 1 - (p - 1)) ≫
                  eqToHom (show B.obj (p - 1 + 1) (i - 1 - (p - 1)) =
                    B.obj (p - 1 + 1) (i - 1 + 1 - (p - 1 + 1)) by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p - 1 + 1) ≫
                  (eqToHom hprevEqH :
                    (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                      ∐ fun r : ℤ => B.obj r (i - r)) :
                A.obj p (i - p) ⟶ (totalComplex B).X i) =
                ((eqToHom (show A.obj p (i - p) = A.obj p (i - 1 - (p - 1)) by
                  congr 1 <;> ring) ≫
                  h.h p (i - 1 - (p - 1)) ≫
                    B.d1 (p - 1) (i - 1 - (p - 1)) ≫
                    eqToHom (show B.obj (p - 1 + 1) (i - 1 - (p - 1)) =
                      B.obj p (i - 1 + 1 - p) by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) p ≫
                    (eqToHom hprevEqH :
                      (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                        ∐ fun r => B.obj r (i - r))) :
                  A.obj p (i - p) ⟶ (totalComplex B).X i) := by
            simpa [totalComplex, Category.assoc] using
              congrArg (fun k =>
                eqToHom (show A.obj p (i - p) = A.obj p (i - 1 - (p - 1)) by
                  congr 1 <;> ring) ≫
                  h.h p (i - 1 - (p - 1)) ≫
                  B.d1 (p - 1) (i - 1 - (p - 1)) ≫ k ≫
                  (eqToHom hprevEqH :
                    (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                      ∐ fun r => B.obj r (i - r))) hindex1_q.symm
          have hprev2_transport_target :
              (eqToHom (show A.obj p (i - p) = A.obj p (i - 1 - (p - 1)) by
                  congr 1 <;> ring) ≫
                h.h p (i - 1 - (p - 1)) ≫
                  B.d2 (p - 1) (i - 1 - (p - 1)) ≫
                  eqToHom (show B.obj (p - 1) (i - 1 - (p - 1) + 1) =
                    B.obj (p - 1) (i - 1 + 1 - (p - 1)) by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p - 1) ≫
                  (eqToHom hprevEqH :
                    (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                      ∐ fun r : ℤ => B.obj r (i - r))) =
                h.h p (i - p) ≫ B.d2 (p - 1) (i - p) ≫
                  eqToHom (by congr 1 <;> ring) ≫
                  Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p - 1) := by
            have hι_prev :
                Sigma.ι (fun r : ℤ => B.obj r (i - 1 + 1 - r)) (p - 1) ≫
                    (eqToHom hprevEqH :
                      (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                        ∐ fun r => B.obj r (i - r)) =
                  eqToHom (show B.obj (p - 1) (i - 1 + 1 - (p - 1)) =
                    B.obj (p - 1) (i - (p - 1)) by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p - 1) := by
              have hnat := eqToHom_naturality
                (fun F : ℤ → C => Sigma.ι F (p - 1))
                (show (fun r : ℤ => B.obj r (i - 1 + 1 - r)) =
                  (fun r : ℤ => B.obj r (i - r)) by
                    funext r
                    congr 1
                    ring)
              simpa only [CategoryTheory.eqToHom_comp_heq_iff,
                CategoryTheory.heq_eqToHom_comp_iff] using hnat
            have hnat :
                eqToHom (show A.obj p (i - p) =
                    A.obj p (i - 1 - (p - 1)) by congr 1 <;> ring) ≫
                  h.h p (i - 1 - (p - 1)) ≫
                    B.d2 (p - 1) (i - 1 - (p - 1)) ≫
                    eqToHom (show B.obj (p - 1) (i - 1 - (p - 1) + 1) =
                      B.obj (p - 1) (i - (p - 1)) by congr 1 <;> ring) =
                  h.h p (i - p) ≫ B.d2 (p - 1) (i - p) := by
              simpa only [Category.assoc] using
                (eqToHom_naturality_assoc
                  (fun q : ℤ => h.h p q ≫ B.d2 (p - 1) q)
                  (show i - p = i - 1 - (p - 1) by ring))
            simpa only [Category.assoc] using
              congrArg (fun k => k ≫ (eqToHom hprevEqH :
                (∐ fun r : ℤ => B.obj r (i - 1 + 1 - r)) ⟶
                  ∐ fun r : ℤ => B.obj r (i - r))) hnat
          refine hhom.trans ?_
          rw [← hmapTarget_smul]
          rw [htransport2]
          conv_rhs =>
            rhs
            rhs
            rw [htransport_desc']
            simp only [Category.assoc]
            rw [← Category.assoc
              (Sigma.ι (fun r : ℤ => B.obj r (i - 1 - r)) (p - 1)) _ _]
            rw [Sigma.ι_desc]
            simp only [Category.assoc, Preadditive.add_comp,
              Linear.units_smul_comp]
          rw [Preadditive.comp_add]
          conv_rhs =>
            lhs
            lhs
            rw [← hA1]
          conv_rhs =>
            rhs
            rw [Preadditive.comp_add]
          change @Eq (A.obj p (i - p) ⟶ ∐ fun r : ℤ => B.obj r (i - r)) _ _
          erw [hprev1_transport_target]
          rw [hprev2_transport_target]
          have hneg :
              (-p.negOnePow) •
                  (h.h p (i - p) ≫ B.d2 (p - 1) (i - p) ≫
                    eqToHom (by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p - 1)) =
                -(p.negOnePow •
                  (h.h p (i - p) ≫ B.d2 (p - 1) (i - p) ≫
                    eqToHom (by congr 1 <;> ring) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p - 1))) := by
            exact Units.neg_smul (R := ℤ) p.negOnePow _
          rw [hneg]
          abel
        refine hfirst.trans ?_
        exact hadd.symm
  · intro n
    dsimp [H]
    rw [if_pos (by ring)]
    simp
/-
  let H : ∀ n m : ℤ, (totalComplex A).X n ⟶ (totalComplex B).X m :=
    fun n m => dite (m = n - 1)
      (fun hm => horizontalTotalHomotopyComponent h.h n ≫
        eqToHom (by subst m; rfl))
      (fun _ => 0)
  refine ⟨{ hom := H, zero := ?_, comm := ?_ }, ?_⟩
  · intro i j hij
    dsimp [H]
    split_ifs with h'
    · exfalso
      apply hij
      change j + 1 = i
      omega
    · rfl
  · intro i
    change totalMapComponent f i = dNext i H + prevD i H + totalMapComponent g i
    have hd :
        dNext i H =
          (totalComplex A).d i (i + 1) ≫ H (i + 1) i :=
      dNext_eq H (by simp [ComplexShape.up])
    have hp :
        prevD i H =
          H i (i - 1) ≫ (totalComplex B).d (i - 1) i :=
      prevD_eq H (by simp [ComplexShape.up])
    rw [hd, hp]
    simp [H]
    rw [← sub_eq_iff_eq_add]
    apply Sigma.hom_ext
    intro p
    have hsub :=
      Preadditive.comp_sub (Sigma.ι (fun r : ℤ => A.obj r (i - r)) p)
        (totalMapComponent f i) (totalMapComponent g i)
    calc
      _ = Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫ totalMapComponent f i -
          Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫ totalMapComponent g i := hsub
      _ = _ := by
        have hadd :
            Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                ((totalComplex A).d i (i + 1) ≫
                    horizontalTotalHomotopyComponent h.h (i + 1) ≫
                    eqToHom (by congr 1; lia) +
                  horizontalTotalHomotopyComponent h.h i ≫
                    (totalComplex B).d (i - 1) i) =
              Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                  ((totalComplex A).d i (i + 1) ≫
                    horizontalTotalHomotopyComponent h.h (i + 1) ≫
                    eqToHom (by congr 1; lia)) +
                Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                  (horizontalTotalHomotopyComponent h.h i ≫
                    (totalComplex B).d (i - 1) i) := by
          apply Preadditive.comp_add
        have hfirst :
            Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫ totalMapComponent f i -
                Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫ totalMapComponent g i =
              Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                  ((totalComplex A).d i (i + 1) ≫
                    horizontalTotalHomotopyComponent h.h (i + 1) ≫
                    eqToHom (by congr 1; lia)) +
                Sigma.ι (fun r : ℤ => A.obj r (i - r)) p ≫
                  (horizontalTotalHomotopyComponent h.h i ≫
                    (totalComplex B).d (i - 1) i) := by
          simp [totalMapComponent, totalComplex, totalDifferential,
            horizontalTotalHomotopyComponent, totalD1Component, totalD2Component]
          have hhom :
              f.f p (i - p) ≫
                    (Sigma.ι (fun r : ℤ => B.obj r (i - r)) p :
                      B.obj p (i - p) ⟶ (totalComplex B).X i) -
                  g.f p (i - p) ≫
                    (Sigma.ι (fun r : ℤ => B.obj r (i - r)) p :
                      B.obj p (i - p) ⟶ (totalComplex B).X i) =
                h.h p (i - p) ≫ B.d1 (p - 1) (i - p) ≫
                    eqToHom (by congr 1; lia) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) p +
                  A.d1 p (i - p) ≫ h.h (p + 1) (i - p) ≫
                    eqToHom (by congr 1; lia) ≫
                    Sigma.ι (fun r : ℤ => B.obj r (i - r)) p := by
            simpa [Category.assoc] using
              congrArg (fun k =>
                k ≫ Sigma.ι (fun r : ℤ => B.obj r (i - r)) p)
                (h.homotopy p (i - p))
          have hmap := congrArg (fun k =>
            k ≫ eqToHom (by congr 1; ring) ≫
              Sigma.ι (fun r : ℤ => B.obj r (i - r)) (p - 1))
            (h.map p (i - p))
          have hsign : (p - 1).negOnePow = -p.negOnePow := by
            simpa using (Int.negOnePow_sub p 1)
          change
            (f.f p (i - p) ≫ Sigma.ι (fun r : ℤ => B.obj r (i - r)) p -
                g.f p (i - p) ≫ Sigma.ι (fun r : ℤ => B.obj r (i - r)) p) = _
          rw [hhom]
          simp only [sub_eq_add_neg, Category.assoc, smul_add, smul_smul,
            Int.negOnePow_succ, Linear.units_smul_comp, hsign]
          rw [← hmap]
          simp [add_assoc, add_comm, add_left_comm]
        refine hfirst.trans ?_
        convert hadd.symm using 1
        congr 1
  · intro n
    dsimp [H]
    rw [if_pos (by ring)]
    simp
-/

theorem totalMap_homotopic_of_horizontal [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f g : DoubleComplexMap A B}
    (h : HorizontalHomotopy f g) :
    Nonempty (Homotopy (totalMap f) (totalMap g)) := by
  exact ⟨(horizontal_total_homotopy_data h).choose⟩

theorem vertical_total_homotopy_components [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f g : DoubleComplexMap A B}
    (h : VerticalHomotopy f g) :
    ∃ H : Homotopy (totalMap f) (totalMap g),
      ∀ n : ℤ,
        H.hom n (n + (-1 : ℤ)) =
          verticalTotalHomotopyComponent h.h n := by
  exact vertical_total_homotopy_data h

theorem horizontal_total_homotopy_components [HasCountableCoproducts C]
    {A B : DoubleComplex C} {f g : DoubleComplexMap A B}
    (h : HorizontalHomotopy f g) :
    ∃ H : Homotopy (totalMap f) (totalMap g),
      ∀ n : ℤ,
        H.hom n (n + (-1 : ℤ)) =
          horizontalTotalHomotopyComponent h.h n := by
  exact horizontal_total_homotopy_data h

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
