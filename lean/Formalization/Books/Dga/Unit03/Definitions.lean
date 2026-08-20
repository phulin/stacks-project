import Formalization.Books.Dga.Unit02.Conventions
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.BifunctorFlip
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Differential graded algebras

This file formalizes the definitions in section 3 of the source.  A
differential graded algebra is represented by a monoid object in the
monoidal category of complexes of `R`-modules.  Thus the multiplication is a
genuine chain map from the total tensor product and its being a chain map is
exactly the Leibniz rule.  The unit is likewise a map from the complex
concentrated in degree zero at `R`.

The source allows either chain or cochain indexing.  The cochain version is
the book-facing `DifferentialGradedAlgebra`; the parallel chain-indexed
version is provided by `ChainDifferentialGradedAlgebra`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open HomologicalComplex
open ComplexShape

universe u

namespace Formalization.Books.Dga.Unit03

/-! ## Complexes and their tensor products -/

/-- Integer-indexed cochain complexes of `R`-modules. -/
abbrev CochainComplexOver (R : Type u) [CommRing R] :=
  CochainComplex (ModuleCat.{u} R) ℤ

/-- Integer-indexed chain complexes of `R`-modules. -/
abbrev ChainComplexOver (R : Type u) [CommRing R] :=
  ChainComplex (ModuleCat.{u} R) ℤ

/-- The total tensor product of two cochain complexes. -/
noncomputable abbrev tensorProductBifunctor (R : Type u) [CommRing R] :
    CochainComplexOver R ⥤ CochainComplexOver R ⥤ CochainComplexOver R :=
  (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex

/-- The total complex `Tot(A ⊗_R B)` of two cochain complexes. -/
noncomputable abbrev tensorProductComplex (R : Type u) [CommRing R]
    (A B : CochainComplexOver R) : CochainComplexOver R :=
  HomologicalComplex.tensorObj A B

/-- The tensor unit complex, concentrated in degree zero at `R`. -/
noncomputable abbrev tensorUnitComplex (R : Type u) [CommRing R] :
    CochainComplexOver R :=
  HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℤ)

/-- Tensoring two morphisms of cochain complexes. -/
noncomputable abbrev tensorHomComplex {R : Type u} [CommRing R]
    {A B C D : CochainComplexOver R} (f : A ⟶ B) (g : C ⟶ D) :
    tensorProductComplex R A C ⟶ tensorProductComplex R B D :=
  HomologicalComplex.tensorHom f g

/- The standard Mathlib tensor-complex construction is also available for
   integer-indexed chain complexes after supplying the same sign homomorphism
   as for cochain complexes.  Mathlib has the chain instance for `ℕ`, but not
   for `ℤ`; this is the small, canonical bridge needed by the source's
   chain-indexed alternative. -/
local instance : TensorSigns (ComplexShape.down ℤ) where
  ε' :=
    { toFun := fun i => Int.negOnePow i.toAdd
      map_one' := by simp
      map_mul' := by
        intro i j
        exact Int.negOnePow_add i.toAdd j.toAdd }
  rel_add p q r (hpq : (ComplexShape.down ℤ).Rel p q) := by
    change q + 1 = p at hpq
    change (q + r) + 1 = p + r
    omega
  add_rel p q r (hpq : (ComplexShape.down ℤ).Rel p q) := by
    change q + 1 = p at hpq
    change (r + q) + 1 = r + p
    omega
  ε'_succ := by
    intro p q hpq
    change q + 1 = p at hpq
    change Int.negOnePow q = -Int.negOnePow p
    rw [← hpq, Int.negOnePow_succ]
    simp

/-- The Koszul symmetry for the integer-indexed chain total complex. -/
local instance : TotalComplexShapeSymmetry
    (ComplexShape.down ℤ) (ComplexShape.down ℤ) (ComplexShape.down ℤ) where
  symm p q := add_comm q p
  σ p q := (p * q).negOnePow
  σ_ε₁ := by
    intro p p' hp q
    change p' + 1 = p at hp
    subst p
    dsimp
    change ((p' + 1) * q).negOnePow * 1 =
      q.negOnePow * (p' * q).negOnePow
    rw [mul_one, add_mul, one_mul, Int.negOnePow_add, mul_comm]
  σ_ε₂ := by
    intro p q q' hq
    change q' + 1 = q at hq
    subst q
    dsimp
    change (p * (q' + 1)).negOnePow * p.negOnePow =
      1 * (p * q').negOnePow
    rw [one_mul, mul_add, Int.negOnePow_add, mul_assoc]
    simp only [mul_one]
    rw [Int.units_mul_self, mul_one]

/-- The total tensor product of two chain complexes. -/
noncomputable abbrev chainTensorProductBifunctor (R : Type u) [CommRing R] :
    ChainComplexOver R ⥤ ChainComplexOver R ⥤ ChainComplexOver R :=
  (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂HomologicalComplex
    (.down ℤ) (.down ℤ) (.down ℤ)

/-- The total tensor product of two chain complexes. -/
noncomputable abbrev chainTensorProductComplex (R : Type u) [CommRing R]
    (A B : ChainComplexOver R) : ChainComplexOver R :=
  HomologicalComplex.tensorObj A B

/-- The tensor unit complex for chain indexing. -/
noncomputable abbrev chainTensorUnitComplex (R : Type u) [CommRing R] :
    ChainComplexOver R :=
  HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.down ℤ)

/-- Tensoring two morphisms of chain complexes. -/
noncomputable abbrev chainTensorHomComplex {R : Type u} [CommRing R]
    {A B C D : ChainComplexOver R} (f : A ⟶ B) (g : C ⟶ D) :
    chainTensorProductComplex R A C ⟶ chainTensorProductComplex R B D :=
  HomologicalComplex.tensorHom f g

/-! ## Differential graded algebras -/

/-- A cochain differential graded `R`-algebra.

The multiplication is a map `Tot(A ⊗ A) ⟶ A`; its chain-map condition is
the source's Leibniz rule, and the monoid-object equations are associativity
and the two unit laws. -/
structure CochainDifferentialGradedAlgebra (R : Type u) [CommRing R] where
  complex : CochainComplexOver R
  multiplication : tensorProductComplex R complex complex ⟶ complex
  unit : tensorUnitComplex R ⟶ complex
  one_mul :
    tensorHomComplex unit (𝟙 complex) ≫ multiplication =
      (HomologicalComplex.leftUnitor complex).hom
  mul_one :
    tensorHomComplex (𝟙 complex) unit ≫ multiplication =
      (HomologicalComplex.rightUnitor complex).hom
  mul_assoc :
    tensorHomComplex multiplication (𝟙 complex) ≫ multiplication =
      (HomologicalComplex.associator complex complex complex).hom ≫
        tensorHomComplex (𝟙 complex) multiplication ≫ multiplication

/-- The chain-indexed form of a differential graded `R`-algebra. -/
structure ChainDifferentialGradedAlgebra (R : Type u) [CommRing R] where
  complex : ChainComplexOver R
  multiplication : chainTensorProductComplex R complex complex ⟶ complex
  unit : chainTensorUnitComplex R ⟶ complex
  one_mul :
    chainTensorHomComplex unit (𝟙 complex) ≫ multiplication =
      (HomologicalComplex.leftUnitor complex).hom
  mul_one :
    chainTensorHomComplex (𝟙 complex) unit ≫ multiplication =
      (HomologicalComplex.rightUnitor complex).hom
  mul_assoc :
    chainTensorHomComplex multiplication (𝟙 complex) ≫ multiplication =
      (HomologicalComplex.associator complex complex complex).hom ≫
        chainTensorHomComplex (𝟙 complex) multiplication ≫ multiplication

/-- The cochain convention used as the default book-facing DGA type. -/
abbrev DifferentialGradedAlgebra (R : Type u) [CommRing R] :=
  CochainDifferentialGradedAlgebra R

/-- The chain convention for a DGA. -/
abbrev ChainDGA (R : Type u) [CommRing R] :=
  ChainDifferentialGradedAlgebra R

/-- The homogeneous multiplication map in a cochain DGA. -/
noncomputable def CochainDifferentialGradedAlgebra.homogeneousMultiplication
    {R : Type u} [CommRing R] (A : CochainDifferentialGradedAlgebra R)
    (p q : ℤ) :
    A.complex.X p ⊗ A.complex.X q ⟶ A.complex.X (p + q) :=
  HomologicalComplex.ιTensorObj A.complex A.complex p q (p + q) rfl ≫
    A.multiplication.f (p + q)

/-- The homogeneous multiplication map in a chain DGA. -/
noncomputable def ChainDifferentialGradedAlgebra.homogeneousMultiplication
    {R : Type u} [CommRing R] (A : ChainDifferentialGradedAlgebra R)
    (p q : ℤ) :
    A.complex.X p ⊗ A.complex.X q ⟶ A.complex.X (p + q) :=
  HomologicalComplex.ιTensorObj A.complex A.complex p q (p + q) rfl ≫
    A.multiplication.f (p + q)

/-! ## Homomorphisms -/

/-- A homomorphism of cochain differential graded algebras. -/
structure CochainDifferentialGradedAlgebraHom
    {R : Type u} [CommRing R]
    (A B : CochainDifferentialGradedAlgebra R) where
  map : A.complex ⟶ B.complex
  map_unit : A.unit ≫ map = B.unit
  map_multiplication :
    A.multiplication ≫ map = tensorHomComplex map map ≫ B.multiplication

/-- A homomorphism of chain differential graded algebras. -/
structure ChainDifferentialGradedAlgebraHom
    {R : Type u} [CommRing R]
    (A B : ChainDifferentialGradedAlgebra R) where
  map : A.complex ⟶ B.complex
  map_unit : A.unit ≫ map = B.unit
  map_multiplication :
    A.multiplication ≫ map = chainTensorHomComplex map map ≫ B.multiplication

/-- A homomorphism in the default cochain convention. -/
abbrev DifferentialGradedAlgebraHom {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R) :=
  CochainDifferentialGradedAlgebraHom A B

/-! ## Commutativity -/

/-- Transport an element between equal homogeneous component indices. -/
def transportComponent {R : Type u} [CommRing R] {c : ComplexShape ℤ}
    {C : HomologicalComplex (ModuleCat.{u} R) c} {p q : ℤ} (h : p = q)
    (x : C.X p) : C.X q :=
  h ▸ x

/-- Graded commutativity for a cochain DGA. -/
def CochainDifferentialGradedAlgebra.IsGradedCommutative
    {R : Type u} [CommRing R] (A : CochainDifferentialGradedAlgebra R) : Prop :=
  ∀ (p q : ℤ) (a : A.complex.X p) (b : A.complex.X q),
    (A.homogeneousMultiplication p q).hom (a ⊗ₜ[R] b) =
      transportComponent (C := A.complex) (add_comm q p)
        ((p * q).negOnePow •
          (A.homogeneousMultiplication q p).hom (b ⊗ₜ[R] a))

/-- Strict graded commutativity for a cochain DGA. -/
def CochainDifferentialGradedAlgebra.IsStrictlyCommutative
    {R : Type u} [CommRing R] (A : CochainDifferentialGradedAlgebra R) : Prop :=
  A.IsGradedCommutative ∧
    ∀ (p : ℤ) (a : A.complex.X p), Odd p →
      (A.homogeneousMultiplication p p).hom (a ⊗ₜ[R] a) = 0

/-- Graded commutativity for a chain DGA. -/
def ChainDifferentialGradedAlgebra.IsGradedCommutative
    {R : Type u} [CommRing R] (A : ChainDifferentialGradedAlgebra R) : Prop :=
  ∀ (p q : ℤ) (a : A.complex.X p) (b : A.complex.X q),
    (A.homogeneousMultiplication p q).hom (a ⊗ₜ[R] b) =
      transportComponent (C := A.complex) (add_comm q p)
        ((p * q).negOnePow •
          (A.homogeneousMultiplication q p).hom (b ⊗ₜ[R] a))

/-- Strict graded commutativity for a chain DGA. -/
def ChainDifferentialGradedAlgebra.IsStrictlyCommutative
    {R : Type u} [CommRing R] (A : ChainDifferentialGradedAlgebra R) : Prop :=
  A.IsGradedCommutative ∧
    ∀ (p : ℤ) (a : A.complex.X p), Odd p →
      (A.homogeneousMultiplication p p).hom (a ⊗ₜ[R] a) = 0

/-- Graded commutativity in the default cochain convention. -/
abbrev IsGradedCommutative {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :=
  A.IsGradedCommutative

/-- Strict graded commutativity in the default cochain convention. -/
abbrev IsStrictlyCommutative {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :=
  A.IsStrictlyCommutative

/-! ## Tensor products of DGAs -/

/- The source notes that this construction is principally intended for
   commutative DGAs.  The data below records the standard signed tensor
   product for arbitrary DGAs over the fixed commutative base; no extra
   commutativity hypothesis is silently added. -/

/-- The signed flip of total tensor products, whose summand sign is
`(-1)^(pq)`.  Mathlib supplies the total-complex construction, while this
map records the Koszul sign and the module-category braiding. -/
noncomputable def tensorFlipHomComponent
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) (n : ℤ) :
    (tensorProductComplex R A B).X n ⟶
      (tensorProductComplex R B A).X n :=
  HomologicalComplex.mapBifunctorDesc (fun p q h =>
    (p * q).negOnePow •
      ((β_ (A.X p) (B.X q)).hom ≫
        ιMapBifunctor B A (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
          (.up ℤ) q p n (by
            rw [ComplexShape.π_symm (.up ℤ) (.up ℤ) (.up ℤ) p q]
            exact h)))

/-- The inverse signed flip of total tensor products. -/
noncomputable def tensorFlipInvComponent
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) (n : ℤ) :
    (tensorProductComplex R B A).X n ⟶
      (tensorProductComplex R A B).X n :=
  HomologicalComplex.mapBifunctorDesc (fun p q h =>
    (p * q).negOnePow •
      ((β_ (B.X p) (A.X q)).hom ≫
        ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
          (.up ℤ) q p n (by
            rw [ComplexShape.π_symm (.up ℤ) (.up ℤ) (.up ℤ) p q]
            exact h)))

private lemma tensorProductComplex_differential_formula_aux
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) (p q : ℤ) :
    ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q (p + q) rfl ≫
        (tensorProductComplex R A B).d (p + q) (p + q + 1) =
      (A.d p (p + 1) ⊗ₘ 𝟙 (B.X q)) ≫
            ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) (p + 1) q (p + q + 1) (by dsimp; omega) +
        p.negOnePow •
          ((𝟙 (A.X p) ⊗ₘ B.d q (q + 1)) ≫
            ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
              (.up ℤ) p (q + 1) (p + q + 1) (by dsimp; omega)) := by
  change _ ≫ (HomologicalComplex.mapBifunctor A B
    (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (.up ℤ)).d
      (p + q) (p + q + 1) = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq A B
      (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (.up ℤ)
      (by rfl) q _ (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq A B
      (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (.up ℤ)
      p (by rfl) _ (by dsimp; omega)]
  dsimp
  simp

private lemma tensorProductComplex_differential_formula_swap_aux
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) (p q n : ℤ)
    (h : q + p = n) :
    ιMapBifunctor B A (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) q p n (by dsimp; omega) ≫
        (tensorProductComplex R B A).d n (n + 1) =
      (B.d q (q + 1) ⊗ₘ 𝟙 (A.X p)) ≫
          ιMapBifunctor B A (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) (q + 1) p (n + 1) (by dsimp; omega) +
        q.negOnePow •
          ((𝟙 (B.X q) ⊗ₘ A.d p (p + 1)) ≫
            ιMapBifunctor B A (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
              (.up ℤ) q (p + 1) (n + 1) (by dsimp; omega)) := by
  subst n
  exact tensorProductComplex_differential_formula_aux R B A q p

private lemma tensorProductComplex_differential_formula_comm_aux
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) (p q n : ℤ)
    (h : q + p = n) :
    ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) q p n (by dsimp; omega) ≫
        (tensorProductComplex R A B).d n (n + 1) =
      (A.d q (q + 1) ⊗ₘ 𝟙 (B.X p)) ≫
          ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) (q + 1) p (n + 1) (by dsimp; omega) +
        q.negOnePow •
          ((𝟙 (A.X q) ⊗ₘ B.d p (p + 1)) ≫
            ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
              (.up ℤ) q (p + 1) (n + 1) (by dsimp; omega)) := by
  subst n
  exact tensorProductComplex_differential_formula_aux R A B q p

private lemma tensorProductComplex_differential_formula_right_aux
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) (p q : ℤ)
    {Z : ModuleCat.{u} R} (f : (tensorProductComplex R A B).X (p + q + 1) ⟶ Z) :
    ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q (p + q) rfl ≫
        ((tensorProductComplex R A B).d (p + q) (p + q + 1) ≫ f) =
      ((A.d p (p + 1) ⊗ₘ 𝟙 (B.X q)) ≫
          ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) (p + 1) q (p + q + 1) (by dsimp; omega) +
        p.negOnePow •
          ((𝟙 (A.X p) ⊗ₘ B.d q (q + 1)) ≫
            ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
              (.up ℤ) p (q + 1) (p + q + 1) (by dsimp; omega))) ≫ f := by
  simpa only [Category.assoc] using congrArg (fun k => k ≫ f)
    (tensorProductComplex_differential_formula_aux R A B p q)

@[reassoc] private lemma tensorFlipHomComponent_on_summand
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) (p q n : ℤ)
    (h : p + q = n) :
    ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q n h ≫ tensorFlipHomComponent R A B n =
      (p * q).negOnePow •
        ((β_ (A.X p) (B.X q)).hom ≫
          ιMapBifunctor B A (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) q p n (by
              rw [ComplexShape.π_symm (.up ℤ) (.up ℤ) (.up ℤ) p q]
              exact h)) := by
  dsimp [tensorFlipHomComponent]
  rw [HomologicalComplex.ι_mapBifunctorDesc]

@[reassoc] private lemma tensorFlipInvComponent_on_summand
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) (p q n : ℤ)
    (h : p + q = n) :
    ιMapBifunctor B A (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q n h ≫ tensorFlipInvComponent R A B n =
      (p * q).negOnePow •
        ((β_ (B.X p) (A.X q)).hom ≫
          ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) q p n (by
              rw [ComplexShape.π_symm (.up ℤ) (.up ℤ) (.up ℤ) p q]
              exact h)) := by
  dsimp [tensorFlipInvComponent]
  rw [HomologicalComplex.ι_mapBifunctorDesc]

private lemma tensorFlipHomComponent_on_summand_right
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) (p q n : ℤ)
    (h : p + q = n) {Z : ModuleCat.{u} R}
    (f : (tensorProductComplex R B A).X n ⟶ Z) :
    ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q n h ≫ (tensorFlipHomComponent R A B n ≫ f) =
      ((p * q).negOnePow •
        ((β_ (A.X p) (B.X q)).hom ≫
          ιMapBifunctor B A (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) q p n (by
              rw [ComplexShape.π_symm (.up ℤ) (.up ℤ) (.up ℤ) p q]
              exact h))) ≫ f := by
  simpa only [Category.assoc] using congrArg (fun k => k ≫ f)
    (tensorFlipHomComponent_on_summand R A B p q n h)

private lemma tensorFlipInvComponent_on_summand_right
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) (p q n : ℤ)
    (h : p + q = n) {Z : ModuleCat.{u} R}
    (f : (tensorProductComplex R A B).X n ⟶ Z) :
    ιMapBifunctor B A (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q n h ≫ (tensorFlipInvComponent R A B n ≫ f) =
      ((p * q).negOnePow •
        ((β_ (B.X p) (A.X q)).hom ≫
          ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) q p n (by
              rw [ComplexShape.π_symm (.up ℤ) (.up ℤ) (.up ℤ) p q]
              exact h))) ≫ f := by
  simpa only [Category.assoc] using congrArg (fun k => k ≫ f)
    (tensorFlipInvComponent_on_summand R A B p q n h)

/-- The signed Koszul flip of total tensor products. -/
noncomputable def tensorFlipIso
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) :
    tensorProductComplex R A B ≅ tensorProductComplex R B A :=
  { hom :=
      { f := tensorFlipHomComponent R A B
        comm' := by
          rintro i _ rfl
          apply HomologicalComplex.mapBifunctor.hom_ext
          intro p q h
          dsimp at h
          subst i
          rw [tensorFlipHomComponent_on_summand_right R A B p q (p + q) rfl]
          simp only [Linear.units_smul_comp, Category.assoc]
          rw [tensorProductComplex_differential_formula_swap_aux R A B p q
                (p + q) (by omega),
              tensorProductComplex_differential_formula_right_aux R A B p q
                (tensorFlipHomComponent R A B (p + q + 1))]
          simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc]
          rw [tensorFlipHomComponent_on_summand R A B (p + 1) q (p + q + 1)
                (by omega),
              tensorFlipHomComponent_on_summand R A B p (q + 1) (p + q + 1)
                (by omega)]
          simp [MonoidalCategory.tensorHom_def, Int.negOnePow_add, mul_add,
            smul_smul, mul_comm]
          have hp : p.negOnePow * (p.negOnePow * (p * q).negOnePow) =
              (p * q).negOnePow := by
            rw [← mul_assoc, Int.units_mul_self, one_mul]
          rw [hp]
          exact add_comm _ _ }
    inv :=
      { f := tensorFlipInvComponent R A B
        comm' := by
          rintro i _ rfl
          apply HomologicalComplex.mapBifunctor.hom_ext
          intro p q h
          dsimp at h
          subst i
          rw [tensorFlipInvComponent_on_summand_right R A B p q (p + q) rfl]
          simp only [Linear.units_smul_comp, Category.assoc]
          rw [tensorProductComplex_differential_formula_comm_aux R A B p q
                (p + q) (by omega),
              tensorProductComplex_differential_formula_right_aux R B A p q
                (tensorFlipInvComponent R A B (p + q + 1))]
          simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc]
          rw [tensorFlipInvComponent_on_summand R A B (p + 1) q (p + q + 1)
                (by omega),
              tensorFlipInvComponent_on_summand R A B p (q + 1) (p + q + 1)
                (by omega)]
          simp [MonoidalCategory.tensorHom_def, Int.negOnePow_add, mul_add,
            smul_smul, mul_comm]
          have hp : p.negOnePow * (p.negOnePow * (p * q).negOnePow) =
              (p * q).negOnePow := by
            rw [← mul_assoc, Int.units_mul_self, one_mul]
          rw [hp]
          exact add_comm _ _ }
    hom_inv_id := by
      apply HomologicalComplex.hom_ext _ _
      intro n
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      dsimp
      dsimp at h
      subst n
      rw [tensorFlipHomComponent_on_summand_right R A B p q (p + q) rfl
        (tensorFlipInvComponent R A B (p + q))]
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [tensorFlipInvComponent_on_summand R A B q p (p + q)
        (by omega)]
      simp
      have hsign : (p * q).negOnePow * (q * p).negOnePow = (1 : ℤˣ) := by
        rw [mul_comm q p, Int.units_mul_self]
      simp only [smul_smul, hsign, one_smul]
    inv_hom_id := by
      apply HomologicalComplex.hom_ext _ _
      intro n
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      dsimp
      dsimp at h
      subst n
      rw [tensorFlipInvComponent_on_summand_right R A B p q (p + q) rfl
        (tensorFlipHomComponent R A B (p + q))]
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [tensorFlipHomComponent_on_summand R A B q p (p + q)
        (by omega)]
      simp
      have hsign : (p * q).negOnePow * (q * p).negOnePow = (1 : ℤˣ) := by
        rw [mul_comm q p, Int.units_mul_self]
      simp only [smul_smul, hsign, one_smul] }

/-- On the `A^p ⊗ B^q` summand, the signed flip is `(-1)^(pq)` followed by
the ordinary tensor braiding. -/
theorem tensorFlip_on_summand
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) (p q : ℤ) :
    ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q (p + q) rfl ≫ (tensorFlipIso R A B).hom.f (p + q) =
      (p * q).negOnePow •
        ((β_ (A.X p) (B.X q)).hom ≫
          ιMapBifunctor B A (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
              (.up ℤ) q p (p + q) (by dsimp; omega)) := by
  dsimp [tensorFlipIso, tensorFlipHomComponent]
  simp

/-- The interchange map which brings the two `A` factors and the two `B`
factors together before multiplying. -/
noncomputable def tensorInterchange
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) :
    tensorProductComplex R (tensorProductComplex R A B)
        (tensorProductComplex R A B) ⟶
      tensorProductComplex R (tensorProductComplex R A A)
        (tensorProductComplex R B B) :=
  (HomologicalComplex.associator A B (tensorProductComplex R A B)).hom ≫
    tensorHomComplex (𝟙 A)
      ((HomologicalComplex.associator B A B).inv ≫
        tensorHomComplex (tensorFlipIso R B A).hom (𝟙 B) ≫
          (HomologicalComplex.associator A B B).hom) ≫
    (HomologicalComplex.associator A A (tensorProductComplex R B B)).inv

/-- The element of the total tensor product represented by a homogeneous pure
tensor. -/
noncomputable def tensorPure
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) (p q : ℤ)
    (a : A.X p) (b : B.X q) : (tensorProductComplex R A B).X (p + q) :=
  (HomologicalComplex.ιTensorObj A B p q (p + q) rfl).hom (a ⊗ₜ[R] b)

/-- Multiplication on the tensor product DGA. -/
noncomputable def tensorProductMultiplication
    {R : Type u} [CommRing R]
    (A B : CochainDifferentialGradedAlgebra R) :
    tensorProductComplex R (tensorProductComplex R A.complex B.complex)
        (tensorProductComplex R A.complex B.complex) ⟶
      tensorProductComplex R A.complex B.complex :=
  tensorInterchange R A.complex B.complex ≫
    tensorHomComplex A.multiplication B.multiplication

/-- Unit of the tensor product DGA. -/
noncomputable def tensorProductUnit
    {R : Type u} [CommRing R]
    (A B : CochainDifferentialGradedAlgebra R) :
    tensorUnitComplex R ⟶ tensorProductComplex R A.complex B.complex :=
  (HomologicalComplex.leftUnitor (tensorUnitComplex R)).inv ≫
    tensorHomComplex A.unit B.unit

/-- Tensor product of two cochain differential graded algebras. -/
noncomputable def tensorProductDGA
    {R : Type u} [CommRing R]
    (A B : CochainDifferentialGradedAlgebra R) :
    CochainDifferentialGradedAlgebra R where
  complex := tensorProductComplex R A.complex B.complex
  multiplication := tensorProductMultiplication A B
  unit := tensorProductUnit A B
  one_mul := by sorry
  mul_one := by sorry
  mul_assoc := by sorry

/-- On homogeneous pure tensors, the tensor-product multiplication has the
source's Koszul sign `(-1)^(p' q)`. -/
theorem tensorProductDGA_multiplication_on_homogeneous
    (R : Type u) [CommRing R]
    (A B : CochainDifferentialGradedAlgebra R)
    (p q p' q' : ℤ)
    (a : A.complex.X p) (b : B.complex.X q)
    (a' : A.complex.X p') (b' : B.complex.X q') :
    ((tensorProductDGA A B).homogeneousMultiplication (p + q) (p' + q')).hom
        (tensorPure R A.complex B.complex p q a b ⊗ₜ[R]
          tensorPure R A.complex B.complex p' q' a' b') =
      transportComponent (C := (tensorProductDGA A B).complex) (by omega)
        ((p' * q).negOnePow •
          tensorPure R A.complex B.complex (p + p') (q + q')
            ((A.homogeneousMultiplication p p').hom (a ⊗ₜ[R] a'))
            ((B.homogeneousMultiplication q q').hom (b ⊗ₜ[R] b'))) := by
  sorry

/-- The tensor product DGA has the total-complex differential formula from
the source: on `A^p ⊗ B^q` it is `d_A ⊗ 1 + (-1)^p 1 ⊗ d_B`. -/
theorem tensorProductComplex_differential_formula
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) (p q : ℤ) :
    ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q (p + q) rfl ≫
        (tensorProductComplex R A B).d (p + q) (p + q + 1) =
      (A.d p (p + 1) ⊗ₘ 𝟙 (B.X q)) ≫
            ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) (p + 1) q (p + q + 1) (by dsimp; omega) +
        p.negOnePow •
          ((𝟙 (A.X p) ⊗ₘ B.d q (q + 1)) ≫
            ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
              (.up ℤ) p (q + 1) (p + q + 1) (by dsimp; omega)) := by
  sorry

/-! The same tensor-product construction for the chain-indexed convention. -/

/-- The signed flip of total tensor products of chain complexes. -/
noncomputable def chainTensorFlipHomComponent
    (R : Type u) [CommRing R] (A B : ChainComplexOver R) (n : ℤ) :
    (chainTensorProductComplex R A B).X n ⟶
      (chainTensorProductComplex R B A).X n :=
  HomologicalComplex.mapBifunctorDesc (fun p q h =>
    (p * q).negOnePow •
      ((β_ (A.X p) (B.X q)).hom ≫
        ιMapBifunctor B A (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
          (.down ℤ) q p n (by
            rw [ComplexShape.π_symm (.down ℤ) (.down ℤ) (.down ℤ) p q]
            exact h)))

/-- The inverse signed flip of total tensor products of chain complexes. -/
noncomputable def chainTensorFlipInvComponent
    (R : Type u) [CommRing R] (A B : ChainComplexOver R) (n : ℤ) :
    (chainTensorProductComplex R B A).X n ⟶
      (chainTensorProductComplex R A B).X n :=
  HomologicalComplex.mapBifunctorDesc (fun p q h =>
    (p * q).negOnePow •
      ((β_ (B.X p) (A.X q)).hom ≫
        ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
          (.down ℤ) q p n (by
            rw [ComplexShape.π_symm (.down ℤ) (.down ℤ) (.down ℤ) p q]
            exact h)))

/-- The signed Koszul flip for chain complexes. -/
noncomputable def chainTensorFlipIso
    (R : Type u) [CommRing R] (A B : ChainComplexOver R) :
    chainTensorProductComplex R A B ≅ chainTensorProductComplex R B A :=
  { hom :=
      { f := chainTensorFlipHomComponent R A B
        comm' := by sorry }
    inv :=
      { f := chainTensorFlipInvComponent R A B
        comm' := by sorry }
    hom_inv_id := by sorry
    inv_hom_id := by sorry }

/-- The interchange map for the chain-indexed tensor product. -/
noncomputable def chainTensorInterchange
    (R : Type u) [CommRing R] (A B : ChainComplexOver R) :
    chainTensorProductComplex R (chainTensorProductComplex R A B)
        (chainTensorProductComplex R A B) ⟶
      chainTensorProductComplex R (chainTensorProductComplex R A A)
        (chainTensorProductComplex R B B) :=
  (HomologicalComplex.associator A B (chainTensorProductComplex R A B)).hom ≫
    chainTensorHomComplex (𝟙 A)
      ((HomologicalComplex.associator B A B).inv ≫
        chainTensorHomComplex (chainTensorFlipIso R B A).hom (𝟙 B) ≫
          (HomologicalComplex.associator A B B).hom) ≫
    (HomologicalComplex.associator A A (chainTensorProductComplex R B B)).inv

/-- Multiplication on the chain-indexed tensor product DGA. -/
noncomputable def chainTensorProductMultiplication
    {R : Type u} [CommRing R]
    (A B : ChainDifferentialGradedAlgebra R) :
    chainTensorProductComplex R (chainTensorProductComplex R A.complex B.complex)
        (chainTensorProductComplex R A.complex B.complex) ⟶
      chainTensorProductComplex R A.complex B.complex :=
  chainTensorInterchange R A.complex B.complex ≫
    chainTensorHomComplex A.multiplication B.multiplication

/-- Unit of the chain-indexed tensor product DGA. -/
noncomputable def chainTensorProductUnit
    {R : Type u} [CommRing R]
    (A B : ChainDifferentialGradedAlgebra R) :
    chainTensorUnitComplex R ⟶
      chainTensorProductComplex R A.complex B.complex :=
  (HomologicalComplex.leftUnitor (chainTensorUnitComplex R)).inv ≫
    chainTensorHomComplex A.unit B.unit

/-- Tensor product of two chain differential graded algebras. -/
noncomputable def chainTensorProductDGA
    {R : Type u} [CommRing R]
    (A B : ChainDifferentialGradedAlgebra R) :
    ChainDifferentialGradedAlgebra R where
  complex := chainTensorProductComplex R A.complex B.complex
  multiplication := chainTensorProductMultiplication A B
  unit := chainTensorProductUnit A B
  one_mul := by sorry
  mul_one := by sorry
  mul_assoc := by sorry

/-- The element of the chain total tensor product represented by a
homogeneous pure tensor. -/
noncomputable def chainTensorPure
    (R : Type u) [CommRing R] (A B : ChainComplexOver R) (p q : ℤ)
    (a : A.X p) (b : B.X q) :
    (chainTensorProductComplex R A B).X (p + q) :=
  (HomologicalComplex.ιTensorObj A B p q (p + q) rfl).hom (a ⊗ₜ[R] b)

/-- On homogeneous pure tensors, the chain tensor-product multiplication has
the source's Koszul sign `(-1)^(p' q)`. -/
theorem chainTensorProductDGA_multiplication_on_homogeneous
    (R : Type u) [CommRing R]
    (A B : ChainDifferentialGradedAlgebra R)
    (p q p' q' : ℤ)
    (a : A.complex.X p) (b : B.complex.X q)
    (a' : A.complex.X p') (b' : B.complex.X q') :
    ((chainTensorProductDGA A B).homogeneousMultiplication (p + q) (p' + q')).hom
        (chainTensorPure R A.complex B.complex p q a b ⊗ₜ[R]
          chainTensorPure R A.complex B.complex p' q' a' b') =
      transportComponent (C := (chainTensorProductDGA A B).complex) (by omega)
        ((p' * q).negOnePow •
          chainTensorPure R A.complex B.complex (p + p') (q + q')
            ((A.homogeneousMultiplication p p').hom (a ⊗ₜ[R] a'))
            ((B.homogeneousMultiplication q q').hom (b ⊗ₜ[R] b'))) := by
  sorry

/-- The differential on the chain total tensor product is
`d_A ⊗ 1 + (-1)^p 1 ⊗ d_B` on the `A_p ⊗ B_q` summand. -/
theorem chainTensorProductComplex_differential_formula
    (R : Type u) [CommRing R] (A B : ChainComplexOver R) (p q : ℤ) :
    ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.down ℤ) p q (p + q) rfl ≫
        (chainTensorProductComplex R A B).d (p + q) (p + q - 1) =
      (A.d p (p - 1) ⊗ₘ 𝟙 (B.X q)) ≫
            ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.down ℤ) (p - 1) q (p + q - 1) (by dsimp; omega) +
        p.negOnePow •
          ((𝟙 (A.X p) ⊗ₘ B.d q (q - 1)) ≫
            ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
              (.down ℤ) p (q - 1) (p + q - 1) (by dsimp; omega)) := by
  sorry

/-- For DGAs, the underlying cochain complex of the tensor product is the
total tensor complex. -/
theorem tensorProductDGA_underlying_is_total
    (R : Type u) [CommRing R]
    (A B : CochainDifferentialGradedAlgebra R) :
    (tensorProductDGA A B).complex =
      (((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex).obj
        A.complex).obj B.complex :=
  rfl

/-- The cochain tensor-product construction is definitionally the total
complex construction used above. -/
theorem tensorProductComplex_is_total
    (R : Type u) [CommRing R] (A B : CochainComplexOver R) :
    tensorProductComplex R A B =
      (((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex).obj A).obj B :=
  rfl

end Formalization.Books.Dga.Unit03
