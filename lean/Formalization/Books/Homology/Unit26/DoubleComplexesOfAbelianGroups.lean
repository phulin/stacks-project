import Formalization.Books.Homology.Unit18.DoubleComplexes
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Homological Algebra, Chapter 26: Double complexes of abelian groups

This file records the four resolution lemmas in the section
“Double complexes of abelian groups”.  Abelian groups are represented by
Mathlib's `AddCommGrpCat`; double complexes and coproduct totalizations are
the canonical interfaces from Chapter 18.

The resolution structures below make explicit the zero-extension in the
unused half-plane.  This is needed because the source's double complexes are
indexed by `ℤ`, whereas its displayed resolutions are indexed by the
nonnegative integers.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open ComplexShape
open Formalization.Books.Homology.Unit18
open scoped ZeroObject

universe u

namespace Formalization.Books.Homology.Unit26

/-! ## Exact augmented sequences -/

/-- An exact sequence beginning with `M → A 0 → A 1 → ⋯`, including exactness
at `M` and at every nonnegative-indexed term.  The family is indexed by `ℤ`
so that it can be used directly with Chapter 18 double complexes; the values
at negative indices are ignored by the predicate. -/
def IsRightExactSequence {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] (M : C) (A : ℤ → C) (ι : M ⟶ A 0)
    (f : ∀ p : ℤ, A p ⟶ A (p + 1))
    (hι : ι ≫ f 0 = 0)
    (hf : ∀ p : ℤ, f p ≫ f (p + 1) = 0) : Prop :=
  (ShortComplex.mk (0 : (0 : C) ⟶ M) ι (by simp)).Exact ∧
    (ShortComplex.mk ι (f 0) hι).Exact ∧
      ∀ p : ℤ, 0 ≤ p →
        (ShortComplex.mk (f p) (f (p + 1)) (hf p)).Exact

/-- An exact sequence `⋯ → A 2 → A 1 → A 0 → M → 0`, with exactness at `M`
and at every nonnegative-indexed term. -/
def IsLeftExactSequence {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] (A : ℤ → C) (M : C)
    (f : ∀ p : ℤ, A (p + 1) ⟶ A p) (π : A 0 ⟶ M)
    (hf : ∀ p : ℤ, f (p + 1) ≫ f p = 0)
    (hπ : f 0 ≫ π = 0) : Prop :=
  (ShortComplex.mk (f 0) π hπ).Exact ∧
    (ShortComplex.mk π (0 : M ⟶ (0 : C)) (by simp)).Exact ∧
      ∀ p : ℤ, 0 ≤ p →
        (ShortComplex.mk (f (p + 1)) (f p) (hf p)).Exact

/-! ## Kernels and cokernels of cochain differentials -/

abbrev AbelianGroupCochainComplex := CochainComplex AddCommGrpCat.{u} ℤ

/-- The categorical kernel of the differential in degree `q`. -/
noncomputable def kernelOfCochainDifferential
    (K : AbelianGroupCochainComplex) (q : ℤ) : AddCommGrpCat.{u} :=
  kernel (K.d q (q + 1))

/-- The map on differential kernels induced by a map of cochain complexes. -/
noncomputable def kernelOfCochainDifferentialMap
    {K L : AbelianGroupCochainComplex} (f : K ⟶ L) (q : ℤ) :
    kernelOfCochainDifferential K q ⟶ kernelOfCochainDifferential L q :=
  kernel.lift (L.d q (q + 1))
    (kernel.ι (K.d q (q + 1)) ≫ f.f q) (by
      change (kernel.ι (K.d q (q + 1)) ≫ f.f q) ≫ L.d q (q + 1) = 0
      rw [Category.assoc, f.comm q (q + 1), ← Category.assoc,
        kernel.condition, zero_comp])

/-- Maps on differential kernels preserve zero composites. -/
theorem kernelOfCochainDifferentialMap_comp_zero
    {K L N : AbelianGroupCochainComplex} (f : K ⟶ L) (g : L ⟶ N)
    (hfg : f ≫ g = 0) (q : ℤ) :
    kernelOfCochainDifferentialMap f q ≫
        kernelOfCochainDifferentialMap g q = 0 := by
  have hfg_q : f.f q ≫ g.f q = 0 := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
      congrArg (fun k => k.f q) hfg
  apply (cancel_mono (kernel.ι (N.d q (q + 1)))).1
  simp only [kernelOfCochainDifferentialMap, kernelOfCochainDifferential,
    Category.assoc, kernel.lift_ι]
  rw [← Category.assoc, kernel.lift_ι]
  simp [Category.assoc, hfg_q]
  change 0 =
    (0 : kernel (K.d q (q + 1)) ⟶ kernel (N.d q (q + 1))) ≫
      kernel.ι (N.d q (q + 1))
  rw [zero_comp]

/-- The categorical cokernel of the differential in degree `q`. -/
noncomputable def cokernelOfCochainDifferential
    (K : AbelianGroupCochainComplex) (q : ℤ) : AddCommGrpCat.{u} :=
  cokernel (K.d q (q + 1))

/-- The map on differential cokernels induced by a map of cochain complexes. -/
noncomputable def cokernelOfCochainDifferentialMap
    {K L : AbelianGroupCochainComplex} (f : K ⟶ L) (q : ℤ) :
    cokernelOfCochainDifferential K q ⟶ cokernelOfCochainDifferential L q :=
  cokernel.desc (K.d q (q + 1))
    (f.f (q + 1) ≫ cokernel.π (L.d q (q + 1))) (by
      change K.d q (q + 1) ≫ f.f (q + 1) ≫
        cokernel.π (L.d q (q + 1)) = 0
      rw [← Category.assoc, ← f.comm q (q + 1), Category.assoc,
        cokernel.condition, comp_zero])

/-- Maps on differential cokernels preserve zero composites. -/
theorem cokernelOfCochainDifferentialMap_comp_zero
    {K L N : AbelianGroupCochainComplex} (f : K ⟶ L) (g : L ⟶ N)
    (hfg : f ≫ g = 0) (q : ℤ) :
    cokernelOfCochainDifferentialMap f q ≫
        cokernelOfCochainDifferentialMap g q = 0 := by
  have hfg_q1 : f.f (q + 1) ≫ g.f (q + 1) = 0 := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
      congrArg (fun k => k.f (q + 1)) hfg
  have hfcond : K.d q (q + 1) ≫ f.f (q + 1) ≫
      cokernel.π (L.d q (q + 1)) = 0 := by
    rw [← Category.assoc, ← f.comm q (q + 1), Category.assoc,
      cokernel.condition, comp_zero]
  have hgcond : L.d q (q + 1) ≫ g.f (q + 1) ≫
      cokernel.π (N.d q (q + 1)) = 0 := by
    rw [← Category.assoc, ← g.comm q (q + 1), Category.assoc,
      cokernel.condition, comp_zero]
  have hπf : cokernel.π (K.d q (q + 1)) ≫
      cokernelOfCochainDifferentialMap f q =
        f.f (q + 1) ≫ cokernel.π (L.d q (q + 1)) := by
    change cokernel.π (K.d q (q + 1)) ≫
      cokernel.desc (K.d q (q + 1))
        (f.f (q + 1) ≫ cokernel.π (L.d q (q + 1))) hfcond = _
    simp
  have hπg : cokernel.π (L.d q (q + 1)) ≫
      cokernelOfCochainDifferentialMap g q =
        g.f (q + 1) ≫ cokernel.π (N.d q (q + 1)) := by
    change cokernel.π (L.d q (q + 1)) ≫
      cokernel.desc (L.d q (q + 1))
        (g.f (q + 1) ≫ cokernel.π (N.d q (q + 1))) hgcond = _
    simp
  have hπg_comp :
      f.f (q + 1) ≫
          (cokernel.π (L.d q (q + 1)) ≫
            cokernelOfCochainDifferentialMap g q) =
        f.f (q + 1) ≫
          (g.f (q + 1) ≫ cokernel.π (N.d q (q + 1))) := by
    exact congrArg (fun k => f.f (q + 1) ≫ k) hπg
  have hfg_π : f.f (q + 1) ≫ g.f (q + 1) ≫
      cokernel.π (N.d q (q + 1)) = 0 := by
    rw [← Category.assoc, hfg_q1, zero_comp]
  have hfg_π_right : f.f (q + 1) ≫
      (g.f (q + 1) ≫ cokernel.π (N.d q (q + 1))) = 0 := by
    simpa only [Category.assoc] using hfg_π
  apply (cancel_epi (cokernel.π (K.d q (q + 1)))).1
  change (cokernel.π (K.d q (q + 1)) ≫
      cokernelOfCochainDifferentialMap f q) ≫
      cokernelOfCochainDifferentialMap g q =
    cokernel.π (K.d q (q + 1)) ≫
      (0 : cokernel (K.d q (q + 1)) ⟶ cokernel (N.d q (q + 1)))
  rw [hπf]
  change f.f (q + 1) ≫
      (cokernel.π (L.d q (q + 1)) ≫
        cokernelOfCochainDifferentialMap g q) =
    cokernel.π (K.d q (q + 1)) ≫
      (0 : cokernel (K.d q (q + 1)) ⟶ cokernel (N.d q (q + 1)))
  rw [hπg_comp, hfg_π_right]
  change 0 =
    cokernel.π (K.d q (q + 1)) ≫
      (0 : cokernel (K.d q (q + 1)) ⟶ cokernel (N.d q (q + 1)))
  rw [comp_zero]

/-! The index transport needed for the left-hand resolution convention. -/

/-- The map `A_{p+1} → A_p`, expressed using the double complex's first
differential and the equality `-(p + 1) + 1 = -p`. -/
def leftResolutionColumnMap
    (A : DoubleComplex AddCommGrpCat.{u}) (p : ℤ) :
    column A (-(p + 1)) ⟶ column A (-p) :=
  columnMap A (-(p + 1)) ≫ eqToHom (by
    congr 1
    ring)

/-- Consecutive maps in the left resolution convention compose to zero. -/
theorem leftResolutionColumnMap_comp_zero
    (A : DoubleComplex AddCommGrpCat.{u}) (p : ℤ) :
    leftResolutionColumnMap A (p + 1) ≫ leftResolutionColumnMap A p = 0 := by
  dsimp [leftResolutionColumnMap]
  simp only [Category.assoc]
  rw [← eqToHom_naturality_assoc (fun r : ℤ => columnMap A r)
    (show -(p + 1 + 1) + 1 = -(p + 1) by ring)]
  simpa [Category.assoc] using
    congrArg (fun f => f ≫ eqToHom (by congr 1; ring))
      (columnMap_comp_zero A (-(p + 1 + 1)))

/-! ## Resolution data -/

/-- A right resolution of a cochain complex by the columns of a double
complex.  `supported` records the zero extension for negative horizontal
degrees. -/
structure RightDoubleComplexResolution (M : AbelianGroupCochainComplex) where
  doubleComplex : DoubleComplex AddCommGrpCat.{u}
  augmentation : M ⟶ column doubleComplex 0
  augmentation_d : augmentation ≫ columnMap doubleComplex 0 = 0
  exact : IsRightExactSequence M (fun p => column doubleComplex p)
    augmentation (fun p => columnMap doubleComplex p)
    augmentation_d (fun p => columnMap_comp_zero doubleComplex p)
  supported : ∀ (p q : ℤ), p < 0 → IsZero (doubleComplex.obj p q)

/-- A left resolution of a cochain complex by the columns of a double
complex.  The indexing `A (p + 1) → A p` is the source's
`⋯ → A₂ → A₁ → A₀`. -/
structure LeftDoubleComplexResolution (M : AbelianGroupCochainComplex) where
  doubleComplex : DoubleComplex AddCommGrpCat.{u}
  augmentation : column doubleComplex 0 ⟶ M
  augmentation_d : leftResolutionColumnMap doubleComplex 0 ≫ augmentation = 0
  exact : IsLeftExactSequence
    (fun p : ℤ => column doubleComplex (-p)) M
    (leftResolutionColumnMap doubleComplex)
    augmentation
    (leftResolutionColumnMap_comp_zero doubleComplex)
    augmentation_d
  supported : ∀ (p q : ℤ), 0 < p → IsZero (doubleComplex.obj p q)

/-- A right resolution satisfying the additional exactness condition on
cokernels of all vertical differentials. -/
structure GoodRightDoubleComplexResolution
    (M : AbelianGroupCochainComplex) extends
    RightDoubleComplexResolution M where
  cokernel_exact : ∀ q : ℤ,
    IsRightExactSequence
      (cokernelOfCochainDifferential M q)
      (fun p : ℤ =>
        cokernelOfCochainDifferential (column toRightDoubleComplexResolution.doubleComplex p) q)
      (cokernelOfCochainDifferentialMap
        toRightDoubleComplexResolution.augmentation q)
      (fun p : ℤ =>
        cokernelOfCochainDifferentialMap
          (columnMap toRightDoubleComplexResolution.doubleComplex p) q)
      (cokernelOfCochainDifferentialMap_comp_zero
        toRightDoubleComplexResolution.augmentation
        (columnMap toRightDoubleComplexResolution.doubleComplex 0)
        toRightDoubleComplexResolution.augmentation_d q)
      (fun p : ℤ => by
        exact cokernelOfCochainDifferentialMap_comp_zero
          (columnMap toRightDoubleComplexResolution.doubleComplex p)
          (columnMap toRightDoubleComplexResolution.doubleComplex (p + 1))
          (columnMap_comp_zero toRightDoubleComplexResolution.doubleComplex p) q)

/-- A left resolution satisfying the additional exactness condition on
kernels of all vertical differentials. -/
structure GoodLeftDoubleComplexResolution
    (M : AbelianGroupCochainComplex) extends
    LeftDoubleComplexResolution M where
  kernel_exact : ∀ q : ℤ,
    IsLeftExactSequence
      (fun p : ℤ =>
        kernelOfCochainDifferential
          (column toLeftDoubleComplexResolution.doubleComplex (-p)) q)
      (kernelOfCochainDifferential M q)
      (fun p : ℤ =>
        kernelOfCochainDifferentialMap
          (leftResolutionColumnMap toLeftDoubleComplexResolution.doubleComplex p) q)
      (kernelOfCochainDifferentialMap
        toLeftDoubleComplexResolution.augmentation q)
      (fun p : ℤ =>
        kernelOfCochainDifferentialMap_comp_zero
          (leftResolutionColumnMap toLeftDoubleComplexResolution.doubleComplex (p + 1))
          (leftResolutionColumnMap toLeftDoubleComplexResolution.doubleComplex p)
          (leftResolutionColumnMap_comp_zero
            toLeftDoubleComplexResolution.doubleComplex p) q)
      (kernelOfCochainDifferentialMap_comp_zero
        (leftResolutionColumnMap toLeftDoubleComplexResolution.doubleComplex 0)
        toLeftDoubleComplexResolution.augmentation
        toLeftDoubleComplexResolution.augmentation_d q)

/-! ## Product totalization -/

/-- The degree-`n` product total term of a double complex. -/
noncomputable def productTotalTerm
    (A : DoubleComplex AddCommGrpCat.{u}) (n : ℤ) : AddCommGrpCat.{u} :=
  ∏ᶜ fun p : ℤ => A.obj p (n - p)

/-- The displayed product-total differential from the source.  The projection
to the `p`-component is the horizontal contribution from `p - 1` plus the
signed vertical contribution from `p`. -/
noncomputable def productTotalDifferential
    (A : DoubleComplex AddCommGrpCat.{u}) (n : ℤ) :
    productTotalTerm A n ⟶ productTotalTerm A (n + 1) :=
  Pi.lift (fun p =>
    (Pi.π (fun r : ℤ => A.obj r (n - r)) (p - 1) ≫
        A.d1 (p - 1) (n - (p - 1)) ≫
        eqToHom (by
          simp [sub_eq_add_neg, add_comm, add_left_comm])) +
      p.negOnePow •
        (Pi.π (fun r : ℤ => A.obj r (n - r)) p ≫
          A.d2 p (n - p) ≫
            eqToHom (by
              simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm])))

private noncomputable def rightResolutionProductTotalMapComponent
    {M : AbelianGroupCochainComplex}
    (R : RightDoubleComplexResolution M) (n : ℤ) :
    M.X n ⟶ ∏ᶜ fun p : ℤ => R.doubleComplex.obj p (n - p) := by
  exact Pi.lift (fun p => by
    classical
    by_cases hp : p = 0
    · subst p
      exact R.augmentation.f n ≫ eqToHom (by
        change (column R.doubleComplex 0).X n =
          R.doubleComplex.obj 0 (n - 0)
        dsimp [column]
        simp)
    · exact 0)

private theorem rightResolutionProductTotalMapComponent_π
    {M : AbelianGroupCochainComplex}
    (R : RightDoubleComplexResolution M) (n p : ℤ) :
    rightResolutionProductTotalMapComponent R n ≫
        Pi.π (fun r : ℤ => R.doubleComplex.obj r (n - r)) p =
      (if hp : p = 0 then
        hp ▸ R.augmentation.f n ≫ eqToHom (by
          dsimp [column]
          simp)
      else 0) := by
  classical
  change (Pi.lift _ ≫ Pi.π _ p) = _
  rw [Pi.lift_π]

private theorem productTotalTerm_eq
    (A : DoubleComplex AddCommGrpCat.{u}) (n : ℤ) :
    productTotalTerm A n = ∏ᶜ fun q : ℤ => A.obj q (n - q) := by
  rfl

private theorem eqToHom_heq_of_eq
    {C : Type*} [Category C] {X Y : C} (h h' : X = Y) :
    eqToHom h ≍ eqToHom h' := by
  cases h
  cases h'
  rfl

private theorem eqToHom_comp_heq_of_eq
    {C : Type*} [Category C] {X X' Y Z : C}
    (e : X = X') (h : X = Y) (h' : X' = Y) (f : Y ⟶ Z) :
    eqToHom h ≫ f ≍ eqToHom h' ≫ f := by
  cases e
  cases h
  cases h'
  rfl

private theorem eqToHom_heq_of_eq'
    {C : Type*} [Category C] {X X' Y Y' : C}
    (eX : X = X') (eY : Y = Y') (h : X = Y) (h' : X' = Y') :
    eqToHom h ≍ eqToHom h' := by
  cases eX
  cases eY
  cases h
  cases h'
  rfl

private theorem doubleComplex_d1_transport_heq
    (A : DoubleComplex AddCommGrpCat.{u})
    (p p' q q' : ℤ) (hp : p' = p) (hq : q = q') :
    eqToHom (by
      change A.obj p' q = A.obj p q'
      rw [hp, hq]) ≫ A.d1 p q' ≍
      A.d1 p' q ≫ eqToHom (by
        change A.obj (p' + 1) q = A.obj (p + 1) q'
        rw [hp, hq]) := by
  cases hp
  cases hq
  rfl

private theorem doubleComplex_d2_transport_heq
    (A : DoubleComplex AddCommGrpCat.{u})
    (p p' q q' : ℤ) (hp : p' = p) (hq : q = q') :
    eqToHom (by
      change A.obj p' q = A.obj p q'
      rw [hp, hq]) ≫ A.d2 p q' ≍
      A.d2 p' q ≫ eqToHom (by
        change A.obj p' (q + 1) = A.obj p (q' + 1)
        rw [hp, hq]) := by
  cases hp
  cases hq
  rfl

private theorem heq_comp_left_fixed
    {C : Type*} [Category C] {X Y Z Z' : C}
    (f : X ⟶ Y) {g : Y ⟶ Z} {g' : Y ⟶ Z'}
    (e : Z = Z') (h : g ≍ g') : f ≫ g ≍ f ≫ g' := by
  exact heq_comp (eq1 := rfl) (eq2 := rfl) (eq3 := e)
    (HEq.rfl) h

private theorem heq_comp_right_fixed
    {C : Type*} [Category C] {X X' Y Z : C}
    {f : X ⟶ Y} {f' : X' ⟶ Y} (e : X = X') (h : f ≍ f')
    (g : Y ⟶ Z) : f ≫ g ≍ f' ≫ g := by
  exact heq_comp (eq1 := e) (eq2 := rfl) (eq3 := rfl)
    h (HEq.rfl)

private theorem heq_comp_transport
    {C : Type*} [Category C]
    {X X' Y Y' Z Z' : C}
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y ⟶ Z) (g' : Y' ⟶ Z')
    (eX : X = X') (eY : Y = Y') (eZ : Z = Z')
    (hf : f ≍ f') (hg : g ≍ g') :
    f ≫ g ≍ f' ≫ g' := by
  exact heq_comp (eq1 := eX) (eq2 := eY) (eq3 := eZ) hf hg

private theorem heq_comp_transport'
    {C : Type*} [Category C]
    {X X' Y Y' Z Z' : C}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    (hf : f ≍ f') (hg : g ≍ g')
    (eX : X = X') (eY : Y = Y') (eZ : Z = Z') :
    f ≫ g ≍ f' ≫ g' := by
  exact heq_comp (eq1 := eX) (eq2 := eY) (eq3 := eZ) hf hg

private noncomputable def productTotalD1Term
    (A : DoubleComplex AddCommGrpCat.{u}) (n p : ℤ) :
    A.obj p (n - p) ⟶ A.obj (p + 1) (n + 1 - (p + 1)) :=
  A.d1 p (n - p) ≫
      eqToHom (by
        change A.obj (p + 1) (n - p) =
          A.obj (p + 1) (n + 1 - (p + 1))
        congr 1 <;> ring)

private noncomputable def productTotalD2Term
    (A : DoubleComplex AddCommGrpCat.{u}) (n p : ℤ) :
    A.obj p (n - p) ⟶ A.obj p (n + 1 - p) :=
  A.d2 p (n - p) ≫
      eqToHom (by
        change A.obj p (n - p + 1) = A.obj p (n + 1 - p)
        congr 1 <;> ring)

private noncomputable def productTotalD1Component
    (A : DoubleComplex AddCommGrpCat.{u}) (n p : ℤ) :
    productTotalTerm A n ⟶ A.obj p (n + 1 - p) :=
  eqToHom (productTotalTerm_eq A n) ≫
    Pi.π (fun r : ℤ => A.obj r (n - r)) (p - 1) ≫
      productTotalD1Term A n (p - 1) ≫
      eqToHom (by
        change A.obj (p - 1 + 1) (n + 1 - (p - 1 + 1)) =
          A.obj p (n + 1 - p)
        congr 1 <;> ring)

private noncomputable def productTotalD2Component
  (A : DoubleComplex AddCommGrpCat.{u}) (n p : ℤ) :
    productTotalTerm A n ⟶ A.obj p (n + 1 - p) :=
  eqToHom (productTotalTerm_eq A n) ≫
    Pi.π (fun r : ℤ => A.obj r (n - r)) p ≫ productTotalD2Term A n p

private noncomputable def productTotalD1Object
    (A : DoubleComplex AddCommGrpCat.{u}) (n p : ℤ) :
    A.obj p (n - p) ⟶ A.obj (p + 1) (n + 1 - (p + 1)) :=
  A.d1 p (n - p) ≫
    eqToHom (by
      change A.obj (p + 1) (n - p) =
        A.obj (p + 1) (n + 1 - (p + 1))
      congr 1 <;> ring)

private noncomputable def productTotalD2Object
    (A : DoubleComplex AddCommGrpCat.{u}) (n p : ℤ) :
    A.obj p (n - p) ⟶ A.obj p (n + 1 - p) :=
  A.d2 p (n - p) ≫
    eqToHom (by
      change A.obj p (n - p + 1) = A.obj p (n + 1 - p)
      congr 1 <;> ring)

private noncomputable def productTotalDifferentialComponent
    (A : DoubleComplex AddCommGrpCat.{u}) (n p : ℤ) :
    productTotalTerm A n ⟶ A.obj p (n + 1 - p) :=
  eqToHom (productTotalTerm_eq A n) ≫
    ((Pi.π (fun r : ℤ => A.obj r (n - r)) (p - 1) ≫
        productTotalD1Term A n (p - 1) ≫
        eqToHom (by
          change A.obj (p - 1 + 1) (n + 1 - (p - 1 + 1)) =
            A.obj p (n + 1 - p)
          congr 1 <;> ring)) +
      p.negOnePow •
        (Pi.π (fun r : ℤ => A.obj r (n - r)) p ≫
          productTotalD2Term A n p))

private theorem productTotalDifferential_π
    (A : DoubleComplex AddCommGrpCat.{u}) (n p : ℤ) :
    productTotalDifferential A n ≫
        Pi.π (fun q : ℤ => A.obj q (n + 1 - q)) p =
      productTotalDifferentialComponent A n p := by
  change (Pi.lift _ ≫ Pi.π _ p) = _
  rw [Pi.lift_π]
  dsimp [productTotalDifferentialComponent, productTotalD1Term,
    productTotalD2Term]
  apply eq_of_heq
  let f : (∏ᶜ fun r : ℤ => A.obj r (n - r)) ⟶ A.obj p (n + 1 - p) :=
    (Pi.π (fun r : ℤ => A.obj r (n - r)) (p - 1) ≫
        productTotalD1Term A n (p - 1) ≫
        eqToHom (by
          change A.obj (p - 1 + 1) (n + 1 - (p - 1 + 1)) =
            A.obj p (n + 1 - p)
          congr 1 <;> ring)) +
      p.negOnePow •
        (Pi.π (fun r : ℤ => A.obj r (n - r)) p ≫
          productTotalD2Term A n p)
  let g : (∏ᶜ fun r : ℤ => A.obj r (n - r)) ⟶ A.obj p (n + 1 - p) :=
    (Pi.π (fun r : ℤ => A.obj r (n - r)) (p - 1) ≫
        A.d1 (p - 1) (n - (p - 1)) ≫
        eqToHom (by
          change A.obj (p - 1 + 1) (n - (p - 1)) =
            A.obj p (n + 1 - p)
          congr 1 <;> ring)) +
      p.negOnePow •
        (Pi.π (fun r : ℤ => A.obj r (n - r)) p ≫
          A.d2 p (n - p) ≫
          eqToHom (by
            change A.obj p (n - p + 1) = A.obj p (n + 1 - p)
            congr 1 <;> ring))
  have hgf : g ≍ f := by
    simp only [g, f, productTotalD1Term, productTotalD2Term,
      Category.assoc, eqToHom_trans]
    exact HEq.rfl
  have hfg : f ≍ eqToHom (productTotalTerm_eq A n) ≫ f :=
    (eqToHom_comp_heq (C := AddCommGrpCat) f
      (productTotalTerm_eq A n)).symm
  simpa only [productTotalTerm, g, f, productTotalD1Term,
    productTotalD2Term, Category.assoc, eqToHom_trans] using hgf.trans hfg

/-- The product-total differential squares to zero. -/
theorem productTotalDifferential_comp_zero
    (A : DoubleComplex AddCommGrpCat.{u}) (n : ℤ) :
    productTotalDifferential A n ≫ productTotalDifferential A (n + 1) = 0 := by
  sorry
  /- Original proof attempt:
  apply Pi.hom_ext
  intro p
  change productTotalDifferential A n ≫
      (productTotalDifferential A (n + 1) ≫
        Pi.π (fun q : ℤ => A.obj q (n + 1 + 1 - q)) p) = _
  rw [productTotalDifferential_π]
  have hcomp :
      productTotalDifferential A n ≫
          productTotalDifferentialComponent A (n + 1) p = 0 := by
    let hq := productTotalTerm_eq A (n + 1)
    have hD :
        productTotalDifferential A n ≫
            eqToHom hq =
          Pi.lift (fun q => productTotalDifferentialComponent A n q) := by
      apply Pi.hom_ext
      intro q
      rw [Pi.lift_π]
      have hπ :
          eqToHom hq ≫
              Pi.π (fun r : ℤ => A.obj r (n + 1 - r)) q =
            Pi.π (fun r : ℤ => A.obj r (n + 1 - r)) q := by
        apply eq_of_heq
        exact eqToHom_comp_heq (R.augmentation.f (n + 1)) _
      rw [Category.assoc, hπ]
      exact productTotalDifferential_π A n q
    have h11 :
        productTotalD1Component A n (p - 1) ≫
            productTotalD1Object A (n + 1) (p - 1) = 0 := by
      dsimp [productTotalD1Component, productTotalD1Term,
        productTotalD1Object]
      simp [Category.assoc, sub_add_cancel]
      have hs := congrArg (fun f =>
          Pi.π (fun r : ℤ => A.obj r (n - r)) (p - 1 - 1) ≫ f ≫
            eqToHom (by
              change A.obj (p - 1 - 1 + 1 + 1) (n - (p - 1 - 1)) =
                A.obj (p - 1 + 1) (n + 1 + 1 - (p - 1 + 1))
              congr 1 <;> ring))
        (A.d1_sq (p - 1 - 1) (n - (p - 1 - 1)))
      convert hs using 1
      · simp only [Category.assoc]
        have ht := doubleComplex_d1_transport_heq A (p - 1)
          (p - 1 - 1 + 1) (n - (p - 1 - 1))
          (n + 1 - (p - 1)) (by ring) (by ring)
        have ht' := heq_comp_left_fixed
          (Pi.π (fun r : ℤ => A.obj r (n - r)) (p - 1 - 1) ≫
            A.d1 (p - 1 - 1) (n - (p - 1 - 1)))
          (by congr 1 <;> ring) ht
        let g : A.obj (p - 1 + 1) (n + 1 - (p - 1)) ⟶
            A.obj (p - 1 + 1) (n + 1 + 1 - (p - 1 + 1)) :=
          eqToHom (by
            change A.obj (p - 1 + 1) (n + 1 - (p - 1)) =
              A.obj (p - 1 + 1) (n + 1 + 1 - (p - 1 + 1))
            congr 1 <;> ring)
        have ht''' := heq_comp_transport' ht' (HEq.rfl : g ≍ g)
          rfl (by congr 1 <;> ring) rfl
        simpa [g, Category.assoc, eqToHom_trans] using ht'''
      · simp
    have h22 :
        productTotalD2Component A n p ≫
            productTotalD2Object A (n + 1) p = 0 := by
      dsimp [productTotalD2Component, productTotalD2Term,
        productTotalD2Object]
      simp [Category.assoc]
      rw [← eqToHom_naturality_assoc (fun q : ℤ => A.d2 p q)
        (show n - p + 1 = n + 1 - p by ring)]
      simpa [Category.assoc] using
        congrArg (fun f =>
          Pi.π (fun r : ℤ => A.obj r (n - r)) p ≫ f ≫
            eqToHom (by congr 1; ring))
          (A.d2_sq p (n - p))
    have hcomm :
        productTotalD1Component A n p ≫
            productTotalD2Object A (n + 1) p =
        productTotalD2Component A n (p - 1) ≫
            productTotalD1Object A (n + 1) (p - 1) ≫
            eqToHom (by
              change A.obj (p - 1 + 1) (n + 1 + 1 - (p - 1 + 1)) =
                A.obj p (n + 1 + 1 - p)
              congr 1 <;> ring) := by
      dsimp [productTotalD1Component, productTotalD1Term,
        productTotalD2Component, productTotalD2Term,
        productTotalD1Object, productTotalD2Object]
      simp [Category.assoc, sub_add_cancel]
      have hs := congrArg (fun f =>
          eqToHom (productTotalTerm_eq A n) ≫
            Pi.π (fun r : ℤ => A.obj r (n - r)) (p - 1) ≫ f ≫
            eqToHom (by
              change A.obj (p - 1 + 1) (n - (p - 1) + 1) =
                A.obj p (n + 1 + 1 - p)
              congr 1 <;> ring))
        (A.comm (p - 1) (n - (p - 1))).symm
      convert hs using 1
      · simp only [Category.assoc]
        have ht := doubleComplex_d2_transport_heq A p (p - 1 + 1)
          (n - (p - 1)) (n + 1 - p) (by ring) (by ring)
        have ht' := heq_comp_left_fixed
          (eqToHom (productTotalTerm_eq A n) ≫
            Pi.π (fun r : ℤ => A.obj r (n - r)) (p - 1) ≫
            A.d1 (p - 1) (n - (p - 1)))
          (by congr 1 <;> ring) ht
        have ht'' := heq_comp_right_fixed rfl ht'
          (eqToHom (by
            change A.obj p (n + 1 - p + 1) =
              A.obj p (n + 1 + 1 - p)
            congr 1 <;> ring))
        apply eq_of_heq
        simpa [Category.assoc, eqToHom_trans] using ht''
      · simp only [Category.assoc]
        have ht := doubleComplex_d1_transport_heq A (p - 1) (p - 1)
          (n - (p - 1) + 1) (n + 1 - (p - 1)) (by ring) (by ring)
        have ht' := heq_comp_left_fixed
          (eqToHom (productTotalTerm_eq A n) ≫
            Pi.π (fun r : ℤ => A.obj r (n - r)) (p - 1) ≫
            A.d2 (p - 1) (n - (p - 1)))
          (by congr 1 <;> ring) ht
        let g : A.obj (p - 1 + 1) (n + 1 - (p - 1)) ⟶
            A.obj p (n + 1 + 1 - p) :=
          eqToHom (by
            change A.obj (p - 1 + 1) (n + 1 - (p - 1)) =
              A.obj p (n + 1 + 1 - p)
            congr 1 <;> ring)
        have ht''' := heq_comp_transport' ht' (HEq.rfl : g ≍ g)
          rfl (by congr 1 <;> ring) rfl
        simpa [g, Category.assoc, eqToHom_trans] using ht'''
    have h11' :
        productTotalD1Component A n (p - 1) ≫
            productTotalD1Object A (n + 1) (p - 1) ≫
            eqToHom (by
              change A.obj (p - 1 + 1) (n + 1 + 1 - (p - 1 + 1)) =
                A.obj p (n + 1 + 1 - p)
              congr 1 <;> ring) = 0 := by
      rw [← Category.assoc, h11, zero_comp]
    have h22' :
        productTotalD2Component A n p ≫
            productTotalD2Object A (n + 1) p = 0 := h22
    have hcomm' :
        productTotalD1Component A n p ≫
            productTotalD2Object A (n + 1) p =
          productTotalD2Component A n (p - 1) ≫
            productTotalD1Object A (n + 1) (p - 1) ≫
            eqToHom (by
              change A.obj (p - 1 + 1) (n + 1 + 1 - (p - 1 + 1)) =
                A.obj p (n + 1 + 1 - p)
              congr 1 <;> ring) := hcomm
    have hsplit1 :
        productTotalDifferentialComponent A n (p - 1) ≫
            productTotalD1Object A (n + 1) (p - 1) ≫
            eqToHom (by
              change A.obj (p - 1 + 1) (n + 1 + 1 - (p - 1 + 1)) =
                A.obj p (n + 1 + 1 - p)
              congr 1 <;> ring) =
          productTotalD1Component A n (p - 1) ≫
              productTotalD1Object A (n + 1) (p - 1) ≫
              eqToHom (by
                change A.obj (p - 1 + 1) (n + 1 + 1 - (p - 1 + 1)) =
                  A.obj p (n + 1 + 1 - p)
                congr 1 <;> ring) +
            (p - 1).negOnePow •
              (productTotalD2Component A n (p - 1) ≫
                productTotalD1Object A (n + 1) (p - 1) ≫
                eqToHom (by
                  change A.obj (p - 1 + 1) (n + 1 + 1 - (p - 1 + 1)) =
                    A.obj p (n + 1 + 1 - p)
                  congr 1 <;> ring)) := by
      dsimp [productTotalDifferentialComponent, productTotalD1Component,
        productTotalD2Component]
      simp [Category.assoc]
    have hsplit2 :
        p.negOnePow •
            (productTotalDifferentialComponent A n p ≫
              productTotalD2Object A (n + 1) p) =
          p.negOnePow •
            (productTotalD1Component A n p ≫
              productTotalD2Object A (n + 1) p) +
            p.negOnePow • p.negOnePow •
              (productTotalD2Component A n p ≫
                productTotalD2Object A (n + 1) p) := by
      dsimp [productTotalDifferentialComponent, productTotalD1Component,
        productTotalD2Component]
      simp [Category.assoc]
    dsimp [productTotalDifferentialComponent]
    rw [← Category.assoc]
    rw [show productTotalDifferential A n ≫
        eqToHom (productTotalTerm_eq A (n + 1)) =
          Pi.lift (fun q => productTotalDifferentialComponent A n q) by
      simpa [hq] using hD]
    rw [Preadditive.comp_add]
    rw [← Category.assoc, Pi.lift_π]
    simp [Category.assoc]
    change
      productTotalDifferentialComponent A n (p - 1) ≫
          productTotalD1Object A (n + 1) (p - 1) ≫
            eqToHom (by
              change A.obj (p - 1 + 1) (n + 1 + 1 - (p - 1 + 1)) =
                A.obj p (n + 1 + 1 - p)
              congr 1 <;> ring) +
        p.negOnePow •
          (productTotalDifferentialComponent A n p ≫
            productTotalD2Object A (n + 1) p) = 0
    rw [hsplit1, hsplit2, h11', ← hcomm', h22']
    have hsign : (p - 1).negOnePow = -p.negOnePow := by
      conv_rhs => rw [show p = (p - 1) + 1 by ring]
      rw [Int.negOnePow_succ]
      simp
    rw [hsign]
    simp
  rw [hcomp]
  apply eq_of_heq
  symm
  apply heq_of_eq
  exact zero_comp
  -/

noncomputable def productTotalComplex
    (A : DoubleComplex AddCommGrpCat.{u}) : AbelianGroupCochainComplex where
  X n := productTotalTerm A n
  d n m := if h : n + 1 = m then h ▸ productTotalDifferential A n else 0
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
    exact productTotalDifferential_comp_zero A n

/-! ## Maps from the displayed resolutions to their total complexes -/

/-- The map from a right resolution to its coproduct total complex. -/
noncomputable def rightResolutionTotalMap
    {M : AbelianGroupCochainComplex}
    (R : RightDoubleComplexResolution M) :
    M ⟶ totalComplex R.doubleComplex where
  f n := R.augmentation.f n ≫
    eqToHom (by
      dsimp [column]
      congr 1
      ring) ≫
      Sigma.ι (fun p : ℤ => R.doubleComplex.obj p (n - p)) 0
  comm' n m hnm := by
    classical
    have hnm' : n + 1 = m := by
      simpa only [ComplexShape.up_Rel] using hnm
    subst m
    cases hnm'
    simp only [totalComplex, dif_pos, totalDifferential, Sigma.ι_desc,
      Category.assoc, Preadditive.comp_add,
      Int.negOnePow_zero, one_smul]
    have haug_d := congrArg (fun f => f.f n) R.augmentation_d
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at haug_d
    have hhor :
        R.augmentation.f n ≫
            eqToHom (by dsimp [column]; congr 1; ring) ≫
            totalD1Component R.doubleComplex n 0 ≫
            Sigma.ι (fun r : ℤ => R.doubleComplex.obj r (n + 1 - r)) (0 + 1) = 0 := by
      dsimp [totalD1Component]
      simp only [Category.assoc]
      change R.augmentation.f n ≫
        eqToHom (by dsimp [column]; congr 1; ring) ≫
          (columnMap R.doubleComplex 0).f (n - 0) ≫
          eqToHom (by dsimp [column]; congr 1; ring) ≫
          Sigma.ι (fun r : ℤ => R.doubleComplex.obj r (n + 1 - r)) (0 + 1) = 0
      rw [← eqToHom_naturality_assoc
        (fun q : ℤ => (columnMap R.doubleComplex 0).f q)
        (show n = n - 0 by ring)]
      rw [← Category.assoc, haug_d, zero_comp]
    have hcomm := R.augmentation.comm n (n + 1)
    have hcolumn :
        R.augmentation.f n ≫
            eqToHom (by dsimp [column]; congr 1; ring) ≫
            (column R.doubleComplex 0).d (n - 0) (n - 0 + 1) ≫
            eqToHom (by dsimp [column]; congr 1; ring) ≫
            Sigma.ι (fun r : ℤ => R.doubleComplex.obj r (n + 1 - r)) 0 =
          M.d n (n + 1) ≫ R.augmentation.f (n + 1) ≫
            eqToHom (by
              change R.doubleComplex.obj 0 (n + 1) =
                R.doubleComplex.obj 0 (n + 1 - 0)
              congr 1
              ring) ≫
            Sigma.ι (fun r : ℤ => R.doubleComplex.obj r (n + 1 - r)) 0 := by
      rw [← eqToHom_naturality_assoc
        (fun q : ℤ => (column R.doubleComplex 0).d q (q + 1))
        (show n = n - 0 by ring)]
      rw [← Category.assoc, hcomm]
      simp [Category.assoc]
    have hvert :
        R.augmentation.f n ≫
            eqToHom (by dsimp [column]; congr 1; ring) ≫
            totalD2Component R.doubleComplex n 0 ≫
            Sigma.ι (fun r : ℤ => R.doubleComplex.obj r (n + 1 - r)) 0 =
          M.d n (n + 1) ≫ R.augmentation.f (n + 1) ≫
            eqToHom (by
              change R.doubleComplex.obj 0 (n + 1) =
                R.doubleComplex.obj 0 (n + 1 - 0)
              congr 1
              ring) ≫
            Sigma.ι (fun r : ℤ => R.doubleComplex.obj r (n + 1 - r)) 0 := by
      simpa [totalD2Component, column, Category.assoc] using hcolumn
    rw [hhor, hvert]
    simp

/-- The map from a right resolution into its product total complex. -/
noncomputable def rightResolutionProductTotalMap
    {M : AbelianGroupCochainComplex}
  (R : RightDoubleComplexResolution M) :
    M ⟶ productTotalComplex R.doubleComplex where
  f n := by
    change M.X n ⟶ ∏ᶜ fun p : ℤ => R.doubleComplex.obj p (n - p)
    exact rightResolutionProductTotalMapComponent R n
  comm' n m hnm := by
    classical
    have hnm' : n + 1 = m := by
      simpa only [ComplexShape.up_Rel] using hnm
    subst m
    change rightResolutionProductTotalMapComponent R n ≫
        (if h : n + 1 = n + 1 then h ▸ productTotalDifferential R.doubleComplex n else 0) =
      M.d n (n + 1) ≫ rightResolutionProductTotalMapComponent R (n + 1)
    apply Pi.hom_ext
    intro p
    split_ifs with h
    · cases h
      change (rightResolutionProductTotalMapComponent R n ≫
        (Pi.lift _ ≫
          Pi.π (fun q : ℤ => R.doubleComplex.obj q (n + 1 - q)) p)) =
        (M.d n (n + 1) ≫ rightResolutionProductTotalMapComponent R (n + 1)) ≫
          Pi.π (fun q : ℤ => R.doubleComplex.obj q (n + 1 - q)) p
      dsimp [productTotalTerm]
      rw [Pi.lift_π]
      rw [Category.assoc, rightResolutionProductTotalMapComponent_π]
      change rightResolutionProductTotalMapComponent R n ≫
          (show (∏ᶜ fun r : ℤ => R.doubleComplex.obj r (n - r)) ⟶
              R.doubleComplex.obj p (n + 1 - p) from _) = _
      rw [Preadditive.comp_add]
      by_cases hp0 : p = 0
      · subst p
        rw [← Category.assoc, rightResolutionProductTotalMapComponent_π]
        simp [rightResolutionProductTotalMapComponent_π, Category.assoc,
          R.augmentation.comm n (n + 1)]
        rw [← Category.assoc, rightResolutionProductTotalMapComponent_π]
        have hcolumn :
            R.augmentation.f n ≫
                eqToHom (by dsimp [column]; simp) ≫
                (column R.doubleComplex 0).d (n - 0) (n - 0 + 1) ≫
                eqToHom (by dsimp [column]) =
              M.d n (n + 1) ≫ R.augmentation.f (n + 1) ≫
                eqToHom (by
                  change R.doubleComplex.obj 0 (n + 1) =
                    R.doubleComplex.obj 0 (n - 0 + 1)
                  congr 1 <;> ring) := by
          rw [← eqToHom_naturality_assoc
            (fun q : ℤ => (column R.doubleComplex 0).d q (q + 1))
            (show n = n - 0 by ring)]
          rw [← Category.assoc, R.augmentation.comm n (n + 1)]
          simp only [Category.assoc]
          congr 1
        convert hcolumn using 1
        · congr 1 <;> ring
        · simp [rightResolutionProductTotalMapComponent_π, column, Category.assoc]
          exact comp_eqToHom_heq
            (R.augmentation.f (n - 0) ≫ R.doubleComplex.d2 0 (n - 0)) _
        · congr 2
          · congr 1 <;> ring
          · congr 1 <;> ring
          · apply eqToHom_heq_of_eq' (C := AddCommGrpCat)
            · congr 1 <;> ring
            · congr 1 <;> ring
      · by_cases hp1 : p = 1
        · subst p
          rw [← Category.assoc, rightResolutionProductTotalMapComponent_π]
          simp [rightResolutionProductTotalMapComponent_π, Category.assoc]
          have haug_d := congrArg (fun f => f.f n) R.augmentation_d
          simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at haug_d
          have hzero :
              rightResolutionProductTotalMapComponent R n ≫
                  Pi.π (fun r : ℤ => R.doubleComplex.obj r (n - r)) 1 = 0 := by
            rw [rightResolutionProductTotalMapComponent_π]
            simp
          have hhor :
              R.augmentation.f n ≫
                  eqToHom (by
                    change (column R.doubleComplex 0).X n =
                      (column R.doubleComplex 0).X (n - 0)
                    dsimp [column]
                    congr 1
                    ring) ≫
                  (columnMap R.doubleComplex 0).f (n - 0) ≫
                  eqToHom (by
                    change (column R.doubleComplex 1).X (n - 0) =
                      R.doubleComplex.obj 1 (n - 0)
                    dsimp [column]) = 0 := by
            rw [← eqToHom_naturality_assoc
              (fun q : ℤ => (columnMap R.doubleComplex 0).f q)
              (show n = n - 0 by ring)]
            rw [← Category.assoc, haug_d, zero_comp]
          have hhor' :
              R.augmentation.f n ≫
                  eqToHom (by
                    change (column R.doubleComplex 0).X n =
                      R.doubleComplex.obj 0 (n + 1 - 1)
                    dsimp [column]
                    congr 1
                    ring) ≫
                  R.doubleComplex.d1 0 (n + 1 - 1) = 0 := by
            have hnat :
                R.augmentation.f n ≫
                    eqToHom (by
                      change (column R.doubleComplex 0).X n =
                        (column R.doubleComplex 0).X (n + 1 - 1)
                      dsimp [column]
                      congr 1
                      ring) ≫
                    (columnMap R.doubleComplex 0).f (n + 1 - 1) ≫
                    eqToHom (by
                      change (column R.doubleComplex 1).X (n + 1 - 1) =
                        R.doubleComplex.obj 1 (n + 1 - 1)
                      dsimp [column]) = 0 := by
              rw [← eqToHom_naturality_assoc
                (fun q : ℤ => (columnMap R.doubleComplex 0).f q)
                (show n = n + 1 - 1 by ring)]
              rw [← Category.assoc, haug_d, zero_comp]
            convert hnat using 1
            · congr 1
            · simp [columnMap, column, Category.assoc]
          have hvert :
              -rightResolutionProductTotalMapComponent R n ≫
                  Pi.π (fun r : ℤ => R.doubleComplex.obj r (n - r)) 1 ≫
                  R.doubleComplex.d2 1 (n - 1) ≫
                  eqToHom (by
                    change R.doubleComplex.obj 1 (n - 1 + 1) =
                      R.doubleComplex.obj 1 (n + 1 - 1)
                    congr 1
                    ring) = 0 := by
            rw [← Category.assoc, ← Category.assoc, hzero, zero_comp]
            simp
          rw [hhor', zero_add]
          rw [hvert]
        · have hp_prev : p - 1 ≠ 0 := by omega
          rw [← Category.assoc, rightResolutionProductTotalMapComponent_π]
          simp [rightResolutionProductTotalMapComponent_π, hp0, hp_prev, hp1,
            Category.assoc]
          rw [← Category.assoc, rightResolutionProductTotalMapComponent_π]
          simp [hp0, hp_prev, hp1, Category.assoc]
    · exact (h rfl).elim

/-- The map from the coproduct total complex of a left resolution to its
resolved complex. -/
noncomputable def leftResolutionTotalMap
    {M : AbelianGroupCochainComplex}
    (R : LeftDoubleComplexResolution M) :
    totalComplex R.doubleComplex ⟶ M where
  f n := by
    classical
    refine Sigma.desc (fun p => ?_)
    by_cases hp : p = 0
    · subst p
      exact eqToHom (by
        dsimp [column]
        simp) ≫ R.augmentation.f n
    · exact 0
  comm' n m hnm := by
    classical
    have hnm' : n + 1 = m := by
      simpa only [ComplexShape.up_Rel] using hnm
    subst m
    cases hnm'
    simp only [totalComplex, dif_pos, totalDifferential,
      Category.assoc, Preadditive.comp_add]
    apply Sigma.hom_ext
    intro p
    simp [Category.assoc]
    by_cases hp0 : p = 0
    · subst p
      simp [totalD2Component, column, Category.assoc,
        R.augmentation.comm n (n + 1)]
      have hcomm := R.augmentation.comm n (n + 1)
      convert hcomm using 1
      · congr 1
        dsimp [column]
        congr 1
        ring
      · exact eqToHom_comp_heq _ _
      · simp only [column, dif_pos, eqToHom_trans]
        have hnat :=
          eqToHom_naturality_assoc
            (fun q : ℤ => R.doubleComplex.d2 0 q)
            (show n - 0 = n by ring)
            (eqToHom (by
              change R.doubleComplex.obj 0 (n + 1) =
                (column R.doubleComplex 0).X (n + 1)
              dsimp [column]
              ) ≫ R.augmentation.f (n + 1))
        have hremove_in :
            eqToHom (by
                change R.doubleComplex.obj 0 (n - 0) =
                  R.doubleComplex.obj 0 n
                congr 1
                ring) ≫ R.doubleComplex.d2 0 n ≫
                (eqToHom (by
                  change R.doubleComplex.obj 0 (n + 1) =
                    (column R.doubleComplex 0).X (n + 1)
                  dsimp [column]) ≫ R.augmentation.f (n + 1)) ≍
              R.doubleComplex.d2 0 n ≫
                (eqToHom (by
                  change R.doubleComplex.obj 0 (n + 1) =
                    (column R.doubleComplex 0).X (n + 1)
                  dsimp [column]) ≫ R.augmentation.f (n + 1)) := by
          exact eqToHom_comp_heq _ _
        have hremove_out :
            R.doubleComplex.d2 0 n ≫
                eqToHom (by
                  change R.doubleComplex.obj 0 (n + 1) =
                    (column R.doubleComplex 0).X (n + 1)
                  dsimp [column]) ≫ R.augmentation.f (n + 1) ≍
              R.doubleComplex.d2 0 n ≫ R.augmentation.f (n + 1) := by
          have h := comp_eqToHom_heq (R.doubleComplex.d2 0 n) (by
            change R.doubleComplex.obj 0 (n + 1) =
              (column R.doubleComplex 0).X (n + 1)
            dsimp [column])
          apply heq_comp (eq1 := rfl) (eq2 := rfl) (eq3 := rfl)
          · exact h
          · rfl
        convert (heq_of_eq hnat).trans (hremove_in.trans hremove_out) using 1
        congr 2
        · congr 1
          ring
        · apply eqToHom_heq_of_eq' (C := AddCommGrpCat)
          · congr 1 <;> ring
          · congr 1 <;> ring
        · apply eqToHom_comp_heq_of_eq (C := AddCommGrpCat)
          congr 1 <;> ring
    · by_cases hp1 : p + 1 = 0
      · have hp : p = -1 := by omega
        subst p
        simp [Category.assoc]
        have haug_d := congrArg (fun f => f.f (n + 1)) R.augmentation_d
        simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at haug_d
        convert haug_d.symm using 1
        · congr 1
        · rfl
        · simp [leftResolutionColumnMap, columnMap, totalD1Component,
            column, sub_eq_add_neg, Category.assoc]
          symm
          conv_lhs => rw [← Category.assoc]
          apply eq_of_heq
          apply heq_comp (eq1 := rfl) (eq2 := rfl) (eq3 := rfl)
          · exact HEq.rfl
          · exact HEq.rfl
      · simp [hp0, hp1, Category.assoc]

/-- The map from the product total complex of a left resolution to its
resolved complex. -/
noncomputable def leftResolutionProductTotalMap
    {M : AbelianGroupCochainComplex}
    (R : LeftDoubleComplexResolution M) :
    productTotalComplex R.doubleComplex ⟶ M where
  f n :=
    Pi.π (fun p : ℤ => R.doubleComplex.obj p (n - p)) 0 ≫
      eqToHom (by congr 1; ring) ≫ R.augmentation.f n
  comm' n m hnm := by
    classical
    have hnm' : n + 1 = m := by
      simpa only [ComplexShape.up_Rel] using hnm
    subst m
    cases hnm'
    change
      (Pi.π (fun p : ℤ => R.doubleComplex.obj p (n - p)) 0 ≫
          eqToHom (by dsimp [column]; congr 1; ring) ≫ R.augmentation.f n) ≫
          M.d n (n + 1) =
        (if h : n + 1 = n + 1 then
            h ▸ productTotalDifferential R.doubleComplex n
          else 0) ≫
          (Pi.π (fun p : ℤ => R.doubleComplex.obj p (n + 1 - p)) 0 ≫
            eqToHom (by dsimp [column]; congr 1; ring) ≫ R.augmentation.f (n + 1))
    rw [dif_pos rfl]
    change
      (Pi.π (fun p : ℤ => R.doubleComplex.obj p (n - p)) 0 ≫
          eqToHom (by dsimp [column]; congr 1; ring) ≫ R.augmentation.f n) ≫
          M.d n (n + 1) =
        (Pi.lift _ ≫
            Pi.π (fun p : ℤ => R.doubleComplex.obj p (n + 1 - p)) 0) ≫
          (eqToHom (by dsimp [column]; congr 1; ring) ≫
            R.augmentation.f (n + 1))
    dsimp [productTotalTerm]
    rw [Pi.lift_π]
    dsimp [productTotalDifferentialComponent, productTotalD1Term,
      productTotalD2Term]
    simp only [Category.assoc, Preadditive.comp_add, Preadditive.comp_zsmul]
    have hhor :
        (Pi.π (fun p : ℤ => R.doubleComplex.obj p (n - p)) (-1) ≫
            R.doubleComplex.d1 (-1) (n - (-1)) ≫
            eqToHom (by
              change R.doubleComplex.obj (-1 + 1) (n - (-1)) =
                R.doubleComplex.obj (-1 + 1) (n + 1 - (-1 + 1))
              congr 1 <;> ring)) ≫
            eqToHom (by
              change R.doubleComplex.obj 0 (n + 1 - 0) =
                (column R.doubleComplex 0).X (n + 1)
              dsimp [column]
              congr 1 <;> ring) ≫
            R.augmentation.f (n + 1) = 0 := by
      simp only [Category.assoc]
      rw [eqToHom_naturality_assoc
        (fun q : ℤ => R.doubleComplex.d1 (-1) q)
        (show n - (-1) = n + 1 - 0 by ring)]
      have haug_d := congrArg (fun f => f.f (n + 1)) R.augmentation_d
      simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at haug_d
      have haug_d' := congrArg
        (fun f =>
          Pi.π (fun p : ℤ => R.doubleComplex.obj p (n - p)) (-1) ≫
            eqToHom (by
              change R.doubleComplex.obj (-1) (n - (-1)) =
                (column R.doubleComplex (-(0 + 1))).X (n + 1)
              dsimp [column]
              congr 1 <;> ring) ≫ f)
        haug_d
      convert haug_d' using 1
      · simp [leftResolutionColumnMap, columnMap, column, Category.assoc,
          eqToHom_trans]
        apply eq_of_heq
        symm
        apply heq_comp_left_fixed
        · rfl
        · apply heq_comp_left_fixed
          · rfl
          · have houter :
                column R.doubleComplex (-(0 + 1) + 1) =
                  column R.doubleComplex (-0) := by
              congr 1 <;> ring
            have hinner :
                (eqToHom houter).f (n + 1) ≫ R.augmentation.f (n + 1) ≍
                  R.augmentation.f (n + 1) := by
              rw [HomologicalComplex.eqToHom_f]
              exact eqToHom_comp_heq (C := AddCommGrpCat)
                (R.augmentation.f (n + 1)) _
            exact hinner
      · symm
        rw [← Category.assoc]
        apply comp_zero
    have hvert :
        (Pi.π (fun p : ℤ => R.doubleComplex.obj p (n - p)) 0 ≫
            R.doubleComplex.d2 0 (n - 0) ≫
            eqToHom (by
              change R.doubleComplex.obj 0 (n - 0 + 1) =
                R.doubleComplex.obj 0 (n + 1 - 0)
              congr 1 <;> ring)) ≫
            eqToHom (by
              change R.doubleComplex.obj 0 (n + 1 - 0) =
                (column R.doubleComplex 0).X (n + 1)
              dsimp [column]
              congr 1 <;> ring) ≫ R.augmentation.f (n + 1) =
          (Pi.π (fun p : ℤ => R.doubleComplex.obj p (n - p)) 0 ≫
            eqToHom (by
              change R.doubleComplex.obj 0 (n - 0) =
                (column R.doubleComplex 0).X n
              dsimp [column]
              congr 1 <;> ring) ≫ R.augmentation.f n) ≫
            M.d n (n + 1) := by
      simp only [Category.assoc]
      have hcomm := congrArg
        (fun f =>
          Pi.π (fun p : ℤ => R.doubleComplex.obj p (n - p)) 0 ≫
            eqToHom (by
              change R.doubleComplex.obj 0 (n - 0) =
                (column R.doubleComplex 0).X n
              change R.doubleComplex.obj 0 (n - 0) = R.doubleComplex.obj 0 n
              congr 1 <;> ring) ≫ f)
        (R.augmentation.comm n (n + 1)).symm
      convert hcomm using 1
      · simp only [column, dif_pos, eqToHom_trans]
        have hnat :=
          eqToHom_naturality_assoc
            (fun q : ℤ => R.doubleComplex.d2 0 q)
            (show n - 0 = n by ring)
            (eqToHom (by
              change R.doubleComplex.obj 0 (n + 1) =
                (column R.doubleComplex 0).X (n + 1)
              dsimp [column]
              ) ≫ R.augmentation.f (n + 1))
        have hnat' := congrArg
          (fun f => Pi.π (fun p : ℤ => R.doubleComplex.obj p (n - p)) 0 ≫ f)
          hnat
        have hremove_out :
            R.doubleComplex.d2 0 n ≫
                eqToHom (by
                  change R.doubleComplex.obj 0 (n + 1) =
                    (column R.doubleComplex 0).X (n + 1)
                  dsimp [column]) ≫ R.augmentation.f (n + 1) ≍
              R.doubleComplex.d2 0 n ≫ R.augmentation.f (n + 1) := by
          have h := comp_eqToHom_heq (R.doubleComplex.d2 0 n) (by
            change R.doubleComplex.obj 0 (n + 1) =
              (column R.doubleComplex 0).X (n + 1)
            dsimp [column])
          apply heq_comp (eq1 := rfl) (eq2 := rfl) (eq3 := rfl)
          · exact h
          · rfl
        have hremove_out' := heq_comp_left_fixed
          (Pi.π (fun p : ℤ => R.doubleComplex.obj p (n - p)) 0 ≫
            eqToHom (by
              change R.doubleComplex.obj 0 (n - 0) =
                (column R.doubleComplex 0).X n
              change R.doubleComplex.obj 0 (n - 0) = R.doubleComplex.obj 0 n
              congr 1 <;> ring)) rfl hremove_out
        have hremove_out'' :
            Pi.π (fun p : ℤ => R.doubleComplex.obj p (n - p)) 0 ≫
                eqToHom (by
                  change R.doubleComplex.obj 0 (n - 0) =
                    (column R.doubleComplex 0).X n
                  change R.doubleComplex.obj 0 (n - 0) = R.doubleComplex.obj 0 n
                  congr 1 <;> ring) ≫
                R.doubleComplex.d2 0 n ≫
                eqToHom (by
                  change R.doubleComplex.obj 0 (n + 1) =
                    (column R.doubleComplex 0).X (n + 1)
                  dsimp [column]) ≫ R.augmentation.f (n + 1) ≍
              Pi.π (fun p : ℤ => R.doubleComplex.obj p (n - p)) 0 ≫
                eqToHom (by
                  change R.doubleComplex.obj 0 (n - 0) =
                    (column R.doubleComplex 0).X n
                  change R.doubleComplex.obj 0 (n - 0) = R.doubleComplex.obj 0 n
                  congr 1 <;> ring) ≫
                R.doubleComplex.d2 0 n ≫ R.augmentation.f (n + 1) := by
          simpa only [Category.assoc] using hremove_out'
        convert (eq_of_heq ((heq_of_eq hnat').trans hremove_out'')) using 1
        congr 2
        apply eq_of_heq
        rw [← Category.assoc, ← Category.assoc]
        apply heq_comp (eq1 := rfl) (eq2 := rfl) (eq3 := rfl)
        · apply heq_comp
          · rfl
          · congr 1 <;> ring
          · change R.doubleComplex.obj 0 (n + 1) = R.doubleComplex.obj 0 (n + 1)
            rfl
          · apply eqToHom_heq_of_eq' (C := AddCommGrpCat)
            · congr 1 <;> ring
            · congr 1 <;> ring
          · apply eqToHom_heq_of_eq' (C := AddCommGrpCat)
            · congr 1 <;> ring
            · congr 1 <;> ring
        · rfl
    simp only [Category.assoc] at hhor hvert
    simp only [Preadditive.add_comp, Preadditive.comp_add,
      Preadditive.comp_zsmul, Category.assoc, one_smul]
    rw [hhor, hvert]
    simp

/-! ## Quasi-isomorphism lemmas -/

/-- A right resolution of complexes becomes a quasi-isomorphism after
coproduct totalization. -/
theorem right_resolution_gives_qis
    {M : AbelianGroupCochainComplex}
    (R : RightDoubleComplexResolution M) :
    QuasiIso (rightResolutionTotalMap R) := by
  sorry

/-- A resolution whose kernel sequences are exact becomes a
quasi-isomorphism after coproduct totalization. -/
theorem good_resolution_gives_qis
    {M : AbelianGroupCochainComplex}
    (R : GoodLeftDoubleComplexResolution M) :
    QuasiIso (leftResolutionTotalMap R.toLeftDoubleComplexResolution) := by
  sorry

/-- A right resolution whose cokernel sequences are exact becomes a
quasi-isomorphism after product totalization. -/
theorem good_right_resolution_gives_qis
    {M : AbelianGroupCochainComplex}
    (R : GoodRightDoubleComplexResolution M) :
    QuasiIso (rightResolutionProductTotalMap R.toRightDoubleComplexResolution) := by
  sorry

/-- An unrestricted left resolution becomes a quasi-isomorphism after product
totalization. -/
theorem resolution_gives_qis
    {M : AbelianGroupCochainComplex}
    (R : LeftDoubleComplexResolution M) :
    QuasiIso (leftResolutionProductTotalMap R) := by
  sorry

end Formalization.Books.Homology.Unit26
