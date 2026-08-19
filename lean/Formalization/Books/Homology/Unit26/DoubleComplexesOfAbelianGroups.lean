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
    M.X n ⟶ productTotalTerm R.doubleComplex n := by
  unfold productTotalTerm
  exact Pi.lift (fun p => by
    classical
    by_cases hp : p = 0
    · subst p
      exact R.augmentation.f n ≫ eqToHom (by
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

/-- The product-total differential squares to zero. -/
theorem productTotalDifferential_comp_zero
    (A : DoubleComplex AddCommGrpCat.{u}) (n : ℤ) :
    productTotalDifferential A n ≫ productTotalDifferential A (n + 1) = 0 := by sorry
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
      Category.assoc, Preadditive.comp_add, Linear.comp_units_smul,
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
      rw [Pi.lift_π]
      exact sorry
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
    sorry

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
    sorry

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
