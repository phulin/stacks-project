import Formalization.Books.Derived.Unit08.HomotopyCategory
import Formalization.Books.Homology.Unit18.DoubleComplexes
import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# More on Algebra, Chapter 58: Tensor products of complexes

The source's tensor product of cochain complexes is Mathlib's total complex of
the tensor-product bicomplex.  The declarations below expose that canonical
construction and the chapter's homotopy-category statements.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open HomologicalComplex
open ComplexShape

universe u

namespace Formalization.Books.MoreAlgebra.Unit58

/-! ## Tensor products of complexes -/

/-- The source's category `Comp(R)` of integer-indexed cochain complexes of
`R`-modules. -/
abbrev Comp (R : Type u) [CommRing R] := CochainComplex (ModuleCat.{u} R) ℤ

/-- The homotopy category `K(R)` of complexes of `R`-modules. -/
abbrev K (R : Type u) [CommRing R] :=
  HomotopyCategory (ModuleCat.{u} R) (.up ℤ)

/-- The bifunctor whose value is the total tensor product of two cochain
complexes. -/
noncomputable abbrev tensorProductBifunctor (R : Type u) [CommRing R] :
    Comp R ⥤ Comp R ⥤ Comp R :=
  (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex

/-- The total tensor product `Tot(L ⊗_R M)` of two cochain complexes. -/
noncomputable abbrev tensorProductComplex (R : Type u) [CommRing R]
    (L M : Comp R) : Comp R :=
  (tensorProductBifunctor R).obj L |>.obj M

/-- Tensoring on the left by a fixed complex. -/
noncomputable abbrev tensorLeftComplexFunctor (R : Type u) [CommRing R]
    (P : Comp R) : Comp R ⥤ Comp R :=
  (tensorProductBifunctor R).obj P

/-- Tensoring on the right by a fixed complex. -/
noncomputable abbrev tensorRightComplexFunctor (R : Type u) [CommRing R]
    (P : Comp R) : Comp R ⥤ Comp R :=
  (tensorProductBifunctor R).flip.obj P

/-- The canonical associativity constraint for total tensor products. -/
structure TensorAssociativityData (R : Type u) [CommRing R]
    (K L M : Comp R) where
  constraint : tensorProductComplex R (tensorProductComplex R K L) M ≅
    tensorProductComplex R K (tensorProductComplex R L M)

theorem tensorAssociator_exists (R : Type u) [CommRing R]
    (K L M : Comp R) : Nonempty (TensorAssociativityData R K L M) := by
  sorry

/-- A chosen associativity constraint for total tensor products. -/
noncomputable def tensorAssociator (R : Type u) [CommRing R]
    (K L M : Comp R) :
    tensorProductComplex R (tensorProductComplex R K L) M ≅
      tensorProductComplex R K (tensorProductComplex R L M) :=
  (Classical.choice (tensorAssociator_exists R K L M)).constraint

/-- The complex concentrated in degree zero at the module `R`, serving as the
tensor unit. -/
noncomputable abbrev tensorUnit (R : Type u) [CommRing R] : Comp R :=
  HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℤ)

/-- The canonical left unit constraint. -/
noncomputable abbrev tensorLeftUnitor (R : Type u) [CommRing R] (M : Comp R) :
    tensorProductComplex R (tensorUnit R) M ≅ M :=
  HomologicalComplex.leftUnitor M

/-- The canonical right unit constraint. -/
noncomputable abbrev tensorRightUnitor (R : Type u) [CommRing R] (M : Comp R) :
    tensorProductComplex R M (tensorUnit R) ≅ M :=
  HomologicalComplex.rightUnitor M

/- The source's component calculation is the standard total-complex
   differential formula.  The `mapBifunctor` API records it on each tensor
   summand, including the Koszul sign on the second differential. -/
theorem tensorProductComplex_differential_formula
    (R : Type u) [CommRing R] (L M : Comp R) (p q : ℤ) :
    ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q (p + q) rfl ≫
        (tensorProductComplex R L M).d (p + q) (p + q + 1) =
      (L.d p (p + 1) ⊗ₘ 𝟙 (M.X q)) ≫
            ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) (p + 1) q (p + q + 1) (by dsimp; omega) +
        p.negOnePow •
          ((𝟙 (L.X p) ⊗ₘ M.d q (q + 1)) ≫
            ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
              (.up ℤ) p (q + 1) (p + q + 1) (by dsimp; omega)) := by
  sorry

/- The sign appearing in the commutativity constraint is the canonical sign
   from `ComplexShape.TensorSigns` for integer cochain complexes. -/
abbrev koszulSign (p q : ℤ) : ℤˣ :=
  ComplexShape.σ (.up ℤ) (.up ℤ) (.up ℤ) p q

/-! ## Symmetry and homotopy -/

/- Mathlib supplies the signed flip of a total complex through
`HomologicalComplex₂.totalFlipIso` and `mapBifunctorFlipIso`.  The remaining
book-facing assertion is that the base module braiding gives the displayed
commutativity constraint on the two tensor factors. -/
structure SignedTensorSymmetryData (R : Type u) [CommRing R]
    (L M : Comp R) where
  constraint : tensorProductComplex R L M ≅ tensorProductComplex R M L
  summand_formula : ∀ (p q : ℤ),
    ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q (p + q) rfl ≫ constraint.hom.f (p + q) =
      (p * q).negOnePow •
        ((β_ (L.X p) (M.X q)).hom ≫
          ιMapBifunctor M L (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) q p (p + q) (by dsimp; omega))

theorem signedTensorSymmetry_exists
    (R : Type u) [CommRing R] (L M : Comp R) :
    Nonempty (SignedTensorSymmetryData R L M) := by
  sorry

/-- A chosen signed commutativity constraint for total tensor products. -/
noncomputable def tensorBraiding (R : Type u) [CommRing R]
    (L M : Comp R) : tensorProductComplex R L M ≅ tensorProductComplex R M L :=
  (Classical.choice (signedTensorSymmetry_exists R L M)).constraint

/-- The chapter's precise signed component formula for the commutativity
constraint.  On the summand `L^p ⊗ M^q`, the sign is `(-1)^(pq)`. -/
theorem tensorBraiding_on_summand
    (R : Type u) [CommRing R] (L M : Comp R) (p q : ℤ) :
    ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q (p + q) rfl ≫ (tensorBraiding R L M).hom.f (p + q) =
      (p * q).negOnePow •
        ((β_ (L.X p) (M.X q)).hom ≫
          ιMapBifunctor M L (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) q p (p + q) (by dsimp; omega)) := by
  exact (Classical.choice (signedTensorSymmetry_exists R L M)).summand_formula p q

/- A small source-facing bundle is useful because Mathlib represents a
symmetric monoidal structure by separate typeclasses, while the chapter
states both pieces together. -/
structure SymmetricMonoidalCategoryData (C : Type*) [Category* C] where
  monoidal : MonoidalCategory C
  symmetric : @SymmetricCategory C _ monoidal

/-- The category of complexes of `R`-modules admits the symmetric monoidal
structure described in the source. -/
theorem cochainComplex_symmetric_monoidal
    (R : Type u) [CommRing R] :
    Nonempty (SymmetricMonoidalCategoryData (Comp R)) := by
  sorry

/-- Homotopic maps remain homotopic after tensoring with a fixed complex. -/
theorem tensorProduct_preserves_homotopies
    (R : Type u) [CommRing R] (P : Comp R)
    {L M : Comp R} (α β : L ⟶ M) (h : Homotopy α β) :
    Nonempty (Homotopy
      ((tensorRightComplexFunctor R P).map α)
      ((tensorRightComplexFunctor R P).map β)) := by
  sorry

theorem tensorProduct_left_preserves_homotopies
    (R : Type u) [CommRing R] (P : Comp R)
    {L M : Comp R} (α β : L ⟶ M) (h : Homotopy α β) :
    Nonempty (Homotopy
      ((tensorLeftComplexFunctor R P).map α)
      ((tensorLeftComplexFunctor R P).map β)) := by
  sorry

/-- Tensoring with `P` therefore descends to an endofunctor of `K(R)`. -/
noncomputable instance tensorRightComplexFunctor_additive
    (R : Type u) [CommRing R] (P : Comp R) :
    (tensorRightComplexFunctor R P).Additive := by
  sorry

noncomputable instance tensorLeftComplexFunctor_additive
    (R : Type u) [CommRing R] (P : Comp R) :
    (tensorLeftComplexFunctor R P).Additive := by
  sorry

/-- Tensoring with `P` therefore descends to an endofunctor of `K(R)`. -/
noncomputable abbrev tensorRightHomotopyFunctor
    (R : Type u) [CommRing R] (P : Comp R) : K R ⥤ K R :=
  CategoryTheory.Quotient.lift
    (homotopic (ModuleCat.{u} R) (.up ℤ))
    ((tensorRightComplexFunctor R P) ⋙
      HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ))
    (by
      intro L M α β h
      obtain ⟨h⟩ := h
      exact HomotopyCategory.eq_of_homotopy _ _
        (Classical.choice (tensorProduct_preserves_homotopies R P α β h)))

/-- The left tensoring functor descends to the homotopy category as well. -/
noncomputable abbrev tensorLeftHomotopyFunctor
    (R : Type u) [CommRing R] (P : Comp R) : K R ⥤ K R :=
  CategoryTheory.Quotient.lift
    (homotopic (ModuleCat.{u} R) (.up ℤ))
    ((tensorLeftComplexFunctor R P) ⋙
      HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ))
    (by
      intro L M α β h
      obtain ⟨h⟩ := h
      exact HomotopyCategory.eq_of_homotopy _ _
        (Classical.choice (tensorProduct_left_preserves_homotopies R P α β h)))

/-- The homotopy category `K(R)` inherits the symmetric monoidal structure. -/
theorem homotopyCategory_symmetric_monoidal
    (R : Type u) [CommRing R] :
    Nonempty (SymmetricMonoidalCategoryData (K R)) := by
  sorry

/-! ## Exactness -/

/- Mathlib's triangulated-functor interface packages the source's
exactness assertion together with the shift-commutation data. -/
structure ExactTriangulatedFunctorData {C D : Type*}
    [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ]
    [HasZeroObject C] [HasZeroObject D]
    [Preadditive C] [Preadditive D]
    [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [∀ (n : ℤ), (shiftFunctor D n).Additive]
    (F : C ⥤ D) where
  pretriangulated_C : Pretriangulated C
  pretriangulated_D : Pretriangulated D
  commShift : F.CommShift ℤ
  triangulated :
    letI := pretriangulated_C
    letI := pretriangulated_D
    letI := commShift
    F.IsTriangulated

/-- Tensoring on the left by a fixed complex is an exact (triangulated)
functor of homotopy categories. -/
theorem tensorLeftHomotopyFunctor_is_triangulated
    (R : Type u) [CommRing R] (P : Comp R) :
    Nonempty (ExactTriangulatedFunctorData (tensorLeftHomotopyFunctor R P)) := by
  sorry

/-- Tensoring on the right by a fixed complex is an exact (triangulated)
functor of homotopy categories. -/
theorem tensorRightHomotopyFunctor_is_triangulated
    (R : Type u) [CommRing R] (P : Comp R) :
    Nonempty (ExactTriangulatedFunctorData (tensorRightHomotopyFunctor R P)) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit58
