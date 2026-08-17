import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Triangulated.Functor
import Formalization.Books.Derived.Unit10.DistinguishedTriangles

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
noncomputable abbrev tensorAssociator (R : Type u) [CommRing R]
    (K L M : Comp R) :
    tensorProductComplex R (tensorProductComplex R K L) M ≅
      tensorProductComplex R K (tensorProductComplex R L M) :=
  HomologicalComplex.associator K L M

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

/- The sign appearing in the commutativity constraint is the Koszul sign
   `(-1)^(pq)` on the summand in degrees `p` and `q`.  This is distinct from
   `ComplexShape.σ`, whose role is to compare the two total-complex index
   conventions and which is `1` for the canonical symmetric total shape. -/
abbrev koszulSign (p q : ℤ) : ℤˣ :=
  (p * q).negOnePow

/-! ## Symmetry and homotopy -/

/- Mathlib supplies the canonical coproduct-desc construction for maps out of
the total tensor product, while the chain-map verification for the signed
flip is the component calculation in the source.  The `comm'` fields below
are the formal chain-map version of the two displayed differential/sign
identities. -/
noncomputable def tensorBraidingHomComponent
    (R : Type u) [CommRing R] (L M : Comp R) (n : ℤ) :
    (tensorProductComplex R L M).X n ⟶ (tensorProductComplex R M L).X n :=
  HomologicalComplex.mapBifunctorDesc (fun p q h =>
    koszulSign p q •
      ((β_ (L.X p) (M.X q)).hom ≫
        ιMapBifunctor M L (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
          (.up ℤ) q p n (by
            rw [ComplexShape.π_symm (.up ℤ) (.up ℤ) (.up ℤ) p q]
            exact h)))

noncomputable def tensorBraidingInvComponent
    (R : Type u) [CommRing R] (L M : Comp R) (n : ℤ) :
    (tensorProductComplex R M L).X n ⟶ (tensorProductComplex R L M).X n :=
  HomologicalComplex.mapBifunctorDesc (fun p q h =>
    koszulSign p q •
      ((β_ (M.X p) (L.X q)).hom ≫
        ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
          (.up ℤ) q p n (by
            rw [ComplexShape.π_symm (.up ℤ) (.up ℤ) (.up ℤ) p q]
            exact h)))

/-- The signed commutativity constraint for total tensor products. -/
noncomputable def tensorBraiding (R : Type u) [CommRing R]
    (L M : Comp R) : tensorProductComplex R L M ≅ tensorProductComplex R M L :=
  { hom :=
      { f := tensorBraidingHomComponent R L M
        comm' := by
          sorry }
    inv :=
      { f := tensorBraidingInvComponent R L M
        comm' := by
          sorry }
    hom_inv_id := by
      sorry
    inv_hom_id := by
      sorry }

/-- The chapter's precise signed component formula for the commutativity
constraint.  On the summand `L^p ⊗ M^q`, the sign is `(-1)^(pq)`. -/
theorem tensorBraiding_on_summand
    (R : Type u) [CommRing R] (L M : Comp R) (p q : ℤ) :
    ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q (p + q) rfl ≫ (tensorBraiding R L M).hom.f (p + q) =
      koszulSign p q •
        ((β_ (L.X p) (M.X q)).hom ≫
          ιMapBifunctor M L (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) q p (p + q) (by dsimp; omega)) := by
  sorry

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
/- The source's explicit `H^n` and the displayed identity
`Tot(α ⊗ id) = Tot(β ⊗ id) + dH + Hd` are represented by the returned
`Homotopy` witness and its `comm` field. -/
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

/-- Tensoring on the left by a fixed complex is an exact (triangulated)
functor of homotopy categories. -/
theorem tensorLeftHomotopyFunctor_is_triangulated
    (R : Type u) [CommRing R] (P : Comp R) :
    Nonempty (Formalization.Books.Derived.Unit10.ExactTriangulatedFunctorData
      (tensorLeftHomotopyFunctor R P)) := by
  sorry

/-- Tensoring on the right by a fixed complex is an exact (triangulated)
functor of homotopy categories. -/
theorem tensorRightHomotopyFunctor_is_triangulated
    (R : Type u) [CommRing R] (P : Comp R) :
    Nonempty (Formalization.Books.Derived.Unit10.ExactTriangulatedFunctorData
      (tensorRightHomotopyFunctor R P)) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit58
