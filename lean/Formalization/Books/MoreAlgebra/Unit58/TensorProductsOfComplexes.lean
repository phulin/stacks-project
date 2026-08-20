import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Formalization.Books.Derived.Unit10.DistinguishedTriangles
import Formalization.Books.MoreAlgebra.Unit56.DerivedCategoriesOfModules

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
abbrev Comp (R : Type u) [CommRing R] :=
  Formalization.Books.MoreAlgebra.Unit56.Comp R

/-- The homotopy category `K(R)` of complexes of `R`-modules. -/
abbrev K (R : Type u) [CommRing R] :=
  Formalization.Books.MoreAlgebra.Unit56.K R

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
  change _ ≫ (HomologicalComplex.mapBifunctor L M
    (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (.up ℤ)).d
      (p + q) (p + q + 1) = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq L M
      (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (.up ℤ)
      (by rfl) q _ (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq L M
      (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (.up ℤ)
      p (by rfl) _ (by dsimp; omega)]
  dsimp
  simp

private lemma tensorProductComplex_differential_formula_swap
    (R : Type u) [CommRing R] (L M : Comp R) (p q n : ℤ)
    (h : q + p = n) :
    ιMapBifunctor M L (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) q p n (by dsimp; omega) ≫
        (tensorProductComplex R M L).d n (n + 1) =
      (M.d q (q + 1) ⊗ₘ 𝟙 (L.X p)) ≫
          ιMapBifunctor M L (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) (q + 1) p (n + 1) (by dsimp; omega) +
        q.negOnePow •
          ((𝟙 (M.X q) ⊗ₘ L.d p (p + 1)) ≫
            ιMapBifunctor M L (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
              (.up ℤ) q (p + 1) (n + 1) (by dsimp; omega)) := by
  subst n
  exact tensorProductComplex_differential_formula R M L q p

private lemma tensorProductComplex_differential_formula_comm
    (R : Type u) [CommRing R] (L M : Comp R) (p q n : ℤ)
    (h : q + p = n) :
    ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) q p n (by dsimp; omega) ≫
        (tensorProductComplex R L M).d n (n + 1) =
      (L.d q (q + 1) ⊗ₘ 𝟙 (M.X p)) ≫
          ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) (q + 1) p (n + 1) (by dsimp; omega) +
        q.negOnePow •
          ((𝟙 (L.X q) ⊗ₘ M.d p (p + 1)) ≫
            ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
              (.up ℤ) q (p + 1) (n + 1) (by dsimp; omega)) := by
  subst n
  exact tensorProductComplex_differential_formula R L M q p

private lemma tensorProductComplex_differential_formula_right
    (R : Type u) [CommRing R] (L M : Comp R) (p q : ℤ)
    {Z : ModuleCat.{u} R} (f : (tensorProductComplex R L M).X (p + q + 1) ⟶ Z) :
    ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q (p + q) rfl ≫
        ((tensorProductComplex R L M).d (p + q) (p + q + 1) ≫ f) =
      ((L.d p (p + 1) ⊗ₘ 𝟙 (M.X q)) ≫
          ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) (p + 1) q (p + q + 1) (by dsimp; omega) +
        p.negOnePow •
          ((𝟙 (L.X p) ⊗ₘ M.d q (q + 1)) ≫
            ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
              (.up ℤ) p (q + 1) (p + q + 1) (by dsimp; omega))) ≫ f := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    simpa only [Category.assoc] using congrArg (fun k => k ≫ f)
      (tensorProductComplex_differential_formula R L M p q)

/- The sign appearing in the commutativity constraint is the Koszul sign
   `(-1)^(pq)` on the summand in degrees `p` and `q`.  Mathlib also has a
   `ComplexShape.σ` field for total-complex shape symmetries; the source's
   component formula is recorded explicitly here rather than identified with
   that implementation detail. -/
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

@[reassoc] private lemma tensorBraidingHomComponent_on_summand
    (R : Type u) [CommRing R] (L M : Comp R) (p q n : ℤ)
    (h : p + q = n) :
    ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q n h ≫ tensorBraidingHomComponent R L M n =
      koszulSign p q •
        ((β_ (L.X p) (M.X q)).hom ≫
          ιMapBifunctor M L (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) q p n (by
              rw [ComplexShape.π_symm (.up ℤ) (.up ℤ) (.up ℤ) p q]
              exact h)) := by
  dsimp [tensorBraidingHomComponent]
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [HomologicalComplex.ι_mapBifunctorDesc]

@[reassoc] private lemma tensorBraidingInvComponent_on_summand
    (R : Type u) [CommRing R] (L M : Comp R) (p q n : ℤ)
    (h : p + q = n) :
    ιMapBifunctor M L (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q n h ≫ tensorBraidingInvComponent R L M n =
      koszulSign p q •
        ((β_ (M.X p) (L.X q)).hom ≫
          ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) q p n (by
              rw [ComplexShape.π_symm (.up ℤ) (.up ℤ) (.up ℤ) p q]
              exact h)) := by
  dsimp [tensorBraidingInvComponent]
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [HomologicalComplex.ι_mapBifunctorDesc]

private lemma tensorBraidingHomComponent_on_summand_right
    (R : Type u) [CommRing R] (L M : Comp R) (p q n : ℤ)
    (h : p + q = n) {Z : ModuleCat.{u} R}
    (f : (tensorProductComplex R M L).X n ⟶ Z) :
    ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q n h ≫ (tensorBraidingHomComponent R L M n ≫ f) =
      (koszulSign p q •
        ((β_ (L.X p) (M.X q)).hom ≫
          ιMapBifunctor M L (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) q p n (by
              rw [ComplexShape.π_symm (.up ℤ) (.up ℤ) (.up ℤ) p q]
              exact h))) ≫ f := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    simpa only [Category.assoc] using congrArg (fun k => k ≫ f)
      (tensorBraidingHomComponent_on_summand R L M p q n h)

private lemma tensorBraidingInvComponent_on_summand_right
    (R : Type u) [CommRing R] (L M : Comp R) (p q n : ℤ)
    (h : p + q = n) {Z : ModuleCat.{u} R}
    (f : (tensorProductComplex R L M).X n ⟶ Z) :
    ιMapBifunctor M L (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.up ℤ) p q n h ≫ (tensorBraidingInvComponent R L M n ≫ f) =
      (koszulSign p q •
        ((β_ (M.X p) (L.X q)).hom ≫
          ιMapBifunctor L M (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
            (.up ℤ) q p n (by
              rw [ComplexShape.π_symm (.up ℤ) (.up ℤ) (.up ℤ) p q]
              exact h))) ≫ f := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    simpa only [Category.assoc] using congrArg (fun k => k ≫ f)
      (tensorBraidingInvComponent_on_summand R L M p q n h)

/-- The signed commutativity constraint for total tensor products. -/
noncomputable def tensorBraiding (R : Type u) [CommRing R]
    (L M : Comp R) : tensorProductComplex R L M ≅ tensorProductComplex R M L :=
  { hom :=
      { f := tensorBraidingHomComponent R L M
        comm' := by
          rintro i _ rfl
          apply HomologicalComplex.mapBifunctor.hom_ext
          intro p q h
          dsimp at h
          subst i
          set_option backward.defeqAttrib.useBackward true in
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
            rw [tensorBraidingHomComponent_on_summand_right R L M p q (p + q) rfl]
          set_option backward.defeqAttrib.useBackward true in
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
            simp only [Linear.units_smul_comp, Category.assoc]
          set_option backward.defeqAttrib.useBackward true in
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
            rw [tensorProductComplex_differential_formula_swap R L M p q (p + q) (by omega),
              tensorProductComplex_differential_formula_right R L M p q
                (tensorBraidingHomComponent R L M (p + q + 1))]
          set_option backward.defeqAttrib.useBackward true in
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
            simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc]
          set_option backward.defeqAttrib.useBackward true in
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
            rw [tensorBraidingHomComponent_on_summand R L M (p + 1) q (p + q + 1)
              (by omega)]
          set_option backward.defeqAttrib.useBackward true in
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
            rw [tensorBraidingHomComponent_on_summand R L M p (q + 1) (p + q + 1)
              (by omega)]
          simp [MonoidalCategory.tensorHom_def, koszulSign,
            Int.negOnePow_add, mul_add, smul_smul,
            mul_comm]
          have hp : p.negOnePow * (p.negOnePow * (p * q).negOnePow) =
              (p * q).negOnePow := by
            rw [← mul_assoc, Int.units_mul_self, one_mul]
          rw [hp]
          exact add_comm _ _ }
    inv :=
      { f := tensorBraidingInvComponent R L M
        comm' := by
          rintro i _ rfl
          apply HomologicalComplex.mapBifunctor.hom_ext
          intro p q h
          dsimp at h
          subst i
          set_option backward.defeqAttrib.useBackward true in
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
            rw [tensorBraidingInvComponent_on_summand_right R L M p q (p + q) rfl]
          set_option backward.defeqAttrib.useBackward true in
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
            simp only [Linear.units_smul_comp, Category.assoc]
          set_option backward.defeqAttrib.useBackward true in
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
            rw [tensorProductComplex_differential_formula_comm R L M p q (p + q) (by omega),
              tensorProductComplex_differential_formula_right R M L p q
                (tensorBraidingInvComponent R L M (p + q + 1))]
          set_option backward.defeqAttrib.useBackward true in
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
            simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc]
          set_option backward.defeqAttrib.useBackward true in
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
            rw [tensorBraidingInvComponent_on_summand R L M (p + 1) q (p + q + 1)
              (by omega)]
          set_option backward.defeqAttrib.useBackward true in
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
            rw [tensorBraidingInvComponent_on_summand R L M p (q + 1) (p + q + 1)
              (by omega)]
          simp [MonoidalCategory.tensorHom_def, koszulSign,
            Int.negOnePow_add, mul_add, smul_smul,
            mul_comm]
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
      set_option backward.defeqAttrib.useBackward true in
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        rw [tensorBraidingHomComponent_on_summand_right R L M p q (p + q) rfl
          (tensorBraidingInvComponent R L M (p + q))]
      set_option backward.defeqAttrib.useBackward true in
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        simp only [Linear.units_smul_comp, Category.assoc]
      set_option backward.defeqAttrib.useBackward true in
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        rw [tensorBraidingInvComponent_on_summand R L M q p (p + q)
          (by omega)]
      simp
      have hsign : koszulSign p q * koszulSign q p = (1 : ℤˣ) := by
        change (p * q).negOnePow * (q * p).negOnePow = (1 : ℤˣ)
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
      set_option backward.defeqAttrib.useBackward true in
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        rw [tensorBraidingInvComponent_on_summand_right R L M p q (p + q) rfl
          (tensorBraidingHomComponent R L M (p + q))]
      set_option backward.defeqAttrib.useBackward true in
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        simp only [Linear.units_smul_comp, Category.assoc]
      set_option backward.defeqAttrib.useBackward true in
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        rw [tensorBraidingHomComponent_on_summand R L M q p (p + q)
          (by omega)]
      simp
      have hsign : koszulSign p q * koszulSign q p = (1 : ℤˣ) := by
        change (p * q).negOnePow * (q * p).negOnePow = (1 : ℤˣ)
        rw [mul_comm q p, Int.units_mul_self]
      simp only [smul_smul, hsign, one_smul] }

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
  exact tensorBraidingHomComponent_on_summand R L M p q (p + q) rfl

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

/-- A chosen symmetric-monoidal package for complexes, for downstream uses
that need to access the structure rather than only its existence. -/
noncomputable def cochainComplexSymmetricMonoidalData
    (R : Type u) [CommRing R] :
    SymmetricMonoidalCategoryData (Comp R) :=
  Classical.choice (cochainComplex_symmetric_monoidal R)

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

/-- A chosen homotopy witnessing preservation under right tensoring. -/
noncomputable def tensorProduct_homotopy
    (R : Type u) [CommRing R] (P : Comp R)
    {L M : Comp R} (α β : L ⟶ M) (h : Homotopy α β) :
    Homotopy
      ((tensorRightComplexFunctor R P).map α)
      ((tensorRightComplexFunctor R P).map β) :=
  Classical.choice (tensorProduct_preserves_homotopies R P α β h)

theorem tensorProduct_left_preserves_homotopies
    (R : Type u) [CommRing R] (P : Comp R)
    {L M : Comp R} (α β : L ⟶ M) (h : Homotopy α β) :
    Nonempty (Homotopy
      ((tensorLeftComplexFunctor R P).map α)
      ((tensorLeftComplexFunctor R P).map β)) := by
  sorry

/-- A chosen homotopy witnessing preservation under left tensoring. -/
noncomputable def tensorProduct_left_homotopy
    (R : Type u) [CommRing R] (P : Comp R)
    {L M : Comp R} (α β : L ⟶ M) (h : Homotopy α β) :
    Homotopy
      ((tensorLeftComplexFunctor R P).map α)
      ((tensorLeftComplexFunctor R P).map β) :=
  Classical.choice (tensorProduct_left_preserves_homotopies R P α β h)

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
        (tensorProduct_homotopy R P α β h))

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
        (tensorProduct_left_homotopy R P α β h))

/-- The homotopy category `K(R)` inherits the symmetric monoidal structure. -/
theorem homotopyCategory_symmetric_monoidal
    (R : Type u) [CommRing R] :
    Nonempty (SymmetricMonoidalCategoryData (K R)) := by
  sorry

/-- A chosen symmetric-monoidal package on `K(R)`. -/
noncomputable def homotopyCategorySymmetricMonoidalData
    (R : Type u) [CommRing R] :
    SymmetricMonoidalCategoryData (K R) :=
  Classical.choice (homotopyCategory_symmetric_monoidal R)

/-! ## Exactness -/

/-- Tensoring on the left by a fixed complex is an exact (triangulated)
functor of homotopy categories. -/
theorem tensorLeftHomotopyFunctor_is_triangulated
    (R : Type u) [CommRing R] (P : Comp R) :
    Nonempty (Formalization.Books.Derived.Unit10.ExactTriangulatedFunctorData
      (tensorLeftHomotopyFunctor R P)) := by
  sorry

/-- A chosen exact-triangulated structure for left tensoring. -/
noncomputable def tensorLeftHomotopyFunctor_exactData
    (R : Type u) [CommRing R] (P : Comp R) :
    Formalization.Books.Derived.Unit10.ExactTriangulatedFunctorData
      (tensorLeftHomotopyFunctor R P) :=
  Classical.choice (tensorLeftHomotopyFunctor_is_triangulated R P)

/-- Tensoring on the right by a fixed complex is an exact (triangulated)
functor of homotopy categories. -/
theorem tensorRightHomotopyFunctor_is_triangulated
    (R : Type u) [CommRing R] (P : Comp R) :
    Nonempty (Formalization.Books.Derived.Unit10.ExactTriangulatedFunctorData
      (tensorRightHomotopyFunctor R P)) := by
  sorry

/-- A chosen exact-triangulated structure for right tensoring. -/
noncomputable def tensorRightHomotopyFunctor_exactData
    (R : Type u) [CommRing R] (P : Comp R) :
    Formalization.Books.Derived.Unit10.ExactTriangulatedFunctorData
      (tensorRightHomotopyFunctor R P) :=
  Classical.choice (tensorRightHomotopyFunctor_is_triangulated R P)

end Formalization.Books.MoreAlgebra.Unit58
