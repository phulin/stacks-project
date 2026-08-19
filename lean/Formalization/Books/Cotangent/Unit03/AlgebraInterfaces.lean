import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# The algebraic adjunction used by the standard resolution

The textbook works with commutative `A`-algebras.  Mathlib's canonical bundled
category for these is `CommAlgCat A`; its forgetful functor is paired here with
the polynomial-algebra functor on sets.
-/

namespace Formalization.Books.Cotangent.Unit03

open CategoryTheory

universe u

variable (A : Type u) [CommRing A]

/-- The free commutative `A`-algebra functor `E ↦ A[E]`. -/
noncomputable def polynomialFree : Type u ⥤ CommAlgCat A where
  obj E := CommAlgCat.of A (MvPolynomial E A)
  map f := CommAlgCat.ofHom (MvPolynomial.rename (R := A) f)
  map_id := by
    intro E
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro e
    change MvPolynomial.rename (R := A) (fun x : E => x) (MvPolynomial.X e) =
      MvPolynomial.X e
    simp
  map_comp := by
    intro E F G f g
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro e
    change MvPolynomial.rename (R := A) (fun x : E => g (f x)) (MvPolynomial.X e) =
      MvPolynomial.rename (R := A) g
        (MvPolynomial.rename (R := A) f (MvPolynomial.X e))
    simp

/-- The forgetful functor from commutative `A`-algebras to sets. -/
abbrev polynomialForget : CommAlgCat A ⥤ Type u := CategoryTheory.forget _

/-- The universal bijection for the free polynomial algebra. -/
noncomputable def polynomialFreeHomEquiv (E : Type u) (C : CommAlgCat A) :
    ((polynomialFree A).obj E ⟶ C) ≃
      (E ⟶ (polynomialForget A).obj C) :=
  { toFun := fun f => TypeCat.ofHom (fun e => f.hom (MvPolynomial.X e))
    invFun := fun g => CommAlgCat.ofHom (MvPolynomial.aeval g)
    left_inv := by
      intro f
      apply CommAlgCat.hom_ext
      apply MvPolynomial.algHom_ext
      intro e
      change MvPolynomial.aeval (R := A)
          (fun e : E => f.hom (MvPolynomial.X e)) (MvPolynomial.X e) =
        f.hom (MvPolynomial.X e)
      rw [MvPolynomial.aeval_X]
    right_inv := by
      intro g
      apply ConcreteCategory.hom_ext
      intro e
      exact MvPolynomial.aeval_X (f := g) e }

/-- The free-forgetful adjunction for polynomial algebras. -/
noncomputable def polynomialFreeAdjunction :
    polynomialFree A ⊣ polynomialForget A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun E C => by
        exact polynomialFreeHomEquiv A E C
      homEquiv_naturality_left_symm := by
        sorry
      homEquiv_naturality_right := by
        sorry }

/-- A proposition recording the free-forgetful adjunction. -/
def PolynomialFreeForgetfulAdjunction : Prop :=
  Nonempty (polynomialFree A ⊣ polynomialForget A)

theorem polynomialFreeForgetfulAdjunction :
    PolynomialFreeForgetfulAdjunction A :=
  ⟨polynomialFreeAdjunction A⟩

/-! ## The arrow-category variant from the source remark -/

/-- The category of commutative `A`-algebra arrows ending in `B`. -/
abbrev AlgebraArrowCategory (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  CostructuredArrow (𝟭 (CommAlgCat A)) (CommAlgCat.of A B)

/-- The category of set maps ending in the underlying set of `B`. -/
abbrev SetArrowCategory (B : Type u) [CommRing B] :=
  CostructuredArrow (𝟭 (Type u)) B

/-- The forgetful functor between the two arrow categories. -/
noncomputable def variantForgetful (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] : AlgebraArrowCategory A B ⥤ SetArrowCategory B :=
  CostructuredArrow.map₂
    (S := 𝟭 (CommAlgCat A)) (T := CommAlgCat.of A B)
    (U := 𝟭 (Type u)) (V := B)
    (F := polynomialForget A) (G := polynomialForget A)
    (NatTrans.id _) (𝟙 B)

/-- The functor sending a set map into `B` to its polynomial `A`-algebra map. -/
noncomputable def variantFree (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] : SetArrowCategory B ⥤ AlgebraArrowCategory A B :=
  CostructuredArrow.map₂
    (S := 𝟭 (Type u)) (T := B)
    (U := 𝟭 (CommAlgCat A)) (V := CommAlgCat.of A B)
    (F := polynomialFree A) (G := polynomialFree A)
    (NatTrans.id _) (CommAlgCat.ofHom (MvPolynomial.aeval (fun b : B => b)))

def variantAlgebraProjection (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] : AlgebraArrowCategory A B ⥤ CommAlgCat A :=
  CostructuredArrow.proj (𝟭 (CommAlgCat A)) (CommAlgCat.of A B)

def variantSetProjection (B : Type u) [CommRing B] : SetArrowCategory B ⥤ Type u :=
  CostructuredArrow.proj (𝟭 (Type u)) B

/-- The hom-set equivalence for the arrow-category adjunction. -/
noncomputable def variantFreeHomEquiv (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (X : AlgebraArrowCategory A B) (Y : SetArrowCategory B) :
    ((variantFree A B).obj Y ⟶ X) ≃
      (Y ⟶ (variantForgetful A B).obj X) := by
  sorry

theorem variant_projection_commutes (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (X : AlgebraArrowCategory A B) :
    (variantSetProjection B).obj ((variantForgetful A B).obj X) =
      (polynomialForget A).obj ((variantAlgebraProjection A B).obj X) := by
  rfl

theorem variant_projection_functors_commute (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] :
    variantForgetful A B ⋙ variantSetProjection B =
      variantAlgebraProjection A B ⋙ polynomialForget A := by
  rfl

/-- The free-forgetful adjunction in the arrow-category variant. -/
noncomputable def variantFreeAdjunction (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] :
    variantFree A B ⊣ variantForgetful A B :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun Y X => variantFreeHomEquiv A B X Y
      homEquiv_naturality_left_symm := by
        sorry
      homEquiv_naturality_right := by
        sorry }

/-- A proposition recording the arrow-category adjunction. -/
def VariantFreeForgetfulAdjunction (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] : Prop :=
  Nonempty (variantFree A B ⊣ variantForgetful A B)

theorem variantFreeForgetfulAdjunction (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] : VariantFreeForgetfulAdjunction A B :=
  ⟨variantFreeAdjunction A B⟩

end Formalization.Books.Cotangent.Unit03
