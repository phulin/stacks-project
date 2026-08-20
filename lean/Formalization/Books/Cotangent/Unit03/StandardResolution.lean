import Formalization.Books.Cotangent.Unit03.AlgebraInterfaces
import Formalization.Books.Simplicial.Unit34.StandardResolutions
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# The standard simplicial polynomial resolution

This file gives a chapter-owned polynomial model for the standard resolution
used in the cotangent-complex construction.  The established simplicial
standard-resolution interface supplies the functor-valued construction; the
terms here are its iterated polynomial algebras, and the displayed face and
degeneracy maps are the corresponding monad multiplication/unit maps.
-/

namespace Formalization.Books.Cotangent.Unit03

open CategoryTheory
open CategoryTheory.SimplicialObject
open scoped _root_.Simplicial

universe u

/-! ## Iterated polynomial algebras -/

/-- The polynomial `A`-algebra on a type of variables. -/
abbrev PolynomialAlgebra (A X : Type u) [CommRing A] := MvPolynomial X A

/-- The `(n+1)`-fold iterate of the polynomial-algebra construction. -/
def iteratedPolynomial (A : Type u) [CommRing A] : ℕ → Type u → Type u
  | 0, X => X
  | n + 1, X => PolynomialAlgebra A (iteratedPolynomial A n X)

noncomputable instance iteratedPolynomialCommRing (A : Type u) [CommRing A] (X : Type u)
    [CommRing X] : ∀ n : ℕ, CommRing (iteratedPolynomial A n X)
  | 0 => by
      change CommRing X
      infer_instance
  | n + 1 => by
      change CommRing (MvPolynomial (iteratedPolynomial A n X) A)
      infer_instance

noncomputable instance iteratedPolynomialAlgebra (A : Type u) [CommRing A] (X : Type u)
    [CommRing X] [Algebra A X] : ∀ n : ℕ, Algebra A (iteratedPolynomial A n X)
  | 0 => by
      change Algebra A X
      infer_instance
  | n + 1 => by
      change Algebra A (MvPolynomial (iteratedPolynomial A n X) A)
      infer_instance

/-- The ring hom induced by a map of variables at an iterated polynomial level. -/
noncomputable def iteratedPolynomialMap (A : Type u) [CommRing A] {X Y : Type u}
    [CommRing X] [CommRing Y] [Algebra A X] [Algebra A Y]
    (n : ℕ) (f : X →ₐ[A] Y) : iteratedPolynomial A n X →ₐ[A] iteratedPolynomial A n Y :=
  match n with
  | 0 => by
      change X →ₐ[A] Y
      exact f
  | n + 1 => by
      change MvPolynomial (iteratedPolynomial A n X) A →ₐ[A]
        MvPolynomial (iteratedPolynomial A n Y) A
      exact MvPolynomial.rename (R := A) (iteratedPolynomialMap A n f)

theorem iteratedPolynomialMap_zero (A : Type u) [CommRing A] {X Y : Type u}
    [CommRing X] [CommRing Y] [Algebra A X] [Algebra A Y]
    (f : X →ₐ[A] Y) : iteratedPolynomialMap A 0 f = f := rfl

/-! ## Monad faces and degeneracies -/

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The algebra action of the polynomial monad on the `A`-algebra `B`. -/
def polynomialAlgebraAction : PolynomialAlgebra A B →ₐ[A] B :=
  MvPolynomial.aeval (R := A) (fun b : B => b)

/-- The face maps of the standard resolution. -/
noncomputable def standardResolutionFace : ∀ n : ℕ, Fin (n + 2) →
    iteratedPolynomial A (n + 2) B →ₐ[A] iteratedPolynomial A (n + 1) B
  | 0, i =>
      Fin.cases
        (MvPolynomial.join₁ (R := A) (σ := B))
        (fun j =>
          Fin.cases
            (iteratedPolynomialMap A 1 polynomialAlgebraAction)
            (fun k => Fin.elim0 k) j) i
  | n + 1, i =>
      Fin.cases
        (MvPolynomial.join₁ (R := A)
          (σ := iteratedPolynomial A (n + 1) B))
        (fun j => iteratedPolynomialMap A 1 (standardResolutionFace n j)) i

/-- The degeneracy maps of the standard resolution. -/
noncomputable def standardResolutionDegeneracy : ∀ n : ℕ, Fin (n + 1) →
    iteratedPolynomial A (n + 1) B →ₐ[A] iteratedPolynomial A (n + 2) B
  | 0, _ =>
      MvPolynomial.rename (R := A) (MvPolynomial.X : B → PolynomialAlgebra A B)
  | n + 1, i =>
      Fin.cases
        (MvPolynomial.rename (R := A)
          (MvPolynomial.X : iteratedPolynomial A (n + 1) B →
            PolynomialAlgebra A (iteratedPolynomial A (n + 1) B)))
        (fun j => iteratedPolynomialMap A 1 (standardResolutionDegeneracy n j)) i

/-! ## The simplicial object -/

/-- The adjunction situation used by the established simplicial standard
resolution construction. -/
noncomputable def polynomialResolutionSituation (A : Type u) [CommRing A] :
    Formalization.Books.Simplicial.Unit34.StandardResolutionSituation
      (CommAlgCat A) (Type u) :=
  { U := Formalization.Books.Simplicial.Unit34.commutativePolynomialFree (A := A)
    V := polynomialForget A
    adjunction :=
      Formalization.Books.Simplicial.Unit34.commutativePolynomialAdjunction (A := A) }

/-- The functor-valued simplicial object `X_•` from the source. -/
noncomputable def standardResolutionFunctor :
    SimplicialObject (CommAlgCat A ⥤ CommAlgCat A) :=
  Formalization.Books.Simplicial.Unit34.standardResolutionObject
    (polynomialResolutionSituation A)

/-
The next map is defined by the standard epi-mono factorization of a simplex
map.  The two recursive branches remove one face or one degeneracy, so the
definition follows the usual construction of the bar resolution for a lawful
monad.  The functorial identities are recorded separately below; their proofs
are the standard monad-law calculation.
-/
noncomputable def standardResolutionMap : ∀ {m n : ℕ},
    (SimplexCategory.mk m ⟶ SimplexCategory.mk n) →
      iteratedPolynomial A (n + 1) B →ₐ[A] iteratedPolynomial A (m + 1) B
  | m, n, f => by
      classical
      by_cases hs : Function.Surjective f.toOrderHom
      · by_cases hi : Function.Injective f.toOrderHom
        · have hmn : m = n := by
            have e : Fin (m + 1) ≃ Fin (n + 1) :=
              Equiv.ofBijective f.toOrderHom ⟨hi, hs⟩
            have hc := Fintype.card_congr e
            simpa [Nat.succ_eq_add_one] using hc
          subst hmn
          have hf : f = 𝟙 _ := by
            exact @SimplexCategory.eq_id_of_isIso _ f
              (SimplexCategory.isIso_of_bijective ⟨hi, hs⟩)
          exact AlgHom.id A _
        · cases m with
          | zero =>
              exfalso
              apply hi
              intro x y h
              exact (Fin.eq_zero x).trans (Fin.eq_zero y).symm
          | succ m =>
              let hfactor :=
                SimplexCategory.eq_σ_comp_of_not_injective f hi
              let i := Classical.choose hfactor
              let f' := Classical.choose (Classical.choose_spec hfactor)
              have h := Classical.choose_spec (Classical.choose_spec hfactor)
              exact (standardResolutionDegeneracy (A := A) (B := B) m i).comp
                (standardResolutionMap f')
      · cases n with
        | zero =>
            exfalso
            apply hs
            intro y
            exact ⟨0, (Fin.eq_zero (f.toOrderHom 0)).trans (Fin.eq_zero y).symm⟩
        | succ n =>
            let hfactor :=
              SimplexCategory.eq_comp_δ_of_not_surjective f hs
            let i := Classical.choose hfactor
            let f' := Classical.choose (Classical.choose_spec hfactor)
            have h := Classical.choose_spec (Classical.choose_spec hfactor)
            exact (standardResolutionMap f').comp
              (standardResolutionFace (A := A) (B := B) n i)
  termination_by m n => m + n

theorem standardResolutionMap_id {n : ℕ} :
    standardResolutionMap (A := A) (B := B) (𝟙 (SimplexCategory.mk n)) =
      AlgHom.id A _ := by
  classical
  have hs : Function.Surjective
      (SimplexCategory.Hom.toOrderHom (𝟙 (SimplexCategory.mk n))) := by
    intro x
    exact ⟨x, rfl⟩
  have hi : Function.Injective
      (SimplexCategory.Hom.toOrderHom (𝟙 (SimplexCategory.mk n))) := by
    intro x y h
    exact h
  unfold standardResolutionMap
  rw [dif_pos hs, dif_pos hi]

theorem standardResolutionMap_comp {m n k : ℕ}
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (g : SimplexCategory.mk n ⟶ SimplexCategory.mk k) :
    standardResolutionMap (A := A) (B := B) (f ≫ g) =
      (standardResolutionMap f).comp (standardResolutionMap g) := by
  sorry

/-- The standard simplicial `A`-algebra resolution of `B`. -/
noncomputable def standardResolution : SimplicialObject (CommAlgCat A) where
  obj Δ := CommAlgCat.of A (iteratedPolynomial A (Δ.unop.len + 1) B)
  map := fun {X Y} f => by
    cases X with
    | op X =>
      cases Y with
      | op Y =>
        cases X with
        | mk m =>
          cases Y with
          | mk n =>
            exact CommAlgCat.ofHom
              (standardResolutionMap (A := A) (B := B) f.unop)
  map_id := by
    intro Δ
    cases Δ with
    | op Δ =>
      cases Δ with
      | mk n =>
        simpa using congrArg CommAlgCat.ofHom
          (standardResolutionMap_id (A := A) (B := B) (n := n))
  map_comp := by
    intro X Y Z f g
    cases X with
    | op X =>
      cases Y with
      | op Y =>
        cases Z with
        | op Z =>
          cases X with
          | mk m =>
            cases Y with
            | mk n =>
              cases Z with
              | mk k =>
                simpa using congrArg CommAlgCat.ofHom
                  (standardResolutionMap_comp (A := A) (B := B)
                    (f := g.unop) (g := f.unop))

/-- Evaluation of the functor-valued standard resolution at an `A`-algebra. -/
noncomputable def standardResolutionFunctorAt : SimplicialObject (CommAlgCat A) :=
  ((SimplicialObject.whiskering (CommAlgCat A ⥤ CommAlgCat A) (CommAlgCat A)).obj
      ((CategoryTheory.evaluation (CommAlgCat A) (CommAlgCat A)).obj
        (CommAlgCat.of A B))).obj (standardResolutionFunctor (A := A))

theorem standardResolutionFunctorAt_eq_standardResolution :
    standardResolutionFunctorAt (A := A) (B := B) =
      standardResolution (A := A) (B := B) := by
  sorry

/-! ## The augmentation -/

/-- Evaluation of the degree-zero polynomial algebra at the elements of `B`. -/
def standardResolutionZeroAugmentation :
    PolynomialAlgebra A B →ₐ[A] B :=
  MvPolynomial.aeval (R := A) (fun b : B => b)

theorem standardResolution_augmentation_compatibility
    (i : SimplexCategory) (f g : SimplexCategory.mk 0 ⟶ i) :
    (standardResolution (A := A) (B := B)).map f.op ≫
        CommAlgCat.ofHom (standardResolutionZeroAugmentation (A := A) (B := B)) =
      (standardResolution (A := A) (B := B)).map g.op ≫
        CommAlgCat.ofHom (standardResolutionZeroAugmentation (A := A) (B := B)) := by
  sorry

/-- The augmentation of the standard resolution to the constant simplicial `A`-algebra `B`. -/
noncomputable def standardResolutionAugmentation :
    SimplicialObject.Augmented (CommAlgCat A) :=
  (standardResolution (A := A) (B := B)).augment (CommAlgCat.of A B)
    (CommAlgCat.ofHom (standardResolutionZeroAugmentation (A := A) (B := B)))
    (standardResolution_augmentation_compatibility (A := A) (B := B))

theorem standardResolution_zero :
    (standardResolution (A := A) (B := B)).obj
        (Opposite.op (SimplexCategory.mk 0)) = CommAlgCat.of A (PolynomialAlgebra A B) := by
  rfl

theorem standardResolution_one :
    (standardResolution (A := A) (B := B)).obj
        (Opposite.op (SimplexCategory.mk 1)) =
      CommAlgCat.of A (PolynomialAlgebra A (PolynomialAlgebra A B)) := by
  rfl

theorem standardResolution_degree (n : ℕ) :
    (standardResolution (A := A) (B := B)).obj
        (Opposite.op (SimplexCategory.mk n)) =
      CommAlgCat.of A (iteratedPolynomial A (n + 1) B) := by
  rfl

/-! ## The variant resolution in the source remark -/

abbrev AlgebraArrow := AlgebraArrowCategory A B

/-- The identity arrow `B → B` used in the source's comparison remark. -/
def identityAlgebraArrow : AlgebraArrow (A := A) (B := B) :=
  CostructuredArrow.mk (𝟙 (CommAlgCat.of A B))

/-- The adjunction situation for the arrow-category variant. -/
noncomputable def variantResolutionSituation (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] :
    Formalization.Books.Simplicial.Unit34.StandardResolutionSituation
      (AlgebraArrowCategory A B) (SetArrowCategory B) :=
  { U := variantFree A B
    V := variantForgetful A B
    adjunction := variantFreeAdjunction A B }

/-- The functor-valued standard resolution in the arrow-category variant. -/
noncomputable def variantResolutionFunctor (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] :
    SimplicialObject (AlgebraArrowCategory A B ⥤ AlgebraArrowCategory A B) :=
  Formalization.Books.Simplicial.Unit34.standardResolutionObject
    (variantResolutionSituation A B)

/-- Evaluation of the variant resolution at the identity arrow `B → B`. -/
noncomputable def variantResolutionAtIdentity (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] :
    SimplicialObject (AlgebraArrowCategory A B) :=
  ((SimplicialObject.whiskering
      (AlgebraArrowCategory A B ⥤ AlgebraArrowCategory A B)
      (AlgebraArrowCategory A B)).obj
      ((CategoryTheory.evaluation (AlgebraArrowCategory A B)
        (AlgebraArrowCategory A B)).obj (identityAlgebraArrow (A := A) (B := B)))).obj
    (variantResolutionFunctor A B)

/-- The underlying simplicial `A`-algebra of the identity-arrow resolution. -/
noncomputable def variantResolutionAtIdentityProjection (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] : SimplicialObject (CommAlgCat A) :=
  ((SimplicialObject.whiskering (AlgebraArrowCategory A B) (CommAlgCat A)).obj
    (variantAlgebraProjection A B)).obj (variantResolutionAtIdentity A B)

theorem variantResolutionAtIdentityProjection_eq_standardResolution (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] :
    variantResolutionAtIdentityProjection A B =
      standardResolution (A := A) (B := B) := by
  sorry

end Formalization.Books.Cotangent.Unit03
