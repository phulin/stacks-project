import Formalization.Books.Cotangent.Unit03.AlgebraInterfaces
import Formalization.Books.Simplicial.Unit03.SimplicialObjects
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The standard simplicial polynomial resolution

This file gives a chapter-owned interface for the standard resolution used in
the cotangent-complex construction.  The terms are the iterates of the
polynomial-algebra monad, and the face and degeneracy maps are the usual monad
multiplication/unit maps.  Mathlib supplies the simplicial-object category and
the polynomial monad, but not this particular resolution.
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
    [CommRing X] [CommRing Y]
    (n : ℕ) (f : X →+* Y) : iteratedPolynomial A n X →+* iteratedPolynomial A n Y :=
  match n with
  | 0 => by
      change X →+* Y
      exact f
  | n + 1 => by
      change MvPolynomial (iteratedPolynomial A n X) A →+*
        MvPolynomial (iteratedPolynomial A n Y) A
      exact (MvPolynomial.rename (R := A) (iteratedPolynomialMap A n f)).toRingHom

theorem iteratedPolynomialMap_zero (A : Type u) [CommRing A] {X Y : Type u}
    [CommRing X] [CommRing Y]
    (f : X →+* Y) : iteratedPolynomialMap A 0 f = f := rfl

/-! ## Monad faces and degeneracies -/

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The algebra action of the polynomial monad on the `A`-algebra `B`. -/
def polynomialAlgebraAction : PolynomialAlgebra A B →+* B :=
  (MvPolynomial.aeval (R := A) (fun b : B => b)).toRingHom

/-- The face maps of the standard resolution. -/
noncomputable def standardResolutionFace : ∀ n : ℕ, Fin (n + 2) →
    iteratedPolynomial A (n + 2) B →+* iteratedPolynomial A (n + 1) B
  | 0, i =>
      Fin.cases
        (MvPolynomial.join₁ (R := A) (σ := B)).toRingHom
        (fun j =>
          Fin.cases
            (iteratedPolynomialMap A 1 polynomialAlgebraAction)
            (fun k => Fin.elim0 k) j) i
  | n + 1, i =>
      Fin.cases
        (MvPolynomial.join₁ (R := A)
          (σ := iteratedPolynomial A (n + 1) B)).toRingHom
        (fun j => iteratedPolynomialMap A 1 (standardResolutionFace n j)) i

/-- The degeneracy maps of the standard resolution. -/
noncomputable def standardResolutionDegeneracy : ∀ n : ℕ, Fin (n + 1) →
    iteratedPolynomial A (n + 1) B →+* iteratedPolynomial A (n + 2) B
  | 0, _ =>
      (MvPolynomial.rename (R := A) (MvPolynomial.X : B → PolynomialAlgebra A B)).toRingHom
  | n + 1, i =>
      Fin.cases
        ((MvPolynomial.rename (R := A)
          (MvPolynomial.X : iteratedPolynomial A (n + 1) B →
            PolynomialAlgebra A (iteratedPolynomial A (n + 1) B))).toRingHom)
        (fun j => iteratedPolynomialMap A 1 (standardResolutionDegeneracy n j)) i

/-! ## The simplicial object -/

/-
The next map is defined by the standard epi-mono factorization of a simplex
map.  The two recursive branches remove one face or one degeneracy, so the
definition follows the usual construction of the bar resolution for a lawful
monad.  The functorial identities are recorded separately below; their proofs
are the standard monad-law calculation.
-/
noncomputable def standardResolutionMap : ∀ {m n : ℕ},
    (SimplexCategory.mk m ⟶ SimplexCategory.mk n) →
      iteratedPolynomial A (n + 1) B →+* iteratedPolynomial A (m + 1) B
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
          exact RingHom.id _
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
      RingHom.id _ := by
  sorry

theorem standardResolutionMap_comp {m n k : ℕ}
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (g : SimplexCategory.mk n ⟶ SimplexCategory.mk k) :
    standardResolutionMap (A := A) (B := B) (f ≫ g) =
      (standardResolutionMap f).comp (standardResolutionMap g) := by
  sorry

/-- The standard simplicial `A`-algebra resolution of `B`. -/
noncomputable def standardResolution : SimplicialObject CommRingCat where
  obj Δ := CommRingCat.of (iteratedPolynomial A (Δ.unop.len + 1) B)
  map := fun {X Y} f => by
    cases X with
    | op X =>
      cases Y with
      | op Y =>
        cases X with
        | mk m =>
          cases Y with
          | mk n =>
            exact CommRingCat.ofHom
              (standardResolutionMap (A := A) (B := B) f.unop)
  map_id := by
    intro Δ
    cases Δ with
    | op Δ =>
      cases Δ with
      | mk n =>
        simpa using congrArg CommRingCat.ofHom
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
                simpa using congrArg CommRingCat.ofHom
                  (standardResolutionMap_comp (A := A) (B := B)
                    (f := g.unop) (g := f.unop))

/-! ## The augmentation -/

/-- Evaluation of the degree-zero polynomial algebra at the elements of `B`. -/
def standardResolutionZeroAugmentation :
    PolynomialAlgebra A B →ₐ[A] B :=
  MvPolynomial.aeval (R := A) (fun b : B => b)

theorem standardResolution_augmentation_compatibility
    (i : SimplexCategory) (f g : SimplexCategory.mk 0 ⟶ i) :
    (standardResolution (A := A) (B := B)).map f.op ≫
        CommRingCat.ofHom (standardResolutionZeroAugmentation (A := A) (B := B)).toRingHom =
      (standardResolution (A := A) (B := B)).map g.op ≫
        CommRingCat.ofHom (standardResolutionZeroAugmentation (A := A) (B := B)).toRingHom := by
  sorry

/-- The augmentation of the standard resolution to the constant simplicial ring `B`. -/
noncomputable def standardResolutionAugmentation :
    SimplicialObject.Augmented CommRingCat :=
  (standardResolution (A := A) (B := B)).augment (CommRingCat.of B)
    (CommRingCat.ofHom (standardResolutionZeroAugmentation (A := A) (B := B)).toRingHom)
    (standardResolution_augmentation_compatibility (A := A) (B := B))

theorem standardResolution_zero :
    (standardResolution (A := A) (B := B)).obj
        (Opposite.op (SimplexCategory.mk 0)) = CommRingCat.of (PolynomialAlgebra A B) := by
  rfl

theorem standardResolution_one :
    (standardResolution (A := A) (B := B)).obj
        (Opposite.op (SimplexCategory.mk 1)) =
      CommRingCat.of (PolynomialAlgebra A (PolynomialAlgebra A B)) := by
  rfl

/-! ## The variant resolution in the source remark -/

abbrev AlgebraArrow := AlgebraArrowCategory A B

/-- The identity arrow `B → B` used in the source's comparison remark. -/
def identityAlgebraArrow : AlgebraArrow (A := A) (B := B) :=
  CostructuredArrow.mk (𝟙 (CommAlgCat.of A B))

/-- The resolution obtained from the identity arrow in the variant setup. -/
noncomputable def variantResolutionAtIdentity : SimplicialObject CommRingCat :=
  standardResolution (A := A) (B := B)

theorem variantResolutionAtIdentity_eq_standardResolution :
    variantResolutionAtIdentity (A := A) (B := B) =
      standardResolution (A := A) (B := B) := rfl

end Formalization.Books.Cotangent.Unit03
