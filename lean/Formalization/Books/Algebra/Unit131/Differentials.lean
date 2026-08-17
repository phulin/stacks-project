import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Commutative Algebra, Chapter 131: Differentials

The source's derivations and modules of Kähler differentials are Mathlib's
`Derivation` and `KaehlerDifferential`.  The declarations below keep the
source order while exposing the source-facing statements that are not already
single canonical Mathlib declarations.
-/

namespace Formalization.Books.Algebra.Unit131

open scoped TensorProduct

attribute [local instance] SMulCommClass.of_commMonoid

/-! ## Derivations and the universal differential -/

/- The source's `Der_R(S, M)` is Mathlib's `Derivation R S M`.  Its additive
   and scalar-module structures, the equivalent R-linearity observation
   `D (r * a) = r • D a`, and postcomposition by a module map are already
   supplied by `Mathlib.RingTheory.Derivation.Basic`. -/

/- The source's presentation by free modules and relations is represented by
   Mathlib's canonical Kähler differential quotient.  This abbreviation is
   only a source-facing name for that construction. -/
abbrev ModuleOfDifferentials (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : Type _ :=
  KaehlerDifferential R S

/- The universal derivation is the canonical Mathlib construction, not a
   second quotient presentation. -/
noncomputable def universalDifferential
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Derivation R S (ModuleOfDifferentials R S) :=
  KaehlerDifferential.D R S

/- Composition with a linear map is the source's functoriality in the module. -/
def postcomposeDerivation
    {R S M N : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module S N] [Module R M] [Module R N]
    [IsScalarTower R S M] [IsScalarTower R S N]
    (D : Derivation R S M) (f : M →ₗ[S] N) : Derivation R S N :=
  f.compDer D

/- The universal-property isomorphism `Hom_S(Ω_{S/R}, M) ≅ Der_R(S, M)`. -/
noncomputable def derivationsEquivLinearMaps
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] :
    (ModuleOfDifferentials R S →ₗ[S] M) ≃ₗ[S] Derivation R S M :=
  KaehlerDifferential.linearMapEquivDerivation R S

theorem moduleOfDifferentials_subsingleton_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (h : Function.Surjective (algebraMap R S)) :
    Subsingleton (ModuleOfDifferentials R S) :=
  KaehlerDifferential.subsingleton_of_surjective R S h

/-! ## Functoriality -/

/- A square of algebra maps is written in Mathlib's orientation
   `A → B` over `R → T`. -/
noncomputable def mapOfDifferentials
    {R T A B : Type*} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R T] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra T B]
    [IsScalarTower R A B] [IsScalarTower R T B] [SMulCommClass T A B] :
    ModuleOfDifferentials R A →ₗ[A] ModuleOfDifferentials T B :=
  KaehlerDifferential.map R T A B

theorem mapOfDifferentials_apply_universalDifferential
    {R T A B : Type*} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R T] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra T B]
    [IsScalarTower R A B] [IsScalarTower R T B] [SMulCommClass T A B]
    (a : A) :
    mapOfDifferentials (R := R) (T := T) (A := A) (B := B)
        (universalDifferential R A a) =
      universalDifferential T B (algebraMap A B a) :=
  KaehlerDifferential.map_D R T A B a

theorem mapOfDifferentials_smul_universalDifferential
    {R T A B : Type*} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R T] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra T B]
    [IsScalarTower R A B] [IsScalarTower R T B] [SMulCommClass T A B]
    (a b : A) :
    mapOfDifferentials (R := R) (T := T) (A := A) (B := B)
        (a • universalDifferential R A b) =
      algebraMap A B a • universalDifferential T B (algebraMap A B b) := by
  sorry

/-! ## Colimits and surjective maps -/

/- The source writes the colimit assertion in shorthand.  Since it does not
   specify the filtered category, its ring-map cocones, or the scalar action
   on the resulting module colimit, there is no source-faithful Lean type for
   that line without adding categorical data not present in the text.  The
   canonical maps above are the precise functorial content used by the later
   statements. -/

theorem mapOfDifferentials_surjective
    {R T A B : Type*} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R T] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra T B]
    [IsScalarTower R A B] [IsScalarTower R T B] [SMulCommClass T A B]
    (h : Function.Surjective (algebraMap A B)) :
    Function.Surjective (mapOfDifferentials (R := R) (T := T) (A := A) (B := B)) :=
  KaehlerDifferential.map_surjective_of_surjective R T A B h

theorem mapOfDifferentials_ker_span
    {R T A B : Type*} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R T] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra T B]
    [IsScalarTower R A B] [IsScalarTower R T B] [SMulCommClass T A B]
    (h : Function.Surjective (algebraMap A B)) :
    LinearMap.ker (mapOfDifferentials (R := R) (T := T) (A := A) (B := B)) =
      Submodule.span A
        ((universalDifferential R A) ''
          {a : A | ∃ t : T, algebraMap A B a = algebraMap T B t}) := by
  sorry

/- If `i` lies in the kernel of `A →+* B`, the witness `t = 0` in the
   displayed generator set accounts for the source's parenthetical special
   case. -/

/-! ## Exact sequences, localization, and quotients -/

theorem exact_sequence_of_differentials
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] :
    Function.Exact (KaehlerDifferential.mapBaseChange A B C)
      (KaehlerDifferential.map A B C C) :=
  KaehlerDifferential.exact_mapBaseChange_map A B C

theorem exact_sequence_of_differentials_surjective
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] :
    Function.Surjective (KaehlerDifferential.map A B C C) :=
  KaehlerDifferential.map_surjective A B C

/- The first localization assertion is an ordinary bijectivity statement.  The
   second is expressed by the standard `IsLocalizedModule` predicate, which
   records the source's localized-module isomorphism without falsely claiming
   that the unlocalized map itself is bijective. -/
theorem localize_differentials_base
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid A)
    [Algebra (Localization S) B] [IsScalarTower A (Localization S) B]
    (hS : ∀ s, s ∈ S → IsUnit (algebraMap A B s)) :
    Function.Bijective (KaehlerDifferential.map A (Localization S) B B) := by
  sorry

noncomputable def localizationDifferentialMap
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid B) :
    letI : Algebra B (Localization S) := inferInstance
    letI : Algebra A (Localization S) :=
      Algebra.compHom (Localization S) (algebraMap A B)
    letI : SMul B (Localization S) :=
      (inferInstance : Algebra B (Localization S)).toSMul
    letI : SMul A (Localization S) :=
      (inferInstance : Algebra A (Localization S)).toSMul
    letI : IsScalarTower A B (Localization S) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower A A (Localization S) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : SMulCommClass A B (Localization S) :=
      SMulCommClass.of_commMonoid A B (Localization S)
    ModuleOfDifferentials A B →ₗ[B] ModuleOfDifferentials A (Localization S) := by
  letI : Algebra B (Localization S) := inferInstance
  letI : Algebra A (Localization S) :=
    Algebra.compHom (Localization S) (algebraMap A B)
  letI : SMul B (Localization S) :=
    (inferInstance : Algebra B (Localization S)).toSMul
  letI : SMul A (Localization S) :=
    (inferInstance : Algebra A (Localization S)).toSMul
  letI : IsScalarTower A B (Localization S) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A A (Localization S) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : SMulCommClass A B (Localization S) :=
    SMulCommClass.of_commMonoid A B (Localization S)
  exact KaehlerDifferential.map A A B (Localization S)

theorem localize_differentials_top
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid B) :
    letI : Algebra B (Localization S) := inferInstance
    letI : Algebra A (Localization S) :=
      Algebra.compHom (Localization S) (algebraMap A B)
    letI : SMul B (Localization S) :=
      (inferInstance : Algebra B (Localization S)).toSMul
    letI : SMul A (Localization S) :=
      (inferInstance : Algebra A (Localization S)).toSMul
    letI : IsScalarTower A B (Localization S) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower A A (Localization S) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : SMulCommClass A B (Localization S) :=
      SMulCommClass.of_commMonoid A B (Localization S)
    IsLocalizedModule S (localizationDifferentialMap (A := A) (B := B) S) := by
  sorry

theorem conormal_differential_exact
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (h : Function.Surjective (algebraMap A B)) :
    Function.Exact (KaehlerDifferential.kerCotangentToTensor R A B)
      (KaehlerDifferential.mapBaseChange R A B) :=
  KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h

theorem conormal_differential_surjective
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (h : Function.Surjective (algebraMap A B)) :
    Function.Surjective (KaehlerDifferential.mapBaseChange R A B) :=
  KaehlerDifferential.mapBaseChange_surjective R A B h

theorem conormal_differential_on_generator
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (x : RingHom.ker (algebraMap A B)) :
    KaehlerDifferential.kerCotangentToTensor R A B (Ideal.toCotangent _ x) =
      1 ⊗ₜ[A] universalDifferential R A x.1 :=
  KaehlerDifferential.kerCotangentToTensor_toCotangent R A B x

theorem conormal_differential_split
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (h : Function.Surjective (algebraMap A B))
    (sectionMap : B →ₐ[R] A)
    (sectionMap_right_inverse :
      ∀ b, algebraMap A B (sectionMap b) = b) :
    ∃ e : ModuleOfDifferentials R B →ₗ[B]
        B ⊗[A] ModuleOfDifferentials R A,
      (KaehlerDifferential.mapBaseChange R A B).comp e = LinearMap.id := by
  sorry

noncomputable def differentialModPowerMap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal S) {n : ℕ} :
    let S' := S ⧸ I ^ (n + 1)
    let T := S ⧸ I ^ n
    letI : Algebra S' T :=
      (Ideal.Quotient.factorPow I (Nat.le_succ n)).toAlgebra
    (T ⊗[S] ModuleOfDifferentials R S) →ₗ[T]
      (T ⊗[S'] ModuleOfDifferentials R S') := by
  let S' := S ⧸ I ^ (n + 1)
  let T := S ⧸ I ^ n
  letI : Algebra S' T :=
    (Ideal.Quotient.factorPow I (Nat.le_succ n)).toAlgebra
  letI : Algebra S T := Algebra.compHom T (algebraMap S S')
  letI : IsScalarTower S S' T := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower S T T := by
    constructor
    intro r t x
    change (algebraMap S T r * t) * x = algebraMap S T r * (t * x)
    rw [mul_assoc]
  let g : ModuleOfDifferentials R S →ₗ[S] ModuleOfDifferentials R S' :=
    KaehlerDifferential.map R R S S'
  let m₁ :=
    @TensorProduct.AlgebraTensorModule.map
      S T T (ModuleOfDifferentials R S) T (ModuleOfDifferentials R S')
      _ _ _ _ _ _ (inferInstance : IsScalarTower S T T) _ _ _ _ _
      (inferInstance : IsScalarTower S T T) _ _
      (LinearMap.id) g
  letI : IsScalarTower S' T T := by
    constructor
    intro r t x
    change (algebraMap S' T r * t) * x = algebraMap S' T r * (t * x)
    rw [mul_assoc]
  let e₀ :=
    @TensorProduct.AlgebraTensorModule.cancelBaseChange
      S S' T T (ModuleOfDifferentials R S')
      _ _ _ _ _ _ _ _ _ _ (inferInstance : IsScalarTower S T T) _ _ _ _
      (inferInstance : IsScalarTower S' T T)
  letI : TensorProduct.CompatibleSMul S S' S' (ModuleOfDifferentials R S') :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (M := S') (N := ModuleOfDifferentials R S')
      (show Function.Surjective (algebraMap S S') from Ideal.Quotient.mk_surjective)
  let m₂ :=
    TensorProduct.AlgebraTensorModule.map
      (R := S') (A := T) (M := T)
      (N := S' ⊗[S] ModuleOfDifferentials R S') (P := T)
      (Q := ModuleOfDifferentials R S')
      (LinearMap.id) (TensorProduct.lidOfCompatibleSMul S S'
        (ModuleOfDifferentials R S')).toLinearMap
  exact m₂.comp (e₀.symm.toLinearMap.comp m₁)

theorem differential_mod_power_ideal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal S) {n : ℕ} (hn : 1 ≤ n) :
    let S' := S ⧸ I ^ (n + 1)
    let T := S ⧸ I ^ n
    letI : Algebra S' T :=
      (Ideal.Quotient.factorPow I (Nat.le_succ n)).toAlgebra
    Function.Bijective
      (differentialModPowerMap (R := R) (S := S) I (n := n)) := by
  sorry

/-! ## Base change and the diagonal -/

noncomputable def baseChangeDifferentialsEquiv
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S]
    [Algebra R R'] [Algebra R S] :
    letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra.IsPushout R R' S (R' ⊗[R] S) := inferInstance
    letI : Module (R' ⊗[R] S) (R' ⊗[R] ModuleOfDifferentials R S) :=
      KaehlerDifferential.moduleBaseChange' R R' S (R' ⊗[R] S)
    -- Mathlib's tensor-product convention puts the base-change factor first.
    R' ⊗[R] ModuleOfDifferentials R S ≃ₗ[R' ⊗[R] S]
      ModuleOfDifferentials R' (R' ⊗[R] S) := by
  letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra.IsPushout R R' S (R' ⊗[R] S) := inferInstance
  letI : Module (R' ⊗[R] S) (R' ⊗[R] ModuleOfDifferentials R S) :=
    KaehlerDifferential.moduleBaseChange' R R' S (R' ⊗[R] S)
  let e := KaehlerDifferential.tensorKaehlerEquivBase R R' S (R' ⊗[R] S)
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := ?_ }
  intro b x
  exact KaehlerDifferential.map_liftBaseChange_smul R R' S (R' ⊗[R] S) b x

noncomputable def diagonalDifferentialsEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    ModuleOfDifferentials R S ≃ₗ[S]
      (KaehlerDifferential.ideal R S).Cotangent :=
  by
    change (KaehlerDifferential.ideal R S).Cotangent ≃ₗ[S]
      (KaehlerDifferential.ideal R S).Cotangent
    exact LinearEquiv.refl S (KaehlerDifferential.ideal R S).Cotangent

theorem diagonalDifferentialsEquiv_formula
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (a b : S) :
    diagonalDifferentialsEquiv (R := R) (S := S)
        (a • universalDifferential R S b) =
      a • (KaehlerDifferential.ideal R S).toCotangent
        ⟨1 ⊗ₜ[R] b - b ⊗ₜ[R] 1,
          KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R b⟩ := by
  sorry

/-! ## Polynomial rings and finiteness -/

noncomputable def polynomialDifferentialBasis
    (R : Type*) [CommRing R] (n : ℕ) :
    Module.Basis (Fin n) (MvPolynomial (Fin n) R)
      (ModuleOfDifferentials R (MvPolynomial (Fin n) R)) :=
  KaehlerDifferential.mvPolynomialBasis R (Fin n)

theorem polynomialDifferentialBasis_apply
    (R : Type*) [CommRing R] (n : ℕ) (i : Fin n) :
    polynomialDifferentialBasis R n i =
      universalDifferential R (MvPolynomial (Fin n) R) (MvPolynomial.X i) :=
  KaehlerDifferential.mvPolynomialBasis_apply R (Fin n) i

theorem polynomial_differentials_free
    (R : Type*) [CommRing R] (n : ℕ) :
    Module.Free (MvPolynomial (Fin n) R)
      (ModuleOfDifferentials R (MvPolynomial (Fin n) R)) := by
  infer_instance

theorem polynomial_differentials_finite
    (R : Type*) [CommRing R] (n : ℕ) :
    Module.Finite (MvPolynomial (Fin n) R)
      (ModuleOfDifferentials R (MvPolynomial (Fin n) R)) := by
  infer_instance

theorem differentials_finitely_presented
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] :
    Module.FinitePresentation S (ModuleOfDifferentials R S) := by
  infer_instance

theorem differentials_finitely_generated
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] :
    Module.Finite S (ModuleOfDifferentials R S) := by
  infer_instance

end Formalization.Books.Algebra.Unit131
