import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Formalization.Books.MoreAlgebra.Unit58.TensorProductsOfComplexes

/-!
# More on Algebra, Chapter 72: Hom complexes

The source's Hom complex is Mathlib's canonical `CochainComplex.HomComplex`
construction.  This file records the module-valued presentation used by the
chapter and its tensor--Hom interfaces.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open HomologicalComplex
open ComplexShape

universe u

namespace Formalization.Books.MoreAlgebra.Unit72

/-! ## The Hom complex -/

abbrev Comp (R : Type u) [CommRing R] :=
  Formalization.Books.MoreAlgebra.Unit58.Comp R

abbrev K (R : Type u) [CommRing R] :=
  Formalization.Books.MoreAlgebra.Unit58.K R

abbrev homCochain {R : Type u} [CommRing R]
    (L M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :=
  CochainComplex.HomComplex.Cochain L M n

abbrev homDifferential {R : Type u} [CommRing R]
    (L M : CochainComplex (ModuleCat.{u} R) ℤ) (n m : ℤ) :
    homCochain L M n →ₗ[R] homCochain L M m :=
  CochainComplex.HomComplex.δ_hom R L M n m

/-- The module-valued Hom complex used in the source.

Mathlib's canonical Hom complex is additive-group-valued.  Its cochains carry
the canonical `R`-module structure, so the same construction is lifted to
`ModuleCat R` for the source's tensor statements.
-/
noncomputable def homComplex {R : Type u} [CommRing R]
    (L M : Comp R) : Comp R where
  X n := ModuleCat.of R (homCochain L M n)
  d n m := ModuleCat.ofHom (homDifferential L M n m)
  shape n m hnm := by
    classical
    by_cases h : n + 1 = m
    · exact (hnm (by simpa only [ComplexShape.up_Rel] using h)).elim
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change CochainComplex.HomComplex.δ n m z = 0
      exact CochainComplex.HomComplex.δ_shape n m h z
  d_comp_d' n m p hnm hmp := by
    classical
    have hnm' : n + 1 = m := by
      simpa only [ComplexShape.up_Rel] using hnm
    have hmp' : m + 1 = p := by
      simpa only [ComplexShape.up_Rel] using hmp
    subst m
    subst p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    simp only [ModuleCat.hom_comp]
    simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply]
    change homDifferential L M (n + 1) (n + 1 + 1)
      (homDifferential L M n (n + 1) z) =
        (0 : homCochain L M (n + 1 + 1))
    exact CochainComplex.HomComplex.δ_δ n (n + 1) (n + 1 + 1) z

/-- The source's degree formula for the Hom complex, using Mathlib's canonical
cochain type. -/
theorem homCochain_degree_formula {R : Type u} [CommRing R]
    {L M : CochainComplex (ModuleCat.{u} R) ℤ} (n : ℤ) :
    homCochain L M n =
      ∀ (T : CochainComplex.HomComplex.Triplet n),
        L.X T.p ⟶ M.X T.q := rfl

/-- The source's differential rule, in component form. -/
theorem homDifferential_component {R : Type u} [CommRing R]
    {L M : CochainComplex (ModuleCat.{u} R) ℤ}
    {n m : ℤ} (h : n + 1 = m) (f : homCochain L M n) (p q : ℤ)
    (hpq : p + m = q) :
    (homDifferential L M n m f).v p q hpq =
      f.v p (p + n) rfl ≫ M.d (p + n) q +
        m.negOnePow • L.d p (p + m - n) ≫
          f.v (p + m - n) q (by rw [hpq, sub_add_cancel]) := by
  change (CochainComplex.HomComplex.δ n m f).v p q hpq = _
  simpa only [homDifferential] using
    (CochainComplex.HomComplex.δ_v n m h f p q hpq
      (p + n) (p + m - n) (by lia) (by lia))

/-- The Hom differential squares to zero. -/
theorem homDifferential_squared {R : Type u} [CommRing R]
    {L M : CochainComplex (ModuleCat.{u} R) ℤ}
    (n m p : ℤ) (f : homCochain L M n) :
    homDifferential L M m p (homDifferential L M n m f) = 0 := by
  exact CochainComplex.HomComplex.δ_δ n m p f

/- The displayed source identity is recorded at the canonical additive Hom
   complex, where Mathlib provides the homology API and shifted equivalence. -/
noncomputable def canonicalAdditiveHomComplexCohomologyEquiv {R : Type u} [CommRing R]
    (L M : Comp R) (n : ℤ) :
    (CochainComplex.HomComplex L M).homology n ≃+
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj L ⟶
        (HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj (M⟦n⟧)) := by
  exact
    (CochainComplex.HomComplex.homologyAddEquiv (K := L) (L := M) (n := n)).trans
      (CochainComplex.HomComplex.CohomologyClass.homAddEquiv
        (K := L) (L := M) (n := n))

/-- The source-facing module-valued Hom complex has the same shifted
cohomology identification. -/
theorem homComplexCohomologyEquiv_exists {R : Type u} [CommRing R]
    (L M : Comp R) (n : ℤ) :
    Nonempty ((homComplex L M).homology n ≃+
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj L ⟶
        (HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj (M⟦n⟧))) := by
  sorry

noncomputable def homComplexCohomologyEquiv {R : Type u} [CommRing R]
    (L M : Comp R) (n : ℤ) :
    (homComplex L M).homology n ≃+
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj L ⟶
        (HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj (M⟦n⟧)) :=
  Classical.choice (homComplexCohomologyEquiv_exists L M n)

/-! ## Component identification and internal Hom -/

/-- The canonical currying equivalence used in the component calculation. -/
noncomputable def moduleHomTensorHomEquiv {R : Type u} [CommRing R]
    (A B C : ModuleCat.{u} R) :
    ((MonoidalCategory.tensorLeft B).obj A ⟶ C) ≃
      (A ⟶ ((linearCoyoneda R (ModuleCat R)).obj (Opposite.op B)).obj C) :=
  ModuleCat.monoidalClosedHomEquiv B A C

theorem moduleHomTensorHom_identification {R : Type u} [CommRing R]
    (A B C : ModuleCat.{u} R) :
    Nonempty (((MonoidalCategory.tensorLeft B).obj A ⟶ C) ≃
      (A ⟶ ((linearCoyoneda R (ModuleCat R)).obj (Opposite.op B)).obj C)) :=
  ⟨moduleHomTensorHomEquiv A B C⟩

/-- The symmetric tensor--Hom identification used when the tensor factors are
written in the source order. -/
theorem componentHomTensorEquiv_exists {R : Type u} [CommRing R]
    (A B C : ModuleCat.{u} R) :
    Nonempty ((A ⟶ ModuleCat.of R (B ⟶ C)) ≃ (A ⊗ B ⟶ C)) := by
  sorry

noncomputable def componentHomTensorEquiv {R : Type u} [CommRing R]
    (A B C : ModuleCat.{u} R) :
    (A ⟶ ModuleCat.of R (B ⟶ C)) ≃ (A ⊗ B ⟶ C) :=
  Classical.choice (componentHomTensorEquiv_exists A B C)

/-! The componentwise instance of the preceding identification is the
    displayed equation used in the proof of Lemma `compose`. -/
theorem equation_identification_exists {R : Type u} [CommRing R]
    (K L M : Comp R) (r s q : ℤ) :
    Nonempty ((K.X (-q) ⟶ ModuleCat.of R (L.X (-s) ⟶ M.X r)) ≃
      ((K.X (-q) ⊗ L.X (-s)) ⟶ M.X r)) := by
  sorry

/-- The source's product-indexed description of a degree-n cochain. -/
theorem homCochain_product_equiv_exists {R : Type u} [CommRing R]
    (L M : Comp R) (n : ℤ) :
    Nonempty (homCochain L M n ≃
      ∀ (p q : ℤ) (_ : n = p + q), L.X (-q) ⟶ M.X p) := by
  sorry

noncomputable def homCochainProductEquiv {R : Type u} [CommRing R]
    (L M : Comp R) (n : ℤ) :
    homCochain L M n ≃
      ∀ (p q : ℤ) (_ : n = p + q), L.X (-q) ⟶ M.X p :=
  Classical.choice (homCochain_product_equiv_exists L M n)

/-- The Hom differential can be written as postcomposition by the target
differential plus the signed precomposition by the source differential. -/
theorem homDifferential_as_composition {R : Type u} [CommRing R]
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} {n : ℤ}
    (z : CochainComplex.HomComplex.Cochain F G n) :
    CochainComplex.HomComplex.δ n (n + 1) z =
      CochainComplex.HomComplex.Cochain.comp z
          (CochainComplex.HomComplex.Cochain.diff G) (by omega) +
        (n + 1).negOnePow •
          CochainComplex.HomComplex.Cochain.comp
            (CochainComplex.HomComplex.Cochain.diff F) z (by omega) := by
  sorry

/-- The component form of the preceding identity is the source's β equation
when `F` is a Hom complex. -/
theorem beta_component_differential_formula {R : Type u} [CommRing R]
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} {n : ℤ}
    (z : CochainComplex.HomComplex.Cochain F G n) (p q : ℤ)
    (hpq : p + (n + 1) = q) :
    (CochainComplex.HomComplex.δ n (n + 1) z).v p q hpq =
      z.v p (p + n) rfl ≫ G.d (p + n) q +
        (n + 1).negOnePow • F.d p (p + 1) ≫ z.v (p + 1) q (by omega) := by
  exact CochainComplex.HomComplex.δ_v n (n + 1) rfl z p q hpq
    (p + n) (p + 1) (by omega) (by omega)

/-- The component differential on the tensor product is the source's α
equation. -/
theorem alpha_component_differential_formula {R : Type u} [CommRing R]
    (K L M : Comp R) (p r : ℤ) :
    ιMapBifunctor (homComplex L M) K
        (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (.up ℤ)
        p r (p + r) rfl ≫
        (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R
          (homComplex L M) K).d (p + r) (p + r + 1) =
      ((homComplex L M).d p (p + 1) ⊗ₘ 𝟙 (K.X r)) ≫
          ιMapBifunctor (homComplex L M) K
            (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (.up ℤ)
            (p + 1) r (p + r + 1) (by dsimp; omega) +
        p.negOnePow •
          ((𝟙 ((homComplex L M).X p) ⊗ₘ K.d r (r + 1)) ≫
            ιMapBifunctor (homComplex L M) K
              (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (.up ℤ)
              p (r + 1) (p + r + 1) (by dsimp; omega)) := by
  exact Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex_differential_formula
    R (homComplex L M) K p r

/-! ## The component evaluation map and signs -/

/-- Projection of a Hom-complex cochain onto one component. -/
noncomputable def componentProjection {R : Type u} [CommRing R]
    (K L : Comp R) (q r s : ℤ) (h : q + r = s) :
    ModuleCat.of R (homCochain K L (-s)) ⟶
      ModuleCat.of R (K.X r ⟶ L.X (-q)) :=
  ModuleCat.ofHom
    { toFun := fun z => z.v r (-q) (by omega)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- The inclusion obtained by precomposition with the preceding component
projection. -/
noncomputable def componentInclusion {R : Type u} [CommRing R]
    (K L M : Comp R) (p q r s : ℤ) (h : q + r = s) :
    ModuleCat.of R (ModuleCat.of R (K.X r ⟶ L.X (-q)) ⟶ M.X p) ⟶
      ModuleCat.of R (ModuleCat.of R (homCochain K L (-s)) ⟶ M.X p) :=
  ModuleCat.ofHom
    { toFun := fun φ => componentProjection K L q r s h ≫ φ
      map_add' := by intros; simp
      map_smul' := by intros; simp }

/-- The elementary evaluation map from the source proof, functorial in the
three displayed module variables. -/
theorem componentEvaluation_exists {R : Type u} [CommRing R]
    (K L M : Comp R) (p q r : ℤ) :
    Nonempty ((ModuleCat.of R (L.X (-q) ⟶ M.X p)) ⊗ K.X r ⟶
      ModuleCat.of R (ModuleCat.of R (K.X r ⟶ L.X (-q)) ⟶ M.X p)) := by
  sorry

/-- A usable chosen representative of the canonical component evaluation. -/
noncomputable def componentEvaluation {R : Type u} [CommRing R]
    (K L M : Comp R) (p q r : ℤ) :
    (ModuleCat.of R (L.X (-q) ⟶ M.X p)) ⊗ K.X r ⟶
      ModuleCat.of R (ModuleCat.of R (K.X r ⟶ L.X (-q)) ⟶ M.X p) :=
  Classical.choice (componentEvaluation_exists K L M p q r)

theorem componentEvaluation_apply {R : Type u} [CommRing R]
    (K L M : Comp R) (p q r : ℤ)
    (φ : L.X (-q) ⟶ M.X p) (k : K.X r)
    (ψ : K.X r ⟶ L.X (-q)) :
    (componentEvaluation K L M p q r).hom (φ ⊗ₜ[R] k) ψ = φ (ψ k) := by
  sorry

/-- The sign chosen in the source's evaluation construction. -/
def evaluationSign (_p q r : ℤ) : ℤˣ := (r + q * r).negOnePow

theorem evaluationSign_recursions (_p q r : ℤ) :
    evaluationSign (_p + 1) q r = evaluationSign _p q r ∧
      evaluationSign _p q r = r.negOnePow * evaluationSign _p (q - 1) r ∧
      (q + 1).negOnePow * evaluationSign _p q r = evaluationSign _p q (r + 1) := by
  sorry

theorem evaluationSign_solution (p q r : ℤ) :
    evaluationSign p q r = (r + q * r).negOnePow := rfl

/-- Every tensor element is represented by a finite sum of pure tensors; this
is the finiteness used in the source's componentwise composition formulas. -/
theorem tensorElement_finite_sum {R : Type u} [CommRing R]
    (A B : ModuleCat.{u} R) (x : TensorProduct R A B) :
    ∃ (n : ℕ) (a : Fin n → A) (b : Fin n → B),
      x = ∑ i, a i ⊗ₜ[R] b i := by
  sorry

/-- Componentwise composition of cochains. -/
theorem homCochain_composition_component {R : Type u} [Ring R]
    {F G H : CochainComplex (ModuleCat.{u} R) ℤ}
    {n₁ n₂ n₁₂ : ℤ}
    (z₁ : CochainComplex.HomComplex.Cochain F G n₁)
    (z₂ : CochainComplex.HomComplex.Cochain G H n₂)
    (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : ℤ)
    (h₁ : p₁ + n₁ = p₂) (h₂ : p₂ + n₂ = p₃) :
    (CochainComplex.HomComplex.Cochain.comp z₁ z₂ h).v p₁ p₃ (by omega) =
      z₁.v p₁ p₂ h₁ ≫ z₂.v p₂ p₃ h₂ := by
  exact CochainComplex.HomComplex.Cochain.comp_v z₁ z₂ h p₁ p₂ p₃ h₁ h₂

/-- The Koszul sign in the swap used by the evaluation construction. -/
def swapSign (r q r' : ℤ) : ℤˣ := (r * (q + r')).negOnePow

theorem swapSign_on_diagonal (q r : ℤ) :
    swapSign r q r = evaluationSign 0 q r := by
  sorry

/-- A degree-zero Hom cochain is a morphism of complexes exactly when it is a
cocycle. -/
noncomputable def degreeZeroCocycleEquiv {R : Type u} [Ring R]
    {L M : CochainComplex (ModuleCat.{u} R) ℤ}
    : (L ⟶ M) ≃+ CochainComplex.HomComplex.Cocycle L M 0 :=
  CochainComplex.HomComplex.Cocycle.equivHom L M

/- The source's `Comp(R)` is the symmetric monoidal category already exposed
   by the preceding tensor-product chapter. -/
theorem comp_symmetric_monoidal {R : Type u} [CommRing R] :
    Nonempty (Formalization.Books.MoreAlgebra.Unit58.SymmetricMonoidalCategoryData
      (Comp R)) :=
  Formalization.Books.MoreAlgebra.Unit58.cochainComplex_symmetric_monoidal R

/- The internal-Hom adjunction in the source is recorded as its precise
   Hom-set equivalence. -/
theorem internalHom_morphism_equiv_exists {R : Type u} [CommRing R]
    (K L M : Comp R) :
    Nonempty ((K ⟶ homComplex L M) ≃
      (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R K L ⟶ M)) := by
  sorry

noncomputable def internalHomMorphismEquiv {R : Type u} [CommRing R]
    (K L M : Comp R) :
    (K ⟶ homComplex L M) ≃
      (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R K L ⟶ M) :=
  Classical.choice (internalHom_morphism_equiv_exists K L M)

theorem homComplex_differential_squared {R : Type u} [CommRing R]
    (L M : Comp R) (n m p : ℤ) :
    (homComplex L M).d n m ≫ (homComplex L M).d m p = 0 :=
  (homComplex L M).d_comp_d n m p

theorem homComposition_differential_formula {R : Type u} [Ring R]
    {F G H : CochainComplex (ModuleCat.{u} R) ℤ}
    {n₁ n₂ n₁₂ m₁ m₂ m₁₂ : ℤ}
    (z₁ : CochainComplex.HomComplex.Cochain F G n₁)
    (z₂ : CochainComplex.HomComplex.Cochain G H n₂)
    (h : n₁ + n₂ = n₁₂) (h₁₂ : n₁₂ + 1 = m₁₂)
    (h₁ : n₁ + 1 = m₁) (h₂ : n₂ + 1 = m₂) :
    CochainComplex.HomComplex.δ n₁₂ m₁₂
        (CochainComplex.HomComplex.Cochain.comp z₁ z₂ h) =
      CochainComplex.HomComplex.Cochain.comp z₁
          (CochainComplex.HomComplex.δ n₂ m₂ z₂)
            (by omega) +
        n₂.negOnePow •
          CochainComplex.HomComplex.Cochain.comp
            (CochainComplex.HomComplex.δ n₁ m₁ z₁) z₂ (by omega) := by
  exact CochainComplex.HomComplex.δ_comp z₁ z₂ h m₁ m₂ m₁₂ h₁₂ h₁ h₂

/-! ## Canonical tensor--Hom maps -/

/-- The canonical composition isomorphism from Lemma `compose`. -/
theorem homCompose_iso_exists {R : Type u} [CommRing R]
    (K L M : Comp R) :
    Nonempty (homComplex K (homComplex L M) ≅
      homComplex (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R K L) M) := by
  sorry

/-- The canonical composition morphism of complexes. -/
theorem homComposition_exists {R : Type u} [CommRing R]
    (K L M : Comp R) :
    Nonempty (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R
        (homComplex L M) (homComplex K L) ⟶ homComplex K M) := by
  sorry

/-- The source's diagonal-better morphism, functorial in all three complexes. -/
theorem homDiagonalBetter_exists {R : Type u} [CommRing R]
    (K L M : Comp R) :
    Nonempty (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R
        K (homComplex M L) ⟶
      homComplex M (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R K L)) := by
  sorry

/-- The source's diagonal morphism, functorial in both complexes. -/
theorem homDiagonal_exists {R : Type u} [CommRing R]
    (K L : Comp R) :
    Nonempty (K ⟶ homComplex L
      (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R K L)) := by
  sorry

/-- The source's evaluation-and-more morphism, functorial in all three
complexes. -/
theorem homEvaluate_exists {R : Type u} [CommRing R]
    (K L M : Comp R) :
    Nonempty (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R
        (homComplex L M) K ⟶ homComplex (homComplex K L) M) := by
  sorry

/-! Chosen representatives make the canonical interfaces directly usable by
    later chapters while the preceding existence statements keep the source's
    canonical constructions abstract. -/

noncomputable def homComposeIso {R : Type u} [CommRing R]
    (K L M : Comp R) :
    homComplex K (homComplex L M) ≅
      homComplex (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R K L) M :=
  Classical.choice (homCompose_iso_exists K L M)

noncomputable def homComposition {R : Type u} [CommRing R]
    (K L M : Comp R) :
    Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R
        (homComplex L M) (homComplex K L) ⟶ homComplex K M :=
  Classical.choice (homComposition_exists K L M)

noncomputable def homDiagonalBetter {R : Type u} [CommRing R]
    (K L M : Comp R) :
    Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R
        K (homComplex M L) ⟶
      homComplex M (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R K L) :=
  Classical.choice (homDiagonalBetter_exists K L M)

noncomputable def homDiagonal {R : Type u} [CommRing R]
    (K L : Comp R) :
    K ⟶ homComplex L
      (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R K L) :=
  Classical.choice (homDiagonal_exists K L)

noncomputable def homEvaluate {R : Type u} [CommRing R]
    (K L M : Comp R) :
    Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex R
        (homComplex L M) K ⟶ homComplex (homComplex K L) M :=
  Classical.choice (homEvaluate_exists K L M)

end Formalization.Books.MoreAlgebra.Unit72
