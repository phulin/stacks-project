import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Formalization.Books.Derived.Unit04.ElementaryResults
import Formalization.Books.Derived.Unit11.DerivedCategories

/-!
# Derived Categories, Chapter 19: projective resolutions

The object-level resolution is Mathlib's canonical
`CategoryTheory.ProjectiveResolution`.  The source also uses resolutions of
arbitrary integer-indexed cochain complexes, so this file records the
source-facing bounded-above, termwise-projective package for those complexes.
The comparison and lifting results are stated with the canonical homotopy and
derived-category morphisms; their proofs are deferred to the prove stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u

namespace Formalization.Books.Derived.Unit19

/-! ## Projective resolutions -/

/- The source's object-level notion is Mathlib's canonical projective
  resolution.  Mathlib uses a nonnegative chain complex and an augmentation
  to the degree-zero stalk; this is the dual indexing convention for the
  source's integer-indexed cochain presentation. -/
abbrev ObjectProjectiveResolution
    {A : Type u} [Category.{v} A] [Abelian A] (X : A) :=
  CategoryTheory.ProjectiveResolution X

/-- A bounded-above, termwise-projective complex equipped with a
quasi-isomorphism to `K`. -/
structure ComplexProjectiveResolution
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : BookComplex A) where
  /-- The complex used as the resolution. -/
  source : BookComplex A
  /-- The resolution map. -/
  map : source ⟶ K
  /-- The resolution is bounded above. -/
  boundedAbove : IsBoundedAbove source
  /-- Every term of the resolution is projective. -/
  termwiseProjective : ∀ n : ℤ, Projective (source.X n)
  /-- The resolution map is a quasi-isomorphism. -/
  quasiIso : QuasiIso map

/-- The source-facing predicate for a specified complex and resolution map. -/
def IsComplexProjectiveResolution
    {A : Type u} [Category.{v} A] [Abelian A]
    (K P : BookComplex A) (f : P ⟶ K) : Prop :=
  IsBoundedAbove P ∧
    (∀ n : ℤ, Projective (P.X n)) ∧ QuasiIso f

/- The four object-level conditions are recorded with the canonical stalk
  complex.  The degree-zero homology map is the categorical form of the
  induced map from `Coker(d⁻¹)` to the object being resolved. -/
def IsObjectProjectiveResolution
    {A : Type u} [Category.{v} A] [Abelian A]
    (X : A) (P : BookComplex A)
    (f : P ⟶ (CochainComplex.singleFunctor A 0).obj X) : Prop :=
  (∀ n : ℤ, 0 < n → IsZero (P.X n)) ∧
    (∀ n : ℤ, Projective (P.X n)) ∧
      IsIso (HomologicalComplex.homologyMap f 0) ∧
        (∀ n : ℤ, n < 0 → IsZero (P.homology n))

theorem object_projective_resolution_cochain_map_is_quasiIso
    {A : Type u} [Category.{v} A] [Abelian A]
    {X : A} {P : BookComplex A}
    {f : P ⟶ (CochainComplex.singleFunctor A 0).obj X}
    (hP : IsObjectProjectiveResolution X P f) : QuasiIso f := by
  sorry

theorem object_projective_resolution_cochain_exists
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughProjectives A]
    (X : A) :
    ∃ (P : BookComplex A)
      (f : P ⟶ (CochainComplex.singleFunctor A 0).obj X),
      IsObjectProjectiveResolution X P f := by
  sorry

theorem object_projective_resolution_termwise_projective
    {A : Type u} [Category.{v} A] [Abelian A]
    {X : A} (R : ObjectProjectiveResolution X) :
    ∀ n : ℕ, Projective (R.complex.X n) := by
  exact R.projective

theorem object_projective_resolution_quasiIso
    {A : Type u} [Category.{v} A] [Abelian A]
    {X : A} (R : ObjectProjectiveResolution X) : QuasiIso R.π := by
  exact R.quasiIso

theorem object_projective_resolution_augmented_exact
    {A : Type u} [Category.{v} A] [Abelian A]
    {X : A} (R : ObjectProjectiveResolution X) :
    (ShortComplex.mk (R.complex.d 1 0) (R.π.f 0)
      R.complex_d_comp_π_f_zero).Exact := by
  exact R.exact₀

theorem object_projective_resolution_exact_succ
    {A : Type u} [Category.{v} A] [Abelian A]
    {X : A} (R : ObjectProjectiveResolution X) (n : ℕ) :
    (ShortComplex.mk (R.complex.d (n + 2) (n + 1))
      (R.complex.d (n + 1) n)
      (R.complex.d_comp_d (n + 2) (n + 1) n)).Exact := by
  exact R.exact_succ n

theorem object_projective_resolution_exists
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughProjectives A]
    (X : A) : Nonempty (ObjectProjectiveResolution X) := by
  sorry

/-! ## Boundedness and existence -/

theorem cohomology_bounded_above_of_projective_resolution
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : BookComplex A} (R : ComplexProjectiveResolution K) :
    ∃ a : ℤ, ∀ n : ℤ, a < n → IsZero (K.homology n) := by
  sorry

theorem projective_resolution_of_cohomology_bounded_above
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : BookComplex A}
    (hK : ∃ a : ℤ, ∀ n : ℤ, a < n → IsZero (K.homology n)) :
    ∃ (L : BookComplex A) (f : L ⟶ K),
      QuasiIso f ∧ IsBoundedAbove L := by
  sorry

theorem complex_projective_resolution_exists
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughProjectives A]
    {K : BookComplex A}
    (hK : ∃ a : ℤ, ∀ n : ℤ, a < n → IsZero (K.homology n)) :
    Nonempty (ComplexProjectiveResolution K) := by
  sorry

theorem complex_projective_resolution_exists_with_epi
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughProjectives A]
    (K : BookComplex A) (a : ℤ) (hK : K.IsStrictlyLE a) :
    ∃ R : ComplexProjectiveResolution K,
      R.source.IsStrictlyLE a ∧
        ∀ n : ℤ, Epi (R.map.f n) := by
  sorry

/-! ## Acyclic complexes -/

theorem projective_to_acyclic_is_homotopic_zero
    {A : Type u} [Category.{v} A] [Abelian A]
    {K P : BookComplex A} (hK : K.Acyclic)
    (hP : IsBoundedAbove P)
    (hPproj : ∀ n : ℤ, Projective (P.X n)) (f : P ⟶ K) :
    Nonempty (Homotopy f 0) := by
  sorry

/-! ## Quasi-isomorphisms and lifting -/

theorem quasiIso_postcomposition_from_projective_bijective
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L P : BookComplex A} (α : K ⟶ L) (hα : QuasiIso α)
    (hP : IsBoundedAbove P)
    (hPproj : ∀ n : ℤ, Projective (P.X n)) :
    Function.Bijective
      (fun (β :
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P ⟶
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =>
        β ≫ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map α) := by
  sorry

theorem projective_resolution_lift_up_to_homotopy
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L P : BookComplex A} (α : L ⟶ K) (γ : P ⟶ K)
    (hα : QuasiIso α) (hP : IsBoundedAbove P)
    (hPproj : ∀ n : ℤ, Projective (P.X n)) :
    ∃ β : P ⟶ L, Nonempty (Homotopy (β ≫ α) γ) := by
  sorry

theorem projective_resolution_lift_of_degreewise_epi
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L P : BookComplex A} (α : L ⟶ K) (γ : P ⟶ K)
    (hα : QuasiIso α) (hP : IsBoundedAbove P)
    (hPproj : ∀ n : ℤ, Projective (P.X n))
    (hepi : ∀ n : ℤ, Epi (α.f n)) :
    ∃ β : P ⟶ L, β ≫ α = γ := by
  sorry

theorem projective_resolution_lift_unique_up_to_homotopy
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L P : BookComplex A} (α : L ⟶ K) (γ : P ⟶ K)
    (hα : QuasiIso α) (hP : IsBoundedAbove P)
    (hPproj : ∀ n : ℤ, Projective (P.X n))
    (β₁ β₂ : P ⟶ L)
    (hβ₁ : Nonempty (Homotopy (β₁ ≫ α) γ))
    (hβ₂ : Nonempty (Homotopy (β₂ ≫ α) γ)) :
    Nonempty (Homotopy β₁ β₂) := by
  sorry

/-! ## Morphisms from a projective complex -/

theorem morphisms_from_projective_complex_bijective
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : BookComplex A) (L : BookHomotopyCategory A)
    (hP : IsBoundedAbove P)
    (hPproj : ∀ n : ℤ, Projective (P.X n)) :
    Function.Bijective
      ((DerivedCategory.Qh (C := A)).map :
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P ⟶ L) → _) := by
  sorry

/-! ## Short exact sequences and projective resolutions -/

/- The diagram in the source is recorded by the bottom short exact row,
  its two commutative squares, and three `ComplexProjectiveResolution`
  witnesses.  The source writes `Comp⁺` here, but projective resolutions are
  bounded above, so the mathematically consistent dual is `Comp⁻`. -/
def ProjectiveResolutionShortExactData
    {A : Type u} [Category.{v} A] [Abelian A]
    (S : ShortComplex (CompMinus A))
    (P₁ P₂ P₃ : CompMinus A)
    (a : P₁ ⟶ S.X₁) (b : P₂ ⟶ S.X₂) (c : P₃ ⟶ S.X₃) : Prop :=
  IsComplexProjectiveResolution S.X₁.obj P₁.obj a.hom ∧
    IsComplexProjectiveResolution S.X₂.obj P₂.obj b.hom ∧
      IsComplexProjectiveResolution S.X₃.obj P₃.obj c.hom ∧
        ∃ (u : P₁ ⟶ P₂) (v : P₂ ⟶ P₃) (h : u ≫ v = 0),
          (ShortComplex.mk u v h).ShortExact ∧
            u ≫ b = a ≫ S.f ∧ v ≫ c = b ≫ S.g

theorem projective_resolution_short_exact
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughProjectives A]
    (S : ShortComplex (CompMinus A)) (hS : S.ShortExact) :
    ∃ (P₁ P₂ P₃ : CompMinus A)
      (a : P₁ ⟶ S.X₁) (b : P₂ ⟶ S.X₂) (c : P₃ ⟶ S.X₃),
      ProjectiveResolutionShortExactData S P₁ P₂ P₃ a b c := by
  sorry

theorem projective_resolution_short_exact_with_right
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughProjectives A]
    (S : ShortComplex (CompMinus A)) (hS : S.ShortExact)
    (P₃ : CompMinus A) (c : P₃ ⟶ S.X₃)
    (hc : IsComplexProjectiveResolution S.X₃.obj P₃.obj c.hom) :
    ∃ (P₁ P₂ : CompMinus A)
      (a : P₁ ⟶ S.X₁) (b : P₂ ⟶ S.X₂),
      ProjectiveResolutionShortExactData S P₁ P₂ P₃ a b c := by
  sorry

/-! ## Precise vanishing -/

theorem precise_vanishing_projective
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {P K : BookComplex A} (n : ℤ)
    (hP : IsBounded P)
    (hPproj : ∀ i : ℤ, Projective (P.X i))
    (hPzero : ∀ i : ℤ, i < n → IsZero (P.X i))
    (hK : ∀ i : ℤ, n ≤ i → IsZero (K.homology i)) :
    Formalization.Books.Derived.Unit04.HomIsZero
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ∧
      Function.Bijective
        ((DerivedCategory.Qh (C := A)).map :
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P ⟶
              (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) → _) ∧
      Formalization.Books.Derived.Unit04.HomIsZero
        ((DerivedCategory.Q (C := A)).obj P)
        ((DerivedCategory.Q (C := A)).obj K) := by
  sorry

/-! ## The lifting lemma -/

theorem projective_resolution_lift_map
    {A : Type u} [Category.{v} A] [Abelian A]
    {E L P : BookComplex A} (β : P ⟶ L) (α : E ⟶ L) (n : ℤ)
    (hP : IsBounded P)
    (hPproj : ∀ i : ℤ, Projective (P.X i))
    (hPzero : ∀ i : ℤ, i < n → IsZero (P.X i))
    (hα : (∀ i : ℤ, n < i →
        IsIso (HomologicalComplex.homologyMap α i)) ∧
      Epi (HomologicalComplex.homologyMap α n)) :
    ∃ γ : P ⟶ E, Nonempty (Homotopy (γ ≫ α) β) := by
  sorry

end Formalization.Books.Derived.Unit19
