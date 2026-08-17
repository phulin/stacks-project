import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Formalization.Books.Derived.Unit04.ElementaryResults
import Formalization.Books.Derived.Unit11.DerivedCategories

/-!
# Derived Categories, Chapter 18: injective resolutions

The object-level resolution is Mathlib's canonical `InjectiveResolution`.
The source also uses resolutions of arbitrary complexes, so this file adds the
small source-facing package for a bounded-below termwise injective complex
quasi-isomorphic to a given complex.  The comparison statements use
Mathlib's `IsKInjective` and derived-category localization APIs.
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

namespace Formalization.Books.Derived.Unit18

/-! ## The two notions of injective resolution -/

/- The source's object-level notion is already Mathlib's canonical
  `CategoryTheory.InjectiveResolution`.  Its `cochainComplex` and `ι'`
  provide the source's integer-indexed complex and quasi-isomorphism. -/
abbrev ObjectInjectiveResolution
    {A : Type u} [Category.{v} A] [Abelian A] (X : A) :=
  CategoryTheory.InjectiveResolution X

/-- A bounded-below termwise injective complex equipped with a
quasi-isomorphism from `K`. -/
structure ComplexInjectiveResolution
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : BookComplex A) where
  /-- The complex used as the resolution. -/
  target : BookComplex A
  /-- The resolution map. -/
  map : K ⟶ target
  /-- The target is bounded below. -/
  boundedBelow : IsBoundedBelow target
  /-- Every term of the target is injective. -/
  termwiseInjective : ∀ n : ℤ, Injective (target.X n)
  /-- The resolution map is a quasi-isomorphism. -/
  quasiIso : QuasiIso map

/- The canonical object resolution also gives the corresponding resolution of
  the stalk complex in degree zero. -/
noncomputable def object_injective_resolution_as_complex
    {A : Type u} [Category.{v} A] [Abelian A] {X : A}
    (R : ObjectInjectiveResolution X) :
    ComplexInjectiveResolution ((CochainComplex.singleFunctor A 0).obj X) where
  target := R.cochainComplex
  map := R.ι'
  boundedBelow := ⟨0, inferInstance⟩
  termwiseInjective := fun _ => inferInstance
  quasiIso := inferInstance

/-- The source-facing predicate for a specified target and resolution map. -/
def IsComplexInjectiveResolution
    {A : Type u} [Category.{v} A] [Abelian A]
    (K I : BookComplex A) (f : K ⟶ I) : Prop :=
  IsBoundedBelow I ∧
    (∀ n : ℤ, Injective (I.X n)) ∧ QuasiIso f

/- The source's zero-degree kernel condition is exactly the canonical
  `isLimitKernelFork` field/API, and the positive cohomology vanishing is the
  corresponding consequence of the canonical quasi-isomorphism. -/
noncomputable def object_injective_resolution_zero_is_kernel
    {A : Type u} [Category.{v} A] [Abelian A] {X : A}
    (R : ObjectInjectiveResolution X) :
    IsLimit R.kernelFork :=
  R.isLimitKernelFork

theorem object_injective_resolution_cochain_properties
    {A : Type u} [Category.{v} A] [Abelian A] {X : A}
    (R : ObjectInjectiveResolution X) :
    IsBoundedBelow R.cochainComplex ∧
      (∀ n : ℤ, Injective (R.cochainComplex.X n)) ∧
        QuasiIso R.ι' := by
  exact ⟨⟨0, inferInstance⟩, (fun _ => inferInstance), inferInstance⟩

theorem object_injective_resolution_positive_cohomology_zero
    {A : Type u} [Category.{v} A] [Abelian A] {X : A}
    (R : ObjectInjectiveResolution X) :
    ∀ n : ℤ, 0 < n → IsZero (R.cochainComplex.homology n) := by
  sorry

/- The construction below is Mathlib's actual enough-injectives construction,
  rather than a second resolution construction. -/
noncomputable def canonical_object_injective_resolution
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (X : A) : ObjectInjectiveResolution X :=
  CategoryTheory.InjectiveResolution.of X

theorem object_injective_resolution_exists
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (X : A) : Nonempty (ObjectInjectiveResolution X) :=
  ⟨canonical_object_injective_resolution X⟩

/-! ## Boundedness and existence -/

theorem cohomology_bounded_below_of_injective_resolution
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : BookComplex A} (R : ComplexInjectiveResolution K) :
    ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.homology n) := by
  sorry

theorem injective_resolution_of_cohomology_bounded_below
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : BookComplex A}
    (hK : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    ∃ (L : BookComplex A) (f : K ⟶ L),
      QuasiIso f ∧ IsBoundedBelow L := by
  sorry

theorem complex_injective_resolution_exists
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {K : BookComplex A}
    (hK : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    Nonempty (ComplexInjectiveResolution K) := by
  sorry

theorem complex_injective_resolution_exists_with_mono
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (K : BookComplex A) (a : ℤ) (hK : K.IsStrictlyGE a) :
    ∃ R : ComplexInjectiveResolution K,
      R.target.IsStrictlyGE a ∧
        ∀ n : ℤ, Mono (R.map.f n) := by
  sorry

/-! ## Acyclic complexes and K-injective complexes -/

theorem isKInjective_of_bounded_below_termwise_injective
    {A : Type u} [Category.{v} A] [Abelian A]
    (I : BookComplex A) (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n)) :
    I.IsKInjective := by
  obtain ⟨a, ha⟩ := hI
  let _ : I.IsStrictlyGE a := ha
  let _ : ∀ n : ℤ, Injective (I.X n) := hIinj
  exact CochainComplex.isKInjective_of_injective I a

theorem acyclic_to_injective_is_homotopic_zero
    {A : Type u} [Category.{v} A] [Abelian A]
    {K I : BookComplex A} (hK : K.Acyclic)
    (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n)) (f : K ⟶ I) :
    Nonempty (Homotopy f 0) := by
  let _ : I.IsKInjective :=
    isKInjective_of_bounded_below_termwise_injective I hI hIinj
  exact CochainComplex.IsKInjective.nonempty_homotopy_zero f hK

/-! ## The cone remark -/

theorem quasiIso_mapping_cone_is_acyclic
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L : BookComplex A} (f : K ⟶ L) (hf : QuasiIso f) :
    (CochainComplex.mappingCone f).Acyclic := by
  sorry

theorem mapping_cone_triangle_distinguished
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L : BookComplex A} (f : K ⟶ L) :
    CochainComplex.mappingCone.triangleh f ∈
      distTriang (BookHomotopyCategory A) :=
  HomotopyCategory.mappingCone_triangleh_distinguished f

/- The exact Hom sequence in the source remark is the standard co-special
  property of a distinguished triangle; the two outer vanishings are supplied
  by `acyclic_to_injective_is_homotopic_zero`. -/
theorem mapping_cone_triangle_coSpecial
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L : BookComplex A} (f : K ⟶ L) :
    Formalization.Books.Derived.Unit04.CoSpecialTriangle
      (CochainComplex.mappingCone.triangleh f) := by
  exact Formalization.Books.Derived.Unit04.distinguished_triangle_coSpecial _
    (mapping_cone_triangle_distinguished f)

/- The conclusion of the cone argument is the bijectivity of precomposition
  with a quasi-isomorphism on homotopy classes into a bounded-below injective
  complex. -/
theorem quasiIso_precomposition_to_injective_bijective
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L I : BookComplex A} (α : K ⟶ L) (hα : QuasiIso α)
    (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n)) :
    Function.Bijective
      (fun (β :
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L ⟶
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) =>
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map α ≫ β) := by
  sorry

/- The image/intersection identity used in the degreewise-monomorphism part
  of the lifting lemma is recorded with Mathlib's canonical subobject images. -/
theorem quasiIso_degreewise_mono_image_intersection
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L : BookComplex A} (α : K ⟶ L) (n : ℤ)
    (hα : QuasiIso α) (hmono : ∀ n : ℤ, Mono (α.f n)) :
    imageSubobject (K.d (n - 1) n ≫ α.f n) =
      imageSubobject (α.f n) ⊓ imageSubobject (L.d (n - 1) n) := by
  sorry

/-! ## Lifting and uniqueness -/

theorem injective_resolution_lift_up_to_homotopy
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L I : BookComplex A} (α : K ⟶ L) (γ : K ⟶ I)
    (hα : QuasiIso α) (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n)) :
    ∃ β : L ⟶ I, Nonempty (Homotopy (α ≫ β) γ) := by
  sorry

theorem injective_resolution_lift_of_degreewise_mono
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L I : BookComplex A} (α : K ⟶ L) (γ : K ⟶ I)
    (hα : QuasiIso α) (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n))
    (hmono : ∀ n : ℤ, Mono (α.f n)) :
    ∃ β : L ⟶ I, α ≫ β = γ := by
  sorry

theorem injective_resolution_lift_unique_up_to_homotopy
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L I : BookComplex A} (α : K ⟶ L) (γ : K ⟶ I)
    (hα : QuasiIso α) (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n))
    (β₁ β₂ : L ⟶ I)
    (hβ₁ : Nonempty (Homotopy (α ≫ β₁) γ))
    (hβ₂ : Nonempty (Homotopy (α ≫ β₂) γ)) :
    Nonempty (Homotopy β₁ β₂) := by
  sorry

/-! ## Morphisms into an injective complex -/

theorem morphisms_into_injective_complex_bijective
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (L : BookHomotopyCategory A) (I : BookComplex A)
    (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n)) :
    Function.Bijective
      ((DerivedCategory.Qh (C := A)).map :
        (L ⟶ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) → _) := by
  let _ : I.IsKInjective :=
    isKInjective_of_bounded_below_termwise_injective I hI hIinj
  exact derivedCategory_map_bijective_to_KInjective A L I

/-! ## Short exact sequences and their injective resolutions -/

/- The diagram in the source is recorded by the bottom short exact row,
  its two commutative squares, and three `ComplexInjectiveResolution`
  witnesses. -/
def InjectiveResolutionShortExactData
    {A : Type u} [Category.{v} A] [Abelian A]
    (S : ShortComplex (CompPlus A))
    (I₁ I₂ I₃ : CompPlus A)
    (a : S.X₁ ⟶ I₁) (b : S.X₂ ⟶ I₂) (c : S.X₃ ⟶ I₃) : Prop :=
  IsComplexInjectiveResolution S.X₁.obj I₁.obj a.hom ∧
    IsComplexInjectiveResolution S.X₂.obj I₂.obj b.hom ∧
      IsComplexInjectiveResolution S.X₃.obj I₃.obj c.hom ∧
        ∃ (u : I₁ ⟶ I₂) (v : I₂ ⟶ I₃) (h : u ≫ v = 0),
          (ShortComplex.mk u v h).ShortExact ∧
            a ≫ u = S.f ≫ b ∧ b ≫ v = S.g ≫ c

theorem injective_resolution_short_exact
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (S : ShortComplex (CompPlus A)) (hS : S.ShortExact) :
    ∃ (I₁ I₂ I₃ : CompPlus A)
      (a : S.X₁ ⟶ I₁) (b : S.X₂ ⟶ I₂) (c : S.X₃ ⟶ I₃),
      InjectiveResolutionShortExactData S I₁ I₂ I₃ a b c := by
  sorry

theorem injective_resolution_short_exact_with_left
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (S : ShortComplex (CompPlus A)) (hS : S.ShortExact)
    (I₁ : CompPlus A) (a : S.X₁ ⟶ I₁)
    (ha : IsComplexInjectiveResolution S.X₁.obj I₁.obj a.hom) :
    ∃ (I₂ I₃ : CompPlus A)
      (b : S.X₂ ⟶ I₂) (c : S.X₃ ⟶ I₃),
      InjectiveResolutionShortExactData S I₁ I₂ I₃ a b c := by
  sorry

theorem injective_resolution_short_exact_nonnegative
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (S : ShortComplex (CompPlus A)) (hS : S.ShortExact)
    (hS₀ : S.X₁.obj.IsStrictlyGE 0 ∧
      S.X₂.obj.IsStrictlyGE 0 ∧ S.X₃.obj.IsStrictlyGE 0) :
    ∃ (I₁ I₂ I₃ : CompPlus A)
      (a : S.X₁ ⟶ I₁) (b : S.X₂ ⟶ I₂) (c : S.X₃ ⟶ I₃),
      InjectiveResolutionShortExactData S I₁ I₂ I₃ a b c ∧
        I₁.obj.IsStrictlyGE 0 ∧ I₂.obj.IsStrictlyGE 0 ∧ I₃.obj.IsStrictlyGE 0 := by
  sorry

theorem injective_resolution_short_exact_with_left_nonnegative
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (S : ShortComplex (CompPlus A)) (hS : S.ShortExact)
    (I₁ : CompPlus A) (a : S.X₁ ⟶ I₁)
    (ha : IsComplexInjectiveResolution S.X₁.obj I₁.obj a.hom)
    (hS₀ : S.X₁.obj.IsStrictlyGE 0 ∧
      S.X₂.obj.IsStrictlyGE 0 ∧ S.X₃.obj.IsStrictlyGE 0)
    (hI₁₀ : I₁.obj.IsStrictlyGE 0) :
    ∃ (I₂ I₃ : CompPlus A)
      (b : S.X₂ ⟶ I₂) (c : S.X₃ ⟶ I₃),
      InjectiveResolutionShortExactData S I₁ I₂ I₃ a b c ∧
        I₂.obj.IsStrictlyGE 0 ∧ I₃.obj.IsStrictlyGE 0 := by
  sorry

/- The source's item (4) is literally the placeholder `add more here`; it
  does not specify a mathematical assertion and therefore has no Lean field. -/

end Formalization.Books.Derived.Unit18
