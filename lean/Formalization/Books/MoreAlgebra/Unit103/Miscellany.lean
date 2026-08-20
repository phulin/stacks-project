import Formalization.Books.MoreAlgebra.Unit101.SystemsOfModules
import Formalization.Books.MoreAlgebra.Unit102.SystemsOfModulesBis
import Formalization.Books.MoreAlgebra.Unit69.ProjectiveDimension
import Formalization.Books.MoreAlgebra.Unit60.DerivedBaseChange
import Formalization.Books.Categories.Unit22.EssentiallyConstantSystems
import Formalization.Books.Derived.Unit34.DerivedLimits
import Formalization.Books.MoreAlgebra.Unit56.DerivedCategoriesOfModules
import Formalization.Books.Algebra.Unit75.TorGroups
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.SetTheory.Cardinal.ToNat

/-!
# More on Algebra, Chapter 103: Miscellany

This file records the seven precise lemmas in the source section.  Existing
module quotient systems, derived Ext, Tor, derived limits, and categorical
projective dimension are reused throughout.  The long cardinal argument is
represented by source-facing data structures so that its maps, subcomplexes,
cohomological conditions, and cardinal estimate remain available to users.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit21
open Formalization.Books.Categories.Unit22
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit27
open Formalization.Books.Derived.Unit34
open Formalization.Books.MoreAlgebra.Unit56
open Formalization.Books.MoreAlgebra.Unit60
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit69
open Formalization.Books.MoreAlgebra.Unit74
open Formalization.Books.MoreAlgebra.Unit92
open Formalization.Books.MoreAlgebra.Unit101
open Formalization.Books.MoreAlgebra.Unit102
open Formalization.Books.Algebra.Unit75
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w u v u'

namespace Formalization.Books.MoreAlgebra.Unit103

abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

abbrev Comp (R : Type u) [CommRing R] := Unit74.Comp R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] := Unit74.D R

/-! ## 103.1. Ext and Tor stabilization -/

/- The source's “essentially constant with value X” includes the limiting
value.  The cone is required to be a limit cone, while the earlier Categories
22 predicate supplies the pro-essential constancy condition. -/
def EssentiallyConstantWithLimitValue
    {C : Type u'} [Category.{v} C] (F : ℕᵒᵖ ⥤ C) (X : C) : Prop :=
  ∃ c : Cone F,
    IsEssentiallyConstantPro F c ∧ Nonempty (IsLimit c) ∧ Nonempty (c.pt ≅ X)

/- The Ext system in the first lemma is the quotient system `M/I^n M`,
followed by the canonical derived Ext functor in the second variable. -/
theorem derivedExtMap_id
    {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (K L : D A) (i : ℤ) :
    Unit102.derivedExtMap i (𝟙 K) (𝟙 L) =
      𝟙 (Unit102.derivedExt K L i) := by
  sorry

theorem derivedExtMap_comp
    {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (K X Y Z : D A) (i : ℤ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Unit102.derivedExtMap i (𝟙 K) (f ≫ g) =
      Unit102.derivedExtMap i (𝟙 K) f ≫
        Unit102.derivedExtMap i (𝟙 K) g := by
  sorry

noncomputable def derivedExtFunctor
    {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (K : D A) (i : ℤ) : D A ⥤ Mod A where
  obj L := Unit102.derivedExt K L i
  map g := Unit102.derivedExtMap i (𝟙 K) g
  map_id := by
    intro X
    exact derivedExtMap_id K X i
  map_comp := by
    intro X Y Z f g
    exact derivedExtMap_comp K X Y Z i f g

noncomputable def derivedExtQuotientSystem
    {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (K : D A)
    (M : Mod A) (i : ℤ) : ℕᵒᵖ ⥤ Mod A :=
  Unit101.idealQuotientSystem I M ⋙ moduleInDerivedFunctor ⋙ derivedExtFunctor K i

theorem lemma_ext_annihilated_into
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (K : D A) (a : ℤ)
    (hK : IsPseudoCoherent A K)
    (hExt : ∀ (M : Mod A), Module.Finite A (M : Type u) →
      ∀ i : ℤ, a ≤ i →
        annihilatedByPower I (derivedExt K (moduleInDerived A M) i)) :
    ∀ (i : ℤ), a ≤ i → ∀ (M : Mod A),
      Module.Finite A (M : Type u) →
        EssentiallyConstantWithLimitValue
          (derivedExtQuotientSystem I K M i)
          (derivedExt K (moduleInDerived A M) i) := by
  sorry

theorem lemma_tor_annihilated
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M N : Mod A)
    (hM : Module.Finite A (M : Type u))
    (hN : annihilatedByIdealPower I 1 N) :
    ∃ n : ℕ, 0 < n ∧ ∀ p : ℕ,
      torMapFirst (N := N) (Unit102.idealPowerToAmbient I n M) p = 0 := by
  sorry

/-! ## 103.2. Derived inverse limits and tensor products -/

abbrev ModuleSystem (R : Type u) [CommRing R] := ℕᵒᵖ ⥤ Mod R

noncomputable abbrev moduleDerivedSystem
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : ModuleSystem R) :
    DerivedInverseSystem (D R) :=
  M ⋙ moduleInDerivedFunctor

noncomputable def moduleRlim
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M : ModuleSystem R) : D R :=
  derivedLimit (moduleDerivedSystem M) (exists_isDerivedLimit _)

noncomputable abbrev tensorModuleSystem
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (M : ModuleSystem R) :
    DerivedInverseSystem (D R) :=
  Unit92.derivedTensorInverseSystem K (moduleDerivedSystem M)

noncomputable def tensorModuleRlim
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (M : ModuleSystem R) : D R :=
  derivedLimit (tensorModuleSystem K M) (exists_isDerivedLimit _)

theorem lemma_pseudo_coherent_tensor_limit
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (M : ModuleSystem R)
    (hK : IsPseudoCoherent R K) :
    Nonempty (tensorModuleRlim K M ≅ Unit74.derivedTensor K (moduleRlim M)) := by
  sorry

/-! ## 103.3. Projective-dimension additivity -/

noncomputable def quotientModuleAsRModule
    {R : Type u} [CommRing R] (I : Ideal R) : Mod R :=
  ringMapModule (Ideal.Quotient.mk I)

noncomputable def restrictQuotientModule
    {R : Type u} [CommRing R] (I : Ideal R) (E : Mod (R ⧸ I)) : Mod R :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj E

theorem lemma_additivity_of_pd
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (E : Mod (R ⧸ I))
    (hE0 : Nontrivial (E : Type u))
    (hEfinite : Module.Finite (R ⧸ I) (E : Type u))
    (hquotient : ∃ n : ℕ,
      CategoryTheory.HasProjectiveDimensionLE
        (quotientModuleAsRModule I) n)
    (hE : ∃ n : ℕ,
      CategoryTheory.HasProjectiveDimensionLE E n) :
    (∃ n : ℕ,
      CategoryTheory.HasProjectiveDimensionLE (restrictQuotientModule I E) n) ∧
      CategoryTheory.projectiveDimension (restrictQuotientModule I E) =
        CategoryTheory.projectiveDimension (quotientModuleAsRModule I) +
          CategoryTheory.projectiveDimension E := by
  sorry

/-! ## 103.4. The cardinal-bounded enlargement lemma -/

/- A subcomplex is represented by a complex with a degreewise monomorphic
inclusion.  This avoids introducing a second complex implementation. -/
structure ComplexSubcomplex {R : Type u} [CommRing R] (K : Comp R) where
  complex : Comp R
  inclusion : complex ⟶ K
  mono : ∀ i : ℤ, Mono (inclusion.f i)

noncomputable def restrictScalarsComplexMap
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {K L : Comp B} (g : K ⟶ L) :
    restrictScalarsComplex f K ⟶ restrictScalarsComplex f L :=
  ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map g

noncomputable abbrev baseChangedDerivedComplex
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (f : A →+* B) (K : Comp A) : D B :=
  (Unit60.derivedBaseChangeFunctor f).obj ((Unit60.derivedQuotient A).obj K)

noncomputable def baseChangedDerivedMap
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (f : A →+* B) {K L : Comp A} (g : K ⟶ L) :
    baseChangedDerivedComplex f K ⟶ baseChangedDerivedComplex f L :=
  (Unit60.derivedBaseChangeFunctor f).map ((Unit60.derivedQuotient A).map g)

noncomputable def derivedComplexMap
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] {K L : Comp R} (g : K ⟶ L) :
    (Unit74.derivedQuotient R).obj K ⟶ (Unit74.derivedQuotient R).obj L :=
  (Unit74.derivedQuotient R).map g

structure EnlargeDerivedMap
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (f : A →+* B) (K : Comp A) (L : Comp B) where
  map : baseChangedDerivedComplex f K ⟶ (Unit60.derivedQuotient B).obj L

def cohomologyKernelMapsToZero
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] {X Y Z : D R}
    (u : X ⟶ Y) (v : X ⟶ Z) : Prop :=
  ∀ i : ℤ, ∀ x : ((derivedCohomologyFunctor (Mod R) i).obj X : Type u),
    ((derivedCohomologyFunctor (Mod R) i).map v).hom x = 0 →
      ((derivedCohomologyFunctor (Mod R) i).map u).hom x = 0

def cohomologyImageContained
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] {X Y Z : D R}
    (u : X ⟶ Y) (v : Z ⟶ Y) : Prop :=
  ∀ i : ℤ, ∀ x : ((derivedCohomologyFunctor (Mod R) i).obj X : Type u),
    ∃ y : ((derivedCohomologyFunctor (Mod R) i).obj Z : Type u),
      ((derivedCohomologyFunctor (Mod R) i).map u).hom x =
        ((derivedCohomologyFunctor (Mod R) i).map v).hom y

structure EnlargeInput
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (f : A →+* B) where
  M : Comp A
  N : Comp B
  a : M ⟶ restrictScalarsComplex f N
  comparison : EnlargeDerivedMap f M N
  comparison_isIso : IsIso comparison.map
  M₁ : ComplexSubcomplex M
  N₁ : ComplexSubcomplex N
  a₁ : EnlargeDerivedMap f M₁.complex N₁.complex
  subcomplex_map : ∃ b : M₁.complex ⟶ restrictScalarsComplex f N₁.complex,
    b ≫ restrictScalarsComplexMap f N₁.inclusion = M₁.inclusion ≫ a

def enlargeCardinal
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Cardinal.{u} :=
  let _ := f
  max (max (Cardinal.mk A) (Cardinal.mk B)) Cardinal.aleph0

def pairedComplexCardinal
    {A B : Type u} [CommRing A] [CommRing B]
    (K : Comp A) (L : Comp B) : Cardinal.{u} :=
  Cardinal.mk (Sum (Σ i : ℤ, (K.X i : Type u))
    (Σ i : ℤ, (L.X i : Type u)))

structure EnlargeConclusion
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    {f : A →+* B} (X : EnlargeInput f) where
  M₂ : ComplexSubcomplex X.M
  N₂ : ComplexSubcomplex X.N
  M₁_to_M₂ : X.M₁.complex ⟶ M₂.complex
  M₁_to_M₂_factor : M₁_to_M₂ ≫ M₂.inclusion = X.M₁.inclusion
  N₁_to_N₂ : X.N₁.complex ⟶ N₂.complex
  N₁_to_N₂_factor : N₁_to_N₂ ≫ N₂.inclusion = X.N₁.inclusion
  a₂ : EnlargeDerivedMap f M₂.complex N₂.complex
  a₂_complex_map : ∃ b : M₂.complex ⟶ restrictScalarsComplex f N₂.complex,
    b ≫ restrictScalarsComplexMap f N₂.inclusion =
      M₂.inclusion ≫ X.a
  property_one : cohomologyKernelMapsToZero
    (baseChangedDerivedMap f M₁_to_M₂) X.a₁.map
  property_two : cohomologyImageContained
    (derivedComplexMap N₁_to_N₂) a₂.map
  cardinal_bound : pairedComplexCardinal M₂.complex N₂.complex ≤
    max (enlargeCardinal f) (pairedComplexCardinal X.M₁.complex X.N₁.complex)

theorem lemma_enlarge
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (Mod A)] [HasDerivedCategory.{w} (Mod B)]
    (f : A →+* B) (X : EnlargeInput f) :
    Nonempty (EnlargeConclusion X) := by
  sorry

/-! ## 103.5. Principal localization -/

noncomputable def localizedModuleAsRModule
    {R : Type u} [CommRing R] (f : R) (M : Mod R) : Mod R :=
  ModuleCat.of R (LocalizedModule (Submonoid.powers f) (M : Type u))

def IsDerivedConeOf
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (M C : D R) (f : M ⟶ M) : Prop :=
  ∃ T : Triangle (D R),
    ∃ h₁ : T.obj₁ = M, ∃ h₂ : T.obj₂ = M,
      T.obj₃ = C ∧
      T.mor₁ = eqToHom h₁ ≫ f ≫ eqToHom h₂.symm ∧
        T ∈ distTriang (D R)

theorem lemma_f_bounded
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (f : R) (M C : D R)
    (hf : M ⟶ M) (hC : IsDerivedConeOf M C hf)
    (hlocal : ∀ i : ℤ, i < 0 →
      IsZero (localizedModuleAsRModule f
        ((derivedCohomologyFunctor (Mod R) i).obj M)))
    (hcone : ∀ i : ℤ, i < -1 →
      IsZero ((derivedCohomologyFunctor (Mod R) i).obj C)) :
    ∀ i : ℤ, i < 0 →
      IsZero ((derivedCohomologyFunctor (Mod R) i).obj M) := by
  sorry

def IsFlatModulePlacedAfterBaseChange
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (Mod S)]
    (g : R →+* S) (M : D R) : Prop :=
  ∃ N : Mod S, Module.Flat S (N : Type u) ∧
    Nonempty ((Unit60.derivedBaseChangeFunctor g).obj M ≅ moduleInDerived S N)

theorem lemma_f_flat
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (f : R) (M : D R)
    [HasDerivedCategory.{w} (Mod (Localization.Away f))]
    [HasDerivedCategory.{w} (Mod (R ⧸ Ideal.span ({f} : Set R)))]
    (hpositive : ∀ i : ℤ, 0 < i →
      IsZero ((derivedCohomologyFunctor (Mod R) i).obj M))
    (hlocal : IsFlatModulePlacedAfterBaseChange
      (algebraMap R (Localization.Away f)) M)
    (hclosed : IsFlatModulePlacedAfterBaseChange
      (Ideal.Quotient.mk (Ideal.span ({f} : Set R))) M) :
    ∃ N : Mod R, Module.Flat R (N : Type u) ∧
      Nonempty (moduleInDerived R N ≅ M) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit103
