import Formalization.Books.Dga.Unit22.Core
import Formalization.Books.Derived.Unit33.DerivedColimits

/-!
# Differential Graded Algebra, Chapter 23: the canonical delta-functor

The source constructs the connecting morphism from the mapping cone of the
first map in a short exact sequence.  Chapter 22 supplies the DG-module
category, homotopy-category model, localization, and quasi-isomorphism
interfaces.  The small cone and exact-sequence records below expose the
remaining DGA-specific data without duplicating Mathlib's triangle and
derived-colimit interfaces.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Dga.Unit14
open Formalization.Books.Dga.Unit20
open Formalization.Books.Dga.Unit22
open Formalization.Books.Derived.Unit33
open Formalization.Books.Homology.Unit03

universe u v w wk vk

namespace Formalization.Books.Dga.Unit23

variable {R : Type u} {A : ℤ → Type v}
  [CommRing R]
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]

abbrev DGModule
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) :=
  Unit22.DGModule D

abbrev DGMap
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M N : DGModule D) := Unit22.DGMap M N

abbrev DgDerivedCategory
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) :=
  Unit22.DgDerivedCategory H

/-! ## Short exact sequences -/

/- A zero DG map is not needed by the preceding chapters' resolution
   interfaces, but it is part of the short-complex language used by this
   chapter. -/
def dgZeroMap
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M N : DGModule D) : DGMap M N where
  underlying :=
    { app := fun n => 0
      map_action := by
        intro i j m a
        change 0 = N.graded.action (0 : N.graded.component i) a
        rw [N.graded.action_zero_left] }
  commutes_with_differential := by
    intro n m
    change N.differential n 0 = 0
    rw [map_zero]

@[simp] theorem dgZeroMap_underlying_app
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DGModule D} (n : ℤ) :
    (dgZeroMap M N).underlying.app n = 0 := rfl

/- The source works in the abelian category of DG modules.  The current DGA
  API expresses exactness componentwise, so this record is the corresponding
  usable short-exact interface. -/
structure DgShortExact
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (K L M : DGModule D) where
  f : DGMap K L
  g : DGMap L M
  complex : DifferentialGradedModuleHom.comp f g = dgZeroMap K M
  mono : ∀ n : ℤ, Function.Injective (f.underlying.app n)
  epi : ∀ n : ℤ, Function.Surjective (g.underlying.app n)
  exact : Unit20.IsExactPair f g

namespace DgShortExact

variable {D : DifferentialGradedAlgebraData (R := R) (A := A)}
  {K L M : DGModule D}

structure Splitting (S : DgShortExact K L M) where
  retraction : DGMap L K
  sectionMap : DGMap M L
  retraction_f : DifferentialGradedModuleHom.comp S.f retraction =
    DifferentialGradedModuleHom.id K
  section_g : DifferentialGradedModuleHom.comp sectionMap S.g =
    DifferentialGradedModuleHom.id M

def IsSplit (S : DgShortExact K L M) : Prop :=
  Nonempty (Splitting S)

end DgShortExact

/-! A morphism of short exact sequences, used for naturality. -/
structure DgShortExactHom
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K₁ L₁ M₁ K₂ L₂ M₂ : DGModule D}
    (S₁ : DgShortExact K₁ L₁ M₁)
    (S₂ : DgShortExact K₂ L₂ M₂) where
  τ₁ : DGMap K₁ K₂
  τ₂ : DGMap L₁ L₂
  τ₃ : DGMap M₁ M₂
  comm₁₂ : DifferentialGradedModuleHom.comp S₁.f τ₂ =
    DifferentialGradedModuleHom.comp τ₁ S₂.f
  comm₂₃ : DifferentialGradedModuleHom.comp S₁.g τ₃ =
    DifferentialGradedModuleHom.comp τ₂ S₂.g

/-! ## The cone and its localization -/

/- The four maps record the biproduct presentation `L ⊕ K` used in the
   source's description of the cone.  The displayed equations are the part
   of the biproduct API needed here. -/
structure DgBiproduct
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (X Y : DGModule D) where
  object : DGModule D
  inl : DGMap X object
  inr : DGMap Y object
  fst : DGMap object X
  snd : DGMap object Y
  inl_fst : DifferentialGradedModuleHom.comp inl fst =
    DifferentialGradedModuleHom.id X
  inr_snd : DifferentialGradedModuleHom.comp inr snd =
    DifferentialGradedModuleHom.id Y
  inl_snd : DifferentialGradedModuleHom.comp inl snd = dgZeroMap X Y
  inr_fst : DifferentialGradedModuleHom.comp inr fst = dgZeroMap Y X
  universal : ∀ (Z : DGModule D) (f : DGMap X Z) (g : DGMap Y Z),
    ∃! h : DGMap object Z,
      DifferentialGradedModuleHom.comp inl h = f ∧
        DifferentialGradedModuleHom.comp inr h = g

structure DgMappingCone
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K L : DGModule D}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat)
    (a : DGMap K L) where
  sum : DgBiproduct L K
  inclusion : DGMap L sum.object
  inclusion_eq : inclusion = sum.inl
  projection : DGMap sum.object L
  projection_eq : projection = sum.fst
  connecting : H.quotient.obj sum.object ⟶
    (shiftFunctor Kcat (1 : ℤ)).obj (H.quotient.obj K)
  distinguished :
    Triangle.mk (H.quotient.map a) (H.quotient.map inclusion) (-connecting) ∈
      distTriang Kcat

namespace DgMappingCone

abbrev object
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K L : DGModule D}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    {H : DgHomotopyCategoryModel D Kcat}
    {a : DGMap K L} (C : DgMappingCone H a) : DGModule D :=
  C.sum.object

theorem exists_dgMappingCone
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K L : DGModule D}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) (a : DGMap K L) :
    Nonempty (DgMappingCone H a) := by
  sorry

noncomputable def canonical
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K L : DGModule D}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) (a : DGMap K L) :
    DgMappingCone H a :=
  Classical.choice (exists_dgMappingCone H a)

end DgMappingCone

/- The chosen triangulation of the derived localization is the chapter 22
   interface.  These instances make Mathlib's `Triangle` and `distTriang`
   notation available for the chapter's derived-category statements. -/
noncomputable def dgChosenDerivedTriangulatedData
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) :
    DgDerivedCategoryTriangulatedData H :=
  Classical.choice (derived_category_is_triangulated H)

noncomputable instance dgDerivedPreadditive
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) :
  Preadditive (DgDerivedCategory H) :=
  (dgChosenDerivedTriangulatedData H).preadditive

theorem exists_dgDerivedFiniteProducts
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) :
    Nonempty (HasFiniteProducts (DgDerivedCategory H)) := by
  sorry

noncomputable instance dgDerivedHasFiniteProducts
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) :
    HasFiniteProducts (DgDerivedCategory H) :=
  Classical.choice (exists_dgDerivedFiniteProducts H)

noncomputable instance dgDerivedAdditive
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) :
    AdditiveCategory (DgDerivedCategory H) where
  toPreadditive := dgDerivedPreadditive H
  toHasFiniteProducts := dgDerivedHasFiniteProducts H

noncomputable instance dgDerivedHasZeroObject
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) :
    HasZeroObject (DgDerivedCategory H) :=
  (dgChosenDerivedTriangulatedData H).hasZeroObject

noncomputable instance dgDerivedHasShift
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) :
    HasShift (DgDerivedCategory H) ℤ :=
  (dgChosenDerivedTriangulatedData H).hasShift

noncomputable instance dgDerivedShiftAdditive
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) (n : ℤ) :
    (shiftFunctor (DgDerivedCategory H) n).Additive :=
  (dgChosenDerivedTriangulatedData H).shiftAdditive n

noncomputable instance dgDerivedPretriangulated
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) :
    Pretriangulated (DgDerivedCategory H) :=
  (dgChosenDerivedTriangulatedData H).pretriangulated

noncomputable instance dgDerivedTriangulated
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) :
    IsTriangulated (DgDerivedCategory H) :=
  (dgChosenDerivedTriangulatedData H).triangulated

/- The localization-shift comparison is the categorical form of the
   commutation used when the cone triangle is transported to the derived
   category. -/
structure DgDerivedShiftCompatibility
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) where
  shiftIso : ∀ n : ℤ,
    (dgDerivedLocalization H ⋙ shiftFunctor (DgDerivedCategory H) n) ≅
      (shiftFunctor Kcat n ⋙ dgDerivedLocalization H)

theorem exists_dgDerivedShiftCompatibility
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) :
    Nonempty (DgDerivedShiftCompatibility H) := by
  sorry

noncomputable def dgDerivedShiftCompatibility
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) :
    DgDerivedShiftCompatibility H :=
  Classical.choice (exists_dgDerivedShiftCompatibility H)

abbrev dgCanonicalFunctor
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) :
    DifferentialGradedModuleCategory D ⥤ DgDerivedCategory H :=
  H.quotient ⋙ dgDerivedLocalization H

noncomputable def dgLocalizedConnecting
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K L : DGModule D}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat)
    {a : DGMap K L} (C : DgMappingCone H a) :
    (dgCanonicalFunctor H).obj C.object ⟶
      (shiftFunctor (DgDerivedCategory H) (1 : ℤ)).obj
        ((dgCanonicalFunctor H).obj K) :=
  (dgDerivedLocalization H).map C.connecting ≫
    ((dgDerivedShiftCompatibility H).shiftIso (1 : ℤ)).inv.app
      (H.quotient.obj K)

/- The map `q` is definitionally the cone projection to `L` followed by the
   epimorphism `b : L ⟶ M`. -/
def dgConeQ
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K L M : DGModule D}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat)
    (S : DgShortExact K L M) :
    DGMap (DgMappingCone.canonical H S.f).object M :=
  DifferentialGradedModuleHom.comp
    (DgMappingCone.canonical H S.f).projection S.g

theorem dgConeQ_comp_inclusion
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K L M : DGModule D}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) (S : DgShortExact K L M) :
    DifferentialGradedModuleHom.comp
        (DgMappingCone.canonical H S.f).inclusion (dgConeQ H S) = S.g := by
  sorry

/- The kernel calculation and the acyclicity of the identity cone are stated
   separately so both source assertions remain available to later users. -/
structure DgKernelData
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {X Y : DGModule D} (q : DGMap X Y) where
  object : DGModule D
  inclusion : DGMap object X
  vanishes : DifferentialGradedModuleHom.comp inclusion q = dgZeroMap object Y
  lift : ∀ {Z : DGModule D} (u : DGMap Z X),
    DifferentialGradedModuleHom.comp u q = dgZeroMap Z Y →
      ∃ v : DGMap Z object,
        DifferentialGradedModuleHom.comp v inclusion = u
  unique : ∀ {Z : DGModule D} (u : DGMap Z X)
    (hu : DifferentialGradedModuleHom.comp u q = dgZeroMap Z Y)
    (v v' : DGMap Z object),
    DifferentialGradedModuleHom.comp v inclusion = u →
    DifferentialGradedModuleHom.comp v' inclusion = u → v = v'

theorem dgCone_kernel_is_identity_cone
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K L M : DGModule D}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) (S : DgShortExact K L M) :
    ∃ ker : DgKernelData (dgConeQ H S),
      Nonempty (ker.object ≅ (DgMappingCone.canonical H (DifferentialGradedModuleHom.id K)).object) := by
  sorry

theorem dgIdentityCone_acyclic
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) (K : DGModule D) :
    DgAcyclic (DgMappingCone.canonical H (DifferentialGradedModuleHom.id K)).object := by
  sorry

theorem dgConeQ_quasi_isomorphism
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K L M : DGModule D}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) (S : DgShortExact K L M) :
    Unit22.DgQuasiIsomorphism (dgConeQ H S) := by
  sorry

theorem dgConeQ_localized_isIso
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K L M : DGModule D}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) (S : DgShortExact K L M) :
    IsIso ((dgCanonicalFunctor H).map (dgConeQ H S)) := by
  sorry

theorem dgLocalizedConeTriangle_distinguished
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K L M : DGModule D}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) (S : DgShortExact K L M) :
    Triangle.mk ((dgCanonicalFunctor H).map S.f)
      ((dgCanonicalFunctor H).map (DgMappingCone.canonical H S.f).inclusion)
      (-dgLocalizedConnecting H (DgMappingCone.canonical H S.f)) ∈
      distTriang (DgDerivedCategory H) := by
  sorry

/-! ## The canonical delta-functor -/

structure DgHomotopyDeltaFunctorData
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) where
  delta : ∀ {K L M : DGModule D},
    DgShortExact K L M →
      @Quiver.Hom Kcat (inferInstance : Quiver Kcat)
        (H.quotient.obj M)
        ((shiftFunctor Kcat (1 : ℤ)).obj (H.quotient.obj K))
  distinguished : ∀ {K L M : DGModule D} (S : DgShortExact K L M),
    Triangle.mk (H.quotient.map S.f) (H.quotient.map S.g) (delta S) ∈
      distTriang Kcat
  naturality : ∀ {K₁ L₁ M₁ K₂ L₂ M₂ : DGModule D}
    {S₁ : DgShortExact K₁ L₁ M₁} {S₂ : DgShortExact K₂ L₂ M₂}
    (φ : DgShortExactHom S₁ S₂),
    H.quotient.map φ.τ₃ ≫ delta S₂ =
      delta S₁ ≫ (shiftFunctor Kcat (1 : ℤ)).map (H.quotient.map φ.τ₁)

/- The source's “not in general” assertion is made precise by the standard
   nonsplit-extension obstruction. -/
theorem homotopyCanonicalFunctor_not_delta_of_nonsplit
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat)
    {K L M : DGModule D} (S : DgShortExact K L M)
    (hS : ¬ S.IsSplit) :
    ¬ Nonempty (DgHomotopyDeltaFunctorData H) := by
  sorry

noncomputable def dgCanonicalDelta
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K L M : DGModule D}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) (S : DgShortExact K L M) :
    (dgCanonicalFunctor H).obj M ⟶
      (shiftFunctor (DgDerivedCategory H) (1 : ℤ)).obj
        ((dgCanonicalFunctor H).obj K) := by
  let C := DgMappingCone.canonical H S.f
  letI := dgConeQ_localized_isIso H S
  exact -((inv ((dgCanonicalFunctor H).map (dgConeQ H S))) ≫
    dgLocalizedConnecting H C)

noncomputable def dgCanonicalTriangle
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) {K L M : DGModule D}
    (S : DgShortExact K L M) : Triangle (DgDerivedCategory H) :=
  Triangle.mk ((dgCanonicalFunctor H).map S.f) ((dgCanonicalFunctor H).map S.g)
    (dgCanonicalDelta H S)

structure DgCanonicalDeltaFunctorData
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) where
  delta : ∀ {K L M : DGModule D}, DgShortExact K L M →
    @Quiver.Hom (DgDerivedCategory H)
      (inferInstance : Quiver (DgDerivedCategory H))
      ((dgCanonicalFunctor H).obj M)
      ((shiftFunctor (DgDerivedCategory H) (1 : ℤ)).obj
        ((dgCanonicalFunctor H).obj K))
  distinguished : ∀ {K L M : DGModule D} (S : DgShortExact K L M),
    Triangle.mk ((dgCanonicalFunctor H).map S.f)
      ((dgCanonicalFunctor H).map S.g) (delta S) ∈
      distTriang (DgDerivedCategory H)
  naturality : ∀ {K₁ L₁ M₁ K₂ L₂ M₂ : DGModule D}
    {S₁ : DgShortExact K₁ L₁ M₁} {S₂ : DgShortExact K₂ L₂ M₂}
    (φ : DgShortExactHom S₁ S₂),
    (dgCanonicalFunctor H).map φ.τ₃ ≫ delta S₂ =
      delta S₁ ≫ (shiftFunctor (DgDerivedCategory H) (1 : ℤ)).map
        ((dgCanonicalFunctor H).map φ.τ₁)

theorem dgCanonicalFunctor_is_deltaFunctor
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) :
    Nonempty (DgCanonicalDeltaFunctorData H) := by
  sorry

noncomputable def dgCanonicalDeltaFunctor
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) :
    DgCanonicalDeltaFunctorData H :=
  Classical.choice (dgCanonicalFunctor_is_deltaFunctor H)

theorem dgCanonicalTriangle_distinguished
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) {K L M : DGModule D}
    (S : DgShortExact K L M) :
    dgCanonicalTriangle H S ∈ distTriang (DgDerivedCategory H) := by
  sorry

theorem dgCanonicalDelta_naturality
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat)
    {K₁ L₁ M₁ K₂ L₂ M₂ : DGModule D}
    {S₁ : DgShortExact K₁ L₁ M₁} {S₂ : DgShortExact K₂ L₂ M₂}
    (φ : DgShortExactHom S₁ S₂) :
    (dgCanonicalFunctor H).map φ.τ₃ ≫ dgCanonicalDelta H S₂ =
      dgCanonicalDelta H S₁ ≫ (shiftFunctor (DgDerivedCategory H) (1 : ℤ)).map
        ((dgCanonicalFunctor H).map φ.τ₁) := by
  sorry

/-! ## Sequential homotopy colimits -/

abbrev DgSequentialSystem
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) :=
  ℕ ⥤ DGModule D

abbrev dgSequentialTransition
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (F : DgSequentialSystem D) (n : ℕ) :
    DGMap (F.obj n) (F.obj (n + 1)) :=
  F.map (homOfLE (Nat.le_succ n))

structure DgSequentialColimit
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (F : DgSequentialSystem D) where
  object : DGModule D
  ι : ∀ n, DGMap (F.obj n) object
  compatible : ∀ n,
    DifferentialGradedModuleHom.comp (dgSequentialTransition F n) (ι (n + 1)) = ι n
  universal : ∀ (X : DGModule D) (f : ∀ n, DGMap (F.obj n) X),
    ∃! g : DGMap object X, ∀ n,
      DifferentialGradedModuleHom.comp (ι n) g = f n

theorem exists_dgSequentialColimit
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (F : DgSequentialSystem D) : Nonempty (DgSequentialColimit F) := by
  sorry

abbrev DgDerivedSequentialSystem
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) (F : DgSequentialSystem D) :=
  F ⋙ dgCanonicalFunctor H

theorem dgDerivedSystem_has_coproduct
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat)
    (P : DgDerivedProductsData H) (F : DgSequentialSystem D) :
    Nonempty (HasCoproduct (fun n => (DgDerivedSequentialSystem H F).obj n)) := by
  sorry

abbrev DgIsDerivedColimit
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) (F : DgSequentialSystem D)
    [HasCoproduct (fun n => (DgDerivedSequentialSystem H F).obj n)]
    (X : DgDerivedCategory H) :=
  IsDerivedColimit (DgDerivedSequentialSystem H F) X

noncomputable def dgHomotopyColimit
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) (F : DgSequentialSystem D)
    [HasCoproduct (fun n => (DgDerivedSequentialSystem H F).obj n)]
    (hF : ∃ X, DgIsDerivedColimit H F X) : DgDerivedCategory H :=
  homotopyColimit (DgDerivedSequentialSystem H F) hF

theorem dgHomotopyColimit_is_termwise_colimit
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {Kcat : Type wk} [Category.{vk} Kcat] [AdditiveCategory Kcat]
    [HasShift Kcat ℤ] [∀ n : ℤ, (shiftFunctor Kcat n).Additive]
    [Pretriangulated Kcat]
    (H : DgHomotopyCategoryModel D Kcat) (F : DgSequentialSystem D)
    [HasCoproduct (fun n => (DgDerivedSequentialSystem H F).obj n)]
    (C : DgSequentialColimit F)
    (hF : ∃ X, DgIsDerivedColimit H F X) :
    Nonempty (dgHomotopyColimit H F hF ≅
      (dgCanonicalFunctor H).obj C.object) := by
  sorry

end Formalization.Books.Dga.Unit23
