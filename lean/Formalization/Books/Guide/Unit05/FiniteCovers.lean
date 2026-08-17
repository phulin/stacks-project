import Formalization.Books.Guide.Unit05.Core

/-!
# Chapter 5, Section 6: existence of finite covers by schemes
-/

noncomputable section

open CategoryTheory
open Formalization.Books.StacksMorphisms.Unit07

universe u v

namespace Formalization.Books.Guide.Unit05

structure SchemeFiniteCover {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  scheme : C
  schemeStructure : IsScheme scheme
  map : scheme ⟶ X
  finite : IsFiniteMorphism map
  surjective : Surjective map

def HasFiniteSchemeCover {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  Nonempty (SchemeFiniteCover X)

def IsModuliSpaceMap {C : Type u} [Category.{v} C] [StackCategory C]
    {X Y : C} (f : X ⟶ Y) : Prop :=
  IsProperMorphism f ∧ Function.Bijective (stackPointMap f)

theorem vistoli_finite_cover_of_deligne_mumford_moduli_space
    {C : Type u} [Category.{v} C] [StackCategory C] (X Y : C)
    (f : X ⟶ Y) (hDM : IsDeligneMumfordStack X)
    (hmoduli : IsModuliSpaceMap f) :
    HasFiniteSchemeCover X := by
  sorry

structure FiniteGenericallyEtaleSchemeCover {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  scheme : C
  schemeStructure : IsScheme scheme
  map : scheme ⟶ X
  finite : IsFiniteMorphism map
  surjective : Surjective map
  genericallyEtale : IsGenericallyEtaleMorphism map

theorem laumon_moret_bailly_finite_generically_etale_cover
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hDM : IsDeligneMumfordStack X) (hfiniteType : IsFiniteTypeStack X)
    (hnoetherianBase : Prop) :
    Nonempty (FiniteGenericallyEtaleSchemeCover X) := by
  sorry

structure NormalAlgebraicSpaceFiniteGroupQuotient {C : Type u}
    [Category.{v} C] [StackCategory C] where
  algebraicSpace : C
  normal : Prop
  noetherian : Prop
  coverScheme : C
  coverSchemeIsScheme : IsScheme coverScheme
  finiteGroup : Type u
  groupStructure : Group finiteGroup
  quotientPresentation : Prop

theorem normal_noetherian_algebraic_space_is_finite_group_quotient
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : NormalAlgebraicSpaceFiniteGroupQuotient (C := C)) :
    D.quotientPresentation := by
  sorry

structure DiagonalPropertyData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  base : C
  quasiFiniteDiagonal : Prop

def HasQuasiFiniteDiagonal {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ D : DiagonalPropertyData X, D.quasiFiniteDiagonal

structure FiniteSurjectiveSchemeCover {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  scheme : C
  schemeStructure : IsScheme scheme
  map : scheme ⟶ X
  finite : IsFiniteMorphism map
  surjective : Surjective map

def HasFiniteSurjectiveSchemeCover {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  Nonempty (FiniteSurjectiveSchemeCover X)

theorem quasi_finite_diagonal_iff_finite_surjective_scheme_cover
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hfiniteType : IsFiniteTypeStack X) (hnoetherianBase : Prop) :
    HasQuasiFiniteDiagonal X ↔ HasFiniteSurjectiveSchemeCover X := by
  sorry

structure SmoothQuasiProjectiveFiniteFlatCover {C : Type u}
    [Category.{v} C] [StackCategory C] (X : C) where
  scheme : C
  schemeStructure : IsScheme scheme
  map : scheme ⟶ X
  smooth : IsSmoothMorphism map
  quasiProjective : IsQuasiProjectiveStack scheme
  finite : IsFiniteMorphism map
  flat : Flat map

theorem kresch_vistoli_smooth_finite_flat_cover
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hsmooth : IsSmoothStack X) (hseparated : IsSeparatedStack X)
    (hDM : IsDeligneMumfordStack X) (hfiniteTypeOverField : Prop)
    (hcoarseQuasiProjective : Prop) :
    Nonempty (SmoothQuasiProjectiveFiniteFlatCover X) := by
  sorry

structure ProperQuasiProjectiveSchemeCover {C : Type u} [Category.{v} C]
    [StackCategory C] (X S : C) where
  scheme : C
  schemeStructure : IsScheme scheme
  map : scheme ⟶ X
  proper : IsProperMorphism map
  surjective : Surjective map
  quasiProjectiveOverBase : Prop

theorem olsson_proper_quasi_projective_scheme_cover
    {C : Type u} [Category.{v} C] [StackCategory C] (X S : C)
    (hartin : IsArtinStack X) (hseparated : IsSeparatedStack X)
    (hfiniteTypeOverBase : Prop) :
    Nonempty (ProperQuasiProjectiveSchemeCover X S) := by
  sorry

structure DenseQuasiCompactOpenSubstack {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  openSubstack : C
  inclusion : openSubstack ⟶ X
  dense : Prop
  quasiCompact : Prop
  openImmersion : Prop

structure RydhApproximationCover {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  scheme : C
  schemeStructure : IsScheme scheme
  map : scheme ⟶ X
  finite : IsFiniteMorphism map
  finitelyPresented : Prop
  surjective : Surjective map
  denseOpen : DenseQuasiCompactOpenSubstack X
  flatOverDenseOpen : Prop
  etaleOverDenseOpen : Prop

structure RydhNoetherianApproximationHypotheses {C : Type u}
    [Category.{v} C] [StackCategory C] (X : C) where
  quasiCompact : Prop
  quasiFiniteSeparatedDiagonal : Prop
  deligneMumfordAlternative : Prop
  quasiCompactSeparatedDiagonalAlternative : Prop

theorem rydh_noetherian_approximation_theorem_B
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (H : RydhNoetherianApproximationHypotheses X) :
    Nonempty (RydhApproximationCover X) := by
  sorry

end Formalization.Books.Guide.Unit05
