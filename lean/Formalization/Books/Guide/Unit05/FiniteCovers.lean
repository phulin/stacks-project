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
    (hnoetherianBase : Prop) (hbaseNoetherian : hnoetherianBase) :
    Nonempty (FiniteGenericallyEtaleSchemeCover X) := by
  sorry

structure NormalNoetherianAlgebraicSpaceData {C : Type u}
    [Category.{v} C] [StackCategory C] where
  algebraicSpace : C
  algebraicSpaceIsAlgebraicSpace : IsAlgebraicSpace algebraicSpace
  normal : Prop
  noetherian : Prop

structure NormalAlgebraicSpaceFiniteGroupQuotient {C : Type u}
    [Category.{v} C] [StackCategory C]
    (D : NormalNoetherianAlgebraicSpaceData (C := C)) where
  coverScheme : C
  coverSchemeIsScheme : IsScheme coverScheme
  finiteGroup : Type u
  groupStructure : Group finiteGroup
  quotientMap : coverScheme ⟶ D.algebraicSpace
  quotientIsTheFiniteGroupQuotient : Prop
  quotientPresentation : Prop

theorem normal_noetherian_algebraic_space_is_finite_group_quotient
    {C : Type u} [Category.{v} C] [StackCategory C]
    (D : NormalNoetherianAlgebraicSpaceData (C := C))
    (hnormal : D.normal) (hnoetherian : D.noetherian) :
    Nonempty (NormalAlgebraicSpaceFiniteGroupQuotient D) := by
  sorry

abbrev FiniteSurjectiveSchemeCover {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) := SchemeFiniteCover X

def HasFiniteSurjectiveSchemeCover {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  HasFiniteSchemeCover X

theorem quasi_finite_diagonal_iff_finite_surjective_scheme_cover
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hfiniteType : IsFiniteTypeStack X) (hnoetherianBase : Prop)
    (hbaseNoetherian : hnoetherianBase) :
    HasQuasiFiniteDiagonal X ↔ HasFiniteSurjectiveSchemeCover X := by
  sorry

structure SmoothQuasiProjectiveFiniteFlatCover {C : Type u}
    [Category.{v} C] [StackCategory C] (X : C) where
  scheme : C
  schemeStructure : IsScheme scheme
  map : scheme ⟶ X
  smooth : IsSmoothStack scheme
  quasiProjective : IsQuasiProjectiveStack scheme
  finite : IsFiniteMorphism map
  flat : Flat map
  surjective : Surjective map

theorem kresch_vistoli_smooth_finite_flat_cover
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    (hsmooth : IsSmoothStack X) (hseparated : IsSeparatedStack X)
    (hDM : IsDeligneMumfordStack X) (hfiniteTypeOverField : Prop)
    (hfiniteTypeOverFieldProof : hfiniteTypeOverField)
    (hcoarseQuasiProjective : Prop)
    (hcoarseQuasiProjectiveProof : hcoarseQuasiProjective) :
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
    (hfiniteTypeOverBase : Prop) (hfiniteTypeOverBaseProof : hfiniteTypeOverBase) :
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
  quasiCompact : IsQuasiCompactStack X
  quasiFiniteSeparatedDiagonal : Prop
  deligneMumfordAlternative : IsDeligneMumfordStack X
  quasiCompactSeparatedDiagonalAlternative : Prop
  hasApplicableAlternative :
    quasiFiniteSeparatedDiagonal ∨
      (IsDeligneMumfordStack X ∧ quasiCompactSeparatedDiagonalAlternative)

theorem rydh_noetherian_approximation_theorem_B
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (H : RydhNoetherianApproximationHypotheses X) :
    ∃ W : RydhApproximationCover X,
      W.flatOverDenseOpen ∨ W.etaleOverDenseOpen := by
  sorry

end Formalization.Books.Guide.Unit05
