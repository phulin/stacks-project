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

class VistoliFiniteCoverLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  finiteCover : ∀ (X Y : C) (f : X ⟶ Y), IsDeligneMumfordStack X →
    IsModuliSpaceMap f → HasFiniteSchemeCover X

theorem vistoli_finite_cover_of_deligne_mumford_moduli_space
    {C : Type u} [Category.{v} C] [StackCategory C] (X Y : C)
    [VistoliFiniteCoverLaws (C := C)]
    (f : X ⟶ Y) (hDM : IsDeligneMumfordStack X)
    (hmoduli : IsModuliSpaceMap f) :
    HasFiniteSchemeCover X :=
  VistoliFiniteCoverLaws.finiteCover X Y f hDM hmoduli

structure FiniteGenericallyEtaleSchemeCover {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  scheme : C
  schemeStructure : IsScheme scheme
  map : scheme ⟶ X
  finite : IsFiniteMorphism map
  surjective : Surjective map
  genericallyEtale : IsGenericallyEtaleMorphism map

class LaumonMoretBaillyCoverLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  finiteGenericallyEtaleCover : ∀ (X : C)
    (_hDM : IsDeligneMumfordStack X) (_hfiniteType : IsFiniteTypeStack X)
    (hnoetherianBase : Prop) (_hbaseNoetherian : hnoetherianBase),
    Nonempty (FiniteGenericallyEtaleSchemeCover X)

theorem laumon_moret_bailly_finite_generically_etale_cover
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [LaumonMoretBaillyCoverLaws (C := C)]
    (hDM : IsDeligneMumfordStack X) (hfiniteType : IsFiniteTypeStack X)
    (hnoetherianBase : Prop) (hbaseNoetherian : hnoetherianBase) :
    Nonempty (FiniteGenericallyEtaleSchemeCover X) :=
  LaumonMoretBaillyCoverLaws.finiteGenericallyEtaleCover X hDM hfiniteType
    hnoetherianBase hbaseNoetherian

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

class NormalAlgebraicSpaceQuotientLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  finiteGroupQuotient : ∀ (D : NormalNoetherianAlgebraicSpaceData (C := C)),
    D.normal → D.noetherian →
    Nonempty (NormalAlgebraicSpaceFiniteGroupQuotient D)

theorem normal_noetherian_algebraic_space_is_finite_group_quotient
    {C : Type u} [Category.{v} C] [StackCategory C]
    [NormalAlgebraicSpaceQuotientLaws (C := C)]
    (D : NormalNoetherianAlgebraicSpaceData (C := C))
    (hnormal : D.normal) (hnoetherian : D.noetherian) :
    Nonempty (NormalAlgebraicSpaceFiniteGroupQuotient D) :=
  NormalAlgebraicSpaceQuotientLaws.finiteGroupQuotient D hnormal hnoetherian

abbrev FiniteSurjectiveSchemeCover {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) := SchemeFiniteCover X

def HasFiniteSurjectiveSchemeCover {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  HasFiniteSchemeCover X

class QuasiFiniteDiagonalCoverLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  diagonalIffCover : ∀ (X : C) (_hfiniteType : IsFiniteTypeStack X)
    (hnoetherianBase : Prop) (_hbaseNoetherian : hnoetherianBase),
    HasQuasiFiniteDiagonal X ↔ HasFiniteSurjectiveSchemeCover X

theorem quasi_finite_diagonal_iff_finite_surjective_scheme_cover
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [QuasiFiniteDiagonalCoverLaws (C := C)]
    (hfiniteType : IsFiniteTypeStack X) (hnoetherianBase : Prop)
    (hbaseNoetherian : hnoetherianBase) :
    HasQuasiFiniteDiagonal X ↔ HasFiniteSurjectiveSchemeCover X :=
  QuasiFiniteDiagonalCoverLaws.diagonalIffCover X hfiniteType hnoetherianBase
    hbaseNoetherian

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

class KreschVistoliCoverLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  smoothFiniteFlatCover : ∀ (X : C) (_hsmooth : IsSmoothStack X)
    (_hseparated : IsSeparatedStack X) (_hDM : IsDeligneMumfordStack X)
    (hfiniteTypeOverField : Prop) (_hfiniteTypeOverFieldProof : hfiniteTypeOverField)
    (hcoarseQuasiProjective : Prop) (_hcoarseQuasiProjectiveProof : hcoarseQuasiProjective),
    Nonempty (SmoothQuasiProjectiveFiniteFlatCover X)

theorem kresch_vistoli_smooth_finite_flat_cover
    {C : Type u} [Category.{v} C] [StackCategory C] (X : C)
    [KreschVistoliCoverLaws (C := C)]
    (hsmooth : IsSmoothStack X) (hseparated : IsSeparatedStack X)
    (hDM : IsDeligneMumfordStack X) (hfiniteTypeOverField : Prop)
    (hfiniteTypeOverFieldProof : hfiniteTypeOverField)
    (hcoarseQuasiProjective : Prop)
    (hcoarseQuasiProjectiveProof : hcoarseQuasiProjective) :
    Nonempty (SmoothQuasiProjectiveFiniteFlatCover X) :=
  KreschVistoliCoverLaws.smoothFiniteFlatCover X hsmooth hseparated hDM
    hfiniteTypeOverField hfiniteTypeOverFieldProof hcoarseQuasiProjective
    hcoarseQuasiProjectiveProof

structure ProperQuasiProjectiveSchemeCover {C : Type u} [Category.{v} C]
    [StackCategory C] (X S : C) where
  scheme : C
  schemeStructure : IsScheme scheme
  map : scheme ⟶ X
  proper : IsProperMorphism map
  surjective : Surjective map
  quasiProjectiveOverBase : Prop

class OlssonProperCoverLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  properCover : ∀ (X S : C) (_hartin : IsArtinStack X)
    (_hseparated : IsSeparatedStack X) (hfiniteTypeOverBase : Prop)
    (_hfiniteTypeOverBaseProof : hfiniteTypeOverBase),
    Nonempty (ProperQuasiProjectiveSchemeCover X S)

theorem olsson_proper_quasi_projective_scheme_cover
    {C : Type u} [Category.{v} C] [StackCategory C] (X S : C)
    [OlssonProperCoverLaws (C := C)]
    (hartin : IsArtinStack X) (hseparated : IsSeparatedStack X)
    (hfiniteTypeOverBase : Prop) (hfiniteTypeOverBaseProof : hfiniteTypeOverBase) :
    Nonempty (ProperQuasiProjectiveSchemeCover X S) :=
  OlssonProperCoverLaws.properCover X S hartin hseparated hfiniteTypeOverBase
    hfiniteTypeOverBaseProof

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

class RydhApproximationLaws {C : Type u} [Category.{v} C]
    [StackCategory C] where
  approximation : ∀ {X : C} (_H : RydhNoetherianApproximationHypotheses X),
    ∃ W : RydhApproximationCover X,
      W.flatOverDenseOpen ∨ W.etaleOverDenseOpen

theorem rydh_noetherian_approximation_theorem_B
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    [RydhApproximationLaws (C := C)]
    (H : RydhNoetherianApproximationHypotheses X) :
    ∃ W : RydhApproximationCover X,
      W.flatOverDenseOpen ∨ W.etaleOverDenseOpen :=
  RydhApproximationLaws.approximation H

end Formalization.Books.Guide.Unit05
