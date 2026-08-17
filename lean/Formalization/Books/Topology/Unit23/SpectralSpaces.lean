import Formalization.Books.Topology.Unit08.IrreducibleComponents
import Formalization.Books.Topology.Unit10.KrullDimension
import Formalization.Books.Topology.Unit14.LimitsOfSpaces
import Formalization.Books.Topology.Unit19.Specialization
import Formalization.Books.Topology.Unit22.ProfiniteSpaces
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Topology, Chapter 23: Spectral spaces

Mathlib's `SpectralSpace`, `IsSpectralMap`, and `constructibleTopology` are
the canonical interfaces for the definitions in the source.  The earlier
chapters supply the source-facing profinite predicate, specialization maps,
connected-components space, soberification, and the two-point example.
-/

namespace Formalization.Books.Topology.Unit23

open Set Function CategoryTheory CategoryTheory.Limits _root_.Topology TopologicalSpace
open Formalization.Books.Topology.Unit08
open Formalization.Books.Topology.Unit10
open Formalization.Books.Topology.Unit22

universe u v

variable {X : Type u} [TopologicalSpace X]

section SpectralSpaces

/-! ### The definition and the constructible topology -/

/-- Mathlib's bundled definition expands to the source's sobriety,
quasi-compactness, quasi-separatedness, and compact-open basis conditions.
Sobriety is represented by `QuasiSober` together with `T0Space`. -/
theorem spectralSpace_iff_source_conditions :
    SpectralSpace X ↔
      T0Space X ∧ CompactSpace X ∧ QuasiSober X ∧
        QuasiSeparatedSpace X ∧ PrespectralSpace X := by
  sorry

/- The source's spectral-map definition is Mathlib's `IsSpectralMap`, whose
   structure already contains continuity and compact-open preimages.  The
   earlier chapter API supplies the corresponding source-facing expansion. -/

/-- A source open is open for the constructible topology on a spectral space. -/
theorem isOpen_constructibleTopology_of_isOpen [SpectralSpace X]
    {U : Set X} (hU : IsOpen U) :
    IsOpen[constructibleTopology X] U := by
  sorry

/-- A constructible subset is clopen for the constructible topology. -/
theorem isConstructible_isOpen_isClosed_constructibleTopology [SpectralSpace X]
    {E : Set X} (hE : IsConstructible E) :
    IsOpen[constructibleTopology X] E ∧ IsClosed[constructibleTopology X] E := by
  sorry

/-- A subset closed in the source topology is closed for the constructible
topology. -/
theorem isClosed_constructibleTopology_of_isClosed [SpectralSpace X]
    {E : Set X} (hE : IsClosed E) :
    IsClosed[constructibleTopology X] E := by
  sorry

/-- The constructible topology is the coarsest topology making every
constructible subset clopen. -/
theorem constructibleTopology_is_coarsest_for_constructible_clopen
    [SpectralSpace X] :
    (∀ E : Set X, IsConstructible E →
      IsOpen[constructibleTopology X] E ∧ IsClosed[constructibleTopology X] E) ∧
      ∀ t : TopologicalSpace X,
        (∀ E : Set X, IsConstructible E → IsOpen[t] E ∧ IsClosed[t] E) →
          constructibleTopology X ≤ t := by
  sorry

/-- Open subsets of the constructible topology are unions of constructible
subsets, as in the source. -/
theorem isOpen_constructibleTopology_iff_iUnion_isConstructible [SpectralSpace X]
    {E : Set X} :
    IsOpen[constructibleTopology X] E ↔
      ∃ S : Set (Set X), (∀ U ∈ S, IsConstructible U) ∧ ⋃₀ S = E := by
  sorry

/-- Closed subsets of the constructible topology are intersections of
constructible subsets, as in the source. -/
theorem isClosed_constructibleTopology_iff_iInter_isConstructible [SpectralSpace X]
    {E : Set X} :
    IsClosed[constructibleTopology X] E ↔
      ∃ S : Set (Set X), (∀ U ∈ S, IsConstructible U) ∧ ⋂₀ S = E := by
  sorry

/-! ### Constructible topology on spectral spaces -/

/-- The constructible topology of a spectral space is quasi-compact,
Hausdorff, and totally disconnected. -/
theorem constructibleTopology_is_hausdorff_totallyDisconnected_quasiCompact
    [SpectralSpace X] :
    @T2Space X (constructibleTopology X) ∧
      @TotallyDisconnectedSpace X (constructibleTopology X) ∧
        @CompactSpace X (constructibleTopology X) := by
  sorry

/-- A spectral map is continuous for the constructible topologies, has
quasi-compact fibres, and has constructibly closed image. -/
theorem spectralMap_constructibleTopology_properties
    {Y : Type v} [TopologicalSpace Y] [SpectralSpace X] [SpectralSpace Y]
    (f : X → Y) (hf : IsSpectralMap f) :
    Continuous[constructibleTopology X, constructibleTopology Y] f ∧
      (∀ y : Y, IsCompact (f ⁻¹' ({y} : Set Y))) ∧
        IsClosed[constructibleTopology Y] (Set.range f) := by
  sorry

/-- For maps between spectral spaces, continuity for the constructible
topologies is equivalent to being a spectral map. -/
theorem isSpectralMap_iff_continuous_constructibleTopology
    {Y : Type v} [TopologicalSpace Y] [SpectralSpace X] [SpectralSpace Y]
    {f : X → Y} (hf : Continuous f) :
    IsSpectralMap f ↔
      Continuous[constructibleTopology X, constructibleTopology Y] f := by
  sorry

/-- A subspace closed in the constructible topology of a spectral space is
spectral for its induced topology. -/
theorem spectralSpace_subtype_of_constructible_closed [SpectralSpace X]
    {E : Set X} (hE : IsClosed[constructibleTopology X] E) :
    SpectralSpace E := by
  sorry

theorem spectralSpace_subtype_of_isConstructible [SpectralSpace X]
    {E : Set X} (hE : IsConstructible E) :
    SpectralSpace E := by
  sorry

theorem spectralSpace_subtype_of_isClosed [SpectralSpace X]
    {E : Set X} (hE : IsClosed E) :
    SpectralSpace E := by
  sorry

/-! ### Specialization and generalization -/

/-- A point in the closure of a constructibly closed subset is a specialization
of a point of that subset. -/
theorem exists_generalization_mem_of_mem_closure_of_constructibleClosed
    [SpectralSpace X] {E : Set X}
    (_hE : IsClosed[constructibleTopology X] E) {x : X}
    (hx : x ∈ closure E) :
    ∃ y ∈ E, y ⤳ x := by
  sorry

/-- A constructibly closed subset stable under specialization is closed in the
source topology. -/
theorem isClosed_of_constructibleClosed_of_stableUnderSpecialization
    [SpectralSpace X] {E : Set X}
    (hE : IsClosed[constructibleTopology X] E)
    (hstable : StableUnderSpecialization E) :
    IsClosed E := by
  sorry

/-- A constructibly open subset stable under generalization is open in the
source topology. -/
theorem isOpen_of_constructibleOpen_of_stableUnderGeneralization
    [SpectralSpace X] {E : Set X}
    (hE : IsOpen[constructibleTopology X] E)
    (hstable : StableUnderGeneralization E) :
    IsOpen E := by
  sorry

/-- Two points of a spectral space either have a common generalization or have
disjoint open neighbourhoods. -/
theorem spectral_two_point_dichotomy [SpectralSpace X] (x y : X) :
    (∃ z : X, z ⤳ x ∧ z ⤳ y) ∨
      ∃ U V : Set X,
        IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V := by
  sorry

/-! ### Profinite spectral spaces -/

/-- The eight stated conditions characterizing profinite spectral spaces.
The unfinished ninth item in the source is intentionally not included. -/
theorem isProfiniteSpace_TFAE_spectral_separation_conditions [SpectralSpace X] :
    List.TFAE
      [IsProfiniteSpace X,
        T2Space X,
        TotallyDisconnectedSpace X,
        (∀ U : Set X, IsOpen U → IsCompact U → IsClosed U),
        (∀ ⦃x y : X⦄, x ⤳ y → x = y),
        (∀ x : X, IsClosed ({x} : Set X)),
        (∀ x : X, ∃ C : irreducibleComponents X,
          IsGenericPoint x (C : Set X)),
        constructibleTopology X = (inferInstance : TopologicalSpace X)] := by
  sorry

/-- The connected-components space of a spectral space is profinite. -/
theorem connectedComponents_isProfiniteSpace [SpectralSpace X] :
    IsProfiniteSpace (ConnectedComponents X) := by
  sorry

/-- The product of two spectral spaces is spectral. -/
theorem spectralSpace_prod {Y : Type v} [TopologicalSpace Y]
    [SpectralSpace X] [SpectralSpace Y] :
    SpectralSpace (X × Y) := by
  sorry

/-- A bijective spectral map between spectral spaces is a homeomorphism when
specializations or generalizations lift along it. -/
theorem isHomeomorph_of_bijective_spectralMap_of_lift
    {Y : Type v} [TopologicalSpace Y] [SpectralSpace X] [SpectralSpace Y]
    (f : X → Y) (hf : IsSpectralMap f) (hbijective : Function.Bijective f)
    (hlift : GeneralizingMap f ∨ SpecializingMap f) :
    IsHomeomorph f := by
  sorry

/-! ### Inverse limits -/

/-- The inverse limit of a cofiltered diagram of finite sober spaces is
spectral.  Sobriety is expressed canonically as `QuasiSober` plus `T0Space`. -/
theorem spectralSpace_of_directed_inverse_limit_finite_sober
    {J : Type v} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{max v u})
    (hfinite : ∀ j, Finite (F.obj j))
    (hsober : ∀ j, QuasiSober (F.obj j))
    (hT0 : ∀ j, T0Space (F.obj j)) :
    SpectralSpace ((limit F : TopCat.{max v u}) : Type (max v u)) := by
  sorry

/-- A bundled source-facing interface for a directed inverse system of finite
sober topological spaces. -/
structure DirectedFiniteSoberPresentation (X : Type u) [TopologicalSpace X] where
  index : Type u
  [category : SmallCategory index]
  [cofiltered : IsCofiltered index]
  diagram : index ⥤ TopCat.{u}
  finite : ∀ i, Finite (diagram.obj i)
  sober : ∀ i, QuasiSober (diagram.obj i)
  t0 : ∀ i, T0Space (diagram.obj i)
  homeomorph : X ≃ₜ ((limit diagram : TopCat.{u}) : Type u)

/-- A topological space is spectral exactly when it is homeomorphic to a
directed inverse limit of finite sober spaces. -/
theorem spectralSpace_iff_directed_inverse_limit_finite_sober :
    SpectralSpace X ↔
      Nonempty (DirectedFiniteSoberPresentation X) := by
  sorry

/-! ### The two-point product presentation -/

/-- The earlier chapter's `KrullTwoPointSpace` is the two-point space with one
generic point and one closed point used by the source. -/
theorem krullTwoPointSpace_is_finite_sober :
    Finite KrullTwoPointSpace ∧
      QuasiSober KrullTwoPointSpace ∧
        T0Space KrullTwoPointSpace := by
  sorry

/-- Spectral spaces are precisely the constructibly closed subspaces of
products of copies of the two-point space, up to homeomorphism. -/
theorem spectralSpace_iff_constructibleClosed_subspace_of_product_twoPoint :
    SpectralSpace X ↔
      ∃ (I : Type u) (E : Set (I → KrullTwoPointSpace)),
        IsClosed[constructibleTopology (I → KrullTwoPointSpace)] E ∧
          Nonempty (X ≃ₜ E) := by
  sorry

/-! ### Soberification and Noetherian spaces -/

/-- The soberification of a quasi-compact space is quasi-compact. -/
theorem soberification_is_quasiCompact [CompactSpace X] :
    CompactSpace (Soberification X) := by
  sorry

/-- The soberification of a quasi-compact prespectral quasi-separated space is
spectral. -/
theorem soberification_is_spectral [CompactSpace X] [PrespectralSpace X]
    [QuasiSeparatedSpace X] :
    SpectralSpace (Soberification X) := by
  sorry

/-- The soberification of a Noetherian space is Noetherian and spectral. -/
theorem soberification_is_noetherian_spectral [NoetherianSpace X] :
    NoetherianSpace (Soberification X) ∧ SpectralSpace (Soberification X) := by
  sorry

end SpectralSpaces

end Formalization.Books.Topology.Unit23
