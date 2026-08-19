import Formalization.Books.Algebra.Unit76.FunctorialitiesForTor
import Formalization.Books.Derived.Unit08.HomotopyCategory
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Homology.Unit24.FilteredComplexes
import Formalization.Books.MoreAlgebra.Unit59.DerivedTensorProduct
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# More on Algebra, Chapter 62: Spectral sequences for Tor

The source's four examples are recorded as source-facing spectral-sequence
data.  Tor groups use the canonical resolution construction from Algebra,
Chapter 75, while the derived tensor products and bounded-above derived
categories use the interfaces from Chapters 56 and 59.  The homological
indexing in the first two examples is kept explicitly: it is not silently
replaced by the cohomological indexing convention used by the filtered
cochain-complex API.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit71
open Formalization.Books.Algebra.Unit75
open Formalization.Books.Algebra.Unit76
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.MoreAlgebra.Unit56
open Formalization.Books.MoreAlgebra.Unit57
open Formalization.Books.MoreAlgebra.Unit58
open Formalization.Books.MoreAlgebra.Unit59

universe u w

namespace Formalization.Books.MoreAlgebra.Unit62

/-! ## Common Tor and abutment notation -/

abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

/- The source allows a chain complex indexed by all integers, bounded below.
   This is the canonical chain-complex shape, and its homology is the
   categorical homology functor supplied by Mathlib. -/
abbrev ModuleChainComplexZ (R : Type u) [CommRing R] :=
  ChainComplex (Mod R) ℤ

def IsBoundedBelowChainComplex {R : Type u} [CommRing R]
    (K : ModuleChainComplexZ R) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, i ≤ n → IsZero (K.X i)

abbrev chainComplexHomology {R : Type u} [CommRing R]
    (K : ModuleChainComplexZ R) (i : ℤ) : Mod R :=
  (HomologicalComplex.homologyFunctor (Mod R) (ComplexShape.down ℤ) i).obj K

/- Reversing the grading turns the source's bounded-below chain complex into
   the bounded-above cochain complex used by the derived-tensor API. -/
noncomputable def chainToCochain {R : Type u} [CommRing R]
    (K : ModuleChainComplexZ R) : Comp (Mod R) where
  X n := K.X (-n)
  d n m := if h : n + 1 = m then K.d (-n) (-m) else 0
  shape n m hnm := by
    classical
    split_ifs with h
    · exact (hnm (by simpa only [ComplexShape.up_Rel] using h)).elim
    · rfl
  d_comp_d' n m k hnm hmk := by
    classical
    have hnm' : n + 1 = m := by
      simpa only [ComplexShape.up_Rel] using hnm
    have hmk' : m + 1 = k := by
      simpa only [ComplexShape.up_Rel] using hmk
    rw [dif_pos hnm', dif_pos hmk']
    exact K.d_comp_d' (-n) (-m) (-k) (by
      simp only [ComplexShape.down_Rel]
      omega) (by
      simp only [ComplexShape.down_Rel]
      omega)

/- Extending Tor by zero to negative degrees lets the page indices remain
   integer-indexed, as they are in the source's bigraded notation. -/
noncomputable def torModuleZ {R : Type u} [CommRing R]
    (M N : Mod R) (j : ℤ) : Mod R :=
  if h : 0 ≤ j then Tor M N j.toNat else ModuleCat.of R (Fin 0 → R)

noncomputable def chainDerivedTensorHomology {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : ModuleChainComplexZ R) (M : Mod R) (n : ℤ) : Mod R :=
  (derivedCohomologyFunctor (Mod R) (-n)).obj
    (derivedTensor
      ((derivedComplexQuotient R).obj (chainToCochain K))
      ((derivedComplexQuotient R).obj
        ((CochainComplex.singleFunctor (Mod R) 0).obj M)))

abbrev torAdditiveGroup {R : Type u} [CommRing R]
    (M N : Mod R) (j : ℤ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (torModuleZ M N j : Type u)

noncomputable def chainTorDifferential {R : Type u} [CommRing R]
    (K : ModuleChainComplexZ R) (M : Mod R) (i : ℤ) (j : ℕ) :
    Tor (K.X i) M j ⟶ Tor (K.X (i - 1)) M j :=
  torMapFirst (N := M) (K.d i (i - 1)) j

/- The double complex in the first example has the chain degree of `K` in
   the first coordinate and the chosen free resolution degree in the second.
   Its component comparison records the displayed tensor-product terms. -/
structure TensorDoubleComplex
    {R : Type u} [CommRing R] (K : ModuleChainComplexZ R)
    {M : Mod R} (P : FreeResolution R M) where
  obj : ℤ → ℕ → Mod R
  horizontal : ∀ i : ℤ, ∀ j : ℕ, obj (i + 1) j ⟶ obj i j
  vertical : ∀ i : ℤ, ∀ j : ℕ, obj i (j + 1) ⟶ obj i j
  horizontal_squared : ∀ i : ℤ, ∀ j : ℕ,
    horizontal (i + 1) j ≫ horizontal i j = 0
  vertical_squared : ∀ i : ℤ, ∀ j : ℕ,
    vertical i (j + 1) ≫ vertical i j = 0
  commute : ∀ i : ℤ, ∀ j : ℕ,
    horizontal i (j + 1) ≫ vertical i j =
      vertical (i + 1) j ≫ horizontal i j
  component : ∀ i : ℤ, ∀ j : ℕ,
    Nonempty (obj i j ≅
      MonoidalCategory.tensorObj (K.X i) (P.complex.X j))

structure TensorDoubleComplexData
    {R : Type u} [CommRing R] (K : ModuleChainComplexZ R) (M : Mod R) where
  resolution : FreeResolution R M
  doubleComplex : TensorDoubleComplex K resolution

theorem tensor_double_complex_exists
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (Mod R)]
    (K : ModuleChainComplexZ R) (M : Mod R) :
    Nonempty (TensorDoubleComplexData K M) := by
  sorry

/-! ## The first example: a bounded-below chain complex tensored with a module -/

structure FirstChainTorSpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : ModuleChainComplexZ R) (M : Mod R)
    (hK : IsBoundedBelowChainComplex K) where
  doubleComplex : TensorDoubleComplexData K M
  /-- The pages, with the source's homological bidegrees. -/
  page : ℕ → ℤ → ℤ → Mod R
  /-- The homological differential has bidegree `(r - 1, -r)`. -/
  differential : ∀ r : ℕ, ∀ i j : ℤ,
    page r i j ⟶ page r (i + r - 1) (j - r)
  differential_squared : ∀ r : ℕ, ∀ i j : ℤ,
    differential r i j ≫ differential r (i + r - 1) (j - r) = 0
  e₂_page : ∀ i j : ℤ,
    Nonempty (page 2 i j ≅ torModuleZ (chainComplexHomology K i) M j)
  d₂_induced : ∀ i j : ℤ,
    ∃ φ : torModuleZ (chainComplexHomology K i) M j ⟶
        torModuleZ (chainComplexHomology K (i + 1)) M (j - 2),
      ∃ e₀ : page 2 i j ≅ torModuleZ (chainComplexHomology K i) M j,
      ∃ e₁ : page 2 (i + 1) (j - 2) ≅
          torModuleZ (chainComplexHomology K (i + 1)) M (j - 2),
        e₀.hom ≫ φ = differential 2 i j ≫
          eqToHom (by congr 1 <;> omega) ≫ e₁.hom
  abutment : ℤ → Mod R
  convergence : ∀ n : ℤ,
    Nonempty (abutment n ≅ chainDerivedTensorHomology K M n)

theorem first_chain_tor_spectral_sequence_exists
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : ModuleChainComplexZ R) (M : Mod R)
    (hK : IsBoundedBelowChainComplex K) :
    Nonempty (FirstChainTorSpectralSequenceData K M hK) := by
  sorry

structure SecondChainTorSpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : ModuleChainComplexZ R) (M : Mod R)
    (hK : IsBoundedBelowChainComplex K) where
  doubleComplex : TensorDoubleComplexData K M
  page : ℕ → ℤ → ℤ → Mod R
  /-- The `d₁` in the source goes from the `i`th term to the `(i - 1)`st. -/
  differential : ∀ r : ℕ, ∀ i j : ℤ,
    page r i j ⟶ page r (i - r) j
  differential_squared : ∀ r : ℕ, ∀ i j : ℤ,
    differential r i j ≫ differential r (i - r) j = 0
  e₁_page : ∀ i j : ℤ,
    Nonempty (page 1 i j ≅ torModuleZ (K.X i) M j)
  d₁_induced : ∀ i : ℤ, ∀ j : ℕ,
    ∃ e₀ : page 1 i j ≅ Tor (K.X i) M j,
    ∃ e₁ : page 1 (i - 1) j ≅ Tor (K.X (i - 1)) M j,
      e₀.hom ≫ chainTorDifferential K M i j =
        differential 1 i j ≫ e₁.hom
  abutment : ℤ → Mod R
  convergence : ∀ n : ℤ,
    Nonempty (abutment n ≅ chainDerivedTensorHomology K M n)

theorem second_chain_tor_spectral_sequence_exists
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : ModuleChainComplexZ R) (M : Mod R)
    (hK : IsBoundedBelowChainComplex K) :
    Nonempty (SecondChainTorSpectralSequenceData K M hK) := by
  sorry

noncomputable def firstChainTorSpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : ModuleChainComplexZ R) (M : Mod R)
    (hK : IsBoundedBelowChainComplex K) :
    FirstChainTorSpectralSequenceData K M hK :=
  Classical.choice (first_chain_tor_spectral_sequence_exists K M hK)

noncomputable def secondChainTorSpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : ModuleChainComplexZ R) (M : Mod R)
    (hK : IsBoundedBelowChainComplex K) :
    SecondChainTorSpectralSequenceData K M hK :=
  Classical.choice (second_chain_tor_spectral_sequence_exists K M hK)

theorem first_chain_tor_e₂_page
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : ModuleChainComplexZ R) (M : Mod R)
    (hK : IsBoundedBelowChainComplex K) (i j : ℤ) :
    Nonempty ((firstChainTorSpectralSequenceData K M hK).page 2 i j ≅
      torModuleZ (chainComplexHomology K i) M j) := by
  exact (firstChainTorSpectralSequenceData K M hK).e₂_page i j

theorem second_chain_tor_e₁_page
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : ModuleChainComplexZ R) (M : Mod R)
    (hK : IsBoundedBelowChainComplex K) (i j : ℕ) :
    Nonempty ((secondChainTorSpectralSequenceData K M hK).page 1 i j ≅
      torModuleZ (K.X i) M j) := by
  exact (secondChainTorSpectralSequenceData K M hK).e₁_page i j

/-! ## The change-of-rings example -/

noncomputable def changeOfRingsInnerTor
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Mod R) (m : ℕ) : Mod S :=
  let D := canonicalTorChangeOfRingsData f
  let T := D.target M (ModuleCat.of S S) m
  letI : Module S (restrictedTor f M (ModuleCat.of S S) m) := T.module
  ModuleCat.of S (restrictedTor f M (ModuleCat.of S S) m)

noncomputable def changeOfRingsPage
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Mod R) (N : Mod S) (n m : ℕ) :
    AddCommGrpCat.{u} :=
  AddCommGrpCat.of
    (Tor (changeOfRingsInnerTor f M m) N n : Type u)

noncomputable def changeOfRingsAbutment
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Mod R) (N : Mod S) (k : ℕ) :
    AddCommGrpCat.{u} :=
  AddCommGrpCat.of (Tor M (restrictedModule f N) k : Type u)

/- The displayed tensor identity in the change-of-rings construction is the
   earlier chapter's canonical base-change/tensor-product isomorphism, with
   its direction reversed to match the source. -/
theorem change_of_rings_tensor_identity
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (K : Formalization.Books.MoreAlgebra.Unit59.Comp R)
    (L : Formalization.Books.MoreAlgebra.Unit59.Comp S) :
    Nonempty
      (baseChangeComplex f
          (tensorProductComplex R K (restrictScalarsComplex f L)) ≅
        tensorProductComplex S (baseChangeComplex f K) L) := by
  rcases baseChange_tensorProduct_iso f K L with ⟨e⟩
  exact ⟨e.symm⟩

noncomputable def changeOfRingsResolutionComplex
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {M : Mod R} (P : FreeResolution R M) :
    ChainComplex (Mod S) ℕ :=
  ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    P.complex

structure ChangeOfRingsResolutionData
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Mod R) where
  resolution : FreeResolution R M
  scalarExtended : FreeResolution S (extendedModule f M)
  comparison : Nonempty (scalarExtended.complex ≅
    changeOfRingsResolutionComplex f resolution)

theorem change_of_rings_resolution_data_exists
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Mod R) :
    Nonempty (ChangeOfRingsResolutionData f M) := by
  sorry

noncomputable def changeOfRingsResolutionData
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Mod R) :
    ChangeOfRingsResolutionData f M :=
  Classical.choice (change_of_rings_resolution_data_exists f M)

structure ChangeOfRingsTorSpectralSequenceData
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Mod R) (N : Mod S) where
  resolutionData : ChangeOfRingsResolutionData f M
  /-- The canonical spectral-sequence object supplies all pages and
      differentials, with the source's `d_r` bidegree. -/
  spectralSequence :
    CategoryTheory.E₂CohomologicalSpectralSequence (AddCommGrpCat.{u})
  e₂_page : ∀ n m : ℕ,
    Nonempty ((spectralSequence.page 2).X (n, m) ≅
      changeOfRingsPage f M N n m)
  abutment : ℕ → AddCommGrpCat.{u}
  convergence : ∀ k : ℕ,
    Nonempty (abutment k ≅ changeOfRingsAbutment f M N k)

theorem change_of_rings_tor_spectral_sequence_exists
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Mod R) (N : Mod S) :
    Nonempty (ChangeOfRingsTorSpectralSequenceData f M N) := by
  sorry

noncomputable def changeOfRingsTorSpectralSequenceData
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Mod R) (N : Mod S) :
    ChangeOfRingsTorSpectralSequenceData f M N :=
  Classical.choice (change_of_rings_tor_spectral_sequence_exists f M N)

theorem change_of_rings_tor_e₂_page
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Mod R) (N : Mod S) (n m : ℕ) :
    Nonempty (((changeOfRingsTorSpectralSequenceData f M N).spectralSequence.page 2).X
      (n, m) ≅ changeOfRingsPage f M N n m) := by
  exact (changeOfRingsTorSpectralSequenceData f M N).e₂_page n m

/-! ## The flat base-change example -/

structure BaseChangeSquare (A B A' B' : Type u)
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] where
  aToB : A →+* B
  aToA' : A →+* A'
  bToB' : B →+* B'
  a'ToB' : A' →+* B'
  commutes : bToB'.comp aToB = a'ToB'.comp aToA'
  isPushout : ∀ {C : Type u} [CommRing C]
    (g : B →+* C) (h : A' →+* C),
    g.comp aToB = h.comp aToA' →
    ∃! k : B' →+* C,
      k.comp bToB' = g ∧ k.comp a'ToB' = h

noncomputable def baseChangedModule
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (S : BaseChangeSquare A B A' B') (M : Mod B) : Mod B' :=
  (ModuleCat.extendScalars S.bToB').obj M

noncomputable def baseChangedModuleOverA'
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (S : BaseChangeSquare A B A' B') (M : Mod B) : Mod A' :=
  (ModuleCat.extendScalars S.aToA').obj
    ((ModuleCat.restrictScalars S.aToB).obj M)

def ModuleFlatOver
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (M : Mod B) : Prop :=
  Module.Flat A ((ModuleCat.restrictScalars f).obj M : Type u)

structure BaseChangeModuleIdentifications
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (S : BaseChangeSquare A B A' B') (M N : Mod B) where
  M_iso : Nonempty
    ((ModuleCat.restrictScalars S.a'ToB').obj (baseChangedModule S M) ≅
      baseChangedModuleOverA' S M)
  N_iso : Nonempty
    ((ModuleCat.restrictScalars S.a'ToB').obj (baseChangedModule S N) ≅
      baseChangedModuleOverA' S N)

noncomputable def flatBaseChangeResolutionComplex
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (S : BaseChangeSquare A B A' B') {M : Mod B} (F : FreeResolution B M) :
    ChainComplex (Mod B') ℕ :=
  ((ModuleCat.extendScalars S.bToB').mapHomologicalComplex (ComplexShape.down ℕ)).obj
    F.complex

structure FlatBaseChangeResolutionData
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (S : BaseChangeSquare A B A' B') (M : Mod B)
    (hAB : RingHom.Flat S.aToB)
    (hM : ModuleFlatOver S.aToB M) where
  resolution : FreeResolution B M
  baseChangedResolution : FreeResolution B' (baseChangedModule S M)
  comparison : Nonempty (baseChangedResolution.complex ≅
    flatBaseChangeResolutionComplex S resolution)

theorem flat_base_change_resolution_data_exists
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (S : BaseChangeSquare A B A' B') (M : Mod B)
    (hAB : RingHom.Flat S.aToB)
    (hM : ModuleFlatOver S.aToB M) :
    Nonempty (FlatBaseChangeResolutionData S M hAB hM) := by
  sorry

noncomputable def flatBaseChangePage
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (S : BaseChangeSquare A B A' B') (M N : Mod B) (i j : ℕ) :
    AddCommGrpCat.{u} :=
  AddCommGrpCat.of
    (Tor
      ((ModuleCat.restrictScalars S.aToB).obj (Tor M N j))
      ((ModuleCat.restrictScalars S.aToA').obj (ModuleCat.of A' A')) i : Type u)

noncomputable def flatBaseChangeAbutment
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (S : BaseChangeSquare A B A' B') (M N : Mod B) (k : ℕ) :
    AddCommGrpCat.{u} :=
  AddCommGrpCat.of
    (Tor (baseChangedModule S M) (baseChangedModule S N) k : Type u)

structure FlatBaseChangeTorSpectralSequenceData
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (S : BaseChangeSquare A B A' B') (M N : Mod B)
    (hAB : RingHom.Flat S.aToB)
    (hM : ModuleFlatOver S.aToB M)
    (hN : ModuleFlatOver S.aToB N) where
  resolutionData : FlatBaseChangeResolutionData S M hAB hM
  moduleIdentifications : BaseChangeModuleIdentifications S M N
  /-- The canonical `E₂` spectral sequence, whose `d_r` has bidegree
      `(r, 1-r)`. -/
  spectralSequence :
    CategoryTheory.E₂CohomologicalSpectralSequence (AddCommGrpCat.{u})
  e₂_page : ∀ i j : ℕ,
    Nonempty ((spectralSequence.page 2).X (i, j) ≅
      flatBaseChangePage S M N i j)
  abutment : ℕ → AddCommGrpCat.{u}
  convergence : ∀ k : ℕ,
    Nonempty (abutment k ≅ flatBaseChangeAbutment S M N k)

theorem flat_base_change_tor_spectral_sequence_exists
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (S : BaseChangeSquare A B A' B') (M N : Mod B)
    (hAB : RingHom.Flat S.aToB)
    (hM : ModuleFlatOver S.aToB M)
    (hN : ModuleFlatOver S.aToB N) :
    Nonempty (FlatBaseChangeTorSpectralSequenceData S M N hAB hM hN) := by
  sorry

noncomputable def flatBaseChangeTorSpectralSequenceData
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (S : BaseChangeSquare A B A' B') (M N : Mod B)
    (hAB : RingHom.Flat S.aToB)
    (hM : ModuleFlatOver S.aToB M)
    (hN : ModuleFlatOver S.aToB N) :
    FlatBaseChangeTorSpectralSequenceData S M N hAB hM hN :=
  Classical.choice (flat_base_change_tor_spectral_sequence_exists S M N hAB hM hN)

theorem flat_base_change_tor_e₂_page
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (S : BaseChangeSquare A B A' B') (M N : Mod B)
    (hAB : RingHom.Flat S.aToB)
    (hM : ModuleFlatOver S.aToB M)
    (hN : ModuleFlatOver S.aToB N) (i j : ℕ) :
    Nonempty (((flatBaseChangeTorSpectralSequenceData S M N hAB hM hN).spectralSequence.page 2).X
      (i, j) ≅ flatBaseChangePage S M N i j) := by
  exact (flatBaseChangeTorSpectralSequenceData S M N hAB hM hN).e₂_page i j

/-! ## Derived-category Tor spectral sequences -/

abbrev DerivedD
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] :=
  Formalization.Books.MoreAlgebra.Unit56.D R

abbrev DerivedDMinus
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] :=
  Formalization.Books.MoreAlgebra.Unit56.DMinus R

noncomputable abbrev derivedMinusToDerived
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] : DerivedDMinus R ⥤ DerivedD R :=
  DerivedCategory.Minus.ι

noncomputable abbrev derivedCohomologyMinus
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : DerivedDMinus R) (n : ℤ) : Mod R :=
  (derivedCohomologyFunctor (Mod R) n).obj
    ((derivedMinusToDerived (R := R)).obj K)

noncomputable abbrev derivedTensorMinusModule
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : DerivedDMinus R) (M : Mod R) : DerivedD R :=
  derivedTensor ((derivedMinusToDerived (R := R)).obj K)
    ((derivedMinusToDerived (R := R)).obj (moduleInDMinus R M))

noncomputable abbrev derivedTensorMinusMinus
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : DerivedDMinus R) : DerivedD R :=
  derivedTensor ((derivedMinusToDerived (R := R)).obj K)
    ((derivedMinusToDerived (R := R)).obj L)

structure FirstDerivedTorSpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : DerivedDMinus R) where
  /-- The source's cohomological spectral sequence, including its
      page-to-page quotient data and differentials. -/
  spectralSequence :
    CategoryTheory.E₂CohomologicalSpectralSequence (Mod R)
  e₂_page : ∀ p q : ℤ,
    Nonempty ((spectralSequence.page 2).X (p, q) ≅
      (derivedCohomologyFunctor (Mod R) p).obj
        (derivedTensorMinusModule K (derivedCohomologyMinus L q)))
  abutment : ℤ → Mod R
  convergence : ∀ n : ℤ,
    Nonempty (abutment n ≅
      (derivedCohomologyFunctor (Mod R) n).obj
        (derivedTensorMinusMinus K L))

structure SecondDerivedTorSpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : DerivedDMinus R) where
  /-- The second canonical cohomological spectral sequence for the same
      total derived tensor product. -/
  spectralSequence :
    CategoryTheory.E₂CohomologicalSpectralSequence (Mod R)
  e₂_page : ∀ p q : ℤ,
    Nonempty ((spectralSequence.page 2).X (p, q) ≅
      (derivedCohomologyFunctor (Mod R) p).obj
        (derivedTensorMinusModule L (derivedCohomologyMinus K q)))
  abutment : ℤ → Mod R
  convergence : ∀ n : ℤ,
    Nonempty (abutment n ≅
      (derivedCohomologyFunctor (Mod R) n).obj
        (derivedTensorMinusMinus K L))

theorem first_derived_tor_spectral_sequence_exists
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : DerivedDMinus R) :
    Nonempty (FirstDerivedTorSpectralSequenceData K L) := by
  sorry

theorem second_derived_tor_spectral_sequence_exists
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : DerivedDMinus R) :
    Nonempty (SecondDerivedTorSpectralSequenceData K L) := by
  sorry

noncomputable def firstDerivedTorSpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : DerivedDMinus R) :
    FirstDerivedTorSpectralSequenceData K L :=
  Classical.choice (first_derived_tor_spectral_sequence_exists K L)

noncomputable def secondDerivedTorSpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : DerivedDMinus R) :
    SecondDerivedTorSpectralSequenceData K L :=
  Classical.choice (second_derived_tor_spectral_sequence_exists K L)

theorem first_derived_tor_e₂_page
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : DerivedDMinus R) (p q : ℤ) :
    Nonempty (((firstDerivedTorSpectralSequenceData K L).spectralSequence.page 2).X
      (p, q) ≅
      (derivedCohomologyFunctor (Mod R) p).obj
        (derivedTensorMinusModule K (derivedCohomologyMinus L q))) := by
  exact (firstDerivedTorSpectralSequenceData K L).e₂_page p q

theorem second_derived_tor_e₂_page
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : DerivedDMinus R) (p q : ℤ) :
    Nonempty (((secondDerivedTorSpectralSequenceData K L).spectralSequence.page 2).X
      (p, q) ≅
      (derivedCohomologyFunctor (Mod R) p).obj
        (derivedTensorMinusModule L (derivedCohomologyMinus K q))) := by
  exact (secondDerivedTorSpectralSequenceData K L).e₂_page p q

/- The project already has the canonical bounded-above/projective
   replacement interface.  This predicate records the source's final
   replacement remark without changing the hypotheses of the spectral
   sequence statements. -/
def IsRepresentedByBoundedAboveProjective
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : DerivedDMinus R) : Prop :=
    ∃ P : CochainComplex (Mod R) ℤ, IsBoundedAbove P ∧
    (∀ n : ℤ, Projective (P.X n)) ∧
    Nonempty ((derivedComplexQuotient R).obj P ≅
      (derivedMinusToDerived (R := R)).obj K)

theorem exists_bounded_above_projective_representative
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : DerivedDMinus R) :
    IsRepresentedByBoundedAboveProjective K := by
  sorry

end Formalization.Books.MoreAlgebra.Unit62
