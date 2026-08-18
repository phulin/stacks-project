import Formalization.Books.Dga.Unit06.Cone

/-!
# Differential Graded Algebra, Chapter 7: Admissible short exact sequences

The source distinguishes maps of differential graded modules from maps of the
underlying graded modules.  The small `DgmGradedHom` interface below records
exactly the latter maps, including compatibility with the graded `A`-action
but not with the differential.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit03
open Formalization.Books.Dga.Unit04
open Formalization.Books.Dga.Unit05
open Formalization.Books.Dga.Unit06

universe u

namespace Formalization.Books.Dga.Unit07

/-! ## Graded module maps and admissibility -/

/-- A degree-zero map of the underlying graded right `A`-modules.

The components preserve the grading and the `map_action` field is the
graded-module condition.  No compatibility with the differential is imposed.
-/
structure DgmGradedHom
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M N : DifferentialGradedModule A) where
  component : ∀ n : ℤ, M.complex.X n →ₗ[R] N.complex.X n
  map_action : ∀ (n m : ℤ) (x : M.complex.X n) (a : A.complex.X m),
    component (n + m) (M.actionOnHomogeneous n m x a) =
      N.actionOnHomogeneous n m (component n x) a

namespace DgmGradedHom

/-- The identity map of the underlying graded module. -/
def id
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) : DgmGradedHom M M where
  component n := LinearMap.id
  map_action := by
    intro n m x a
    rfl

/-- Composition of maps of underlying graded modules. -/
def comp
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    (f : DgmGradedHom K L) (g : DgmGradedHom L M) : DgmGradedHom K M where
  component n := (g.component n).comp (f.component n)
  map_action := by
    intro n m x a
    change g.component (n + m) (f.component (n + m)
        (K.actionOnHomogeneous n m x a)) =
      M.actionOnHomogeneous n m (g.component n (f.component n x)) a
    rw [f.map_action, g.map_action]

@[simp]
theorem comp_component
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    (f : DgmGradedHom K L) (g : DgmGradedHom L M) (n : ℤ)
    (x : K.complex.X n) :
    (comp f g).component n x = g.component n (f.component n x) := rfl

end DgmGradedHom

/-- A graded left inverse for a differential graded module homomorphism. -/
def DgmGradedLeftInverse
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) (r : DgmGradedHom L K) : Prop :=
  ∀ (n : ℤ) (x : K.complex.X n), r.component n (f.underlying.f n x) = x

/-- A graded right inverse for a differential graded module homomorphism. -/
def DgmGradedRightInverse
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {L M : DifferentialGradedModule A}
(g : DifferentialGradedModuleHom L M) (s : DgmGradedHom M L) : Prop :=
  ∀ (n : ℤ) (x : L.complex.X n), s.component n (g.underlying.f n x) = x

/-- The source's notion of an admissible monomorphism. -/
def DgmAdmissibleMonomorphism
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) : Prop :=
  ∃ r : DgmGradedHom L K, DgmGradedLeftInverse f r

/-- The source's notion of an admissible epimorphism. -/
def DgmAdmissibleEpimorphism
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {L M : DifferentialGradedModule A}
    (g : DifferentialGradedModuleHom L M) : Prop :=
  ∃ s : DgmGradedHom M L, DgmGradedRightInverse g s

/-- Splitting data for a short complex after forgetting differentials. -/
structure DgmGradedSplitting
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (S : ShortComplex (DifferentialGradedModuleCategory A)) where
  sectionMap : DgmGradedHom S.X₃ S.X₂
  retraction : DgmGradedHom S.X₂ S.X₁
  section_rightInverse : DgmGradedRightInverse S.g sectionMap
  retraction_leftInverse : DgmGradedLeftInverse S.f retraction

/-- An admissible short exact sequence of differential graded modules. -/
structure DgmAdmissibleShortExactSequence
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (S : ShortComplex (DifferentialGradedModuleCategory A)) : Prop where
  shortExact : S.ShortExact
  splitting : Nonempty (DgmGradedSplitting S)

/-! ## The connecting morphism -/

/-- The componentwise formula `π d_L s`, regarded as a map into `K[1]`. -/
def dgmConnectingComponent
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
  (s : DgmGradedHom M L) (π : DgmGradedHom L K) (n : ℤ) :
    M.complex.X n →ₗ[R] (dgmShift K (1 : ℤ)).complex.X n :=
  ((π.component (n + 1)).comp (L.complex.d n (n + 1)).hom).comp
    (s.component n)

/-- The condition on the chosen splitting in the connecting-morphism lemma. -/
def DgmGradedKernelEqImage
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    (s : DgmGradedHom M L) (π : DgmGradedHom L K) : Prop :=
  ∀ n : ℤ, {x | π.component n x = 0} = Set.range (s.component n)

/-- Data expressing the source's connecting morphism and its effect on
cohomology. -/
structure DgmConnectingMapData
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S)
    (s : DgmGradedHom S.X₃ S.X₂) (π : DgmGradedHom S.X₂ S.X₁) where
  map : DifferentialGradedModuleHom S.X₃ (dgmShift S.X₁ (1 : ℤ))
  component_eq : ∀ (n : ℤ) (x : S.X₃.complex.X n),
    map.underlying.f n x = dgmConnectingComponent s π n x
  induces_boundary : ∀ n : ℤ,
    dgmCohomologyMap map n ≫
        (dgmShiftCohomologyIso S.X₁ (1 : ℤ) n).hom =
      dgmConnectingMap hS.shortExact n

/-- The connecting morphism furnished by an admissible short exact sequence. -/
theorem dgmConnectingMapData_exists
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S)
    (s : DgmGradedHom S.X₃ S.X₂) (π : DgmGradedHom S.X₂ S.X₁)
    (hs : DgmGradedRightInverse S.g s)
    (hπ : DgmGradedLeftInverse S.f π)
    (hker : DgmGradedKernelEqImage s π) :
    Nonempty (DgmConnectingMapData hS s π) := by
  sorry

/-- The source-facing connecting-morphism assertion. -/
theorem admissibleShortExactSequence_connecting_morphism
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S)
    (s : DgmGradedHom S.X₃ S.X₂) (π : DgmGradedHom S.X₂ S.X₁)
    (hs : DgmGradedRightInverse S.g s)
    (hπ : DgmGradedLeftInverse S.f π)
    (hker : DgmGradedKernelEqImage s π) :
    Nonempty (DgmConnectingMapData hS s π) :=
  dgmConnectingMapData_exists hS s π hs hπ hker

/-! ## Homotopy-commuting squares -/

/-- A homotopy equivalence of differential graded module maps. -/
def DgmHomotopyEquivalence
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom M N) : Prop :=
  ∃ inverse : DifferentialGradedModuleHom N M,
    DifferentialGradedModuleHomotopic
        (differentialGradedModuleHomComp f inverse) (𝟙 M) ∧
      DifferentialGradedModuleHomotopic
        (differentialGradedModuleHomComp inverse f) (𝟙 N)

/-- If the left map of a homotopy-commuting square is admissible, the right
map can be changed within its homotopy class to make the square commute. -/
theorem dgm_make_commute_of_admissible_mono
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M N : DifferentialGradedModule A}
    {f : DifferentialGradedModuleHom K L}
    {a : DifferentialGradedModuleHom K M}
    {b : DifferentialGradedModuleHom L N}
    {g : DifferentialGradedModuleHom M N}
    (hcomm : DifferentialGradedModuleHomotopic
      (differentialGradedModuleHomComp f b)
      (differentialGradedModuleHomComp a g))
    (hf : DgmAdmissibleMonomorphism f) :
    ∃ b' : DifferentialGradedModuleHom L N,
      DifferentialGradedModuleHomotopic b b' ∧
        differentialGradedModuleHomComp f b' =
          differentialGradedModuleHomComp a g := by
  sorry

/-- If the right map of a homotopy-commuting square is admissible, the left
map can be changed within its homotopy class to make the square commute. -/
theorem dgm_make_commute_of_admissible_epi
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M N : DifferentialGradedModule A}
    {f : DifferentialGradedModuleHom K L}
    {a : DifferentialGradedModuleHom K M}
    {b : DifferentialGradedModuleHom L N}
    {g : DifferentialGradedModuleHom M N}
    (hcomm : DifferentialGradedModuleHomotopic
      (differentialGradedModuleHomComp f b)
      (differentialGradedModuleHomComp a g))
    (hg : DgmAdmissibleEpimorphism g) :
    ∃ a' : DifferentialGradedModuleHom K M,
      DifferentialGradedModuleHomotopic a a' ∧
        differentialGradedModuleHomComp f b =
          differentialGradedModuleHomComp a' g := by
  sorry

/-! ## Cone factorization -/

/-- Factorization data from the source's cone construction. -/
structure DgmAdmissibleFactorization
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (α : DifferentialGradedModuleHom K L) where
  middle : DifferentialGradedModule A
  inclusion : DifferentialGradedModuleHom K middle
  projection : DifferentialGradedModuleHom middle L
  sectionMap : DifferentialGradedModuleHom L middle
  factorization : differentialGradedModuleHomComp inclusion projection = α
  inclusion_admissible : DgmAdmissibleMonomorphism inclusion
  projection_section :
    differentialGradedModuleHomComp sectionMap projection = 𝟙 L
  section_projection_homotopic : DifferentialGradedModuleHomotopic
    (differentialGradedModuleHomComp projection sectionMap) (𝟙 middle)

/-- Every differential graded module map admits the source's admissible
factorization, obtained from `L ⊕ C(1_K)`. -/
theorem dgm_make_injective
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (α : DifferentialGradedModuleHom K L) :
    Nonempty (DgmAdmissibleFactorization α) := by
  sorry

/-! ## Replacing a finite sequence by admissible monomorphisms -/

/-- A finite sequence of composable differential graded module maps. -/
structure DgmComposableSequence
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) (n : ℕ) where
  object : Fin (n + 1) → DifferentialGradedModule A
  map : ∀ i : Fin n,
    DifferentialGradedModuleHom (object i.castSucc) (object i.succ)

/-- The chosen homotopy equivalence `Mᵢ → Lᵢ` in the sequence replacement. -/
def DgmSequenceVertical
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} {n : ℕ}
    (M L : DgmComposableSequence A n) : Type _ :=
  ∀ i : Fin (n + 1),
    DifferentialGradedModuleHom (M.object i) (L.object i)

/-- The finite sequence lemma from the source. -/
theorem dgm_sequence_maps_split
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} {n : ℕ}
    (L : DgmComposableSequence A n) :
    ∃ M : DgmComposableSequence A n,
      ∃ v : DgmSequenceVertical M L,
        (∀ i : Fin n, DgmAdmissibleMonomorphism (M.map i)) ∧
        (∀ i : Fin (n + 1), DgmHomotopyEquivalence (v i)) ∧
        (∀ i : Fin n,
          differentialGradedModuleHomComp (M.map i) (v i.succ) =
            differentialGradedModuleHomComp (v i.castSucc) (L.map i)) := by
  sorry

/-! ## Nilpotence -/

/-- The two homotopy-commuting squares attached to a map of admissible short
exact sequences, with zero maps on the outside terms. -/
structure DgmNilpotentSquareData
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S₁ S₂ : ShortComplex (DifferentialGradedModuleCategory A)}
    (b : DifferentialGradedModuleHom S₁.X₂ S₂.X₂) where
  left : DifferentialGradedModuleHomotopic
    (differentialGradedModuleHomComp S₁.f b)
    (differentialGradedModuleHomComp (0 : DifferentialGradedModuleHom S₁.X₁ S₂.X₁) S₂.f)
  right : DifferentialGradedModuleHomotopic
    (differentialGradedModuleHomComp b S₂.g)
    (differentialGradedModuleHomComp S₁.g (0 : DifferentialGradedModuleHom S₁.X₃ S₂.X₃))

/-- If two consecutive maps have the homotopy-commuting zero-boundary
squares from the source, their composite is null-homotopic. -/
theorem dgm_nilpotent
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S₁ S₂ S₃ : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS₁ : DgmAdmissibleShortExactSequence S₁)
    (hS₂ : DgmAdmissibleShortExactSequence S₂)
    (hS₃ : DgmAdmissibleShortExactSequence S₃)
    {b : DifferentialGradedModuleHom S₁.X₂ S₂.X₂}
    {b' : DifferentialGradedModuleHom S₂.X₂ S₃.X₂}
    (h₁ : DgmNilpotentSquareData b)
    (h₂ : DgmNilpotentSquareData b') :
    DifferentialGradedModuleHomotopic
      (differentialGradedModuleHomComp b b')
      (0 : DifferentialGradedModuleHom S₁.X₂ S₃.X₂) := by
  sorry

end Formalization.Books.Dga.Unit07
