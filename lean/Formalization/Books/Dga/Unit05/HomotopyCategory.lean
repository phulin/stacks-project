import Formalization.Books.Dga.Unit04.DifferentialGradedModules
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# Differential Graded Algebra, Chapter 5: The homotopy category

The homotopies in this chapter are the homotopies of the underlying cochain
complexes together with the additional requirement that their degree `-1`
components are maps of graded right `A`-modules.  Mathlib's `Homotopy` already
supplies the degree condition and the equation involving the differentials;
the extra field below records the `A`-module condition.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit03
open Formalization.Books.Dga.Unit04

universe u

namespace Formalization.Books.Dga.Unit05

/-! ## Homotopies -/

/-- A homotopy of differential graded module maps.

The `homotopy` field is Mathlib's chain homotopy of the underlying cochain
complex maps.  Its relevant component in degree `n` is a map
`M.complex.X n ⟶ N.complex.X (n - 1)`.  The second field says that these
components commute with the homogeneous right `A`-actions.  `HEq` records the
canonical equality between the two associatively reindexed target degrees.
-/
structure DifferentialGradedModuleHomotopy
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    (f g : DifferentialGradedModuleHom M N) where
  homotopy : Homotopy f.underlying g.underlying
  map_action :
    ∀ (n m : ℤ) (x : M.complex.X n) (a : A.complex.X m),
      HEq
        ((homotopy.hom (n + m) ((n + m) - 1)).hom
          (M.actionOnHomogeneous n m x a))
        (N.actionOnHomogeneous (n - 1) m
          ((homotopy.hom n (n - 1)).hom x) a)

namespace DifferentialGradedModuleHomotopy

/-- The degree `-1` component of a differential graded module homotopy. -/
def component
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    {f g : DifferentialGradedModuleHom M N}
    (H : DifferentialGradedModuleHomotopy f g) (n : ℤ) :
    M.complex.X n →ₗ[R] N.complex.X (n - 1) :=
  (H.homotopy.hom n (n - 1)).hom

end DifferentialGradedModuleHomotopy

/-!
The following predicate is the relation used for the source's phrase
“`f` and `g` are homotopic”.  It is intentionally a proposition, while
`DifferentialGradedModuleHomotopy` retains a chosen homotopy for constructions.
-/

/-- Two differential graded module maps are homotopic when a compatible
degree `-1` homotopy exists between them. -/
def DifferentialGradedModuleHomotopic
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    (f g : DifferentialGradedModuleHom M N) : Prop :=
  Nonempty (DifferentialGradedModuleHomotopy f g)

/-- Composition in the differential graded module category, with its hom-set
type made explicit for declarations whose expected type is a homotopy. -/
def differentialGradedModuleHomComp
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    (a : DifferentialGradedModuleHom K L)
    (f : DifferentialGradedModuleHom L M) :
    DifferentialGradedModuleHom K M :=
  (differentialGradedModuleCategory A).comp a f

namespace DifferentialGradedModuleHomotopy

/-- Reflexivity of differential graded module homotopy. -/
def refl
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom M N) :
    DifferentialGradedModuleHomotopy f f where
  homotopy := Homotopy.refl f.underlying
  map_action := by sorry

/-- Symmetry of differential graded module homotopy. -/
def symm
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    {f g : DifferentialGradedModuleHom M N}
    (H : DifferentialGradedModuleHomotopy f g) :
    DifferentialGradedModuleHomotopy g f where
  homotopy := H.homotopy.symm
  map_action := by sorry

/-- Transitivity of differential graded module homotopy. -/
def trans
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    {f g h : DifferentialGradedModuleHom M N}
    (H₁ : DifferentialGradedModuleHomotopy f g)
    (H₂ : DifferentialGradedModuleHomotopy g h) :
    DifferentialGradedModuleHomotopy f h where
  homotopy := H₁.homotopy.trans H₂.homotopy
  map_action := by sorry

/-- Addition of compatible homotopies. -/
def add
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    {f₁ g₁ f₂ g₂ : DifferentialGradedModuleHom M N}
    (H₁ : DifferentialGradedModuleHomotopy f₁ g₁)
    (H₂ : DifferentialGradedModuleHomotopy f₂ g₂) :
    DifferentialGradedModuleHomotopy (f₁ + f₂) (g₁ + g₂) where
  homotopy := Homotopy.add H₁.homotopy H₂.homotopy
  map_action := by sorry

/-- Precomposition preserves compatible homotopies. -/
def compLeft
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    {f g : DifferentialGradedModuleHom L M}
    (H : DifferentialGradedModuleHomotopy f g)
    (a : DifferentialGradedModuleHom K L) :
    DifferentialGradedModuleHomotopy
      (differentialGradedModuleHomComp a f)
      (differentialGradedModuleHomComp a g) where
  homotopy := H.homotopy.compLeft a.underlying
  map_action := by sorry

/-- Postcomposition preserves compatible homotopies. -/
def compRight
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {L M N : DifferentialGradedModule A}
    {f g : DifferentialGradedModuleHom L M}
    (H : DifferentialGradedModuleHomotopy f g)
    (c : DifferentialGradedModuleHom M N) :
    DifferentialGradedModuleHomotopy
      (differentialGradedModuleHomComp f c)
      (differentialGradedModuleHomComp g c) where
  homotopy := H.homotopy.compRight c.underlying
  map_action := by sorry

/-- The homotopy obtained by pre- and postcomposing a given one. -/
def comp
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M N : DifferentialGradedModule A}
    {f g : DifferentialGradedModuleHom L M}
    (H : DifferentialGradedModuleHomotopy f g)
    (a : DifferentialGradedModuleHom K L)
    (c : DifferentialGradedModuleHom M N) :
    DifferentialGradedModuleHomotopy
      (differentialGradedModuleHomComp (differentialGradedModuleHomComp a f) c)
      (differentialGradedModuleHomComp (differentialGradedModuleHomComp a g) c) :=
  (H.compLeft a).compRight c

end DifferentialGradedModuleHomotopy

/-- Composition on either side carries a compatible homotopy to a compatible
homotopy, as in the source's composition lemma. -/
theorem differentialGradedModuleHomotopic_comp
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M N : DifferentialGradedModule A}
    {f g : DifferentialGradedModuleHom L M}
    (a : DifferentialGradedModuleHom K L)
    (c : DifferentialGradedModuleHom M N)
    (H : DifferentialGradedModuleHomotopy f g) :
    DifferentialGradedModuleHomotopic
      (differentialGradedModuleHomComp (differentialGradedModuleHomComp a f) c)
      (differentialGradedModuleHomComp (differentialGradedModuleHomComp a g) c) :=
  ⟨H.comp a c⟩

/-- Homotopy is an equivalence relation on every differential graded module
hom-set. -/
theorem differentialGradedModuleHomotopic_equivalence
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M N : DifferentialGradedModule A) :
    Equivalence (fun f g : DifferentialGradedModuleHom M N =>
      DifferentialGradedModuleHomotopic f g) := by
  refine
    { refl := fun f => ⟨DifferentialGradedModuleHomotopy.refl f⟩
      symm := ?_
      trans := ?_ }
  · intro f g h
    rcases h with ⟨H⟩
    exact ⟨H.symm⟩
  · intro f g h h₁ h₂
    rcases h₁ with ⟨H₁⟩
    rcases h₂ with ⟨H₂⟩
    exact ⟨H₁.trans H₂⟩

/-! ## The shifted-map observation -/

/-- The morphism into the `[-1]` shift represented by a homotopy from a map to
itself.

The underlying degree `-1` components are the map, the `A`-linearity is the
`map_action` field, and the chain-map condition is the homotopy equation with
`f - f = 0`. -/
noncomputable def DifferentialGradedModuleHomotopy.toShiftedMap
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    {f : DifferentialGradedModuleHom M N}
    (H : DifferentialGradedModuleHomotopy f f) :
    DifferentialGradedModuleHom M (dgmShift N (-1)) :=
  ⟨HomologicalComplex.Hom.mk
      (fun n => H.homotopy.hom n (n - 1)) (by sorry), by sorry⟩

/-- A homotopy from a map to itself therefore gives a morphism into the
`[-1]` shift. -/
noncomputable def homotopy_eq_gives_shifted_map
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    {f : DifferentialGradedModuleHom M N}
    (H : DifferentialGradedModuleHomotopy f f) :
    DifferentialGradedModuleHom M (dgmShift N (-1)) :=
  H.toShiftedMap

/-! ## The homotopy category -/

/-- The homotopy relation on the category of differential graded modules. -/
def differentialGradedModuleHomotopyRelation
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :
    HomRel (DifferentialGradedModuleCategory A) :=
  fun _ _ f g => DifferentialGradedModuleHomotopic f g

instance differentialGradedModuleHomotopyCongruence
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :
    Congruence (differentialGradedModuleHomotopyRelation A) where
  equivalence := by
    intro M N
    exact differentialGradedModuleHomotopic_equivalence M N
  comp_left := by
    intro K L M a f g h
    rcases h with ⟨H⟩
    exact ⟨H.compLeft a⟩
  comp_right := by
    intro L M N f g c h
    rcases h with ⟨H⟩
    exact ⟨H.compRight c⟩

/-- The homotopy category `K(Mod_(A,d))`. -/
abbrev DifferentialGradedModuleHomotopyCategory
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :=
  CategoryTheory.Quotient (differentialGradedModuleHomotopyRelation A)

/-- The quotient functor from differential graded modules to their homotopy
category. -/
abbrev differentialGradedModuleHomotopyQuotient
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :
    DifferentialGradedModuleCategory A ⥤
      DifferentialGradedModuleHomotopyCategory A :=
  CategoryTheory.Quotient.functor (differentialGradedModuleHomotopyRelation A)

/-- The homotopy category is preadditive, using addition of compatible
homotopies. -/
noncomputable instance differentialGradedModuleHomotopyCategoryPreadditive
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :
    Preadditive (DifferentialGradedModuleHomotopyCategory A) :=
  CategoryTheory.Quotient.preadditive
    (differentialGradedModuleHomotopyRelation A) (by
      intro M N f₁ f₂ g₁ g₂ h₁ h₂
      rcases h₁ with ⟨H₁⟩
      rcases h₂ with ⟨H₂⟩
      exact ⟨H₁.add H₂⟩)

/-! ## Direct sums and products -/

/-- The homotopy category has arbitrary products. -/
noncomputable instance differentialGradedModuleHomotopyCategoryHasProducts
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :
    HasProducts (DifferentialGradedModuleHomotopyCategory A) := by
  sorry

/-- The homotopy category has arbitrary direct sums (coproducts). -/
noncomputable instance differentialGradedModuleHomotopyCategoryHasCoproducts
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :
    HasCoproducts (DifferentialGradedModuleHomotopyCategory A) := by
  sorry

/-- Source-facing conjunction of the direct-sum and product assertions. -/
theorem differentialGradedModuleHomotopyCategory_has_directSums_and_products
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :
    HasCoproducts (DifferentialGradedModuleHomotopyCategory A) ∧
      HasProducts (DifferentialGradedModuleHomotopyCategory A) :=
  ⟨inferInstance, inferInstance⟩

end Formalization.Books.Dga.Unit05
