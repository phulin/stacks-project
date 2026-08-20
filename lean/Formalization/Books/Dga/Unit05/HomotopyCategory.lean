import Formalization.Books.Dga.Unit04.DifferentialGradedModules
import Mathlib.Algebra.Homology.HomotopyCategory

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
  map_action := by
    intro n m x a
    simp [Homotopy.refl, Homotopy.ofEq,
      DifferentialGradedModule.actionOnHomogeneous]
    rw [show (n + m) - 1 = (n - 1) + m by omega]

end DifferentialGradedModuleHomotopy

/-! The following theorem interfaces record the closure properties of the
source's homotopy relation.  Their proofs are proposition proofs and are
intentionally left for the prove stage; the declarations expose the
interfaces needed by the quotient category. -/

/-- Symmetry of a compatible homotopy. -/
theorem differentialGradedModuleHomotopy_symm
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    {f g : DifferentialGradedModuleHom M N}
    (H : DifferentialGradedModuleHomotopy f g) :
    Nonempty (DifferentialGradedModuleHomotopy g f) := by
  refine ⟨{ homotopy := H.homotopy.symm, map_action := ?_ }⟩
  intro n m x a
  have h := H.map_action n m x a
  rw [show (n + m) - 1 = (n - 1) + m by omega] at h
  have h' := congrArg (fun z => -z) (eq_of_heq h)
  simp [Homotopy.symm, DifferentialGradedModule.actionOnHomogeneous,
    TensorProduct.neg_tmul]
  rw [show (n + m) - 1 = (n - 1) + m by omega]
  apply heq_of_eq
  exact h'

/-- Transitivity of compatible homotopies. -/
theorem differentialGradedModuleHomotopy_trans
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    {f g h : DifferentialGradedModuleHom M N}
    (H₁ : DifferentialGradedModuleHomotopy f g)
    (H₂ : DifferentialGradedModuleHomotopy g h) :
    Nonempty (DifferentialGradedModuleHomotopy f h) := by
  refine ⟨{ homotopy := H₁.homotopy.trans H₂.homotopy, map_action := ?_ }⟩
  intro n m x a
  simp [Homotopy.trans, DifferentialGradedModule.actionOnHomogeneous]
  rw [show (n + m) - 1 = (n - 1) + m by omega]
  apply heq_of_eq
  rw [map_add]
  rw [TensorProduct.add_tmul]
  exact (H₁.map_action n m x a).trans (H₂.map_action n m x a)

/-- Addition of compatible homotopies. -/
theorem differentialGradedModuleHomotopy_add
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    {f₁ g₁ f₂ g₂ : DifferentialGradedModuleHom M N}
    (H₁ : DifferentialGradedModuleHomotopy f₁ g₁)
    (H₂ : DifferentialGradedModuleHomotopy f₂ g₂) :
    Nonempty (DifferentialGradedModuleHomotopy (f₁ + f₂) (g₁ + g₂)) := by
  refine ⟨{ homotopy := H₁.homotopy.add H₂.homotopy, map_action := ?_ }⟩
  intro n m x a
  simp [Homotopy.add, DifferentialGradedModule.actionOnHomogeneous]
  rw [show (n + m) - 1 = (n - 1) + m by omega]
  apply heq_of_eq
  rw [map_add]
  rw [TensorProduct.add_tmul]
  rw [add_assoc]
  exact congrArg₂ (· + ·) (eq_of_heq (H₁.map_action n m x a))
    (eq_of_heq (H₂.map_action n m x a))

/-- Precomposition preserves compatible homotopies. -/
theorem differentialGradedModuleHomotopy_comp_left
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    {f g : DifferentialGradedModuleHom L M}
    (a : DifferentialGradedModuleHom K L)
    (H : DifferentialGradedModuleHomotopy f g) :
    Nonempty (DifferentialGradedModuleHomotopy
      (differentialGradedModuleHomComp a f)
      (differentialGradedModuleHomComp a g)) := by
  refine ⟨{ homotopy :=
      { hom := fun i j => a.underlying.f i ≫ H.homotopy.hom i j
        zero := fun i j hij => by
          rw [H.homotopy.zero i j hij, comp_zero]
        comm := fun i => by
          change a.underlying.f i ≫ f.underlying.f i = _
          rw [H.homotopy.comm i]
          simp [dNext_comp_left, prevD, Category.assoc] },
    map_action := ?_ }⟩
  intro n m x b
  have ha := congrArg (fun q => q.f (n + m)) a.underlying_mem
  have ha' := congrArg (fun q => q.hom (x ⊗ₜ[R] b)) ha
  have hh := H.map_action n m (a.underlying.f n x) b
  have ha'' := congrArg
    (fun z => (H.homotopy.hom (n + m) ((n + m) - 1)).hom z) ha'
  rw [show (n + m) - 1 = (n - 1) + m by omega] at hh ⊢
  apply heq_of_eq
  simpa [DifferentialGradedModule.actionOnHomogeneous, tensorHomComplex,
    Category.assoc, ModuleCat.MonoidalCategory.tensorHom_tmul] using
    ha''.trans (eq_of_heq hh)

/-- Postcomposition preserves compatible homotopies. -/
theorem differentialGradedModuleHomotopy_comp_right
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {L M N : DifferentialGradedModule A}
    {f g : DifferentialGradedModuleHom L M}
    (c : DifferentialGradedModuleHom M N)
    (H : DifferentialGradedModuleHomotopy f g) :
    Nonempty (DifferentialGradedModuleHomotopy
      (differentialGradedModuleHomComp f c)
      (differentialGradedModuleHomComp g c)) := by
  refine ⟨{ homotopy :=
      { hom := fun i j => H.homotopy.hom i j ≫ c.underlying.f j
        zero := fun i j hij => by
          rw [H.homotopy.zero i j hij, zero_comp]
        comm := fun i => by
          change f.underlying.f i ≫ c.underlying.f i = _
          rw [H.homotopy.comm i]
          simp [dNext_comp_right, prevD, Category.assoc,
            ← c.underlying.comm] },
    map_action := ?_ }⟩
  intro n m x b
  have hh := H.map_action n m x b
  have hc := congrArg (fun q => q.f ((n - 1) + m)) c.underlying_mem
  have hc' := congrArg (fun q => q.hom
    ((H.homotopy.hom n (n - 1)).hom x ⊗ₜ[R] b)) hc
  rw [show (n + m) - 1 = (n - 1) + m by omega] at hh ⊢
  apply heq_of_eq
  have hh' := congrArg (fun z => c.underlying.f ((n - 1) + m) z) (eq_of_heq hh)
  simpa [DifferentialGradedModule.actionOnHomogeneous, tensorHomComplex,
    Category.assoc, ModuleCat.MonoidalCategory.tensorHom_tmul] using
    hh'.trans hc'

/-- The source's composition lemma: a homotopy remains a homotopy after
pre- and postcomposition. -/
theorem differentialGradedModuleHomotopy_comp
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M N : DifferentialGradedModule A}
    {f g : DifferentialGradedModuleHom L M}
    (a : DifferentialGradedModuleHom K L)
    (c : DifferentialGradedModuleHom M N)
    (H : DifferentialGradedModuleHomotopy f g) :
    Nonempty (DifferentialGradedModuleHomotopy
      (differentialGradedModuleHomComp (differentialGradedModuleHomComp a f) c)
      (differentialGradedModuleHomComp (differentialGradedModuleHomComp a g) c)) := by
  rcases differentialGradedModuleHomotopy_comp_left a H with ⟨H'⟩
  exact differentialGradedModuleHomotopy_comp_right c H'

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
  differentialGradedModuleHomotopy_comp a c H

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
    exact differentialGradedModuleHomotopy_symm H
  · intro f g h h₁ h₂
    rcases h₁ with ⟨H₁⟩
    rcases h₂ with ⟨H₂⟩
    exact differentialGradedModuleHomotopy_trans H₁ H₂

/-! ## The shifted-map observation -/

/-- A homotopy from a map to itself gives a morphism into the `[-1]` shift.

The underlying degree `-1` components are the map, the `A`-linearity is the
`map_action` field, and the chain-map condition is the homotopy equation with
`f - f = 0`.  The existence proof is left for the prove stage. -/
theorem homotopy_eq_gives_shifted_map_exists
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    {f : DifferentialGradedModuleHom M N}
    (H : DifferentialGradedModuleHomotopy f f) :
    Nonempty (DifferentialGradedModuleHom M (dgmShift N (-1))) := by
  sorry

/-- A chosen morphism into the `[-1]` shift associated to a self-homotopy. -/
noncomputable def DifferentialGradedModuleHomotopy.toShiftedMap
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    {f : DifferentialGradedModuleHom M N}
    (H : DifferentialGradedModuleHomotopy f f) :
    DifferentialGradedModuleHom M (dgmShift N (-1)) :=
  Classical.choice (homotopy_eq_gives_shifted_map_exists H)

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
    exact differentialGradedModuleHomotopy_comp_left a H
  comp_right := by
    intro L M N f g c h
    rcases h with ⟨H⟩
    exact differentialGradedModuleHomotopy_comp_right c H

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
      exact differentialGradedModuleHomotopy_add H₁ H₂)

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
