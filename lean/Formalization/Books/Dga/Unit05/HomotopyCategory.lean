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

private theorem differentialGradedModuleHom_underlying_add
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    (f g : DifferentialGradedModuleHom M N) :
    (f + g).underlying = f.underlying + g.underlying := by
  rfl

private theorem differentialGradedModuleHom_actionOnHomogeneous
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (a : DifferentialGradedModuleHom K L) (n m : ℤ)
    (x : K.complex.X n) (b : A.complex.X m) :
    a.underlying.f (n + m) (K.actionOnHomogeneous n m x b) =
      L.actionOnHomogeneous n m (a.underlying.f n x) b := by
  have ha := congrArg (fun q => q.f (n + m)) a.underlying_mem
  have ha' := congrArg (fun q => q.hom
    ((HomologicalComplex.ιTensorObj K.complex A.complex n m (n + m) rfl).hom
      (x ⊗ₜ[R] b))) ha
  have hi := HomologicalComplex.ι_mapBifunctorMap
    (K₁ := K.complex) (K₂ := A.complex) (L₁ := L.complex) (L₂ := A.complex)
    (f₁ := a.underlying) (f₂ := 𝟙 A.complex)
    (F := MonoidalCategory.curriedTensor (ModuleCat.{u} R))
    (c₁ := ComplexShape.up ℤ) (c₂ := ComplexShape.up ℤ) (c := ComplexShape.up ℤ)
    (i₁ := n) (i₂ := m) (j := n + m) (h := rfl)
  have hi' := congrArg (fun q => q.hom (x ⊗ₜ[R] b)) hi
  have hi'' :
      ((tensorHomComplex a.underlying (𝟙 A.complex)).f (n + m)).hom
          ((HomologicalComplex.ιTensorObj K.complex A.complex n m (n + m) rfl).hom
            (x ⊗ₜ[R] b)) =
        (HomologicalComplex.ιTensorObj L.complex A.complex n m (n + m) rfl).hom
          ((a.underlying.f n).hom x ⊗ₜ[R] b) := by
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hi'
    have hi''' := hi'
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
      HomologicalComplex.id_f] at hi'''
    exact hi'''
  change
    (a.underlying.f (n + m)).hom
        ((K.action.f (n + m)).hom
          ((HomologicalComplex.ιTensorObj K.complex A.complex n m (n + m) rfl).hom
            (x ⊗ₜ[R] b))) =
      (L.action.f (n + m)).hom
        (((tensorHomComplex a.underlying (𝟙 A.complex)).f (n + m)).hom
          ((HomologicalComplex.ιTensorObj K.complex A.complex n m (n + m) rfl).hom
            (x ⊗ₜ[R] b))) at ha'
  rw [hi''] at ha'
  simpa [DifferentialGradedModule.actionOnHomogeneous,
    DifferentialGradedModule.homogeneousAction,
    ModuleCat.MonoidalCategory.tensorHom_tmul] using ha'

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
  rw [TensorProduct.add_tmul]
  rw [map_add]
  have h₁ := H₁.map_action n m x a
  have h₂ := H₂.map_action n m x a
  rw [show (n + m) - 1 = (n - 1) + m by omega] at h₁ h₂
  exact congrArg₂ (· + ·) (eq_of_heq h₁) (eq_of_heq h₂)

/-- Addition of compatible homotopies. -/
theorem differentialGradedModuleHomotopy_add
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    {f₁ g₁ f₂ g₂ : DifferentialGradedModuleHom M N}
    (H₁ : DifferentialGradedModuleHomotopy f₁ g₁)
    (H₂ : DifferentialGradedModuleHomotopy f₂ g₂) :
    Nonempty (DifferentialGradedModuleHomotopy (f₁ + f₂) (g₁ + g₂)) := by
  refine ⟨{ homotopy := ?_, map_action := ?_ }⟩
  · refine
      { hom := H₁.homotopy.hom + H₂.homotopy.hom
        zero := fun i j hij => by
          simp [H₁.homotopy.zero i j hij,
            H₂.homotopy.zero i j hij]
        comm := fun i => by
          have h₁ := H₁.homotopy.comm i
          have h₂ := H₂.homotopy.comm i
          simp only [differentialGradedModuleHom_underlying_add,
            AddMonoidHom.map_add]
          change f₁.underlying.f i + f₂.underlying.f i =
            (dNext i) H₁.homotopy.hom + (dNext i) H₂.homotopy.hom +
              ((prevD i) H₁.homotopy.hom + (prevD i) H₂.homotopy.hom) +
                (g₁.underlying.f i + g₂.underlying.f i)
          rw [h₁, h₂]
          abel }
  · intro n m x a
    simp [DifferentialGradedModule.actionOnHomogeneous]
    rw [show (n + m) - 1 = (n - 1) + m by omega]
    apply heq_of_eq
    rw [TensorProduct.add_tmul]
    rw [map_add]
    have h₁ := H₁.map_action n m x a
    have h₂ := H₂.map_action n m x a
    rw [show (n + m) - 1 = (n - 1) + m by omega] at h₁ h₂
    exact congrArg₂ (· + ·) (eq_of_heq h₁) (eq_of_heq h₂)

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
  refine ⟨?_, ?_⟩
  · refine
      { hom := fun i j => a.underlying.f i ≫ H.homotopy.hom i j
        zero := fun i j hij => by
          rw [H.homotopy.zero i j hij, comp_zero]
        comm := fun i => by
          change a.underlying.f i ≫ f.underlying.f i = _
          rw [H.homotopy.comm i]
          simp only [Preadditive.comp_add, dNext_comp_left,
            prevD_comp_left, differentialGradedModuleHomComp]
          rfl }
  intro n m x b
  have ha := differentialGradedModuleHom_actionOnHomogeneous a n m x b
  have hh := H.map_action n m (a.underlying.f n x) b
  have ha'' := congrArg
    (fun z => (H.homotopy.hom (n + m) ((n + m) - 1)).hom z) ha
  rw [show (n + m) - 1 = (n - 1) + m by omega] at hh ha'' ⊢
  apply heq_of_eq
  simpa [DifferentialGradedModule.actionOnHomogeneous] using
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
  refine ⟨?_, ?_⟩
  · refine
      { hom := fun i j => H.homotopy.hom i j ≫ c.underlying.f j
        zero := fun i j hij => by
          rw [H.homotopy.zero i j hij, zero_comp]
        comm := fun i => by
          change f.underlying.f i ≫ c.underlying.f i = _
          rw [H.homotopy.comm i]
          simp only [Preadditive.add_comp, dNext_comp_right,
            prevD_comp_right, differentialGradedModuleHomComp]
          rfl }
  · intro n m x b
    have hh := H.map_action n m x b
    have hc := differentialGradedModuleHom_actionOnHomogeneous c (n - 1) m
      ((H.homotopy.hom n (n - 1)).hom x) b
    rw [show (n + m) - 1 = (n - 1) + m by omega] at hh ⊢
    apply heq_of_eq
    have hh' := congrArg (fun z => c.underlying.f ((n - 1) + m) z) (eq_of_heq hh)
    simpa [DifferentialGradedModule.actionOnHomogeneous] using hh'.trans hc

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
