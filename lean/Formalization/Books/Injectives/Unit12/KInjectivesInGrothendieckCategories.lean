import Formalization.Books.Injectives.Unit11.InjectivesInGrothendieckCategories
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Injectives, Chapter 12: K-injectives in Grothendieck categories

This file records the statements in the source section.  Complexes are
Mathlib's cochain complexes indexed by `ℤ`, K-injectivity is
`CochainComplex.IsKInjective`, and the size of an object is the canonical
Chapter 11 subobject cardinal.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Formalization.Books.Injectives.Unit12

abbrev Complex (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  CochainComplex C ℤ

abbrev KCategory (C : Type u) [Category.{v} C] [Preadditive C] :=
  HomotopyCategory C (ComplexShape.up ℤ)

/-! ## Complexes, boundedness, and size bounds -/

/-- A cochain complex is bounded above when it is zero in sufficiently high
degrees.  This is the canonical `IsStrictlyLE` support predicate. -/
def IsBoundedAbove {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (K : Complex C) : Prop :=
  ∃ n : ℤ, K.IsStrictlyLE n

/-- The Chapter 11 size bound applied degreewise to a complex. -/
def ComplexSizeAtMost {C : Type u} [Category.{v} C] [Abelian C]
    (κ : Cardinal.{max u v}) (K : Complex C) : Prop :=
  ∀ n : ℤ,
    Formalization.Books.Injectives.Unit11.objectSize (K.X n) ≤ κ

/-- A bounded-above acyclic complex all of whose terms have size at most `κ`.
-/
def BoundedAboveAcyclicOfSizeAtMost
    {C : Type u} [Category.{v} C] [Abelian C]
    (κ : Cardinal.{max u v}) (K : Complex C) : Prop :=
  IsBoundedAbove K ∧ K.Acyclic ∧ ComplexSizeAtMost κ K

/-- The cardinal function `c` in the first source lemma. -/
noncomputable def surjectionBound
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    (U : C) (κ : Cardinal.{max u v}) : Cardinal.{max u v} :=
  Formalization.Books.Injectives.Unit11.objectSize
    (∐ fun _ : κ.out => U)

/-! ## Small subobjects and small acyclic complexes -/

/-- A surjection has a subobject source of the size prescribed by the source's
cardinal function. -/
theorem surjection_bounded_size
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    (U : C) (hU : IsSeparator U) {M N : C} (π : M ⟶ N) (hπ : Epi π) :
    ∃ M' : Subobject M,
      Epi (M'.arrow ≫ π) ∧
        Formalization.Books.Injectives.Unit11.objectSize (M' : C) ≤
          surjectionBound U
            (Formalization.Books.Injectives.Unit11.objectSize N) := by
  sorry

/-- A cardinal bound controls bounded-above acyclic subcomplexes and gives a
coproduct epimorphism from such complexes onto every acyclic complex. -/
def AcyclicComplexBound
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    (κ : Cardinal.{max u v}) : Prop :=
  ∀ (M : Complex C), M.Acyclic →
    ((¬ IsZero M) →
      ∃ P : Subobject M,
        ¬ IsZero (P : Complex C) ∧
          BoundedAboveAcyclicOfSizeAtMost κ (P : Complex C)) ∧
    ∃ (I : Type (max u v)) (Mᵢ : I → Complex C)
      (f : (∐ Mᵢ) ⟶ M),
      Epi f ∧ ∀ i : I, BoundedAboveAcyclicOfSizeAtMost κ (Mᵢ i)

/-- Lemma `acyclic-quotient-complexes-bounded-size`. -/
theorem acyclic_quotient_complexes_bounded_size
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C] :
    ∃ κ : Cardinal.{max u v}, AcyclicComplexBound (C := C) κ := by
  sorry

/-! ## The K-injective criterion -/

/-- Vanishing of a Hom group in the homotopy category `K(C)`. -/
def HomZeroInK
    {C : Type u} [Category.{v} C] [Abelian C]
    (M I : Complex C) : Prop :=
  ∀ f : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I,
    f = 0

/-- Lemma `characterize-K-injective`, using Mathlib's canonical
`CochainComplex.IsKInjective` predicate. -/
theorem characterize_K_injective
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    (κ : Cardinal.{max u v}) (hκ : AcyclicComplexBound (C := C) κ)
    (I : Complex C) (hI : ∀ j : ℤ, Injective (I.X j))
    (hsmall : ∀ (M : Complex C), IsBoundedAbove M → M.Acyclic →
      ComplexSizeAtMost κ M → HomZeroInK M I) :
    I.IsKInjective := by
  sorry

/-! ## Functorial homotopy killing -/

/-- A map of complexes is termwise monomorphic. -/
def TermwiseMono
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : Complex C} (f : K ⟶ L) : Prop :=
  ∀ n : ℤ, Mono (f.f n)

/-- A complex is termwise injective. -/
def TermwiseInjective
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : Complex C) : Prop :=
  ∀ n : ℤ, Injective (K.X n)

/-! The source's suggested choice for the auxiliary complex `Lᵢ` is the
mapping cone of the identity.  We expose Mathlib's canonical cone rather than
introducing a second contractible-complex construction. -/

/-- The mapping cone of the identity of a complex. -/
noncomputable def identityCone
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : Complex C) : Complex C :=
  CochainComplex.mappingCone (𝟙 K)

/-- The canonical inclusion of `K` into its identity cone. -/
noncomputable def identityConeEmbedding
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : Complex C) : K ⟶ identityCone K :=
  CochainComplex.mappingCone.inr (𝟙 K)

/-- The identity cone is acyclic. -/
theorem identityCone_acyclic
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : Complex C) : (identityCone K).Acyclic := by
  sorry

/-- The identity-cone inclusion is termwise monomorphic. -/
theorem identityConeEmbedding_termwise_mono
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : Complex C) : TermwiseMono (identityConeEmbedding K) := by
  sorry

/-- The identity-cone inclusion is null-homotopic. -/
theorem identityConeEmbedding_homotopy_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : Complex C) :
    Nonempty (Homotopy (identityConeEmbedding K) 0) := by
  sorry

/-- The data supplied by the source's functorial homotopy-killing lemma. -/
structure FunctorialHomotopyData
    {C : Type u} [Category.{v} C] [Abelian C]
    {I : Type w} (K : I → Complex C) where
  acyclic : ∀ i : I, (K i).Acyclic
  functor : Complex C ⥤ Complex C
  j : 𝟭 (Complex C) ⟶ functor
  j_termwise_mono : ∀ M : Complex C, TermwiseMono (j.app M)
  j_quasiIso : ∀ M : Complex C, QuasiIso (j.app M)
  homotopy_zero :
    ∀ (i : I) (M : Complex C) (w : K i ⟶ M),
      Nonempty (Homotopy (w ≫ j.app M) 0)

/-- Lemma `functorial-homotopies`. -/
theorem functorial_homotopies
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    {I : Type w} (K : I → Complex C) (hK : ∀ i : I, (K i).Acyclic) :
    Nonempty (FunctorialHomotopyData K) := by
  sorry

/-! ## Functorial termwise injective enlargement -/

/-- The factorization through an injective subobject required by the source's
functorial-injective lemma. -/
structure FunctorialInjectiveData
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C] where
  functor : Complex C ⥤ Complex C
  j : 𝟭 (Complex C) ⟶ functor
  j_termwise_mono : ∀ M : Complex C, TermwiseMono (j.app M)
  j_quasiIso : ∀ M : Complex C, QuasiIso (j.app M)
  factors_through_injective :
    ∀ (M : Complex C) (n : ℤ),
      ∃ (I : Subobject ((functor.obj M).X n))
        (g : M.X n ⟶ (I : C)),
        Injective (I : C) ∧ g ≫ I.arrow = (j.app M).f n

/-- Lemma `functorial-injective`. -/
theorem functorial_injective
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C] :
    Nonempty (FunctorialInjectiveData (C := C)) := by
  sorry

/-! ## The functorial K-injective embedding -/

/-- A K-injective resolution of a specified complex, with the source's
termwise monomorphism and injectivity requirements. -/
structure KInjectiveEmbedding
    {C : Type u} [Category.{v} C] [Abelian C]
    (M : Complex C) where
  target : Complex C
  map : M ⟶ target
  map_quasiIso : QuasiIso map
  map_termwise_mono : TermwiseMono map
  target_termwise_injective : TermwiseInjective target
  target_K_injective : target.IsKInjective

/-- The functorial form of a K-injective embedding. -/
structure FunctorialKInjectiveEmbedding
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C] where
  functor : Complex C ⥤ Complex C
  j : 𝟭 (Complex C) ⟶ functor
  j_quasiIso : ∀ M : Complex C, QuasiIso (j.app M)
  j_termwise_mono : ∀ M : Complex C, TermwiseMono (j.app M)
  functor_termwise_injective : ∀ M : Complex C, TermwiseInjective (functor.obj M)
  functor_K_injective : ∀ M : Complex C, (functor.obj M).IsKInjective

/-- Forgetting the functorial packaging gives the resolution of one complex.
-/
noncomputable def FunctorialKInjectiveEmbedding.resolution
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    (D : FunctorialKInjectiveEmbedding (C := C)) (M : Complex C) :
    KInjectiveEmbedding M where
  target := D.functor.obj M
  map := D.j.app M
  map_quasiIso := D.j_quasiIso M
  map_termwise_mono := D.j_termwise_mono M
  target_termwise_injective := D.functor_termwise_injective M
  target_K_injective := D.functor_K_injective M

/-- Theorem `K-injective-embedding-grothendieck`. -/
theorem K_injective_embedding_grothendieck
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C] :
    Nonempty (FunctorialKInjectiveEmbedding (C := C)) := by
  sorry

/-- The non-functorial first sentence of the source theorem follows from its
functorial form. -/
theorem exists_K_injective_embedding
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C] (M : Complex C) :
    Nonempty (KInjectiveEmbedding M) := by
  obtain ⟨D⟩ := K_injective_embedding_grothendieck (C := C)
  exact ⟨D.resolution M⟩

end Formalization.Books.Injectives.Unit12
