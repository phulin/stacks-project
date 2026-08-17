import Formalization.Books.Homology.Unit14.HomotopyAndShift
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-!
# Homological Algebra, Chapter 15: Truncation of complexes

The source distinguishes brutal ("stupid") truncations from the canonical
truncations.  Mathlib's `stupidTrunc`, `truncLE`, and `truncGE` are the
canonical categorical constructions used below.  Componentwise equality with
zero is expressed by `IsZero`, and componentwise equality with an original
term is expressed by an isomorphism, since zero objects and categorical
quotients are only determined up to canonical isomorphism.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open ComplexShape

universe v u

namespace Formalization.Books.Homology.Unit15

/-! ## Source-facing categorical presentations -/

/-- A categorical way to say that `X` is a subcomplex of `Y`. -/
def HasMonomorphismInto {D : Type u} [Category.{v} D] (X Y : D) : Prop :=
  ∃ f : X ⟶ Y, Mono f

/-- A categorical way to say that `Y` is a quotient of `X`. -/
def HasEpimorphismOnto {D : Type u} [Category.{v} D] (X Y : D) : Prop :=
  ∃ f : X ⟶ Y, Epi f

/-- A quotient presentation of `Q` by a monomorphism from `X` to `Y`. -/
def HasQuotientPresentation {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    [HasCokernels D]
    (X Y Q : D) : Prop :=
  ∃ f : X ⟶ Y, Mono f ∧ Nonempty (cokernel f ≅ Q)

/-- An epimorphism presentation whose kernel is isomorphic to `K`. -/
def HasEpiKernelPresentation {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    [HasKernels D]
    (X Y K : D) : Prop :=
  ∃ f : X ⟶ Y, Epi f ∧ Nonempty (kernel f ≅ K)

/-- The componentwise content of a brutal truncation at an upper bound. -/
def IsStupidTruncationAtMost {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {c : ComplexShape ℤ} (K T : HomologicalComplex C c) (n : ℤ) : Prop :=
  (∀ i : ℤ, i ≤ n → Nonempty (T.X i ≅ K.X i)) ∧
    (∀ i : ℤ, n < i → IsZero (T.X i))

/-- The componentwise content of a brutal truncation at a lower bound. -/
def IsStupidTruncationAtLeast {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {c : ComplexShape ℤ} (K T : HomologicalComplex C c) (n : ℤ) : Prop :=
  (∀ i : ℤ, n ≤ i → Nonempty (T.X i ≅ K.X i)) ∧
    (∀ i : ℤ, i < n → IsZero (T.X i))

/-! ## Chain complexes -/

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Integer half-line embeddings for the chain shape -/

/-- The embedding of the nonnegative chain ray onto the degrees `≥ n`. -/
def chainGEEmbedding (n : ℤ) :
    (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) :=
  ComplexShape.Embedding.mk' _ _ (fun k : ℕ => n + k)
    (by
      intro a b h
      change n + (a : ℤ) = n + (b : ℤ) at h
      omega)
    (by
      intro a b
      change (b + 1 = a) ↔
        (n + (b : ℤ)) + 1 = n + (a : ℤ)
      constructor <;> intro h <;> omega)

instance (n : ℤ) : (chainGEEmbedding n).IsRelIff := by
  constructor
  intro a b h
  change (n + (b : ℤ)) + 1 = n + (a : ℤ) at h
  change b + 1 = a
  have h' : (b : ℤ) + 1 = (a : ℤ) := by omega
  exact_mod_cast h'

instance (n : ℤ) : (chainGEEmbedding n).IsTruncLE where
  mem_prev {i' j} h :=
    ⟨j + 1, by
      change n + (j : ℤ) + 1 = i' at h
      change n + ((j + 1 : ℕ) : ℤ) = i'
      omega⟩

/-- The embedding of the nonnegative chain ray onto the degrees `≤ n`. -/
def chainLEEmbedding (n : ℤ) :
    (ComplexShape.up ℕ).Embedding (ComplexShape.down ℤ) :=
  ComplexShape.Embedding.mk' _ _ (fun k : ℕ => n - k)
    (by
      intro a b h
      change n - (a : ℤ) = n - (b : ℤ) at h
      omega)
    (by
      intro a b
      change (a + 1 = b) ↔
        (n - (b : ℤ)) + 1 = n - (a : ℤ)
      constructor
      · intro h
        have h' : (a : ℤ) + 1 = (b : ℤ) := by
          exact_mod_cast h
        omega
      · intro h
        have h' : (a : ℤ) + 1 = (b : ℤ) := by
          omega
        exact_mod_cast h')

instance (n : ℤ) : (chainLEEmbedding n).IsRelIff := by
  constructor
  intro a b h
  change (n - (b : ℤ)) + 1 = n - (a : ℤ) at h
  change a + 1 = b
  have h' : (a : ℤ) + 1 = (b : ℤ) := by omega
  exact_mod_cast h'

instance (n : ℤ) : (chainLEEmbedding n).IsTruncGE where
  mem_next {j k'} h :=
    ⟨j + 1, by
      change k' + 1 = n - (j : ℤ) at h
      change n - ((j + 1 : ℕ) : ℤ) = k'
      simp only [Nat.cast_add, Nat.cast_one]
      omega⟩

/-! ### The first numbered item: `σ ≤ n` -/

/-- The degree-concentrated chain complex representing `A[-n]`. -/
noncomputable def degreeConcentrated (A : C) (n : ℤ) : ChainComplex C ℤ :=
  Formalization.Books.Homology.Unit14.ChainComplex.concentrated C A (-n)

/-- The stupid truncation `σ ≤ n` of a chain complex. -/
noncomputable def stupidTruncLE (K : ChainComplex C ℤ) (n : ℤ) :
    ChainComplex C ℤ :=
  HomologicalComplex.stupidTrunc K (chainLEEmbedding n)

theorem stupidTruncLE_components (K : ChainComplex C ℤ) (n : ℤ) :
    IsStupidTruncationAtMost K (stupidTruncLE K n) n := by
  sorry

theorem stupidTruncLE_is_subcomplex (K : ChainComplex C ℤ) (n : ℤ) :
    HasMonomorphismInto (stupidTruncLE K n) K := by
  sorry

/-- The source's quotient identity for successive lower brutal truncations. -/
theorem stupidTruncLE_quotient (K : ChainComplex C ℤ) (n : ℤ) :
    HasQuotientPresentation (stupidTruncLE K (n - 1)) (stupidTruncLE K n)
      (degreeConcentrated (K.X n) n) := by
  sorry

/-! ### The second numbered item: `σ ≥ n` -/

/-- The stupid truncation `σ ≥ n` of a chain complex. -/
noncomputable def stupidTruncGE (K : ChainComplex C ℤ) (n : ℤ) :
    ChainComplex C ℤ :=
  HomologicalComplex.stupidTrunc K (chainGEEmbedding n)

theorem stupidTruncGE_components (K : ChainComplex C ℤ) (n : ℤ) :
    IsStupidTruncationAtLeast K (stupidTruncGE K n) n := by
  sorry

theorem stupidTruncGE_is_quotient (K : ChainComplex C ℤ) (n : ℤ) :
    HasEpimorphismOnto K (stupidTruncGE K n) := by
  sorry

/-- The successive lower brutal truncation map is an epimorphism with the
degree-`n` complex as its kernel. -/
theorem stupidTruncGE_transition (K : ChainComplex C ℤ) (n : ℤ) :
    HasEpiKernelPresentation (stupidTruncGE K n) (stupidTruncGE K (n + 1))
      (degreeConcentrated (K.X n) n) := by
  sorry

/-! ### The third numbered item: canonical `τ ≥ n` -/

/-- The canonical truncation `τ ≥ n` of a chain complex.  Mathlib's
`truncLE` uses the cycle object at the boundary degree. -/
noncomputable def canonicalTruncGE (K : ChainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : ChainComplex C ℤ :=
  HomologicalComplex.truncLE K (chainGEEmbedding n)

/-- The canonical map `τ ≥ n K ⟶ K`. -/
noncomputable def canonicalTruncGEι (K : ChainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : canonicalTruncGE K n ⟶ K :=
  HomologicalComplex.ιTruncLE K (chainGEEmbedding n)

theorem canonicalTruncGE_boundary (K : ChainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] :
    Nonempty ((canonicalTruncGE K n).X n ≅ K.cycles n) := by
  sorry

theorem canonicalTruncGE_homology_above (K : ChainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : n ≤ i) :
    QuasiIsoAt (canonicalTruncGEι K n) i := by
  sorry

theorem canonicalTruncGE_homology_below (K : ChainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : i < n) :
    IsZero ((canonicalTruncGE K n).homology i) := by
  sorry

/-! ### The fourth numbered item: canonical `τ ≤ n` -/

/-- The canonical truncation `τ ≤ n` of a chain complex.  Mathlib's
`truncGE` uses the opcycle (cokernel) object at the boundary degree. -/
noncomputable def canonicalTruncLE (K : ChainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : ChainComplex C ℤ :=
  HomologicalComplex.truncGE K (chainLEEmbedding n)

/-- The canonical map `K ⟶ τ ≤ n K`. -/
noncomputable def canonicalTruncLEπ (K : ChainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : K ⟶ canonicalTruncLE K n :=
  HomologicalComplex.πTruncGE K (chainLEEmbedding n)

theorem canonicalTruncLE_boundary (K : ChainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] :
    Nonempty ((canonicalTruncLE K n).X n ≅ K.opcycles n) := by
  sorry

theorem canonicalTruncLE_homology_below (K : ChainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : i ≤ n) :
    QuasiIsoAt (canonicalTruncLEπ K n) i := by
  sorry

theorem canonicalTruncLE_homology_above (K : ChainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : n < i) :
    IsZero ((canonicalTruncLE K n).homology i) := by
  sorry

end ChainComplex

/-! ## Cochain complexes -/

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### The first numbered item: `σ ≥ n` -/

/-- The degree-concentrated cochain complex representing `A[-n]`. -/
noncomputable def degreeConcentrated (A : C) (n : ℤ) : CochainComplex C ℤ :=
  Formalization.Books.Homology.Unit14.CochainComplex.concentrated C A (-n)

/-- The stupid truncation `σ ≥ n` of a cochain complex. -/
noncomputable def stupidTruncGE (K : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex C ℤ :=
  HomologicalComplex.stupidTrunc K (ComplexShape.embeddingUpIntGE n)

theorem stupidTruncGE_components (K : CochainComplex C ℤ) (n : ℤ) :
    IsStupidTruncationAtLeast K (stupidTruncGE K n) n := by
  sorry

theorem stupidTruncGE_is_subcomplex (K : CochainComplex C ℤ) (n : ℤ) :
    HasMonomorphismInto (stupidTruncGE K n) K := by
  sorry

/-- The source's quotient identity for successive upper brutal truncations. -/
theorem stupidTruncGE_quotient (K : CochainComplex C ℤ) (n : ℤ) :
    HasQuotientPresentation (stupidTruncGE K (n + 1)) (stupidTruncGE K n)
      (degreeConcentrated (K.X n) n) := by
  sorry

/-! ### The second numbered item: `σ ≤ n` -/

/-- The stupid truncation `σ ≤ n` of a cochain complex. -/
noncomputable def stupidTruncLE (K : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex C ℤ :=
  HomologicalComplex.stupidTrunc K (ComplexShape.embeddingUpIntLE n)

theorem stupidTruncLE_components (K : CochainComplex C ℤ) (n : ℤ) :
    IsStupidTruncationAtMost K (stupidTruncLE K n) n := by
  sorry

theorem stupidTruncLE_is_quotient (K : CochainComplex C ℤ) (n : ℤ) :
    HasEpimorphismOnto K (stupidTruncLE K n) := by
  sorry

/-- The successive upper brutal truncation map is an epimorphism with the
degree-`n` complex as its kernel. -/
theorem stupidTruncLE_transition (K : CochainComplex C ℤ) (n : ℤ) :
    HasEpiKernelPresentation (stupidTruncLE K n) (stupidTruncLE K (n - 1))
      (degreeConcentrated (K.X n) n) := by
  sorry

/-! ### The third numbered item: canonical `τ ≤ n` -/

/-- The canonical truncation `τ ≤ n` of a cochain complex. -/
noncomputable def canonicalTruncLE (K : CochainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : CochainComplex C ℤ :=
  _root_.CochainComplex.truncLE K n

/-- The canonical map `τ ≤ n K ⟶ K`. -/
noncomputable def canonicalTruncLEι (K : CochainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : canonicalTruncLE K n ⟶ K :=
  _root_.CochainComplex.ιTruncLE K n

theorem canonicalTruncLE_boundary (K : CochainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] :
    Nonempty ((canonicalTruncLE K n).X n ≅ K.cycles n) := by
  sorry

theorem canonicalTruncLE_homology_below (K : CochainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : i ≤ n) :
    QuasiIsoAt (canonicalTruncLEι K n) i := by
  sorry

theorem canonicalTruncLE_homology_above (K : CochainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : n < i) :
    IsZero ((canonicalTruncLE K n).homology i) := by
  sorry

/-! ### The fourth numbered item: canonical `τ ≥ n` -/

/-- The canonical truncation `τ ≥ n` of a cochain complex. -/
noncomputable def canonicalTruncGE (K : CochainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : CochainComplex C ℤ :=
  _root_.CochainComplex.truncGE K n

/-- The canonical map `K ⟶ τ ≥ n K`. -/
noncomputable def canonicalTruncGEπ (K : CochainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : K ⟶ canonicalTruncGE K n :=
  _root_.CochainComplex.πTruncGE K n

theorem canonicalTruncGE_boundary (K : CochainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] :
    Nonempty ((canonicalTruncGE K n).X n ≅ K.opcycles n) := by
  sorry

theorem canonicalTruncGE_homology_above (K : CochainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : n ≤ i) :
    QuasiIsoAt (canonicalTruncGEπ K n) i := by
  sorry

theorem canonicalTruncGE_homology_below (K : CochainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : i < n) :
    IsZero ((canonicalTruncGE K n).homology i) := by
  sorry

end CochainComplex

end Formalization.Books.Homology.Unit15
