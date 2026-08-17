import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Homological Algebra, Chapter 13: Complexes

The source uses chain and cochain complexes indexed by `ℤ`.  Mathlib's
`ChainComplex` and `CochainComplex` are the canonical instances of
`HomologicalComplex` for the down and up shapes, respectively.  This file
therefore records the source statements through those APIs rather than
introducing parallel complex, homotopy, homology, or quasi-isomorphism
structures.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

universe v u

namespace Formalization.Books.Homology.Unit13

/-! ## Chain and cochain complexes -/

/- The source's `Ch_{≥ 0}` and `CoCh_{≥ 0}` are full subcategories.  The
   categorical formulation uses `IsZero` for the statement that a component
   is zero, which is invariant under the choice of a zero object. -/

def chainComplexGEZero
    (C : Type u) [Category.{v} C] [Preadditive C] :
    ObjectProperty (ChainComplex C ℤ) :=
  fun K => ∀ (n : ℤ), n < 0 → IsZero (K.X n)

abbrev chainComplexGEZeroCategory
    (C : Type u) [Category.{v} C] [Preadditive C] :=
  (chainComplexGEZero C).FullSubcategory

def cochainComplexGEZero
    (C : Type u) [Category.{v} C] [Preadditive C] :
    ObjectProperty (CochainComplex C ℤ) :=
  fun K => ∀ (n : ℤ), n < 0 → IsZero (K.X n)

abbrev cochainComplexGEZeroCategory
    (C : Type u) [Category.{v} C] [Preadditive C] :=
  (cochainComplexGEZero C).FullSubcategory

/- The degree-zero embedding used by the source is Mathlib's `single`
   functor.  Its existing component lemmas say that the component in degree
   zero is the input object and all other components are zero. -/

noncomputable def chainComplexSingle
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C] :
    C ⥤ ChainComplex C ℤ :=
  HomologicalComplex.single C (ComplexShape.down ℤ) 0

noncomputable def cochainComplexSingle
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C] :
    C ⥤ CochainComplex C ℤ :=
  HomologicalComplex.single C (ComplexShape.up ℤ) 0

/-! ## Abelian structure and degreewise exactness -/

@[instance_reducible]
def chainComplex_abelian
    (C : Type u) [Category.{v} C] [Abelian C] :
    Abelian (ChainComplex C ℤ) := by
  infer_instance

@[instance_reducible]
def cochainComplex_abelian
    (C : Type u) [Category.{v} C] [Abelian C] :
    Abelian (CochainComplex C ℤ) := by
  infer_instance

theorem chainComplex_mono_iff_degreewise
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : ChainComplex C ℤ} (f : A ⟶ B) :
    Mono f ↔ ∀ n : ℤ, Mono (f.f n) := by
  constructor
  · intro hf n
    let _ : Mono f := hf
    infer_instance
  · intro hf
    exact HomologicalComplex.mono_of_mono_f f hf

theorem chainComplex_epi_iff_degreewise
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : ChainComplex C ℤ} (f : A ⟶ B) :
    Epi f ↔ ∀ n : ℤ, Epi (f.f n) := by
  constructor
  · intro hf n
    let _ : Epi f := hf
    infer_instance
  · intro hf
    exact HomologicalComplex.epi_of_epi_f f hf

theorem chainComplex_exact_iff_degreewise
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex (ChainComplex C ℤ)) :
    S.Exact ↔
      ∀ n : ℤ,
        (S.map (HomologicalComplex.eval C (ComplexShape.down ℤ) n)).Exact :=
  HomologicalComplex.exact_iff_degreewise_exact S

theorem cochainComplex_mono_iff_degreewise
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : CochainComplex C ℤ} (f : A ⟶ B) :
    Mono f ↔ ∀ n : ℤ, Mono (f.f n) := by
  constructor
  · intro hf n
    let _ : Mono f := hf
    infer_instance
  · intro hf
    exact HomologicalComplex.mono_of_mono_f f hf

theorem cochainComplex_epi_iff_degreewise
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : CochainComplex C ℤ} (f : A ⟶ B) :
    Epi f ↔ ∀ n : ℤ, Epi (f.f n) := by
  constructor
  · intro hf n
    let _ : Epi f := hf
    infer_instance
  · intro hf
    exact HomologicalComplex.epi_of_epi_f f hf

theorem cochainComplex_exact_iff_degreewise
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex (CochainComplex C ℤ)) :
    S.Exact ↔
      ∀ n : ℤ,
        (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Exact :=
  HomologicalComplex.exact_iff_degreewise_exact S

/-! ## Homology and cohomology -/

/- `K.homology i` is Mathlib's canonical kernel/image homology object.  The
   following functors are the source's `H_i` and `H^i`; the cochain case uses
   the same canonical homology API for the up-shaped complex. -/

noncomputable def chainHomologyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (i : ℤ) :
    ChainComplex C ℤ ⥤ C :=
  HomologicalComplex.homologyFunctor C (ComplexShape.down ℤ) i

noncomputable def cochainCohomologyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (i : ℤ) :
    CochainComplex C ℤ ⥤ C :=
  HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i

/- These cokernel universal properties are the canonical categorical form of
   `Ker(d_i) / Im(d_{i+1})` and `Ker(d^i) / Im(d^{i-1})`. -/

noncomputable def chainHomologyIsCokernel
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : ChainComplex C ℤ) (i : ℤ) :
    IsColimit
      (CokernelCofork.ofπ (K.homologyπ i)
        (K.toCycles_comp_homologyπ (i + 1) i)) :=
  K.homologyIsCokernel (i + 1) i (ChainComplex.prev ℤ i)

noncomputable def cochainCohomologyIsCokernel
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (i : ℤ) :
    IsColimit
      (CokernelCofork.ofπ (K.homologyπ i)
        (K.toCycles_comp_homologyπ (i - 1) i)) :=
  K.homologyIsCokernel (i - 1) i (CochainComplex.prev ℤ i)

/-! ## Quasi-isomorphisms and acyclic complexes -/

theorem chain_quasiIso_iff_homologyMap_isIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : ChainComplex C ℤ} (f : A ⟶ B) :
    QuasiIso f ↔ ∀ i : ℤ, IsIso (HomologicalComplex.homologyMap f i) := by
  constructor
  · intro hf i
    exact (quasiIsoAt_iff_isIso_homologyMap f i).1
      ((quasiIso_iff f).1 hf i)
  · intro hf
    apply (quasiIso_iff f).2
    intro i
    exact (quasiIsoAt_iff_isIso_homologyMap f i).2 (hf i)

theorem cochain_quasiIso_iff_cohomologyMap_isIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : CochainComplex C ℤ} (f : A ⟶ B) :
    QuasiIso f ↔ ∀ i : ℤ, IsIso (HomologicalComplex.homologyMap f i) := by
  constructor
  · intro hf i
    exact (quasiIsoAt_iff_isIso_homologyMap f i).1
      ((quasiIso_iff f).1 hf i)
  · intro hf
    apply (quasiIso_iff f).2
    intro i
    exact (quasiIsoAt_iff_isIso_homologyMap f i).2 (hf i)

theorem chain_acyclic_iff_homology_isZero
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : ChainComplex C ℤ) :
    K.Acyclic ↔ ∀ i : ℤ, IsZero (K.homology i) := by
  rw [HomologicalComplex.acyclic_iff]
  constructor
  · intro h i
    exact (HomologicalComplex.exactAt_iff_isZero_homology (K := K) (i := i)).1 (h i)
  · intro h i
    exact (HomologicalComplex.exactAt_iff_isZero_homology (K := K) (i := i)).2 (h i)

theorem cochain_acyclic_iff_cohomology_isZero
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) :
    K.Acyclic ↔ ∀ i : ℤ, IsZero (K.homology i) := by
  rw [HomologicalComplex.acyclic_iff]
  constructor
  · intro h i
    exact (HomologicalComplex.exactAt_iff_isZero_homology (K := K) (i := i)).1 (h i)
  · intro h i
    exact (HomologicalComplex.exactAt_iff_isZero_homology (K := K) (i := i)).2 (h i)

/-! ## Homotopies and homotopy equivalences -/

/- Mathlib's `Homotopy` is exactly the source's family of degree-shifting
  homotopy components together with the equation `f - g = dh + hd`; its
  `HomotopyEquiv` is the corresponding canonical equivalence datum. -/

def chain_homotopy_comp
    {C : Type u} [Category.{v} C] [Preadditive C]
    {A B C' D : ChainComplex C ℤ} {f g : B ⟶ C'}
    (a : A ⟶ B) (c : C' ⟶ D) (h : Homotopy f g) :
    Homotopy (a ≫ f ≫ c) (a ≫ g ≫ c) := by
  simpa only [Category.assoc] using (h.compRight c).compLeft a

def cochain_homotopy_comp
    {C : Type u} [Category.{v} C] [Preadditive C]
    {A B C' D : CochainComplex C ℤ} {f g : B ⟶ C'}
    (a : A ⟶ B) (c : C' ⟶ D) (h : Homotopy f g) :
    Homotopy (a ≫ f ≫ c) (a ≫ g ≫ c) := by
  simpa only [Category.assoc] using (h.compRight c).compLeft a

abbrev chainHomotopic
    {C : Type u} [Category.{v} C] [Preadditive C]
    {A B : ChainComplex C ℤ} (f g : A ⟶ B) : Prop :=
  Nonempty (Homotopy f g)

abbrev cochainHomotopic
    {C : Type u} [Category.{v} C] [Preadditive C]
    {A B : CochainComplex C ℤ} (f g : A ⟶ B) : Prop :=
  Nonempty (Homotopy f g)

abbrev chainHomotopyEquivalence
    {C : Type u} [Category.{v} C] [Preadditive C]
    {A B : ChainComplex C ℤ} (f : A ⟶ B) : Prop :=
  HomologicalComplex.homotopyEquivalences C (ComplexShape.down ℤ) f

abbrev cochainHomotopyEquivalence
    {C : Type u} [Category.{v} C] [Preadditive C]
    {A B : CochainComplex C ℤ} (f : A ⟶ B) : Prop :=
  HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ) f

theorem chain_homologyMap_eq_of_homotopy
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : ChainComplex C ℤ} {f g : A ⟶ B} (h : Homotopy f g) (i : ℤ) :
    HomologicalComplex.homologyMap f i = HomologicalComplex.homologyMap g i :=
  h.homologyMap_eq i

theorem cochain_cohomologyMap_eq_of_homotopy
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : CochainComplex C ℤ} {f g : A ⟶ B} (h : Homotopy f g) (i : ℤ) :
    HomologicalComplex.homologyMap f i = HomologicalComplex.homologyMap g i :=
  h.homologyMap_eq i

theorem chain_homotopyEquiv_is_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : ChainComplex C ℤ} {f : A ⟶ B}
    (hf : chainHomotopyEquivalence f) :
    QuasiIso f := by
  rcases hf with ⟨e, rfl⟩
  infer_instance

theorem cochain_homotopyEquiv_is_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : CochainComplex C ℤ} {f : A ⟶ B}
    (hf : cochainHomotopyEquivalence f) :
    QuasiIso f := by
  rcases hf with ⟨e, rfl⟩
  infer_instance

def chainHomotopyEquivalent
    {C : Type u} [Category.{v} C] [Preadditive C]
    (A B : ChainComplex C ℤ) : Prop :=
  Nonempty (HomotopyEquiv A B)

def cochainHomotopyEquivalent
    {C : Type u} [Category.{v} C] [Preadditive C]
    (A B : CochainComplex C ℤ) : Prop :=
  Nonempty (HomotopyEquiv A B)

/-! ## Long exact homology and cohomology sequences -/

/- For the down shape, the next degree after `i` is `i - 1`; for the up
   shape, it is `i + 1`.  The following are the source's connecting maps,
   supplied canonically by the Snake Lemma API. -/

noncomputable def chainConnectingMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (ChainComplex C ℤ)} (hS : S.ShortExact) (i : ℤ) :
    S.X₃.homology i ⟶ S.X₁.homology (i - 1) :=
  hS.δ i (i - 1) (by simp [ComplexShape.down, ComplexShape.down'])

noncomputable def cochainConnectingMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (i : ℤ) :
    S.X₃.homology i ⟶ S.X₁.homology (i + 1) :=
  hS.δ i (i + 1) (by simp [ComplexShape.up, ComplexShape.up'])

/- A six-term exact segment is the canonical finite presentation of the
   displayed long exact sequence. -/

noncomputable def chainHomologySequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (ChainComplex C ℤ)} (hS : S.ShortExact) (i : ℤ) :
    ComposableArrows C 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅ hS i (i - 1)
    (by simp [ComplexShape.down, ComplexShape.down'])

theorem chainHomologySequence_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (ChainComplex C ℤ)} (hS : S.ShortExact) (i : ℤ) :
    (chainHomologySequence hS i).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact hS i (i - 1)
    (by simp [ComplexShape.down, ComplexShape.down'])

noncomputable def cochainCohomologySequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (i : ℤ) :
    ComposableArrows C 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅ hS i (i + 1)
    (by simp [ComplexShape.up, ComplexShape.up'])

theorem cochainCohomologySequence_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (i : ℤ) :
    (cochainCohomologySequence hS i).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact hS i (i + 1)
    (by simp [ComplexShape.up, ComplexShape.up'])

/- Naturality of the connecting maps is the precise functoriality assertion
   in the source's cochain long-exact-sequence lemma (and also applies to the
   chain case). -/

theorem chainConnectingMap_natural
    {C : Type u} [Category.{v} C] [Abelian C]
    {S₁ S₂ : ShortComplex (ChainComplex C ℤ)}
    (φ : S₁ ⟶ S₂) (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (i : ℤ) :
    h₁.δ i (i - 1) (by simp [ComplexShape.down, ComplexShape.down']) ≫
        HomologicalComplex.homologyMap φ.τ₁ (i - 1) =
      HomologicalComplex.homologyMap φ.τ₃ i ≫
        h₂.δ i (i - 1) (by simp [ComplexShape.down, ComplexShape.down']) :=
  HomologicalComplex.HomologySequence.δ_naturality φ h₁ h₂ i (i - 1)
    (by simp [ComplexShape.down, ComplexShape.down'])

theorem cochainConnectingMap_natural
    {C : Type u} [Category.{v} C] [Abelian C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
    (φ : S₁ ⟶ S₂) (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (i : ℤ) :
    h₁.δ i (i + 1) (by simp [ComplexShape.up, ComplexShape.up']) ≫
        HomologicalComplex.homologyMap φ.τ₁ (i + 1) =
      HomologicalComplex.homologyMap φ.τ₃ i ≫
        h₂.δ i (i + 1) (by simp [ComplexShape.up, ComplexShape.up']) :=
  HomologicalComplex.HomologySequence.δ_naturality φ h₁ h₂ i (i + 1)
    (by simp [ComplexShape.up, ComplexShape.up'])

/- The source additionally refers forward to shift compatibility.  The shift
   functor and the cohomology-shift interface are introduced in the following
   source section, so this chapter records the available canonical
   long-exact-sequence and naturality interfaces here and leaves that
   compatibility statement to the later shift formalization. -/

end Formalization.Books.Homology.Unit13
