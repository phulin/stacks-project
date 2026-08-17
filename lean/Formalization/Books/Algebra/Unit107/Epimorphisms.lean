import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.Algebra.Category.Ring.Instances
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Commutative Algebra, Chapter 107: Epimorphisms of rings

Ring epimorphisms are represented by the canonical categorical predicate
`Epi` on `CommRingCat` morphisms.  Tensor-product statements use the
canonical algebra structure induced by a ring homomorphism through
`RingHom.toAlgebra`.
-/

namespace Formalization.Books.Algebra.Unit107

open CategoryTheory
open scoped BigOperators TensorProduct

universe u

noncomputable section

/-! ## Basic properties of epimorphisms -/

/-- The four standard characterizations of an epimorphism of commutative rings.

The second item is the equality of the two canonical maps into the self-tensor
product, the third says that either of those maps is an isomorphism, and the
fourth uses the multiplication map from the self-tensor product.
-/
theorem epimorphism_iff_tensorProduct
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    List.TFAE
      [ Epi (CommRingCat.ofHom f),
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S) =
          (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom,
        IsIso (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S)) ∨
          IsIso (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom),
        IsIso (CommRingCat.ofHom
          ((Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom)) ] := by
  sorry

/-- Epimorphisms are closed under composition. -/
theorem epimorphism_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : Epi (CommRingCat.ofHom f)) (hg : Epi (CommRingCat.ofHom g)) :
    Epi (CommRingCat.ofHom (g.comp f)) := by
  sorry

/-- Base change preserves epimorphisms.

The displayed map is the left inclusion
`R' → R' ⊗[R] S`, which is the source's map `R' → S_{R'}`.
-/
theorem epimorphism_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R')
    (hf : Epi (CommRingCat.ofHom f)) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    Epi (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom :
        R' →+* R' ⊗[R] S)) := by
  sorry

/-- If a composite is an epimorphism, then its second map is an epimorphism. -/
theorem epimorphism_of_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hcomp : Epi (CommRingCat.ofHom (g.comp f))) :
    Epi (CommRingCat.ofHom g) := by
  sorry

/-- The map from the image subring of an epimorphism is again an epimorphism. -/
theorem epimorphism_range_subtype
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Epi (CommRingCat.ofHom f)) :
    Epi (CommRingCat.ofHom f.range.subtype) := by
  sorry

/-- Every localization map is an epimorphism, as used in the local criterion. -/
theorem localization_epimorphism
    {R : Type u} [CommRing R] (M : Submonoid R) :
    Epi (CommRingCat.ofHom (algebraMap R (Localization M))) := by
  infer_instance

/-- Epimorphisms can be checked after localizing at every prime of the base.

Here `Sₚ` is represented by the canonical base-change model
`Rₚ ⊗[R] S`, as in the source text.
-/
theorem epimorphism_iff_localization_at_prime
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Epi (CommRingCat.ofHom f) ↔
      ∀ p : PrimeSpectrum R,
        letI : Algebra R S := f.toAlgebra
        Epi (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom :
            Localization.AtPrime p.asIdeal →+*
              Localization.AtPrime p.asIdeal ⊗[R] S)) := by
  sorry

/-- A ring map is surjective exactly when it is both finite and epic. -/
theorem finite_epimorphism_iff_surjective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (Epi (CommRingCat.ofHom f) ∧ RingHom.Finite f) ↔
      Function.Surjective f := by
  simpa using
    (RingHom.surjective_iff_epi_and_finite
      (f := CommRingCat.ofHom f)).symm

/-- A faithfully flat epimorphism is an isomorphism. -/
theorem isIso_of_faithfullyFlat_of_epimorphism
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Epi (CommRingCat.ofHom f)) (hff : RingHom.FaithfullyFlat f) :
    IsIso (CommRingCat.ofHom f) := by
  sorry

/-- An epimorphism out of a field has either a field target isomorphic to the
source or a subsingleton target ring. -/
theorem epimorphism_from_field
    {k S : Type u} [Field k] [CommRing S] (f : k →+* S)
    (hf : Epi (CommRingCat.ofHom f)) :
    IsIso (CommRingCat.ofHom f) ∨ Subsingleton S := by
  sorry

/-- An epimorphism induces an injective map on spectra and bijections on the
corresponding residue fields. -/
theorem epimorphism_comap_injective_residueField_bijective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Epi (CommRingCat.ofHom f)) :
    Function.Injective (PrimeSpectrum.comap f) ∧
      ∀ q : PrimeSpectrum S,
        Function.Bijective
          (Ideal.ResidueField.map (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl) := by
  sorry

/-! ## Relations in tensor products and the epicenter -/

/-- The source's generator-and-relation criterion for a finite tensor sum.

`m` and `a` are finitely supported functions, so their supports encode the
finite-support hypotheses on the families `mⱼ` and `aᵢⱼ`.
-/
theorem tensor_sum_eq_zero_iff_relations
    {R M N I J : Type u} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (x : I → M) (y : J → N)
    (hx : Submodule.span R (Set.range x) = ⊤)
    (hy : Submodule.span R (Set.range y) = ⊤)
    (m : J →₀ M) :
    letI : DecidableEq I := Classical.decEq I
    letI : DecidableEq J := Classical.decEq J
    (∑ j ∈ m.support, (m j) ⊗ₜ[R] y j = 0) ↔
      ∃ a : (I × J) →₀ R,
        (∀ j : J,
          m j = ∑ ij ∈ a.support,
            if ij.2 = j then a ij • x ij.1 else 0) ∧
        (∀ i : I,
          (0 : N) = ∑ ij ∈ a.support,
            if ij.1 = i then a ij • y ij.2 else 0) := by
  sorry

/-- The finite matrix-factorization criterion for an element equalized by the
two maps into a self-tensor product. -/
theorem tensor_equalizer_iff_matrix_factorization
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (g : S) :
    letI : Algebra R S := f.toAlgebra
    (g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g) ↔
      ∃ n : ℕ, ∃ y z : Fin n → S,
        ∃ x : Matrix (Fin n) (Fin n) R,
          g = ∑ i : Fin n, ∑ j : Fin n, f (x i j) * y i * z j ∧
          (∀ j : Fin n, ∃ r : R,
            ∑ i : Fin n, f (x i j) * y i = f r) ∧
          (∀ i : Fin n, ∃ r : R,
            ∑ j : Fin n, f (x i j) * z j = f r) := by
  sorry

/-- The epicenter of a ring map, equipped with its canonical subalgebra
structure over the source. -/
def epicenter
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    Subalgebra R S := by
  letI : Algebra R S := f.toAlgebra
  exact
    { carrier := {g : S | g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change (x + y) ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] (x + y)
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
        rw [hx, hy]
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change (x * y) ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] (x * y)
        calc
          (x * y) ⊗ₜ[R] (1 : S) =
              (x ⊗ₜ[R] (1 : S)) * (y ⊗ₜ[R] (1 : S)) := by simp
          _ = ((1 : S) ⊗ₜ[R] x) * ((1 : S) ⊗ₜ[R] y) := by rw [hx, hy]
          _ = (1 : S) ⊗ₜ[R] (x * y) := by simp
      algebraMap_mem' := by
        intro r
        change algebraMap R S r ⊗ₜ[R] (1 : S) =
          (1 : S) ⊗ₜ[R] algebraMap R S r
        exact Algebra.TensorProduct.tmul_one_eq_one_tmul r }

@[simp]
theorem mem_epicenter
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (g : S) :
    letI : Algebra R S := f.toAlgebra
    g ∈ epicenter f ↔ g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g := by
  rfl

/-- A finite matrix triple over `f` records the three matrices `(P,U,V)`
in the source's matrix-factorization remark. -/
structure MatrixTriple
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) where
  P : Matrix (Fin n) (Fin n) R
  U : Matrix (Fin 1) (Fin n) R
  V : Matrix (Fin n) (Fin 1) R

/-- A matrix triple is associated to `g` when it comes from a factorization
`g = Y X Z`, with `U = YX` and `V = XZ` after applying `f` coefficientwise. -/
def matrixTripleAssociated
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (g : S) (t : MatrixTriple f n) : Prop :=
  ∃ y z : Fin n → S,
    g = ∑ i : Fin n, ∑ j : Fin n, f (t.P i j) * y i * z j ∧
    (∀ j : Fin n,
      f (t.U 0 j) = ∑ i : Fin n, f (t.P i j) * y i) ∧
    (∀ i : Fin n,
      f (t.V i 0) = ∑ j : Fin n, f (t.P i j) * z j)

/-! ## Cardinality and modules -/

/-- Every element of the epicenter admits an associated finite matrix triple. -/
theorem exists_matrixTriple_associated_of_mem_epicenter
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) {g : S}
    (hg : g ∈ epicenter f) :
    ∃ n : ℕ, ∃ t : MatrixTriple f n, matrixTripleAssociated f g t := by
  sorry

/-- An epimorphism cannot increase the cardinality of the underlying ring. -/
theorem cardinality_target_le_source_of_epimorphism
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Epi (CommRingCat.ofHom f)) :
    Cardinal.mk S ≤ Cardinal.mk R := by
  sorry

/-- The finite-source case in the cardinality argument is in fact surjective. -/
theorem surjective_of_finite_source_of_epimorphism
    {R S : Type u} [CommRing R] [CommRing S] [Finite R] (f : R →+* S)
    (hf : Epi (CommRingCat.ofHom f)) :
    Function.Surjective f := by
  sorry

/-- The ring-epimorphism criterion in terms of restriction of scalars on
module categories. -/
theorem epimorphism_iff_restrictScalars_fullyFaithful
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    let F := ModuleCat.restrictScalars f
    List.TFAE
      [ Epi (CommRingCat.ofHom f),
        ∀ (M N : ModuleCat S),
          Function.Bijective
            (F.map : (M ⟶ N) → (F.obj M ⟶ F.obj N)),
        Nonempty F.FullyFaithful ] := by
  sorry

end

end Formalization.Books.Algebra.Unit107
