import Formalization.Books.Algebra.Unit09.Localization
import Formalization.Books.Algebra.Unit13.TensorAlgebra
import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Formalization.Books.Homology.Unit14.HomotopyAndShift
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# More on Algebra, Chapter 29: The Koszul complex

The chapter's Koszul complexes are expressed using Mathlib's exterior powers and
homological-complex interfaces.  The propositions below record the textbook's
construction and theorem interfaces; the proposition proofs belong to the later
proof stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open ComplexShape

universe u

namespace Formalization.Books.MoreAlgebra.Unit29

/-! ## The exterior differential -/

/-- The homogeneous module used in degree `n` of a Koszul complex. -/
abbrev koszulTerm (R E : Type u) (n : ℕ) [CommRing R] [AddCommGroup E]
    [Module R E] := ⋀[R]^n E

/-- The alternating map which contracts one exterior generator with `φ`. -/
def koszulContractionPre (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (n : ℕ) :
    E →ₗ[R] E [⋀^Fin n]→ₗ[R] (⋀[R]^n E) :=
  { toFun := fun e => (φ e) • exteriorPower.ιMulti R n
    map_add' := by
      intro e e'
      simp [map_add, add_smul]
    map_smul' := by
      intro a e
      simp [map_smul, smul_smul] }

/-- The corresponding contraction with values in the full exterior algebra. -/
def koszulContractionPreAlgebra (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℕ) :
    E →ₗ[R] E [⋀^Fin n]→ₗ[R] ExteriorAlgebra R E :=
  { toFun := fun e => (φ e) • ExteriorAlgebra.ιMulti R n
    map_add' := by
      intro e e'
      simp [map_add, add_smul]
    map_smul' := by
      intro a e
      simp [map_smul, smul_smul] }

/-- Uncurrying the contraction gives the Koszul differential on generators. -/
def koszulContraction (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (n : ℕ) :
    E [⋀^Fin (n + 1)]→ₗ[R] (⋀[R]^n E) :=
  AlternatingMap.alternatizeUncurryFin (koszulContractionPre R E φ n)

/-- The same uncurried map, now regarded as taking values in the exterior algebra. -/
def koszulContractionAlgebra (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℕ) :
    E [⋀^Fin (n + 1)]→ₗ[R] ExteriorAlgebra R E :=
  AlternatingMap.alternatizeUncurryFin (koszulContractionPreAlgebra R E φ n)

/-- The differential on the `n+1`st exterior power. -/
noncomputable def koszulDifferential (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℕ) :
    (⋀[R]^(n + 1) E) →ₗ[R] (⋀[R]^n E) :=
  exteriorPower.alternatingMapLinearEquiv (koszulContraction R E φ n)

/-- The explicit alternating-sum formula for the Koszul differential.

Lean numbers the entries of a `Fin` tuple from zero, so the exponent `i` here
is the source's exponent `i+1` after reindexing. -/
theorem koszulDifferential_apply_ιMulti (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) (n : ℕ)
    (v : Fin (n + 1) → E) :
    koszulDifferential R E φ n (exteriorPower.ιMulti R (n + 1) v) =
      ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) •
        ((φ (v i)) • exteriorPower.ιMulti R n (i.removeNth v)) := by
  sorry

/-- The differential on the full exterior algebra, obtained from the alternating
maps on each homogeneous component. -/
noncomputable def koszulAlgebraDifferential (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) :
    ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E :=
  ExteriorAlgebra.liftAlternating (fun n =>
    match n with
    | 0 => 0
    | n + 1 => koszulContractionAlgebra R E φ n)

/-- The full-algebra version of the explicit differential formula. -/
theorem koszulAlgebraDifferential_apply_ιMulti (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) (n : ℕ)
    (v : Fin (n + 1) → E) :
    koszulAlgebraDifferential R E φ (ExteriorAlgebra.ιMulti R (n + 1) v) =
      ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) •
        ((φ (v i)) • ExteriorAlgebra.ιMulti R n (i.removeNth v)) := by
  sorry

/-- The graded Leibniz identity required of a differential on the exterior algebra. -/
def IsKoszulDerivation (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R)
    (d : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E) : Prop :=
  (∀ (n m : ℕ) (x : ⋀[R]^n E) (y : ⋀[R]^m E),
      d ((x : ExteriorAlgebra R E) * (y : ExteriorAlgebra R E)) =
        d (x : ExteriorAlgebra R E) * (y : ExteriorAlgebra R E) +
          (-1 : R) ^ n •
            ((x : ExteriorAlgebra R E) * d (y : ExteriorAlgebra R E))) ∧
    (∀ e, d (ExteriorAlgebra.ι R e) = algebraMap R (ExteriorAlgebra R E) (φ e))

/-- The commutative DGA underlying the Koszul complex. -/
structure KoszulDGA (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) where
  differential : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E

/-- The canonical Koszul DGA structure. -/
def koszulDGA (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) : KoszulDGA R E φ :=
  { differential := koszulAlgebraDifferential R E φ }

/-- The algebra differential is a graded derivation and squares to zero. -/
def IsKoszulDGA (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (D : KoszulDGA R E φ) : Prop :=
  IsKoszulDerivation R E φ D.differential ∧
    D.differential.comp D.differential = 0

theorem koszulDGA_isDGA (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) : IsKoszulDGA R E φ (koszulDGA R E φ) := by
  sorry

theorem koszulAlgebraDifferential_on_generator (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) (e : E) :
    koszulAlgebraDifferential R E φ (ExteriorAlgebra.ι R e) =
      algebraMap R (ExteriorAlgebra R E) (φ e) := by
  sorry

theorem koszulAlgebraDifferential_unique (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R)
    (d : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E)
    (hd : IsKoszulDerivation R E φ d) :
    d = koszulAlgebraDifferential R E φ := by
  sorry

/-! ## The complex and sequences -/

/-- The Koszul term in an arbitrary integer degree; negative degrees are zero. -/
noncomputable def koszulTermZ (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (n : ℤ) : ModuleCat.{u} R :=
  if 0 ≤ n then ModuleCat.of R (⋀[R]^(Int.toNat n) E)
  else ModuleCat.of R (Fin 0 → R)

/-- The differential of the integer-indexed Koszul complex. -/
noncomputable def koszulDifferentialZ (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℤ) :
    koszulTermZ R E (n + 1) ⟶ koszulTermZ R E n := by
  by_cases hn : 0 ≤ n
  · have hn1 : 0 ≤ n + 1 := by omega
    have hnat : Int.toNat (n + 1) = Int.toNat n + 1 := by
      exact Int.toNat_add hn (by omega)
    simp only [koszulTermZ, if_pos hn1, if_pos hn]
    rw [hnat]
    exact ModuleCat.ofHom (koszulDifferential R E φ (Int.toNat n))
  · by_cases hn1 : 0 ≤ n + 1
    · simp only [koszulTermZ, if_pos hn1, if_neg hn]
      exact 0
    · simp only [koszulTermZ, if_neg hn1, if_neg hn]
      exact 0

theorem koszulDifferentialZ_comp (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℤ) :
    koszulDifferentialZ R E φ (n + 1) ≫ koszulDifferentialZ R E φ n = 0 := by
  sorry

theorem koszulDifferential_comp (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℕ) :
    ModuleCat.ofHom (koszulDifferential R E φ (n + 1)) ≫
        ModuleCat.ofHom (koszulDifferential R E φ n) = 0 := by
  sorry

/-- The homological Koszul complex, indexed over `ℤ` and zero in negative degrees. -/
noncomputable def koszulComplex (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) : ChainComplex (ModuleCat.{u} R) ℤ :=
  ChainComplex.of (fun n => koszulTermZ R E n) (fun n => koszulDifferentialZ R E φ n)
    (koszulDifferentialZ_comp R E φ)

/-- The nonnegative indexing of the same construction, used by the canonical
`down ℕ` total tensor complex. -/
noncomputable def koszulComplexNat (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (⋀[R]^n E))
    (fun n => ModuleCat.ofHom (koszulDifferential R E φ n))
    (koszulDifferential_comp R E φ)

theorem koszulComplex_X_nonnegative (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℕ) :
    (koszulComplex R E φ).X (n : ℤ) = ModuleCat.of R (⋀[R]^n E) := by
  sorry

theorem koszulComplex_X_negative (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℤ) (hn : n < 0) :
    IsZero ((koszulComplex R E φ).X n) := by
  sorry

theorem koszulComplex_d_nonnegative (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (n : ℕ) :
    (koszulComplex R E φ).d (n + 1 : ℤ) n =
      ModuleCat.ofHom (koszulDifferential R E φ n) := by
  sorry

/-- The map associated with a finite sequence, using the standard free module. -/
def sequenceLinearMap (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R) :
    (Fin r → R) →ₗ[R] R :=
  { toFun := fun x => ∑ i, x i * f i
    map_add' := by
      intro x y
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro a x
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_assoc] }

@[simp]
theorem sequenceLinearMap_apply (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R)
    (x : Fin r → R) : sequenceLinearMap R r f x = ∑ i, x i * f i := rfl

/-- The Koszul complex of a sequence. -/
noncomputable def koszulComplexOn (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R) :
    ChainComplex (ModuleCat.{u} R) ℤ :=
  koszulComplex R (Fin r → R) (sequenceLinearMap R r f)

noncomputable def koszulComplexOnNat (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  koszulComplexNat R (Fin r → R) (sequenceLinearMap R r f)

/-- The standard insertion of a final element into a finite sequence. -/
def sequenceAppendLast (r : ℕ) (f : Fin r → R) (g : R) : Fin (r + 1) → R :=
  Fin.lastCases g f

/-! ## Local finite-free presentations and functoriality -/

/-- The canonical localization of a Koszul map at a basic open. -/
noncomputable def localizedKoszulMap
    (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (a : R) :
    LocalizedModule.Away a E →ₗ[Localization.Away a]
      LocalizedModule.Away a R :=
  LocalizedModule.map (Submonoid.powers a) φ

/-- Data for a local finite-free presentation of a Koszul map.  The target is
the localized copy of `R`; it is the module-theoretic form of the localized
ring target. -/
structure KoszulLocalSequencePresentation (R E : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] (φ : E →ₗ[R] R) (a : R) where
  rank : ℕ
  basis : LocalizedModule.Away a E ≃ₗ[Localization.Away a]
    (Fin rank →₀ Localization.Away a)
  sequence : Fin rank → LocalizedModule.Away a R
  map_on_basis : ∀ i,
    localizedKoszulMap R E φ a (basis.symm (Finsupp.single i 1)) = sequence i

theorem koszul_finiteLocallyFree_local
    (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R)
    (hE : Formalization.Books.Algebra.Unit78.FiniteLocallyFree R E) :
    ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ a ∈ s, Nonempty (KoszulLocalSequencePresentation R E φ a) := by
  sorry

/-- The exterior-algebra map induced by a linear map of generators. -/
def koszulAlgebraMap (R E E' : Type u) [CommRing R] [AddCommGroup E]
    [AddCommGroup E'] [Module R E] [Module R E'] (ψ : E →ₗ[R] E') :
    ExteriorAlgebra R E →ₐ[R] ExteriorAlgebra R E' :=
  ExteriorAlgebra.map ψ

/-- Data of the DGA map induced by a map of Koszul generators. -/
structure KoszulDGAHom (R E E' : Type u) [CommRing R] [AddCommGroup E]
    [AddCommGroup E'] [Module R E] [Module R E']
    (φ : E →ₗ[R] R) (φ' : E' →ₗ[R] R) (ψ : E →ₗ[R] E') where
  algebraMap : ExteriorAlgebra R E →ₐ[R] ExteriorAlgebra R E'
  algebraMap_eq_induced : algebraMap = koszulAlgebraMap R E E' ψ
  differential_commutes :
    algebraMap.toLinearMap.comp (koszulAlgebraDifferential R E φ) =
      (koszulAlgebraDifferential R E' φ').comp algebraMap.toLinearMap

theorem koszul_functorial
    (R E E' : Type u) [CommRing R] [AddCommGroup E] [AddCommGroup E']
    [Module R E] [Module R E'] (φ : E →ₗ[R] R) (φ' : E' →ₗ[R] R)
    (ψ : E →ₗ[R] E') (h : φ'.comp ψ = φ) :
    Nonempty (KoszulDGAHom R E E' φ φ' ψ) := by
  sorry

/-- Data of an isomorphism between two Koszul DGAs. -/
structure KoszulDGAIso (R E E' : Type u) [CommRing R] [AddCommGroup E]
    [AddCommGroup E'] [Module R E] [Module R E']
    (φ : E →ₗ[R] R) (φ' : E' →ₗ[R] R) (ψ : E →ₗ[R] E') where
  algebraEquiv : ExteriorAlgebra R E ≃ₐ[R] ExteriorAlgebra R E'
  algebraEquiv_eq_induced : algebraEquiv.toAlgHom = koszulAlgebraMap R E E' ψ
  differential_commutes :
    algebraEquiv.toLinearMap.comp (koszulAlgebraDifferential R E φ) =
      (koszulAlgebraDifferential R E' φ').comp algebraEquiv.toLinearMap

/-- The change-of-basis sequence associated with an invertible matrix acting on
the standard free module. -/
noncomputable def matrixChangeSequence (R : Type u) [CommRing R] (r : ℕ)
    (X : Matrix (Fin r) (Fin r) R) [Invertible X] (f : Fin r → R) : Fin r → R :=
  fun i => sequenceLinearMap R r f
    (Matrix.toLinearEquiv' X (inferInstance : Invertible X) (Pi.single i 1))

theorem koszul_change_basis
    (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R)
    (e : (Fin r → R) ≃ₗ[R] (Fin r → R))
    (g : Fin r → R)
    (h : (sequenceLinearMap R r g) =
      (sequenceLinearMap R r f).comp e.toLinearMap) :
    Nonempty (koszulComplexOn R r f ≅ koszulComplexOn R r g) := by
  sorry

theorem koszul_change_basis_matrix
    (R : Type u) [CommRing R] (r : ℕ) (X : Matrix (Fin r) (Fin r) R)
    [Invertible X] (f : Fin r → R) :
    Nonempty (koszulComplexOn R r f ≅
      koszulComplexOn R r (matrixChangeSequence R r X f)) := by
  sorry

/-! ## Homotopies and annihilation -/

/-- Multiplication by a scalar on every term of a complex. -/
noncomputable def scalarChainMap {α : Type*} [AddRightCancelSemigroup α] [One α]
    [DecidableEq α] (R : Type u) [CommRing R]
    (A : ChainComplex (ModuleCat.{u} R) α) (a : R) : A ⟶ A :=
  ChainComplex.ofHom (fun n => a • 𝟙 (A.X n)) (by
    intro n
    simp)

/-- The abstract Koszul contracting homotopy. -/
theorem koszul_homotopy_abstract
    (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (e : E) :
    Nonempty (Homotopy
      (scalarChainMap R (koszulComplex R E φ) (φ e)) 0) := by
  sorry

theorem koszul_homotopy_sequence
    (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R) (i : Fin r) :
    Nonempty (Homotopy
      (scalarChainMap R (koszulComplexOn R r f) (f i)) 0) := by
  sorry

/-- An ideal acts by zero on a module. -/
def IdealActsByZero (R : Type u) [CommRing R] (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] : Prop :=
  ∀ a ∈ I, ∀ x : M, a • x = 0

theorem koszul_homology_annihilated
    (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R) (n : ℤ) :
    IdealActsByZero R (Ideal.span (Set.range f))
      ((koszulComplexOn R r f).homology n) := by
  sorry

/-! ## Mapping cones -/

/-- Mathlib's homotopy cofiber is the mapping cone of a chain map. -/
noncomputable abbrev homotopyCone {R : Type u} [CommRing R]
    {A B : ChainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) :=
  HomologicalComplex.homotopyCofiber f

/-- The canonical inclusion of the target into a homotopy cone. -/
noncomputable abbrev coneInclusion {R : Type u} [CommRing R]
    {A B : ChainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) :
    B ⟶ homotopyCone f :=
  HomologicalComplex.homotopyCofiber.inr f

/-- A component of the canonical projection from a cone to its shifted source. -/
noncomputable abbrev coneProjectionComponent {R : Type u} [CommRing R]
    {A B : ChainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B)
    (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    (homotopyCone f).X i ⟶ A.X j :=
  HomologicalComplex.homotopyCofiber.fstX f i j hij

theorem homotopyCone_d_fst
    {R : Type u} [CommRing R] {A B : ChainComplex (ModuleCat.{u} R) ℤ}
    (f : A ⟶ B) (i j k : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) (hjk : (ComplexShape.down ℤ).Rel j k) :
    (homotopyCone f).d i j ≫
        HomologicalComplex.homotopyCofiber.fstX f j k hjk =
      -HomologicalComplex.homotopyCofiber.fstX f i j hij ≫ A.d j k := by
  exact HomologicalComplex.homotopyCofiber.d_fstX f i j k hij hjk

theorem homotopyCone_d_snd
    {R : Type u} [CommRing R] {A B : ChainComplex (ModuleCat.{u} R) ℤ}
    (f : A ⟶ B) (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    (homotopyCone f).d i j ≫
        HomologicalComplex.homotopyCofiber.sndX f j =
      HomologicalComplex.homotopyCofiber.fstX f i j hij ≫ f.f j +
        HomologicalComplex.homotopyCofiber.sndX f i ≫ B.d i j := by
  exact HomologicalComplex.homotopyCofiber.d_sndX f i j hij

/-- The map whose cone is the Koszul complex after adjoining one generator. -/
def koszulExtendedMap (R E : Type u) [CommRing R] [AddCommGroup E]
    [Module R E] (φ : E →ₗ[R] R) (f : R) : (E × R) →ₗ[R] R :=
  { toFun := fun x => φ x.1 + f * x.2
    map_add' := by
      intro x y
      simp [map_add]
      rw [mul_add]
      ac_rfl
    map_smul' := by
      intro a x
      simp [smul_eq_mul, mul_add, mul_left_comm] }

theorem koszul_cone_abstract
    (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (f : R) :
    Nonempty (koszulComplex R (E × R) (koszulExtendedMap R E φ f) ≅
      homotopyCone (scalarChainMap R (koszulComplex R E φ) f)) := by
  sorry

theorem koszul_cone_sequence
    (R : Type u) [CommRing R] (r : ℕ) (f : Fin (r + 1) → R) :
    Nonempty (koszulComplexOn R (r + 1) f ≅
      homotopyCone
        (scalarChainMap R
          (koszulComplexOn R r (fun i => f i.castSucc)) (f (Fin.last r)))) := by
  sorry

/-! ## Squared cones and multiplication -/

abbrev IntegerChainComplex (R : Type u) [CommRing R] :=
  ChainComplex (ModuleCat.{u} R) ℤ

noncomputable abbrev chainShiftOne {R : Type u} [CommRing R]
    (A : IntegerChainComplex R) : IntegerChainComplex R :=
  (Formalization.Books.Homology.Unit14.ChainComplex.shiftFunctor
    (ModuleCat.{u} R) (1 : ℤ)).obj A

noncomputable abbrev integerHomotopyCone {R : Type u} [CommRing R]
    {A B : IntegerChainComplex R} (f : A ⟶ B) :=
  HomologicalComplex.homotopyCofiber f

theorem homotopyCone_squared
    (R : Type u) [CommRing R] (A : IntegerChainComplex R) (f g : R) :
    ∃ q : chainShiftOne (integerHomotopyCone (scalarChainMap R A f)) ⟶
        integerHomotopyCone (scalarChainMap R A g),
      Nonempty (HomotopyEquiv
        (integerHomotopyCone (scalarChainMap R A (f * g)))
        (integerHomotopyCone q)) := by
  sorry

theorem koszul_multiplicative_abstract
    (R E : Type u) [CommRing R] [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (f g : R) :
    ∃ q : chainShiftOne
          (koszulComplex R (E × R) (koszulExtendedMap R E φ f)) ⟶
        koszulComplex R (E × R) (koszulExtendedMap R E φ g),
      Nonempty (HomotopyEquiv
        (koszulComplex R (E × R) (koszulExtendedMap R E φ (f * g)))
        (integerHomotopyCone q)) := by
  sorry

theorem koszul_multiplicative_sequence
    (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R) (a b : R) :
    ∃ q : chainShiftOne
          (koszulComplexOn R (r + 1) (sequenceAppendLast r f a)) ⟶
        koszulComplexOn R (r + 1) (sequenceAppendLast r f b),
      Nonempty (HomotopyEquiv
        (koszulComplexOn R (r + 1) (sequenceAppendLast r f (a * b)))
        (integerHomotopyCone q)) := by
  sorry

/-! ## Joins of sequences -/

/-- Concatenation of two finite sequences. -/
def joinSequences {r s : ℕ} (f : Fin r → R) (g : Fin s → R) : Fin (r + s) → R :=
  Fin.append f g

/-- The canonical total tensor complex of two nonnegative chain complexes. -/
abbrev NatChainComplex (R : Type u) [CommRing R] :=
  ChainComplex (ModuleCat.{u} R) ℕ

noncomputable abbrev tensorChainComplex (R : Type u) [CommRing R]
    (K L : NatChainComplex R) : NatChainComplex R :=
  HomologicalComplex.tensorObj K L

theorem koszul_join_sequences
    (R : Type u) [CommRing R] {r s : ℕ} (f : Fin r → R) (g : Fin s → R) :
    Nonempty (koszulComplexOnNat R (r + s) (joinSequences f g) ≅
      tensorChainComplex R (koszulComplexOnNat R r f) (koszulComplexOnNat R s g)) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit29
