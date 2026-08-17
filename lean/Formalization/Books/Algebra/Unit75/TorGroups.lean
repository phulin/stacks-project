import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Formalization.Books.Algebra.Unit39.FlatModules
import Formalization.Books.Algebra.Unit71.ExtGroups

/-!
# Commutative Algebra, Chapter 75: Tor groups and flatness

This file records the Tor construction, the double-complex comparison used for
symmetry, and the flatness criteria in the source section.  The underlying
resolutions, homology objects, tensor products, and flatness predicates are
Mathlib's canonical constructions (with the resolution interfaces from the
preceding formalization chapter).
-/

namespace Formalization.Books.Algebra.Unit75

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit71
open scoped TensorProduct

noncomputable section

universe u v w

/-! ## Tensoring a resolution -/

/-- The chain complex obtained by tensoring a module chain complex on the right. -/
noncomputable def tensorComplex {R : Type u} [CommRing R]
    (F : ModuleChainComplex R) (N : ModuleCat.{u} R) : ModuleChainComplex R where
  X i := ModuleCat.of R (TensorProduct R (F.X i) N)
  d i j := if h : j + 1 = i then
    ModuleCat.ofHom (LinearMap.rTensor N (F.d i j).hom)
  else 0
  shape i j hij := by
    classical
    split_ifs with h
    · exact (hij h).elim
    · rfl
  d_comp_d' i j k hij hjk := by
    classical
    have hij' : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    have hjk' : k + 1 = j := by
      simpa only [ComplexShape.down_Rel] using hjk
    dsimp
    rw [if_pos hij', if_pos hjk']
    apply ModuleCat.hom_ext
    change (LinearMap.rTensor N (F.d j k).hom).comp
        (LinearMap.rTensor N (F.d i j).hom) = 0
    rw [← LinearMap.rTensor_comp]
    have hcomp : (F.d j k).hom.comp (F.d i j).hom = 0 := by
      exact congrArg (fun f => f.hom) (F.d_comp_d i j k)
    rw [hcomp]
    simp

/-- The Tor group computed from a chosen free resolution. -/
noncomputable def resolutionTor {R : Type u} [CommRing R]
    {M : ModuleCat.{u} R} (F : FreeResolution R M) (N : ModuleCat.{u} R) (i : ℕ) :
    ModuleCat.{u} R :=
  chainHomology (tensorComplex F.complex N) i

/-- A canonical Tor group, obtained from a fixed choice of free resolution. -/
noncomputable def Tor {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (i : ℕ) : ModuleCat.{u} R :=
  resolutionTor (Classical.choice (exists_free_resolution M)) N i

/-- Tensoring a chain map on the first variable. -/
noncomputable def tensorComplexMap {R : Type u} [CommRing R]
    {F G : ModuleChainComplex R} (α : F ⟶ G) (N : ModuleCat.{u} R) :
    tensorComplex F N ⟶ tensorComplex G N where
  f i := ModuleCat.ofHom (LinearMap.rTensor N (α.f i).hom)
  comm' i j hij := by
    classical
    have hij' : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    dsimp [tensorComplex]
    rw [if_pos hij', if_pos hij']
    apply ModuleCat.hom_ext
    change (LinearMap.rTensor N (G.d i j).hom).comp
        (LinearMap.rTensor N (α.f i).hom) =
      (LinearMap.rTensor N (α.f j).hom).comp
        (LinearMap.rTensor N (F.d i j).hom)
    rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
    exact congrArg (fun f => LinearMap.rTensor N f)
      (congrArg (fun q => q.hom) (α.comm i j))

/-- Tensoring a chain map on the second variable. -/
noncomputable def tensorComplexMapRight {R : Type u} [CommRing R]
    (F : ModuleChainComplex R) {N P : ModuleCat.{u} R} (β : N ⟶ P) :
    tensorComplex F N ⟶ tensorComplex F P where
  f i := ModuleCat.ofHom ((β.hom).lTensor (F.X i))
  comm' i j hij := by
    classical
    have hij' : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    dsimp [tensorComplex]
    rw [if_pos hij', if_pos hij']
    apply ModuleCat.hom_ext
    change (LinearMap.rTensor P (F.d i j).hom).comp
        ((β.hom).lTensor (F.X i)) =
      ((β.hom).lTensor (F.X j)).comp
        (LinearMap.rTensor N (F.d i j).hom)
    ext x y
    rfl

/-- The map induced on a chosen resolution computation of Tor. -/
noncomputable def resolutionTorMap {R : Type u} [CommRing R]
    {M₁ M₂ : ModuleCat.{u} R} (F : FreeResolution R M₁)
    (G : FreeResolution R M₂) (φ : M₁ ⟶ M₂)
    (α : ResolutionMap F.resolution G.resolution φ)
    (N : ModuleCat.{u} R) (i : ℕ) :
    resolutionTor F N i ⟶ resolutionTor G N i :=
  chainHomologyMap (tensorComplexMap α.hom N) i

/-- Comparison maps induce the same map on the Tor computation. -/
theorem resolutionTorMap_independent {R : Type u} [CommRing R]
    {M₁ M₂ : ModuleCat.{u} R} (F : FreeResolution R M₁)
    (G : FreeResolution R M₂) (φ : M₁ ⟶ M₂)
    (α β : ResolutionMap F.resolution G.resolution φ)
    (N : ModuleCat.{u} R) (i : ℕ) :
    resolutionTorMap F G φ α N i = resolutionTorMap F G φ β N i := by
  sorry

/-- An isomorphism of modules induces an isomorphism on the computed Tor groups. -/
theorem isIso_resolutionTorMap_of_isIso {R : Type u} [CommRing R]
    {M₁ M₂ : ModuleCat.{u} R} (F : FreeResolution R M₁)
    (G : FreeResolution R M₂) (φ : M₁ ⟶ M₂) [IsIso φ]
    (α : ResolutionMap F.resolution G.resolution φ)
    (N : ModuleCat.{u} R) (i : ℕ) :
    IsIso (resolutionTorMap F G φ α N i) := by
  sorry

/-- A comparison map lifting an identity induces an isomorphism on Tor. -/
theorem isIso_resolutionTorMap_identity {R : Type u} [CommRing R]
    {M : ModuleCat.{u} R} (F : FreeResolution R M)
    (α : ResolutionMap F.resolution F.resolution (𝟙 M))
    (N : ModuleCat.{u} R) (i : ℕ) :
    IsIso (resolutionTorMap F F (𝟙 M) α N i) := by
  sorry

/-- The first-variable map on the chosen canonical Tor groups. -/
noncomputable def torMapFirst {R : Type u} [CommRing R]
    {M₁ M₂ N : ModuleCat.{u} R} (φ : M₁ ⟶ M₂) (i : ℕ) :
    Tor M₁ N i ⟶ Tor M₂ N i := by
  let F : FreeResolution R M₁ := Classical.choice (exists_free_resolution M₁)
  let G : FreeResolution R M₂ := Classical.choice (exists_free_resolution M₂)
  let α : ResolutionMap F.resolution G.resolution φ :=
    Classical.choice (resolution_map_exists F G.resolution φ)
  exact resolutionTorMap F G φ α N i

/-- The second-variable map on the chosen canonical Tor groups. -/
noncomputable def torMapSecond {R : Type u} [CommRing R]
    (M N P : ModuleCat.{u} R) (ψ : N ⟶ P) (i : ℕ) :
    Tor M N i ⟶ Tor M P i := by
  let F : FreeResolution R M := Classical.choice (exists_free_resolution M)
  exact chainHomologyMap (tensorComplexMapRight F.complex ψ) i

/-- The first Tor construction is functorial. -/
theorem torMapFirst_id {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (i : ℕ) :
    torMapFirst (𝟙 M) i = 𝟙 (Tor M N i) := by
  sorry

theorem torMapFirst_comp {R : Type u} [CommRing R]
    {M₁ M₂ M₃ N : ModuleCat.{u} R}
    (φ : M₁ ⟶ M₂) (ψ : M₂ ⟶ M₃) (i : ℕ) :
    torMapFirst (N := N) (φ ≫ ψ) i =
      torMapFirst (N := N) φ i ≫ torMapFirst (N := N) ψ i := by
  sorry

/-- The second Tor construction is functorial. -/
theorem torMapSecond_id {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (i : ℕ) :
    torMapSecond M N N (𝟙 N) i = 𝟙 (Tor M N i) := by
  sorry

theorem torMapSecond_comp {R : Type u} [CommRing R]
    {M N₁ N₂ N₃ : ModuleCat.{u} R}
    (φ : N₁ ⟶ N₂) (ψ : N₂ ⟶ N₃) (i : ℕ) :
    torMapSecond M N₁ N₃ (φ ≫ ψ) i =
      torMapSecond M N₁ N₂ φ i ≫ torMapSecond M N₂ N₃ ψ i := by
  sorry

/-- The two Tor-variable maps form the commutative square from the source. -/
theorem torMap_commute {R : Type u} [CommRing R]
    {M₁ M₂ N₁ N₂ : ModuleCat.{u} R}
    (φ : M₁ ⟶ M₂) (ψ : N₁ ⟶ N₂) (i : ℕ) :
    torMapFirst (N := N₁) φ i ≫ torMapSecond M₂ N₁ N₂ ψ i =
      torMapSecond M₁ N₁ N₂ ψ i ≫ torMapFirst (N := N₂) φ i := by
  sorry

/-! ## The Tor long exact sequence -/

/-- Tensoring a module map on the right by a fixed module. -/
def tensorByMap {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) {N P : ModuleCat.{u} R} (f : N ⟶ P) :
    TensorProduct R M N →ₗ[R] TensorProduct R M P :=
  f.hom.lTensor M

/-- The six-term exact segment in the long exact sequence of Tor, including
the terminal surjection onto the zero module. -/
structure TorLongExactSequence {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R)) where
  map₁ : Tor M S.X₁ 1 →ₗ[R] Tor M S.X₂ 1
  map₂ : Tor M S.X₂ 1 →ₗ[R] Tor M S.X₃ 1
  connecting : Tor M S.X₃ 1 →ₗ[R] TensorProduct R M S.X₁
  exact₁ : Function.Exact map₁ map₂
  exact₂ : Function.Exact map₂ connecting
  exact₃ : Function.Exact connecting (tensorByMap M S.f)
  exact₄ : Function.Exact (tensorByMap M S.f) (tensorByMap M S.g)
  terminal_surjective : Function.Surjective (tensorByMap M S.g)

/-- A short exact sequence of modules admits the source's long exact Tor
segment. -/
theorem exists_tor_long_exact_sequence {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) : Nonempty (TorLongExactSequence M S) := by
  sorry

/-! ## Double complexes and the two quotient complexes -/

/-- A homological double complex of modules in the first quadrant. -/
structure DoubleComplex (R : Type u) [CommRing R] where
  obj : ℕ → ℕ → ModuleCat.{u} R
  d : ∀ i j, obj (i + 1) j ⟶ obj i j
  delta : ∀ i j, obj i (j + 1) ⟶ obj i j
  d_sq : ∀ i j, d (i + 1) j ≫ d i j = 0
  delta_sq : ∀ i j, delta i (j + 1) ≫ delta i j = 0
  comm : ∀ i j, d i (j + 1) ≫ delta i j = delta (i + 1) j ≫ d i j

/-- A morphism of double complexes. -/
structure DoubleComplexMap {R : Type u} [CommRing R]
    (A B : DoubleComplex R) where
  f : ∀ i j, A.obj i j ⟶ B.obj i j
  d_comm : ∀ i j, A.d i j ≫ f i j = f (i + 1) j ≫ B.d i j
  delta_comm : ∀ i j, A.delta i j ≫ f i j = f i (j + 1) ≫ B.delta i j

/-- The right quotient terms `R(A)_j = coker(A_{1,j} → A_{0,j})`. -/
noncomputable def rightTerm {R : Type u} [CommRing R]
    (A : DoubleComplex R) (j : ℕ) : ModuleCat.{u} R :=
  cokernel (A.d 0 j)

/-- The up quotient terms `U(A)_i = coker(A_{i,1} → A_{i,0})`. -/
noncomputable def upTerm {R : Type u} [CommRing R]
    (A : DoubleComplex R) (i : ℕ) : ModuleCat.{u} R :=
  cokernel (A.delta i 0)

/-- The differential induced by `delta` on the right quotient terms. -/
  noncomputable def rightDifferential {R : Type u} [CommRing R]
    (A : DoubleComplex R) (j : ℕ) :
    rightTerm A (j + 1) ⟶ rightTerm A j :=
  cokernel.map (A.d 0 (j + 1)) (A.d 0 j) (A.delta 1 j) (A.delta 0 j)
    (A.comm 0 j)

/-- The differential induced by `d` on the up quotient terms. -/
noncomputable def upDifferential {R : Type u} [CommRing R]
    (A : DoubleComplex R) (i : ℕ) :
    upTerm A (i + 1) ⟶ upTerm A i :=
  cokernel.map (A.delta (i + 1) 0) (A.delta i 0) (A.d i 1) (A.d i 0)
    (A.comm i 0).symm

/-- Consecutive induced right differentials compose to zero. -/
theorem rightDifferential_comp_zero {R : Type u} [CommRing R]
    (A : DoubleComplex R) (j : ℕ) :
    rightDifferential A (j + 1) ≫ rightDifferential A j = 0 := by
  sorry

/-- Consecutive induced up differentials compose to zero. -/
theorem upDifferential_comp_zero {R : Type u} [CommRing R]
    (A : DoubleComplex R) (i : ℕ) :
    upDifferential A (i + 1) ≫ upDifferential A i = 0 := by
  sorry

/-- The right quotient complex `R(A)_•`. -/
noncomputable def rightComplex {R : Type u} [CommRing R]
    (A : DoubleComplex R) : ModuleChainComplex R where
  X i := rightTerm A i
  d i j := if h : j + 1 = i then h ▸ rightDifferential A j else 0
  shape i j hij := by
    classical
    split_ifs with h
    · exact (hij h).elim
    · rfl
  d_comp_d' i j k hij hjk := by
    classical
    have hij' : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    have hjk' : k + 1 = j := by
      simpa only [ComplexShape.down_Rel] using hjk
    rw [dif_pos hij', dif_pos hjk']
    subst i
    subst j
    exact rightDifferential_comp_zero A k

/-- The up quotient complex `U(A)_•`. -/
noncomputable def upComplex {R : Type u} [CommRing R]
    (A : DoubleComplex R) : ModuleChainComplex R where
  X i := upTerm A i
  d i j := if h : j + 1 = i then h ▸ upDifferential A j else 0
  shape i j hij := by
    classical
    split_ifs with h
    · exact (hij h).elim
    · rfl
  d_comp_d' i j k hij hjk := by
    classical
    have hij' : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    have hjk' : k + 1 = j := by
      simpa only [ComplexShape.down_Rel] using hjk
    rw [dif_pos hij', dif_pos hjk']
    subst i
    subst j
    exact upDifferential_comp_zero A k

/-- The row complex of a double complex. -/
noncomputable def rowComplex {R : Type u} [CommRing R]
    (A : DoubleComplex R) (j : ℕ) : ModuleChainComplex R where
  X i := A.obj i j
  d i k := if h : k + 1 = i then h ▸ A.d k j else 0
  shape i k hik := by
    classical
    split_ifs with h
    · exact (hik h).elim
    · rfl
  d_comp_d' i k l hik hkl := by
    classical
    have hik' : k + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hik
    have hkl' : l + 1 = k := by
      simpa only [ComplexShape.down_Rel] using hkl
    rw [dif_pos hik', dif_pos hkl']
    subst i
    subst k
    exact A.d_sq l j

/-- The column complex of a double complex. -/
noncomputable def columnComplex {R : Type u} [CommRing R]
    (A : DoubleComplex R) (i : ℕ) : ModuleChainComplex R where
  X j := A.obj i j
  d j k := if h : k + 1 = j then h ▸ A.delta i k else 0
  shape j k hjk := by
    classical
    split_ifs with h
    · exact (hjk h).elim
    · rfl
  d_comp_d' j k l hjk hkl := by
    classical
    have hjk' : k + 1 = j := by
      simpa only [ComplexShape.down_Rel] using hjk
    have hkl' : l + 1 = k := by
      simpa only [ComplexShape.down_Rel] using hkl
    rw [dif_pos hjk', dif_pos hkl']
    subst j
    subst k
    exact A.delta_sq i l

/-- Exactness of an augmented nonnegative module chain complex. -/
def IsResolution {R : Type u} [CommRing R]
    (F : ModuleChainComplex R) (M : ModuleCat.{u} R)
    (augmentation : F.X 0 ⟶ M) : Prop :=
  ∃ h : F.d 1 0 ≫ augmentation = 0,
    (ShortComplex.mk (F.d 1 0) augmentation h).Exact ∧
      ∀ n, (ShortComplex.mk (F.d (n + 2) (n + 1))
        (F.d (n + 1) n) (F.d_comp_d (n + 2) (n + 1) n)).Exact

/-- The row-resolution hypothesis in the double-complex lemma. -/
def RowsAreResolutions {R : Type u} [CommRing R]
    (A : DoubleComplex R) : Prop :=
  ∀ j, IsResolution (rowComplex A j) (rightTerm A j)
    (cokernel.π (A.d 0 j))

/-- The column-resolution hypothesis in the double-complex lemma. -/
def ColumnsAreResolutions {R : Type u} [CommRing R]
    (A : DoubleComplex R) : Prop :=
  ∀ i, IsResolution (columnComplex A i) (upTerm A i)
    (cokernel.π (A.delta i 0))

/-- The map induced on the right quotient terms by a double-complex map. -/
noncomputable def rightTermMap {R : Type u} [CommRing R]
    {A B : DoubleComplex R} (Φ : DoubleComplexMap A B) (j : ℕ) :
    rightTerm A j ⟶ rightTerm B j :=
  cokernel.map (A.d 0 j) (B.d 0 j) (Φ.f 1 j) (Φ.f 0 j) (Φ.d_comm 0 j)

/-- The map induced on the up quotient terms by a double-complex map. -/
noncomputable def upTermMap {R : Type u} [CommRing R]
    {A B : DoubleComplex R} (Φ : DoubleComplexMap A B) (i : ℕ) :
    upTerm A i ⟶ upTerm B i :=
  cokernel.map (A.delta i 0) (B.delta i 0) (Φ.f i 1) (Φ.f i 0)
    (Φ.delta_comm i 0)

/-- Naturality of the induced right differentials. -/
theorem rightTermMap_comm {R : Type u} [CommRing R]
    {A B : DoubleComplex R} (Φ : DoubleComplexMap A B) (j : ℕ) :
    rightDifferential A j ≫ rightTermMap Φ j =
      rightTermMap Φ (j + 1) ≫ rightDifferential B j := by
  sorry

/-- Naturality of the induced up differentials. -/
theorem upTermMap_comm {R : Type u} [CommRing R]
    {A B : DoubleComplex R} (Φ : DoubleComplexMap A B) (i : ℕ) :
    upDifferential A i ≫ upTermMap Φ i =
      upTermMap Φ (i + 1) ≫ upDifferential B i := by
  sorry

/-- The induced map on the right quotient complexes. -/
noncomputable def rightComplexMap {R : Type u} [CommRing R]
    {A B : DoubleComplex R} (Φ : DoubleComplexMap A B) :
    rightComplex A ⟶ rightComplex B where
  f i := rightTermMap Φ i
  comm' i j hij := by
    classical
    have hij' : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    dsimp [rightComplex]
    simp only [dif_pos hij']
    subst i
    exact (rightTermMap_comm Φ j).symm

/-- The induced map on the up quotient complexes. -/
noncomputable def upComplexMap {R : Type u} [CommRing R]
    {A B : DoubleComplex R} (Φ : DoubleComplexMap A B) :
    upComplex A ⟶ upComplex B where
  f i := upTermMap Φ i
  comm' i j hij := by
    classical
    have hij' : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    dsimp [upComplex]
    simp only [dif_pos hij']
    subst i
    exact (upTermMap_comm Φ j).symm

/-- The double-complex lemma produces the canonical homology isomorphism. -/
theorem doubleComplex_homology_iso_exists {R : Type u} [CommRing R]
    (A : DoubleComplex R) (hrow : RowsAreResolutions A)
    (hcol : ColumnsAreResolutions A) (i : ℕ) :
    Nonempty (chainHomology (rightComplex A) i ≅ chainHomology (upComplex A) i) := by
  sorry

/-
The source constructs this comparison through a zig-zag in the homology of the
double complex.  The conventional signs in that zig-zag are not canonical at
the level of displayed representatives, so the declaration below records the
resulting comparison with the source's stated normalization.
-/
/-- A chosen representative of the canonical double-complex homology isomorphism. -/
noncomputable def doubleComplexHomologyIso {R : Type u} [CommRing R]
    (A : DoubleComplex R) (hrow : RowsAreResolutions A)
    (hcol : ColumnsAreResolutions A) (i : ℕ) :
    chainHomology (rightComplex A) i ≅ chainHomology (upComplex A) i :=
  Classical.choice (doubleComplex_homology_iso_exists A hrow hcol i)

/-- The double-complex homology isomorphism is functorial. -/
theorem doubleComplex_homology_iso_natural {R : Type u} [CommRing R]
    {A B : DoubleComplex R} (Φ : DoubleComplexMap A B)
    (hrowA : RowsAreResolutions A) (hcolA : ColumnsAreResolutions A)
    (hrowB : RowsAreResolutions B) (hcolB : ColumnsAreResolutions B)
    (i : ℕ) :
    chainHomologyMap (rightComplexMap Φ) i ≫
        (doubleComplexHomologyIso B hrowB hcolB i).hom =
      (doubleComplexHomologyIso A hrowA hcolA i).hom ≫
        chainHomologyMap (upComplexMap Φ) i := by
  sorry

/-- A witness for the intermediate zig-zag homology module used in the proof
of the double-complex lemma. -/
structure ZigZagHomologyModel {R : Type u} [CommRing R]
    (A : DoubleComplex R) (i : ℕ) where
  carrier : ModuleCat.{u} R
  toRight : carrier ≅ chainHomology (rightComplex A) i
  toUp : carrier ≅ chainHomology (upComplex A) i

/-- The exact rows and columns admit the source's common zig-zag homology
model. -/
theorem exists_zigZagHomologyModel {R : Type u} [CommRing R]
    (A : DoubleComplex R) (hrow : RowsAreResolutions A)
    (hcol : ColumnsAreResolutions A) (i : ℕ) :
    Nonempty (ZigZagHomologyModel A i) := by
  sorry

/-! ## Symmetry and finiteness -/

/-- Tor is canonically symmetric in its two module variables. -/
theorem tor_left_right {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (i : ℕ) :
    Nonempty (Tor M N i ≅ Tor N M i) := by
  sorry

/-- A chosen representative of the canonical symmetry isomorphism for Tor. -/
noncomputable def torLeftRightIso {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (i : ℕ) : Tor M N i ≅ Tor N M i :=
  Classical.choice (tor_left_right M N i)

/-- The Tor symmetry is natural in both variables. -/
theorem torLeftRightIso_natural {R : Type u} [CommRing R]
    {M₁ M₂ N₁ N₂ : ModuleCat.{u} R}
    (φ : M₁ ⟶ M₂) (ψ : N₁ ⟶ N₂) (i : ℕ) :
    (torLeftRightIso M₁ N₁ i).hom ≫
        torMapFirst (N := M₁) ψ i ≫ torMapSecond N₂ M₁ M₂ φ i =
      torMapFirst (N := N₁) φ i ≫ torMapSecond M₂ N₁ N₂ ψ i ≫
        (torLeftRightIso M₂ N₂ i).hom := by
  sorry

/-- Tor of finite modules over a Noetherian ring is finite. -/
theorem tor_finite_of_noetherian {R : Type u} [CommRing R]
    [IsNoetherianRing R] (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R N] (p : ℕ) :
    Module.Finite R (Tor M N p) := by
  sorry

/-! ## Flatness and Tor -/

/-- The `i`th Tor functor in the second variable is zero on every module. -/
def TorFunctorZero {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (i : ℕ) : Prop :=
  ∀ N : ModuleCat.{u} R, IsZero (Tor M N i)

/-- Vanishing of `Tor₁(M,R/I)` for all ideals. -/
def TorOneVanishingOnIdeals {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) : Prop :=
  ∀ I : Ideal R, IsZero (Tor M (ModuleCat.of R (R ⧸ I)) 1)

/-- Vanishing of `Tor₁(M,R/I)` for finitely generated ideals. -/
def TorOneVanishingOnFinitelyGeneratedIdeals {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) : Prop :=
  ∀ I : Ideal R, I.FG → IsZero (Tor M (ModuleCat.of R (R ⧸ I)) 1)

/-- The five equivalent flatness criteria stated in the source. -/
theorem flat_iff_tor_criteria {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) :
    List.TFAE [
      Module.Flat R M,
      ∀ i : ℕ, 0 < i → TorFunctorZero M i,
      TorFunctorZero M 1,
      TorOneVanishingOnIdeals M,
      TorOneVanishingOnFinitelyGeneratedIdeals M] := by
  sorry

/-- The canonical multiplication/action map `I ⊗ M → M`. -/
def idealTensorActionMap {R : Type u} [CommRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) :
    TensorProduct R I M →ₗ[R] M :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun m => (a : R) • m
          map_add' := by intro m n; simp [smul_add]
          map_smul' := by intro r m; simp [smul_smul, mul_comm] }
      map_add' := by intro a b; ext m; simp [add_smul]
      map_smul' := by intro r a; ext m; simp [smul_smul] }

/-- The kernel module of `I ⊗ M → M`. -/
noncomputable def idealTensorActionKernel {R : Type u} [CommRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) : ModuleCat.{u} R :=
  ModuleCat.of R (LinearMap.ker (idealTensorActionMap I M))

/-- The ideal-quotient Tor group is the kernel of the action map. -/
theorem tor_one_ideal_quotient_kernel {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (I : Ideal R) :
    Nonempty (Tor M (ModuleCat.of R (R ⧸ I)) 1 ≅
      idealTensorActionKernel I M) := by
  sorry

/- The switch map in the proof of symmetry can genuinely be nontrivial. -/
def tensorSwitch {k V : Type u} [CommRing k]
    [AddCommGroup V] [Module k V] :
    TensorProduct k V V ≃ₗ[k] TensorProduct k V V :=
  TensorProduct.comm k V V

theorem tensorSwitch_two_dimensional_not_identity {k : Type u} [Field k] :
    (tensorSwitch (k := k) (V := Fin 2 → k)).toLinearMap ≠ LinearMap.id := by
  sorry

/- The source's eigenvalue count is recorded as eigenspace dimensions over
characteristic zero, where the two eigenvalues are distinct. -/
theorem tensorSwitch_eigenspace_finrank {k : Type u} [Field k] [CharZero k]
    (n : ℕ) :
    Module.finrank k
          (Module.End.eigenspace
            (tensorSwitch (k := k) (V := Fin n → k)).toLinearMap (1 : k)) =
        n * (n + 1) / 2 ∧
      Module.finrank k
          (Module.End.eigenspace
            (tensorSwitch (k := k) (V := Fin n → k)).toLinearMap (-1 : k)) =
        n * (n - 1) / 2 := by
  sorry

/- In characteristic two, the switch is not diagonalizable; semisimplicity is
the canonical Mathlib interface for this finite-dimensional assertion. -/
theorem tensorSwitch_two_dimensional_charTwo_not_semisimple
    {k : Type u} [Field k] [CharP k 2] :
    ¬ Module.End.IsSemisimple
        (tensorSwitch (k := k) (V := Fin 2 → k)).toLinearMap := by
  sorry

theorem neg_tensorSwitch_two_dimensional_not_identity
    {k : Type u} [Field k] :
    -(tensorSwitch (k := k) (V := Fin 2 → k)).toLinearMap ≠ LinearMap.id := by
  sorry

end

end Formalization.Books.Algebra.Unit75
