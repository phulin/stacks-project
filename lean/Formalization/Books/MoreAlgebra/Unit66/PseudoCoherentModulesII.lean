import Formalization.Books.MoreAlgebra.Unit65.PseudoCoherentModules
import Formalization.Books.Derived.Unit27.ExtGroups
import Formalization.Books.Algebra.Unit10.InternalHom
import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Ideal.Operations

/-!
# More on Algebra, Chapter 66: Pseudo-coherent modules, II

This file records the seven lemmas in the section.  Chapter 65 supplies the
pseudo-coherence predicates; the derived Ext convention is the shifted-Hom
convention from Derived Categories, Chapter 27.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Formalization.Books.Algebra.Unit10
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit27
open Formalization.Books.MoreAlgebra.Unit56
open Formalization.Books.MoreAlgebra.Unit59
open Formalization.Books.MoreAlgebra.Unit65

universe u v w

namespace Formalization.Books.MoreAlgebra.Unit66

abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] := Unit65.D R

/-! ## Filtered colimits and Ext -/

noncomputable abbrev derivedExtObject
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (M : Mod R) (n : ℤ) : AddCommGrpCat.{w} :=
  AddCommGrpCat.of (DerivedExt K (DerivedObject M) n)

noncomputable def derivedExtPostcompositionFunctor
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (n : ℤ) :
    Mod R ⥤ AddCommGrpCat.{w} where
  obj M := derivedExtObject R K M n
  map f := AddCommGrpCat.ofHom
    (derivedExtPostcomp ((DerivedCategory.singleFunctor (Mod R) 0).map f) n)
  map_id M := by
    ext ξ
    simp [derivedExtPostcomp, derivedExtComp, ShiftedHom.comp_mk₀_id]
  map_comp f g := by
    ext ξ
    simp [derivedExtPostcomp, derivedExtComp, ShiftedHom.comp_mk₀]

noncomputable def derivedExtColimitComparison
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    {J : Type v} [Category.{w} J] [IsFilteredOrEmpty J]
    (F : J ⥤ Mod R) [HasColimit F]
    (K : D R) (n : ℤ)
    [HasColimit (F ⋙ derivedExtPostcompositionFunctor R K n)] :
    colimit (F ⋙ derivedExtPostcompositionFunctor R K n) ⟶
      derivedExtObject R K (colimit F) n := by
  let G := F ⋙ derivedExtPostcompositionFunctor R K n
  let ι : G ⟶ (Functor.const J).obj (derivedExtObject R K (colimit F) n) :=
    { app := fun j => AddCommGrpCat.ofHom
        (derivedExtPostcomp
          ((DerivedCategory.singleFunctor (Mod R) 0).map (colimit.ι F j)) n)
      naturality := by
        intro i j f
        ext ξ
        change DerivedExt K (DerivedObject (F.obj i)) n at ξ
        change
          derivedExtPostcomp
              ((DerivedCategory.singleFunctor (Mod R) 0).map (colimit.ι F j)) n
            (derivedExtPostcomp
              ((DerivedCategory.singleFunctor (Mod R) 0).map (F.map f)) n ξ) =
          derivedExtPostcomp
            ((DerivedCategory.singleFunctor (Mod R) 0).map (colimit.ι F i)) n ξ
        simp only [derivedExtPostcomp, derivedExtComp, ShiftedHom.comp_mk₀]
        change
          (ξ ≫ (shiftFunctor (D R) n).map
              ((DerivedCategory.singleFunctor (Mod R) 0).map (F.map f))) ≫
            (shiftFunctor (D R) n).map
              ((DerivedCategory.singleFunctor (Mod R) 0).map (colimit.ι F j)) =
          ξ ≫ (shiftFunctor (D R) n).map
            ((DerivedCategory.singleFunctor (Mod R) 0).map (colimit.ι F i))
        rw [Category.assoc, ← (shiftFunctor (D R) n).map_comp,
          ← (DerivedCategory.singleFunctor (Mod R) 0).map_comp, colimit.w]
    }
  exact colimit.desc G (Cocone.mk _ ι)

def ExtColimitProperty
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (m : ℤ) : Prop :=
  ∀ {J : Type v} [Category.{w} J] [IsFilteredOrEmpty J]
    (F : J ⥤ Mod R) [HasColimit F]
    [∀ n : ℤ, HasColimit (F ⋙ derivedExtPostcompositionFunctor R K n)],
    (∀ n : ℤ, n < -m → IsIso (derivedExtColimitComparison R F K n)) ∧
      Function.Injective (derivedExtColimitComparison R F K (-m))

theorem pseudoCoherent_colimit_ext
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (m : ℤ)
    (hK : IsMPseudoCoherent R m K) :
    ExtColimitProperty R K m := by
  sorry

theorem characterize_pseudoCoherent_colimit_ext
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (m : ℤ)
    (hK : IsInDMinus R K) :
    IsMPseudoCoherent R m K ↔ ExtColimitProperty R K m := by
  sorry

/-! ## Tensoring Ext with a flat module -/

noncomputable def moduleExtModule
    (R : Type u) [CommRing R] (M N : Mod R) (n : ℕ) : Mod R :=
  ModuleCat.of R (CategoryTheory.Abelian.Ext M N n)

noncomputable abbrev zeroModule (R : Type u) [CommRing R] : Mod R :=
  ModuleCat.of R (Fin 0 → R)

noncomputable def moduleExtModuleZ
    (R : Type u) [CommRing R] (M N : Mod R) (n : ℤ) : Mod R :=
  if 0 ≤ n then moduleExtModule R M N n.toNat else zeroModule R

noncomputable def homTensorComparison
    (R : Type u) [CommRing R] (M N L : Mod R) :
    (ModuleCat.of R
      (TensorProduct R ((M : Type u) →ₗ[R] (N : Type u)) (L : Type u)) : Mod R) ⟶
      (ModuleCat.of R
        ((M : Type u) →ₗ[R] TensorProduct R (N : Type u) (L : Type u)) : Mod R) :=
  ModuleCat.ofHom (TensorProduct.rTensorHomToHomRTensor
    (RingHom.id R) (M : Type u) (N : Type u) (L : Type u))

structure ExtTensorComparisonData
    (R : Type u) [CommRing R] (M N L : Mod R) (n : ℤ) where
  map : MonoidalCategory.tensorObj (moduleExtModuleZ R M N n) L ⟶
    moduleExtModuleZ R M
      (ModuleCat.of R (TensorProduct R (N : Type u) (L : Type u))) n

def ExtTensorComparisonProperty
    (R : Type u) [CommRing R] (M N L : Mod R) (m : ℤ) : Prop :=
  ∀ i : ℤ, i < m → ∃ c : ExtTensorComparisonData R M N L i, IsIso c.map

theorem pseudoCoherence_and_ext
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (L M N : Mod R) (m : ℤ) (hL : Module.Flat R (L : Type u)) :
    (Module.FinitePresentation R (M : Type u) →
      IsIso (homTensorComparison R M N L)) ∧
    (IsMPseudoCoherentModule R (-m) M → ExtTensorComparisonProperty R M N L m) := by
  sorry

structure HomBaseChangeComparisonData
    (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S)
    (M N : Mod R) where
  map : (ModuleCat.extendScalars f).obj
      (ModuleCat.of R ((M : Type u) →ₗ[R] (N : Type u))) ⟶
    ModuleCat.of S
      (((ModuleCat.extendScalars f).obj M : Type u) →ₗ[S]
        ((ModuleCat.extendScalars f).obj N : Type u))

structure ExtBaseChangeComparisonData
    (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S)
    (M N : Mod R) (n : ℤ) where
  map : (ModuleCat.extendScalars f).obj (moduleExtModuleZ R M N n) ⟶
    moduleExtModuleZ S ((ModuleCat.extendScalars f).obj M)
      ((ModuleCat.extendScalars f).obj N) n

theorem pseudoCoherence_and_ext_baseChange
    (R S : Type u) [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (Mod S)]
    (f : R →+* S)
    (hf : RingHom.Flat f) (M N : Mod R) (m : ℤ) :
    (Module.FinitePresentation R (M : Type u) →
      ∃ c : HomBaseChangeComparisonData R S f M N, IsIso c.map) ∧
    (IsMPseudoCoherentModule R (-m) M →
      ∀ i : ℤ, i < m →
        ∃ c : ExtBaseChangeComparisonData R S f M N i, IsIso c.map) := by
  sorry

theorem pseudoCoherence_and_ext_baseChange_noetherian
    (R S : Type u) [CommRing R] [CommRing S] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)] [HasDerivedCategory.{w} (Mod S)]
    (f : R →+* S) (hf : RingHom.Flat f) (M N : Mod R)
    (hM : Module.Finite R (M : Type u)) :
    ∀ i : ℤ, ∃ c : ExtBaseChangeComparisonData R S f M N i, IsIso c.map := by
  sorry

/-! ## Products and derived tensor products -/

noncomputable abbrev derivedModuleProduct
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] {A : Type u} (Q : A → Mod R) : D R :=
  ∏ᶜ fun a => DerivedObject (Q a)

noncomputable def derivedTensorProductProductComparison
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] {A : Type u} (K : D R) (Q : A → D R) :
    derivedTensor K (∏ᶜ Q) ⟶ ∏ᶜ fun a => derivedTensor K (Q a) :=
  Pi.lift (fun a => derivedTensorMap (𝟙 K) (Pi.π Q a))

def IsPseudoCoherentTensorProductCompatible
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) : Prop :=
  ∀ {A : Type u} (Q : A → Mod R),
    IsIso (derivedTensorProductProductComparison R K (fun a => DerivedObject (Q a)))

noncomputable def derivedTensorProductUniformProductComparison
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] {A : Type u} (K : D R) (Q : Mod R) :
    derivedTensor K (DerivedObject (∏ᶜ fun _ : A => Q)) ⟶
      ∏ᶜ fun _ : A => derivedTensor K (DerivedObject Q) :=
  Pi.lift (fun a =>
    derivedTensorMap (𝟙 K)
      ((DerivedCategory.singleFunctor (Mod R) 0).map
        (Pi.π (fun _ : A => Q) a)))

structure DerivedTensorUnitComparisonData
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] where
  iso : ∀ K : D R,
    derivedTensor K (DerivedObject (ModuleCat.of R R)) ≅ K

theorem exists_derivedTensorUnitComparisonData
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] :
    Nonempty (DerivedTensorUnitComparisonData R) := by
  sorry

noncomputable def derivedTensorUnitComparisonData
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] : DerivedTensorUnitComparisonData R :=
  Classical.choice (exists_derivedTensorUnitComparisonData R)

noncomputable def derivedTensorProductFreeProductComparison
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] {A : Type u} (K : D R) :
    derivedTensor K
        (DerivedObject (∏ᶜ fun _ : A => ModuleCat.of R R)) ⟶
      ∏ᶜ fun _ : A => K :=
  Pi.lift (fun a =>
    derivedTensorMap (𝟙 K)
      ((DerivedCategory.singleFunctor (Mod R) 0).map
        (Pi.π (fun _ : A => ModuleCat.of R R) a)) ≫
      ((derivedTensorUnitComparisonData R).iso K).hom)

def IsPseudoCoherentTensorProductUniformCompatible
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) : Prop :=
  ∀ (A : Type u) (Q : Mod R),
    IsIso (derivedTensorProductUniformProductComparison (A := A) R K Q)

def IsPseudoCoherentTensorProductFreeCompatible
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) : Prop :=
  ∀ (A : Type u),
    IsIso (derivedTensorProductFreeProductComparison (A := A) R K)

def IsMPseudoCoherentTensorProductCompatible
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (m : ℤ) : Prop :=
  ∀ {A : Type u} (Q : A → Mod R),
    (∀ i : ℤ, m < i →
      IsIso ((derivedCohomologyFunctor R i).map
        (derivedTensorProductProductComparison R K
          (fun a => DerivedObject (Q a))))) ∧
      Epi ((derivedCohomologyFunctor R m).map
        (derivedTensorProductProductComparison R K
          (fun a => DerivedObject (Q a))))

def IsMPseudoCoherentTensorProductUniformCompatible
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (m : ℤ) : Prop :=
  ∀ (A : Type u) (Q : Mod R),
    (∀ i : ℤ, m < i →
      IsIso ((derivedCohomologyFunctor R i).map
        (derivedTensorProductUniformProductComparison (A := A) R K Q))) ∧
      Epi ((derivedCohomologyFunctor R m).map
        (derivedTensorProductUniformProductComparison (A := A) R K Q))

def IsMPseudoCoherentTensorProductFreeCompatible
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (m : ℤ) : Prop :=
  ∀ (A : Type u),
    (∀ i : ℤ, m < i →
      IsIso ((derivedCohomologyFunctor R i).map
        (derivedTensorProductFreeProductComparison (A := A) R K))) ∧
      Epi ((derivedCohomologyFunctor R m).map
        (derivedTensorProductFreeProductComparison (A := A) R K))

theorem pseudoCoherent_tensor_product_criteria
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (hK : IsInDMinus R K) :
    IsPseudoCoherent R K ↔ IsPseudoCoherentTensorProductCompatible R K := by
  sorry

theorem pseudoCoherent_uniform_tensor_product_criteria
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (hK : IsInDMinus R K) :
    IsPseudoCoherent R K ↔ IsPseudoCoherentTensorProductUniformCompatible R K := by
  sorry

theorem pseudoCoherent_free_tensor_product_criteria
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (hK : IsInDMinus R K) :
    IsPseudoCoherent R K ↔ IsPseudoCoherentTensorProductFreeCompatible R K := by
  sorry

theorem m_pseudoCoherent_tensor_product_criteria
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (m : ℤ) (hK : IsInDMinus R K) :
    IsMPseudoCoherent R m K ↔
      IsMPseudoCoherentTensorProductCompatible R K m := by
  sorry

theorem m_pseudoCoherent_uniform_tensor_product_criteria
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (m : ℤ) (hK : IsInDMinus R K) :
    IsMPseudoCoherent R m K ↔
      IsMPseudoCoherentTensorProductUniformCompatible R K m := by
  sorry

theorem m_pseudoCoherent_free_tensor_product_criteria
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (m : ℤ) (hK : IsInDMinus R K) :
    IsMPseudoCoherent R m K ↔
      IsMPseudoCoherentTensorProductFreeCompatible R K m := by
  sorry

/-! ## Detecting cohomology -/

structure CohomologyDetectionWitness
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (i : ℤ) where
  module : Mod R
  finitelyPresented : FinitelyPresented R module
  map : K ⟶ (shiftFunctor (D R) (-i)).obj (DerivedObject module)
  targetIdentification :
    (derivedCohomologyFunctor R i).obj
        ((shiftFunctor (D R) (-i)).obj (DerivedObject module)) ≅ module
  inducedMap : (derivedCohomologyFunctor R i).obj K ⟶ module
  inducedMap_eq : inducedMap =
    (derivedCohomologyFunctor R i).map map ≫ targetIdentification.hom
  inducedMap_mono : Mono inducedMap

theorem detect_cohomology_pseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (i : ℤ)
    (hK : IsPseudoCoherent R K) :
    Nonempty (CohomologyDetectionWitness R K i) := by
  sorry

structure NoetherianCohomologyDetectionWitness
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (p : Ideal R) (i : ℤ) where
  module : Mod R
  finite : Module.Finite R (module : Type u)
  power : ∃ n : ℕ, p ^ n • (⊤ : Submodule R (module : Type u)) = ⊥
  map : K ⟶ (shiftFunctor (D R) (-i)).obj (DerivedObject module)
  targetIdentification :
    (derivedCohomologyFunctor R i).obj
        ((shiftFunctor (D R) (-i)).obj (DerivedObject module)) ≅ module
  inducedMap : (derivedCohomologyFunctor R i).obj K ⟶ module
  inducedMap_eq : inducedMap =
    (derivedCohomologyFunctor R i).map map ≫ targetIdentification.hom
  inducedMap_nonzero : inducedMap ≠ 0

def cohomologyNonzeroModuloIdeal
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (p : Ideal R) (i : ℤ) : Prop :=
  p • (⊤ : Submodule R ((derivedCohomologyFunctor R i).obj K : Type u)) ≠ ⊤

theorem detect_cohomology_noetherian
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (Mod R)] (K : D R) (p : Ideal R) (hp : p.IsMaximal) (i : ℤ)
    (hK : IsPseudoCoherent R K)
    (hmod : cohomologyNonzeroModuloIdeal R K p i) :
    Nonempty (NoetherianCohomologyDetectionWitness R K p i) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit66
