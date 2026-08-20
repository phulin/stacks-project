import Formalization.Books.Cotangent.Unit03.StandardResolution
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Order.Directed
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The cotangent complex from a simplicial module

The source forms the simplicial `B`-module
`Ω[P_•/A] ⊗_{P_•, ε} B` and then applies the alternating face-map complex.
The former construction changes the base ring degree by degree and is not a
single Mathlib functor.  This file therefore packages that simplicial module
with its canonical degreewise tensor terms, and applies Mathlib's actual
alternating-face-map and extension constructions to it.
-/

namespace Formalization.Books.Cotangent.Unit03

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open scoped _root_.Simplicial TensorProduct

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-! ## Degreewise tensor terms -/

/-- The augmentation map in simplicial degree `n`. -/
noncomputable def standardResolutionAugmentationMap (n : ℕ) :
    iteratedPolynomial A (n + 1) B →ₐ[A] B :=
  ((standardResolutionAugmentation (A := A) (B := B)).hom.app
      (Opposite.op (SimplexCategory.mk n))).hom

/-- The degree-`n` module `Ω[P_n/A] ⊗_{P_n} B`. -/
noncomputable def standardCotangentTerm (n : ℕ) : Type u :=
  let P := iteratedPolynomial A (n + 1) B
  let ε := standardResolutionAugmentationMap (A := A) (B := B) n
  letI := ε.toRingHom.toAlgebra
  -- The factors are written in the symmetric order `B ⊗[P] Ω[P/A]`,
  -- which exposes the canonical `B`-module structure.
  TensorProduct P B (KaehlerDifferential A P)

noncomputable instance standardCotangentTermAddCommGroup (n : ℕ) :
    AddCommGroup (standardCotangentTerm (A := A) (B := B) n) := by
  let P := iteratedPolynomial A (n + 1) B
  let ε := standardResolutionAugmentationMap (A := A) (B := B) n
  letI := ε.toRingHom.toAlgebra
  change AddCommGroup (TensorProduct P B (KaehlerDifferential A P))
  infer_instance

noncomputable instance standardCotangentTermModule (n : ℕ) :
    Module B (standardCotangentTerm (A := A) (B := B) n) := by
  let P := iteratedPolynomial A (n + 1) B
  let ε := standardResolutionAugmentationMap (A := A) (B := B) n
  letI := ε.toRingHom.toAlgebra
  change Module B (TensorProduct P B (KaehlerDifferential A P))
  infer_instance

/-- A simplicial `B`-module with the degreewise terms required by the source. -/
structure CotangentSimplicialModule (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] where
  module : SimplicialObject (ModuleCat.{u} B)
  termIso : ∀ n : ℕ,
      module.obj (Opposite.op (SimplexCategory.mk n)) ≅
      ModuleCat.of B (standardCotangentTerm (A := A) (B := B) n)

private noncomputable def standardCotangentTermMap
    (P Q : Type u) [CommRing P] [CommRing Q] [Algebra A P] [Algebra A Q]
    (f : P →ₐ[A] Q) (εP : P →ₐ[A] B) (εQ : Q →ₐ[A] B)
    (hε : εQ.comp f = εP) :
    letI := εP.toRingHom.toAlgebra
    letI := εQ.toRingHom.toAlgebra
    TensorProduct P B (KaehlerDifferential A P) →ₗ[B]
      TensorProduct Q B (KaehlerDifferential A Q) := by
  letI := f.toRingHom.toAlgebra
  letI := εP.toRingHom.toAlgebra
  letI := εQ.toRingHom.toAlgebra
  letI : IsScalarTower P Q B :=
    IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom hε).symm
  let l : KaehlerDifferential A P →ₗ[P]
      TensorProduct Q B (KaehlerDifferential A Q) :=
    (TensorProduct.mk Q B (KaehlerDifferential A Q) 1).restrictScalars P ∘ₗ
      KaehlerDifferential.map A A P Q
  exact LinearMap.liftBaseChange B l

private lemma standardCotangentDifferentialMap_id
    (P : Type u) [CommRing P] [Algebra A P] :
    KaehlerDifferential.map A A P P = LinearMap.id := by
  apply Derivation.liftKaehlerDifferential_unique
  ext x
  simp

private def standardCotangentRestrictMap
    (P Q M N : Type u) [CommSemiring P] [Semiring Q]
    [AddCommMonoid M] [AddCommMonoid N] [Module Q M] [Module Q N]
    [Module P M] [Module P N] [Algebra P Q]
    (f : M →ₗ[Q] N) (h : ∀ (c : P) (x : M), f (c • x) = c • f x) :
    M →ₗ[P] N :=
  { toFun := f
    map_add' := f.map_add
    map_smul' := h }

private lemma standardCotangentDifferentialMap_comp
    (P Q R : Type u) [CommRing P] [CommRing Q] [CommRing R]
    [Algebra A P] [Algebra A Q] [Algebra A R]
    (f : P →ₐ[A] Q) (g : Q →ₐ[A] R) :
    letI := f.toRingHom.toAlgebra
    letI := g.toRingHom.toAlgebra
    letI := (g.comp f).toRingHom.toAlgebra
    letI : Module P (KaehlerDifferential A Q) :=
      Module.compHom (KaehlerDifferential A Q) (algebraMap P Q)
    letI : Module P (KaehlerDifferential A R) :=
      Module.compHom (KaehlerDifferential A R) (algebraMap P Q)
    letI : IsScalarTower P Q (KaehlerDifferential A Q) :=
      IsScalarTower.of_compHom P Q (KaehlerDifferential A Q)
    letI : IsScalarTower P Q (KaehlerDifferential A R) :=
      IsScalarTower.of_compHom P Q (KaehlerDifferential A R)
    KaehlerDifferential.map A A P R =
      standardCotangentRestrictMap P Q (KaehlerDifferential A Q)
        (KaehlerDifferential A R) (KaehlerDifferential.map A A Q R) (by
          intro c x
          change (KaehlerDifferential.map A A Q R)
              ((algebraMap P Q c) • x) =
            (algebraMap P Q c) • (KaehlerDifferential.map A A Q R) x
          rw [(KaehlerDifferential.map A A Q R).map_smul]) ∘ₗ
        KaehlerDifferential.map A A P Q := by
  let _ := f.toRingHom.toAlgebra
  let _ := g.toRingHom.toAlgebra
  let _ := (g.comp f).toRingHom.toAlgebra
  let _ : Module P (KaehlerDifferential A Q) :=
    Module.compHom (KaehlerDifferential A Q) (algebraMap P Q)
  let _ : Module P (KaehlerDifferential A R) :=
    Module.compHom (KaehlerDifferential A R) (algebraMap P Q)
  let _ : IsScalarTower P Q (KaehlerDifferential A Q) :=
    IsScalarTower.of_compHom P Q (KaehlerDifferential A Q)
  let _ : IsScalarTower P Q (KaehlerDifferential A R) :=
    IsScalarTower.of_compHom P Q (KaehlerDifferential A R)
  apply Derivation.liftKaehlerDifferential_unique
  ext x
  change (KaehlerDifferential.map A A P R) (KaehlerDifferential.D A P x) =
    (KaehlerDifferential.map A A Q R)
      (KaehlerDifferential.map A A P Q (KaehlerDifferential.D A P x))
  simp only [KaehlerDifferential.map_D]
  rw [show algebraMap P R x = algebraMap Q R (algebraMap P Q x) by rfl]

private lemma standardCotangentTermMap_id
    (P : Type u) [CommRing P] [Algebra A P]
    (ε : P →ₐ[A] B) :
    letI := ε.toRingHom.toAlgebra
    standardCotangentTermMap P P (AlgHom.id A P) ε ε (by simp) =
      LinearMap.id := by
  let _ := ε.toRingHom.toAlgebra
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      calc
        _ = _ := LinearMap.map_add _ x y
        _ = _ := congrArg₂ (· + ·) hx hy
        _ = _ := (LinearMap.map_add _ x y).symm
  | tmul b ω =>
      change (LinearMap.liftBaseChange B
        ((TensorProduct.mk P B (KaehlerDifferential A P) 1).restrictScalars P ∘ₗ
          KaehlerDifferential.map A A P P)) (b ⊗ₜ[P] ω) = b ⊗ₜ[P] ω
      rw [LinearMap.liftBaseChange_tmul]
      simp [standardCotangentDifferentialMap_id]
      rw [TensorProduct.smul_tmul']
      simp

private lemma standardCotangentTermMap_comp
    (P Q R : Type u) [CommRing P] [CommRing Q] [CommRing R]
    [Algebra A P] [Algebra A Q] [Algebra A R]
    (f : P →ₐ[A] Q) (g : Q →ₐ[A] R)
    (εP : P →ₐ[A] B) (εQ : Q →ₐ[A] B) (εR : R →ₐ[A] B)
    (hεf : εQ.comp f = εP) (hεg : εR.comp g = εQ) :
    letI := εP.toRingHom.toAlgebra
    letI := εQ.toRingHom.toAlgebra
    letI := εR.toRingHom.toAlgebra
    standardCotangentTermMap P R (g.comp f) εP εR (by
      ext x
      change εR (g (f x)) = εP x
      exact (congrArg (fun k => k (f x)) hεg).trans
        (by simpa only [AlgHom.comp_apply] using congrArg (fun k => k x) hεf)) =
      standardCotangentTermMap Q R g εQ εR hεg ∘ₗ
        standardCotangentTermMap P Q f εP εQ hεf := by
  let _ := f.toRingHom.toAlgebra
  let _ := g.toRingHom.toAlgebra
  let _ := (g.comp f).toRingHom.toAlgebra
  let _ := εP.toRingHom.toAlgebra
  let _ := εQ.toRingHom.toAlgebra
  let _ := εR.toRingHom.toAlgebra
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      calc
        _ = _ := LinearMap.map_add _ x y
        _ = _ := congrArg₂ (· + ·) hx hy
        _ = _ :=
          (LinearMap.map_add
            (standardCotangentTermMap Q R g εQ εR hεg ∘ₗ
              standardCotangentTermMap P Q f εP εQ hεf) x y).symm
  | tmul b ω =>
      simp only [standardCotangentTermMap, LinearMap.liftBaseChange_tmul,
        LinearMap.comp_apply]
      simp only [LinearMap.map_smul]
      rw [standardCotangentDifferentialMap_comp (A := A) (P := P) (Q := Q) (R := R) f g]
      congr 1
      change _ =
        (LinearMap.liftBaseChange B _)
          ((1 : B) ⊗ₜ[Q]
            KaehlerDifferential.map A A P Q ω)
      rw [LinearMap.liftBaseChange_tmul]
      simp [standardCotangentRestrictMap]
      conv_rhs =>
        change (1 : B) ⊗ₜ[R] _
      congr 1

private lemma standardCotangentTermMap_congr
    (P Q : Type u) [CommRing P] [CommRing Q]
    [Algebra A P] [Algebra A Q]
    (f f' : P →ₐ[A] Q) (εP : P →ₐ[A] B) (εQ : Q →ₐ[A] B)
    (hε : εQ.comp f = εP) (hε' : εQ.comp f' = εP)
    (h : f = f') :
    standardCotangentTermMap P Q f εP εQ hε =
      standardCotangentTermMap P Q f' εP εQ hε' := by
  subst f'
  rfl

private lemma standardResolutionAugmentationMap_naturality
    {m n : ℕ} (f : Opposite.op (SimplexCategory.mk m) ⟶
      Opposite.op (SimplexCategory.mk n)) :
    (standardResolutionAugmentationMap (A := A) (B := B) n).comp
        ((standardResolution (A := A) (B := B)).map f).hom =
      standardResolutionAugmentationMap (A := A) (B := B) m := by
  have h := congrArg CommAlgCat.Hom.hom
    ((standardResolutionAugmentation (A := A) (B := B)).hom.naturality f)
  change (CommAlgCat.Hom.hom
      ((standardResolutionAugmentation (A := A) (B := B)).hom.app _)).comp
      (CommAlgCat.Hom.hom
        ((standardResolution (A := A) (B := B)).map f)) =
    CommAlgCat.Hom.hom
      ((standardResolutionAugmentation (A := A) (B := B)).hom.app _)
  exact h

private lemma standardResolutionAugmentationMap_naturality_map
    {m n : ℕ} (f : Opposite.op (SimplexCategory.mk m) ⟶
      Opposite.op (SimplexCategory.mk n)) :
    (standardResolutionAugmentationMap (A := A) (B := B) n).comp
        (standardResolutionMap (A := A) (B := B) f.unop) =
      standardResolutionAugmentationMap (A := A) (B := B) m := by
  apply AlgHom.ext
  intro x
  have h := congrArg (fun k => k x)
    (standardResolutionAugmentationMap_naturality (A := A) (B := B) f)
  change (standardResolutionAugmentationMap (A := A) (B := B) n)
      (standardResolutionMap (A := A) (B := B) f.unop x) =
    (standardResolutionAugmentationMap (A := A) (B := B) m) x at h
  exact h

/-- The simplicial module whose terms are the base-changed differentials of the
standard resolution.  Its maps are induced by the face and degeneracy maps on
the resolution, together with functoriality of Kähler differentials and tensor
base change. -/
private noncomputable def standardCotangentSimplicialModuleModule :
    SimplicialObject (ModuleCat.{u} B) where
  obj Δ := ModuleCat.of B
    (standardCotangentTerm (A := A) (B := B) Δ.unop.len)
  map := fun {X Y} f => by
    classical
    cases X with
    | op X =>
      cases Y with
      | op Y =>
        cases X with
        | mk m =>
          cases Y with
          | mk n =>
            letI : CommRing (iteratedPolynomial A (m + 1) B) :=
              iteratedPolynomialCommRing A B (m + 1)
            letI : Algebra A (iteratedPolynomial A (m + 1) B) :=
              iteratedPolynomialAlgebra A B (m + 1)
            letI : CommRing (iteratedPolynomial A (n + 1) B) :=
              iteratedPolynomialCommRing A B (n + 1)
            letI : Algebra A (iteratedPolynomial A (n + 1) B) :=
              iteratedPolynomialAlgebra A B (n + 1)
            letI : Algebra (iteratedPolynomial A (m + 1) B) B :=
              (standardResolutionAugmentationMap (A := A) (B := B) m).toRingHom.toAlgebra
            letI : Algebra (iteratedPolynomial A (n + 1) B) B :=
              (standardResolutionAugmentationMap (A := A) (B := B) n).toRingHom.toAlgebra
            let F :=
              @standardCotangentTermMap A B _ _ _
                (iteratedPolynomial A (m + 1) B)
                (iteratedPolynomial A (n + 1) B)
                (iteratedPolynomialCommRing A B (m + 1))
                (iteratedPolynomialCommRing A B (n + 1))
                (iteratedPolynomialAlgebra A B (m + 1))
                (iteratedPolynomialAlgebra A B (n + 1))
                (standardResolutionMap (A := A) (B := B) f.unop)
                (standardResolutionAugmentationMap (A := A) (B := B) m)
                (standardResolutionAugmentationMap (A := A) (B := B) n)
                (standardResolutionAugmentationMap_naturality_map f)
            exact ModuleCat.ofHom
              ({ toFun := fun x => by
                   change TensorProduct (iteratedPolynomial A (m + 1) B) B
                     (KaehlerDifferential A (iteratedPolynomial A (m + 1) B)) at x
                   change TensorProduct (iteratedPolynomial A (n + 1) B) B
                     (KaehlerDifferential A (iteratedPolynomial A (n + 1) B))
                   exact F x
                 map_add' := by
                   intro x y
                   exact F.map_add x y
                 map_smul' := by
                   intro c x
                   exact F.map_smul c x } :
                standardCotangentTerm (A := A) (B := B) m →ₗ[B]
                  standardCotangentTerm (A := A) (B := B) n)
  map_id := by
    intro Δ
    cases Δ with
    | op Δ =>
      cases Δ with
      | mk n =>
        let _ : CommRing (iteratedPolynomial A (n + 1) B) :=
          iteratedPolynomialCommRing A B (n + 1)
        let _ : Algebra A (iteratedPolynomial A (n + 1) B) :=
          iteratedPolynomialAlgebra A B (n + 1)
        ext x
        change
          (standardCotangentTermMap
            (iteratedPolynomial A (n + 1) B)
            (iteratedPolynomial A (n + 1) B)
            (standardResolutionMap (A := A) (B := B) (𝟙 _))
            (standardResolutionAugmentationMap (A := A) (B := B) n)
            (standardResolutionAugmentationMap (A := A) (B := B) n)
            (standardResolutionAugmentationMap_naturality_map (A := A) (B := B)
              (𝟙 (Opposite.op (SimplexCategory.mk n))))) x = x
        simp [standardResolutionMap_id, standardCotangentTermMap_id]
        rfl
  map_comp := by
    intro X Y Z f g
    cases X with
    | op X =>
      cases Y with
      | op Y =>
        cases Z with
        | op Z =>
          cases X with
          | mk m =>
            cases Y with
            | mk n =>
              cases Z with
            | mk k =>
                let _ : CommRing (iteratedPolynomial A (m + 1) B) :=
                  iteratedPolynomialCommRing A B (m + 1)
                let _ : Algebra A (iteratedPolynomial A (m + 1) B) :=
                  iteratedPolynomialAlgebra A B (m + 1)
                let _ : CommRing (iteratedPolynomial A (n + 1) B) :=
                  iteratedPolynomialCommRing A B (n + 1)
                let _ : Algebra A (iteratedPolynomial A (n + 1) B) :=
                  iteratedPolynomialAlgebra A B (n + 1)
                let _ : CommRing (iteratedPolynomial A (k + 1) B) :=
                  iteratedPolynomialCommRing A B (k + 1)
                let _ : Algebra A (iteratedPolynomial A (k + 1) B) :=
                  iteratedPolynomialAlgebra A B (k + 1)
                let _ : Algebra (iteratedPolynomial A (m + 1) B) B :=
                  (standardResolutionAugmentationMap (A := A) (B := B) m).toRingHom.toAlgebra
                let _ : Algebra (iteratedPolynomial A (n + 1) B) B :=
                  (standardResolutionAugmentationMap (A := A) (B := B) n).toRingHom.toAlgebra
                let _ : Algebra (iteratedPolynomial A (k + 1) B) B :=
                  (standardResolutionAugmentationMap (A := A) (B := B) k).toRingHom.toAlgebra
                ext x
                change TensorProduct (iteratedPolynomial A (m + 1) B) B
                  (KaehlerDifferential A (iteratedPolynomial A (m + 1) B)) at x
                have hf := standardResolutionAugmentationMap_naturality_map
                  (A := A) (B := B) f
                have hg := standardResolutionAugmentationMap_naturality_map
                  (A := A) (B := B) g
                have hleft :
                    (standardResolutionAugmentationMap (A := A) (B := B) k).comp
                        (standardResolutionMap (A := A) (B := B)
                          (g.unop ≫ f.unop)) =
                      standardResolutionAugmentationMap (A := A) (B := B) m := by
                  have h := standardResolutionAugmentationMap_naturality_map
                    (A := A) (B := B) (f ≫ g)
                  change
                    (standardResolutionAugmentationMap (A := A) (B := B) k).comp
                        (standardResolutionMap (A := A) (B := B)
                          (g.unop ≫ f.unop)) =
                      standardResolutionAugmentationMap (A := A) (B := B) m at h
                  exact h
                have hcomp :
                    (standardResolutionAugmentationMap (A := A) (B := B) k).comp
                        ((standardResolutionMap (A := A) (B := B) g.unop).comp
                          (standardResolutionMap (A := A) (B := B) f.unop)) =
                      standardResolutionAugmentationMap (A := A) (B := B) m := by
                  apply AlgHom.ext
                  intro z
                  have hg' := congrArg
                    (fun q => q (standardResolutionMap (A := A) (B := B) f.unop z)) hg
                  have hf' := congrArg (fun q => q z) hf
                  change
                    (standardResolutionAugmentationMap (A := A) (B := B) k)
                        (standardResolutionMap (A := A) (B := B) g.unop
                          (standardResolutionMap (A := A) (B := B) f.unop z)) =
                      (standardResolutionAugmentationMap (A := A) (B := B) n)
                        (standardResolutionMap (A := A) (B := B) f.unop z) at hg'
                  change
                    (standardResolutionAugmentationMap (A := A) (B := B) n)
                        (standardResolutionMap (A := A) (B := B) f.unop z) =
                      (standardResolutionAugmentationMap (A := A) (B := B) m) z at hf'
                  exact hg'.trans hf'
                change
                  (standardCotangentTermMap
                    (iteratedPolynomial A (m + 1) B)
                    (iteratedPolynomial A (k + 1) B)
                    (standardResolutionMap (A := A) (B := B) (g.unop ≫ f.unop))
                    (standardResolutionAugmentationMap (A := A) (B := B) m)
                    (standardResolutionAugmentationMap (A := A) (B := B) k)
                    hleft) x =
                    (standardCotangentTermMap
                      (iteratedPolynomial A (n + 1) B)
                      (iteratedPolynomial A (k + 1) B)
                      (standardResolutionMap (A := A) (B := B) g.unop)
                      (standardResolutionAugmentationMap (A := A) (B := B) n)
                      (standardResolutionAugmentationMap (A := A) (B := B) k)
                      hg)
                      ((standardCotangentTermMap
                        (iteratedPolynomial A (m + 1) B)
                        (iteratedPolynomial A (n + 1) B)
                        (standardResolutionMap (A := A) (B := B) f.unop)
                        (standardResolutionAugmentationMap (A := A) (B := B) m)
                        (standardResolutionAugmentationMap (A := A) (B := B) n)
                        hf) x)
                have hterm := standardCotangentTermMap_congr
                  (A := A) (B := B)
                  (iteratedPolynomial A (m + 1) B)
                  (iteratedPolynomial A (k + 1) B)
                  (standardResolutionMap (A := A) (B := B) (g.unop ≫ f.unop))
                  ((standardResolutionMap (A := A) (B := B) g.unop).comp
                    (standardResolutionMap (A := A) (B := B) f.unop))
                  (standardResolutionAugmentationMap (A := A) (B := B) m)
                  (standardResolutionAugmentationMap (A := A) (B := B) k)
                  hleft hcomp
                  (standardResolutionMap_comp (A := A) (B := B)
                    (f := g.unop) (g := f.unop))
                calc
                  _ = (standardCotangentTermMap
                    (iteratedPolynomial A (m + 1) B)
                    (iteratedPolynomial A (k + 1) B)
                    ((standardResolutionMap (A := A) (B := B) g.unop).comp
                      (standardResolutionMap (A := A) (B := B) f.unop))
                    (standardResolutionAugmentationMap (A := A) (B := B) m)
                    (standardResolutionAugmentationMap (A := A) (B := B) k)
                    hcomp) x := congrArg (fun q => q x) hterm
                  _ = _ := by
                    simpa only [LinearMap.comp_apply] using congrArg (fun q => q x)
                      (standardCotangentTermMap_comp
                        (A := A) (B := B)
                        (P := iteratedPolynomial A (m + 1) B)
                        (Q := iteratedPolynomial A (n + 1) B)
                        (R := iteratedPolynomial A (k + 1) B)
                        (f := standardResolutionMap (A := A) (B := B) f.unop)
                        (g := standardResolutionMap (A := A) (B := B) g.unop)
                        (εP := standardResolutionAugmentationMap (A := A) (B := B) m)
                        (εQ := standardResolutionAugmentationMap (A := A) (B := B) n)
                        (εR := standardResolutionAugmentationMap (A := A) (B := B) k)
                        hf hg)

noncomputable def standardCotangentSimplicialModule :
    CotangentSimplicialModule (A := A) (B := B) where
  module := standardCotangentSimplicialModuleModule (A := A) (B := B)
  termIso := by
    intro n
    exact Iso.refl _

/-! ## Alternating face-map complex -/

/-- The cochain complex associated to a cotangent simplicial module.

The `embeddingDownNat` extension places simplicial degree `n` in cochain degree
`-n` and makes all positive degrees zero, exactly as in the source convention.
-/
noncomputable def cotangentComplexOf
    (Q : CotangentSimplicialModule (A := A) (B := B)) :
    CochainComplex (ModuleCat.{u} B) ℤ :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} B)).obj Q.module |>.extend
    ComplexShape.embeddingDownNat

noncomputable def cotangentComplex
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    CochainComplex (ModuleCat.{u} B) ℤ :=
  cotangentComplexOf (standardCotangentSimplicialModule (A := A) (B := B))

noncomputable def cotangentComplexOf_degree
    (Q : CotangentSimplicialModule (A := A) (B := B))
    (n : ℕ) :
    (cotangentComplexOf Q).X (-(n : ℤ)) ≅
      Q.module.obj (Opposite.op (SimplexCategory.mk n)) :=
  HomologicalComplex.extendXIso
    ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} B)).obj Q.module)
    ComplexShape.embeddingDownNat (by rfl)

/-- The degree identification with the source's tensor-product term. -/
noncomputable def cotangentComplexOf_term
    (Q : CotangentSimplicialModule (A := A) (B := B))
    (n : ℕ) :
    (cotangentComplexOf Q).X (-(n : ℤ)) ≅
      ModuleCat.of B (standardCotangentTerm (A := A) (B := B) n) :=
  (cotangentComplexOf_degree Q n).trans (Q.termIso n)

noncomputable def cotangentComplex_degree
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) :
    (cotangentComplex A B).X (-(n : ℤ)) ≅
      ModuleCat.of B (standardCotangentTerm (A := A) (B := B) n) :=
  cotangentComplexOf_term (standardCotangentSimplicialModule (A := A) (B := B)) n

theorem cotangentComplex_positive_degree
    (m : ℤ) (hm : 0 < m) :
    CategoryTheory.Limits.IsZero ((cotangentComplex A B).X m) := by
  change IsZero
    ((((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} B)).obj
      (standardCotangentSimplicialModule (A := A) (B := B)).module).extend
        ComplexShape.embeddingDownNat).X m)
  apply HomologicalComplex.isZero_extend_X
  intro n h
  change -(n : ℤ) = m at h
  omega

/-!
The textbook's filtered-colimit lemma is recorded at the level of complexes
as the canonical comparison property below.  The source suppresses the
transition maps on the cotangent complexes; here `D` is the resulting diagram
after the stage complexes have been transported to the common colimit algebra
`B`.  Thus the ring-map system and its induced transition maps are supplied by
the caller through `D`, while the directed-index hypotheses are explicit.
-/
def CotangentComplexColimitStatement {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I]
    (D : I ⥤ CochainComplex (ModuleCat.{u} B) ℤ) : Prop :=
  ∃ c : Cocone D, Nonempty (IsColimit c) ∧
    Nonempty (cotangentComplex A B ≅ c.pt)

end Formalization.Books.Cotangent.Unit03
