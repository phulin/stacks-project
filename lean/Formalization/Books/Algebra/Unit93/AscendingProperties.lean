import Formalization.Books.Algebra.Unit93.CharacterizingProjectiveModules
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Supporting interface for Commutative Algebra, Chapter 94

This file is retained as the implementation imported by Chapter 94's
chapter-facing wrapper.  It is not imported by the Chapter 93 top-level file;
the base-change tensor product is written in Mathlib's canonical orientation
`S ⊗[R] M`.
-/

namespace Formalization.Books.Algebra.Unit93

open Formalization.Books.Algebra.Unit84
open Formalization.Books.Algebra.Unit88
open Formalization.Books.Algebra.Unit89
open scoped TensorProduct

universe u v

noncomputable section

/- The flatness clause is already the earlier, source-faithful theorem
`Formalization.Books.Algebra.Unit39.flat_base_change`; it is included in the
combined interface below rather than duplicated under a parallel name. -/

private theorem countablyGenerated_baseChange
    {R S : Type u} {N : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup N] [Module R N]
    (hN : Module.IsCountablyGenerated R N) :
    Module.IsCountablyGenerated S (S ⊗[R] N) := by
  classical
  rcases hN with ⟨X, hX, hspan⟩
  let gen : Set (S ⊗[R] N) :=
    (fun x : N => (1 : S) ⊗ₜ[R] x) '' X
  refine ⟨gen, hX.image (fun x : N => (1 : S) ⊗ₜ[R] x), ?_⟩
  apply top_unique
  intro z hz
  clear hz
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul s n =>
      have hn : n ∈ Submodule.span R X := by rw [hspan]; trivial
      have h1 : (1 : S) ⊗ₜ[R] n ∈ Submodule.span S gen := by
        refine Submodule.span_induction (p := fun n _ =>
          (1 : S) ⊗ₜ[R] n ∈ Submodule.span S gen) ?_ ?_ ?_ ?_ hn
        · intro x hx
          exact Submodule.subset_span ⟨x, hx, rfl⟩
        · simpa only [TensorProduct.tmul_zero] using
            (Submodule.zero_mem (Submodule.span S gen))
        · intro x y hx hy hpx hpy
          simpa only [TensorProduct.tmul_add] using
            Submodule.add_mem (Submodule.span S gen) hpx hpy
        · intro r n hn hpn
          rw [← TensorProduct.smul_tmul]
          rw [show r • (1 : S) = algebraMap R S r by simp [Algebra.smul_def]]
          simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
            Submodule.smul_mem (Submodule.span S gen) (algebraMap R S r) hpn
      rw [TensorProduct.tmul_eq_smul_one_tmul]
      exact Submodule.smul_mem (Submodule.span S gen) s h1
  | add x y hx hy => exact Submodule.add_mem _ hx hy

private theorem mittagLeffler_baseChange
    {R S : Type u} {M : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    (hML : IsMittagLefflerModule (ModuleCat.of R M)) :
    IsMittagLefflerModule (ModuleCat.of S (S ⊗[R] M)) := by
  classical
  let target : ModuleCat.{max u v} S := ModuleCat.of S (S ⊗[R] M)
  have hcritS :
      IsMittagLefflerModule target ↔
        ∀ (A : Type (max u v)) (Q : A → ModuleCat.{max u v} S),
          Function.Injective (productTensorMap target Q) :=
    (mittagLeffler_tensor_iff target).out 0 1
  apply hcritS.mpr
  intro A Q
  letI (a : A) : Module R (Q a : Type (max u v)) :=
    Module.compHom (Q a : Type (max u v)) (algebraMap R S)
  letI (a : A) : IsScalarTower R S (Q a : Type (max u v)) :=
    IsScalarTower.of_compHom R S (Q a : Type (max u v))
  let RQ : A → ModuleCat.{max u v} R :=
    fun a => ModuleCat.of R (Q a : Type (max u v))
  have hcritR :
      IsMittagLefflerModule (ModuleCat.of R M) ↔
        ∀ (A : Type (max u v)) (Q : A → ModuleCat.{max u v} R),
          Function.Injective (productTensorMap (ModuleCat.of R M) Q) :=
    (mittagLeffler_tensor_iff (ModuleCat.of R M)).out 0 1
  have hinj : Function.Injective (productTensorMap (ModuleCat.of R M) RQ) :=
    hcritR.mp hML A RQ
  let e : TensorProduct S (S ⊗[R] M) (∀ a, (Q a : Type (max u v))) ≃ₗ[R]
      TensorProduct R M (∀ a, (Q a : Type (max u v))) :=
    ((TensorProduct.comm S (S ⊗[R] M) (∀ a, (Q a : Type (max u v)))).restrictScalars R).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S
        (∀ a, (Q a : Type (max u v))) M).restrictScalars R) |>.trans
        (TensorProduct.comm R (∀ a, (Q a : Type (max u v))) M)
  let ea (a : A) : TensorProduct S (S ⊗[R] M) (Q a : Type (max u v)) ≃ₗ[R]
      TensorProduct R M (Q a : Type (max u v)) :=
    ((TensorProduct.comm S (S ⊗[R] M) (Q a : Type (max u v))).restrictScalars R).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S
        (Q a : Type (max u v)) M).restrictScalars R) |>.trans
        (TensorProduct.comm R (Q a : Type (max u v)) M)
  have he (x : TensorProduct S (S ⊗[R] M)
      (∀ a, (Q a : Type (max u v)))) (a : A) :
      ea a (productTensorMap target Q x a) =
        productTensorMap (ModuleCat.of R M) RQ (e x) a := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]
    | tmul t q =>
        induction t using TensorProduct.induction_on with
        | zero => simp only [TensorProduct.zero_tmul, map_zero, Pi.zero_apply]
        | tmul s m => simp [e, ea, productTensorMap, Pi.smul_apply]
        | add x y hx hy =>
            simp only [TensorProduct.add_tmul, map_add]
            change ea a (productTensorMap target Q (x ⊗ₜ[S] q) a +
              productTensorMap target Q (y ⊗ₜ[S] q) a) =
              productTensorMap (ModuleCat.of R M) RQ (e (x ⊗ₜ[S] q)) a +
                productTensorMap (ModuleCat.of R M) RQ (e (y ⊗ₜ[S] q)) a
            rw [map_add, hx, hy]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  intro x y hxy
  apply e.injective
  apply hinj
  funext a
  rw [← he x a, ← he y a, congrFun hxy a]

private theorem directSum_baseChange
    {R S : Type u} {M : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    (hM : IsDirectSumOfCountablyGeneratedModules (ModuleCat.of R M)) :
    IsDirectSumOfCountablyGeneratedModules
      (ModuleCat.of S (S ⊗[R] M)) := by
  classical
  rcases hM with ⟨ι, N, hN, ⟨eM⟩⟩
  let N' : ι → ModuleCat.{max u v} S :=
    fun i => ModuleCat.of S (S ⊗[R] (N i : Type v))
  let eBase : (S ⊗[R] M) ≃ₗ[S]
      DirectSum ι (fun i => (N' i : Type (max u v))) :=
    (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl S S) eM).trans
      (TensorProduct.directSumRight R S S (fun i => (N i : Type v)))
  let ι' : Type (max u v) := ULift.{u} ι
  let eι : ι ≃ ι' := (Equiv.ulift : ι' ≃ ι).symm
  let N'' : ι' → ModuleCat.{max u v} S :=
    fun j => N' (eι.symm j)
  have hN'' (j : ι') : Module.IsCountablyGenerated S (N'' j : Type (max u v)) := by
    exact countablyGenerated_baseChange (hN (eι.symm j))
  let reindex : DirectSum ι (fun i => (N' i : Type (max u v))) ≃ₗ[S]
      DirectSum ι' (fun j => (N'' j : Type (max u v))) :=
    DirectSum.lequivCongrLeft S eι
  let e' := eBase.trans reindex
  exact ⟨ι', N'', hN'', ⟨e'⟩⟩

/-- All four properties in the source ascend along arbitrary ring maps. -/
theorem ascend_properties_modules
    {R S : Type u} {M : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] :
    (Module.Flat R M → Module.Flat S (S ⊗[R] M)) ∧
      (IsMittagLefflerModule (ModuleCat.of R M) →
        IsMittagLefflerModule (ModuleCat.of S (S ⊗[R] M))) ∧
        (IsDirectSumOfCountablyGeneratedModules (ModuleCat.of R M) →
          IsDirectSumOfCountablyGeneratedModules
            (ModuleCat.of S (S ⊗[R] M))) ∧
          (Module.Projective R M → Module.Projective S (S ⊗[R] M)) := by
  refine ⟨Formalization.Books.Algebra.Unit39.flat_base_change, ?_⟩
  refine ⟨mittagLeffler_baseChange, ?_⟩
  refine ⟨directSum_baseChange, ?_⟩
  intro hP
  exact Module.Projective.tensorProduct (R := S) (R₀ := R) (M := S) (N := M)
    (hM := inferInstance) (hN := hP)

end

end Formalization.Books.Algebra.Unit93
