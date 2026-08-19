import Mathlib.Algebra.Module.GradedModule
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Basic
import Formalization.Books.Algebra.Unit150.FormallyEtaleMaps

/-!
# More on Algebra, Chapter 4: A comment on the Artin-Rees property

The source's powers of an ideal acting on a module are written with
`I ^ n • ⊤`, and cokernels are represented by Mathlib's canonical submodule
quotients.  The associated graded construction uses the external `DirectSum`
graded-ring and graded-module interfaces.
-/

namespace Formalization.Books.MoreAlgebra.Unit04

open DirectSum
open scoped DirectSum TensorProduct

universe u v

noncomputable section

/-! ## Artin-Rees bounds and approximate complexes -/

/-- `c` works for `f` in the Artin-Rees lemma for the ideal `I`.

The source writes `f(M) ∩ I^n N ⊆ f(I^(n-c) M)`.  The canonical Mathlib
forms of these two submodules are `LinearMap.range`/`inf` and
`Submodule.map`/`smul`.
-/
def ArtinReesWorks
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (f : M →ₗ[R] N) (c : ℕ) : Prop :=
  ∀ n ≥ c,
    LinearMap.range f ⊓ I ^ n • (⊤ : Submodule R N) ≤
      Submodule.map f (I ^ (n - c) • (⊤ : Submodule R M))

/-- Every map between finite modules over a Noetherian ring has a working
Artin-Rees exponent. -/
theorem exists_artinReesWorks
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N]
    (I : Ideal R) (f : M →ₗ[R] N) :
    ∃ c : ℕ, ArtinReesWorks I f c := by
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.range f)
  refine ⟨c, ?_⟩
  intro n hn
  rw [inf_comm, hc n hn]
  refine Submodule.smul_le.mpr ?_
  intro r hr x hx
  rcases hx.2 with ⟨y, hy⟩
  refine ⟨r • y, Submodule.smul_mem_smul hr ?_, ?_⟩
  · exact Submodule.mem_top
  · change f (r • y) = r • x
    rw [map_smul, hy]

/-- Equality modulo a submodule, expressed by equality after the canonical
quotient map. -/
def LinearMap.CongruentModulo
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (P : Submodule R N) (f g : M →ₗ[R] N) : Prop :=
  P.mkQ.comp f = P.mkQ.comp g

/-- The preimage estimate proved while correcting an approximate complex. -/
theorem approximate_complex_preimage
    {A L M N : Type*} [CommRing A]
    [AddCommGroup L] [Module A L]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [IsNoetherianRing A]
    [Module.Finite A L] [Module.Finite A M] [Module.Finite A N]
    (I : Ideal A) (c : ℕ)
    (f : L →ₗ[A] M) (g : M →ₗ[A] N)
    (f' : L →ₗ[A] M) (g' : M →ₗ[A] N)
    (hS : Function.Exact f g)
    (hc_f : ArtinReesWorks I f c)
    (hc_g : ArtinReesWorks I g c)
    (hf : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A M)) f' f)
    (hg : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A N)) g' g) :
    ∀ n ≥ c,
      Submodule.comap g' (I ^ n • (⊤ : Submodule A N)) ≤
        LinearMap.range f' ⊔ I ^ (n - c) • (⊤ : Submodule A M) := by
  sorry

/-- The approximate-complex lemma.  The source's assertion that `S` is a
complex is implied by its stronger exactness hypothesis; the complex
condition for `S'` is retained explicitly.  Its displayed kernel/intersection
calculation is represented by the stronger preimage estimate above together
with the canonical `Function.Exact` conclusion. -/
theorem approximate_complex
    {A L M N : Type*} [CommRing A]
    [AddCommGroup L] [Module A L]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [IsNoetherianRing A]
    [Module.Finite A L] [Module.Finite A M] [Module.Finite A N]
    (I : Ideal A) (c : ℕ)
    (f : L →ₗ[A] M) (g : M →ₗ[A] N)
    (f' : L →ₗ[A] M) (g' : M →ₗ[A] N)
    (hS : Function.Exact f g) (hS' : g'.comp f' = 0)
    (hI : I ≤ Ring.jacobson A)
    (hc_f : ArtinReesWorks I f c)
    (hc_g : ArtinReesWorks I g c)
    (hf : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A M)) f' f)
    (hg : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A N)) g' g) :
    ArtinReesWorks I g' c ∧ Function.Exact f' g' := by
  have hdiff_g (x : M) : g' x - g x ∈ I ^ (c + 1) • (⊤ : Submodule A N) := by
    have h := congrArg (fun k : M →ₗ[A] N ⧸ (I ^ (c + 1) • (⊤ : Submodule A N)) => k x)
      (show (I ^ (c + 1) • (⊤ : Submodule A N)).mkQ.comp g' =
        (I ^ (c + 1) • (⊤ : Submodule A N)).mkQ.comp g from hg)
    exact (Submodule.Quotient.eq _).mp h
  have hdiff_f (x : L) : f' x - f x ∈ I ^ (c + 1) • (⊤ : Submodule A M) := by
    have h := congrArg (fun k : L →ₗ[A] M ⧸ (I ^ (c + 1) • (⊤ : Submodule A M)) => k x)
      (show (I ^ (c + 1) • (⊤ : Submodule A M)).mkQ.comp f' =
        (I ^ (c + 1) • (⊤ : Submodule A M)).mkQ.comp f from hf)
    exact (Submodule.Quotient.eq _).mp h
  have hdiff_pow (r : ℕ) (a : M) (ha : a ∈ I ^ r • (⊤ : Submodule A M)) :
      g' a - g a ∈ I ^ (r + c + 1) • (⊤ : Submodule A N) := by
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro s hs x hx
      rw [map_smul, map_smul, ← smul_sub]
      have hmem : s • (g' x - g x) ∈ I ^ r • (I ^ (c + 1) • (⊤ : Submodule A N)) :=
        Submodule.smul_mem_smul hs (hdiff_g x)
      have hpow : I ^ r • (I ^ (c + 1) • (⊤ : Submodule A N)) =
          I ^ (r + c + 1) • (⊤ : Submodule A N) := by
        rw [← Submodule.smul_assoc]
        have hprod : I ^ r • I ^ (c + 1) = I ^ (r + c + 1) := by
          change I ^ r * I ^ (c + 1) = I ^ (r + c + 1)
          exact (I.pow_add (m := r) (n := c + 1) (by omega)).symm
        rw [hprod]
      exact hpow ▸ hmem
    · intro x y hx hy
      rw [map_add, map_add]
      convert add_mem hx hy using 1 ; abel
  have hdiff_f_pow (r : ℕ) (a : L) (ha : a ∈ I ^ r • (⊤ : Submodule A L)) :
      f' a - f a ∈ I ^ (r + c + 1) • (⊤ : Submodule A M) := by
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro s hs x hx
      rw [map_smul, map_smul, ← smul_sub]
      have hmem : s • (f' x - f x) ∈ I ^ r • (I ^ (c + 1) • (⊤ : Submodule A M)) :=
        Submodule.smul_mem_smul hs (hdiff_f x)
      have hpow : I ^ r • (I ^ (c + 1) • (⊤ : Submodule A M)) =
          I ^ (r + c + 1) • (⊤ : Submodule A M) := by
        rw [← Submodule.smul_assoc]
        have hprod : I ^ r • I ^ (c + 1) = I ^ (r + c + 1) := by
          change I ^ r * I ^ (c + 1) = I ^ (r + c + 1)
          exact (I.pow_add (m := r) (n := c + 1) (by omega)).symm
        rw [hprod]
      exact hpow ▸ hmem
    · intro x y hx hy
      rw [map_add, map_add]
      convert add_mem hx hy using 1 ; abel
  have hpreimage : ∀ n ≥ c,
      Submodule.comap g' (I ^ n • (⊤ : Submodule A N)) ≤
        LinearMap.range f' ⊔ I ^ (n - c) • (⊤ : Submodule A M) := by
    intro n hn
    let k := n - c
    have hstep : ∀ q r : ℕ, q + r = k → ∀ a : M,
        a ∈ I ^ r • (⊤ : Submodule A M) →
        g' a ∈ I ^ n • (⊤ : Submodule A N) →
        a ∈ LinearMap.range f' ⊔ I ^ k • (⊤ : Submodule A M) := by
      intro q
      induction q with
      | zero =>
          intro r hr a haP haG
          have hrk : r = k := by omega
          exact (show I ^ k • (⊤ : Submodule A M) ≤
              LinearMap.range f' ⊔ I ^ k • (⊤ : Submodule A M) from le_sup_right) (hrk ▸ haP)
      | succ q ih =>
          intro r hr a haP haG
          have hrk : r < k := by omega
          have hrpow : I ^ (r + 1) • (⊤ : Submodule A M) ≤
              I ^ r • (⊤ : Submodule A M) := by
            exact Submodule.smul_mono
              (Ideal.pow_le_pow_right (show r ≤ r + 1 by omega)) le_rfl
          have hdiff : g' a - g a ∈ I ^ (r + c + 1) • (⊤ : Submodule A N) :=
            hdiff_pow r a haP
          have hpow : I ^ n • (⊤ : Submodule A N) ≤
              I ^ (r + c + 1) • (⊤ : Submodule A N) := by
            exact Submodule.smul_mono
              (Ideal.pow_le_pow_right (by omega)) le_rfl
          have hga : g a ∈ I ^ (r + c + 1) • (⊤ : Submodule A N) := by
            have hsub := sub_mem (hpow haG) hdiff
            convert hsub using 1 ; abel
          have har := hc_g (r + c + 1) (by omega)
          have hgm : g a ∈ LinearMap.range g ⊓ I ^ (r + c + 1) •
              (⊤ : Submodule A N) := ⟨⟨a, rfl⟩, hga⟩
          rcases har hgm with ⟨y, hy, hgy⟩
          have hy' : y ∈ I ^ (r + 1) • (⊤ : Submodule A M) := by
            have he : r + c + 1 - c = r + 1 := by omega
            simpa [he] using hy
          have hker : a - y ∈ LinearMap.ker g := by
            rw [LinearMap.mem_ker]
            rw [map_sub, hgy, sub_self]
          have hrange : a - y ∈ LinearMap.range f := by
            rw [← hS.linearMap_ker_eq]
            exact hker
          rcases hrange with ⟨b₀, hb₀⟩
          have hfbmem : f b₀ ∈ I ^ r • (⊤ : Submodule A M) := by
            have hmem : a - y ∈ I ^ r • (⊤ : Submodule A M) :=
              sub_mem haP (hrpow hy')
            simpa [hb₀] using hmem
          have hgood : ∃ b : L, f b = a - y ∧
              f' b - f b ∈ I ^ (r + 1) • (⊤ : Submodule A M) := by
            by_cases hrc : c ≤ r
            · have harf := hc_f r hrc
              have hfm : f b₀ ∈ LinearMap.range f ⊓ I ^ r •
                  (⊤ : Submodule A M) := ⟨⟨b₀, rfl⟩, by simpa [hb₀] using hfbmem⟩
              rcases harf hfm with ⟨b, hb, hfb⟩
              refine ⟨b, hfb.trans hb₀, ?_⟩
              have hfd := hdiff_f_pow (r - c) b hb
              have he : r - c + c + 1 = r + 1 := by
                rw [Nat.sub_add_cancel hrc]
              simpa [he] using hfd
            · refine ⟨b₀, hb₀, ?_⟩
              exact (Submodule.smul_mono
                (Ideal.pow_le_pow_right (by omega)) le_rfl) (hdiff_f b₀)
          rcases hgood with ⟨b, hfb, hfdiff⟩
          have ha2 : a - f' b ∈ I ^ (r + 1) • (⊤ : Submodule A M) := by
            have htmp := sub_mem hy' hfdiff
            have haeq : a = f b + y := by
              rw [hfb]
              abel
            rw [haeq]
            convert htmp using 1 ; abel
          have hga2 : g' (a - f' b) ∈ I ^ n • (⊤ : Submodule A N) := by
            have hzero : g' (f' b) = 0 := by
              have h := congrArg (fun k : L →ₗ[A] N => k b) hS'
              simpa using h
            have hga2eq : g' (a - f' b) = g' a := by
              rw [map_sub, hzero, sub_zero]
            rw [hga2eq]
            exact haG
          have hi := ih (r + 1) (by omega) (a - f' b) ha2 hga2
          have hfb' : f' b ∈ LinearMap.range f' := ⟨b, rfl⟩
          have heq : a = f' b + (a - f' b) := by abel
          rw [heq]
          have hfbSup : f' b ∈ LinearMap.range f' ⊔ I ^ k •
              (⊤ : Submodule A M) :=
            (show LinearMap.range f' ≤ LinearMap.range f' ⊔ I ^ k •
              (⊤ : Submodule A M) from le_sup_left) hfb'
          exact add_mem hfbSup hi
    intro a ha
    have ha0 : a ∈ I ^ 0 • (⊤ : Submodule A M) := by
      rw [Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    exact hstep k 0 (by omega) a ha0 ha
  refine ⟨?_, ?_⟩
  · intro n hn
    rintro x ⟨⟨a, rfl⟩, ha⟩
    rcases Submodule.mem_sup.mp ((hpreimage n hn) ha) with ⟨u, hu, y, hy, huy⟩
    rcases hu with ⟨b, hub⟩
    have hzero : g' (f' b) = 0 := by
      have h := congrArg (fun k : L →ₗ[A] N => k b) hS'
      simpa using h
    refine ⟨y, hy, ?_⟩
    rw [← huy, ← hub, map_add, hzero, zero_add]
  · apply LinearMap.exact_of_comp_eq_zero_of_ker_le_range hS'
    intro x hx
    let Q : Submodule A M := LinearMap.range f'
    let q : M →ₗ[A] M ⧸ Q := Q.mkQ
    have hmem : q x ∈ (⨅ i : ℕ, I ^ i • (⊤ : Submodule A (M ⧸ Q))) := by
      rw [Submodule.mem_iInf]
      intro i
      have hxi : x ∈ Submodule.comap g' (I ^ (c + i) •
          (⊤ : Submodule A N)) := by
        change g' x ∈ I ^ (c + i) • (⊤ : Submodule A N)
        rw [hx]
        exact Submodule.zero_mem _
      have hi := (hpreimage (c + i) (by omega)) hxi
      have hi' : x ∈ LinearMap.range f' ⊔ I ^ i •
          (⊤ : Submodule A M) := by
        have he : c + i - c = i := Nat.add_sub_cancel_left c i
        simpa [he] using hi
      have hmap : (I ^ i • (⊤ : Submodule A M)).map q =
          I ^ i • (⊤ : Submodule A (M ⧸ Q)) := by
        rw [Submodule.map_smul'' (I ^ i) (⊤ : Submodule A M) q,
          Submodule.map_top, Submodule.range_mkQ]
      have hqi : q x ∈
          (LinearMap.range f' ⊔ I ^ i • (⊤ : Submodule A M)).map q :=
        Submodule.mem_map_of_mem hi'
      rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, hmap] at hqi
      exact hqi
    have hzero : q x = 0 := by
      have hI' : I ≤ (⊥ : Ideal A).jacobson := by
        rw [Ideal.jacobson_bot]
        exact hI
      have hbot : q x ∈ (⊥ : Submodule A (M ⧸ Q)) := by
        rw [← Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I hI']
        exact hmem
      exact (Submodule.mem_bot A).mp hbot
    change (Submodule.Quotient.mk x : M ⧸ Q) = 0 at hzero
    exact (Submodule.Quotient.mk_eq_zero Q).mp hzero

/-! ## Associated graded modules -/

/-- A subquotient of a submodule, written with the subtype as its carrier. -/
abbrev submoduleQuotient
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (P Q : Submodule R M) : Type _ :=
  HasQuotient.Quotient (P : Type _) (Q.comap P.subtype)

/-- The degree-`n` component `I^n/I^(n+1)` of the associated graded ring.
The denominator is pulled back to the subtype `I^n` so that the quotient is
literally the source's degreewise quotient. -/
abbrev associatedGradedRingPiece
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) : Type u :=
  submoduleQuotient (I ^ n : Submodule R R) (I ^ (n + 1) : Submodule R R)

/-- The degree-`n` component `I^n M/I^(n+1) M` of the associated graded
module. -/
abbrev associatedGradedModulePiece
    {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    (I : Ideal R) (n : ℕ) : Type _ :=
  submoduleQuotient (I ^ n • (⊤ : Submodule R M))
    (I ^ (n + 1) • (⊤ : Submodule R M))

/-- The associated graded ring `Gr_I(A)`, with the direct-sum carrier. -/
abbrev associatedGradedRing
    {R : Type u} [CommRing R] (I : Ideal R) : Type u :=
  DirectSum ℕ (associatedGradedRingPiece I)

/-- The associated graded module `Gr_I(M)`, with the direct-sum carrier. -/
abbrev associatedGradedModule
    {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    (I : Ideal R) : Type _ :=
  DirectSum ℕ (fun n => associatedGradedModulePiece (M := M) I n)

/-- The canonical graded-ring operations on the degreewise ideal quotients.
The construction is the usual product of ideal powers followed by passage to
the quotient; its existence is recorded as an interface because the proving
stage supplies the quotient-compatibility calculations. -/
theorem associatedGradedRing_gcommRing_exists
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty (DirectSum.GCommRing (associatedGradedRingPiece I)) := by
  exact Formalization.Books.Algebra.Unit150.associatedGradedRing_gcommRing_exists I

noncomputable instance associatedGradedRing_gcommRing
    {R : Type u} [CommRing R] (I : Ideal R) :
    DirectSum.GCommRing (associatedGradedRingPiece I) :=
  Classical.choice (associatedGradedRing_gcommRing_exists I)

/-- The canonical graded-module action of `Gr_I(A)` on `Gr_I(M)`. -/
theorem associatedGradedModule_gmodule_exists
    {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    Nonempty (DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n)) := by
  sorry

noncomputable instance associatedGradedModule_gmodule
    {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n) :=
  Classical.choice (associatedGradedModule_gmodule_exists I)

/-- A graded linear equivalence between the direct-sum associated graded
modules.  The linear equivalence is over `Gr_I(A)` and the two component
conditions make degree preservation explicit. -/
structure AssociatedGradedLinearEquiv
    {R : Type u} [CommRing R]
    (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] where
  toLinearEquiv :
    associatedGradedModule (M := M) I ≃ₗ[associatedGradedRing I]
      associatedGradedModule (M := N) I
  map_component' : ∀ (n : ℕ) (x : associatedGradedModulePiece (M := M) I n),
    ∃ y : associatedGradedModulePiece (M := N) I n,
      toLinearEquiv (DirectSum.of _ n x) = DirectSum.of _ n y
  inv_component' : ∀ (n : ℕ) (y : associatedGradedModulePiece (M := N) I n),
    ∃ x : associatedGradedModulePiece (M := M) I n,
      toLinearEquiv.symm (DirectSum.of _ n y) = DirectSum.of _ n x

/-- The denominator occurring in the degree-`n` quotient description of
`Gr_I(Coker(g))`. -/
def gradedCokernelDenominator
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (g : M →ₗ[R] N) (n : ℕ) : Submodule R N :=
  I ^ (n + 1) • (⊤ : Submodule R N) ⊔
    (LinearMap.range g ⊓ I ^ n • (⊤ : Submodule R N))

/-- The degree-`n` quotient appearing in the source's formula for the
associated graded cokernel. -/
abbrev gradedCokernelPiece
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (g : M →ₗ[R] N) (n : ℕ) : Type _ :=
  submoduleQuotient (I ^ n • (⊤ : Submodule R N))
    (gradedCokernelDenominator I g n)

/-- The concrete module cokernel used for `Coker(g)`. -/
abbrev linearMapCokernel
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) : Type _ :=
  N ⧸ LinearMap.range g

/-- Degreewise form of the source's identity
`Gr_I(Coker(g))_n = I^n N/(I^(n+1)N + g(M) ∩ I^nN)`. -/
theorem associatedGraded_cokernel_piece_equiv
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (g : M →ₗ[R] N) (n : ℕ) :
    Nonempty (associatedGradedModulePiece (M := linearMapCokernel g) I n ≃ₗ[R]
      gradedCokernelPiece I g n) := by
  classical
  let P : Submodule R N := I ^ n • (⊤ : Submodule R N)
  let Q : Submodule R N := I ^ (n + 1) • (⊤ : Submodule R N)
  let K : Submodule R N := LinearMap.range g
  let C := N ⧸ K
  let P' : Submodule R C := I ^ n • (⊤ : Submodule R C)
  let Q' : Submodule R C := I ^ (n + 1) • (⊤ : Submodule R C)
  let D : Submodule R N := Q ⊔ (K ⊓ P)
  have hP : P.map K.mkQ = P' := by
    dsimp [P, P']
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  have hQ : Q.map K.mkQ = Q' := by
    dsimp [Q, Q']
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  have hQP : Q ≤ P := by
    dsimp [Q, P]
    exact Submodule.smul_mono
      (Ideal.pow_le_pow_right (show n ≤ n + 1 by omega)) le_rfl
  have hpre : Q'.comap K.mkQ = K ⊔ Q := by
    rw [← hQ, Submodule.comap_map_mkQ]
  have hmod : P ⊓ (K ⊔ Q) = D := by
    dsimp [D]
    rw [inf_comm P, sup_comm K Q, sup_inf_assoc_of_le K hQP]
  let u : P →ₗ[R] P' :=
    (K.mkQ.comp P.subtype).codRestrict P' (by
      intro x
      rw [← hP]
      exact Submodule.mem_map_of_mem x.property)
  let v : P →ₗ[R] (P' ⧸ Q'.comap P'.subtype) :=
    (Q'.comap P'.subtype).mkQ.comp u
  have hv : Function.Surjective v := by
    intro z
    refine Submodule.Quotient.induction_on _ z ?_
    intro y
    have hy : (y : C) ∈ P' := y.property
    have hy' : (y : C) ∈ P.map K.mkQ := by
      simpa only [hP] using hy
    rcases Submodule.mem_map.mp hy' with ⟨z, hz, hzy⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    have heq : u ⟨z, hz⟩ = y := by
      apply Subtype.ext
      exact hzy
    change (Q'.comap P'.subtype).mkQ (u ⟨z, hz⟩) = Submodule.Quotient.mk y
    rw [heq]
    rfl
  have hker : LinearMap.ker v = D.comap P.subtype := by
    ext x
    change v x = 0 ↔ (x : N) ∈ D
    constructor
    · intro hx
      change (Q'.comap P'.subtype).mkQ (u x) = 0 at hx
      have hx' : u x ∈ Q'.comap P'.subtype :=
        (Submodule.Quotient.mk_eq_zero (Q'.comap P'.subtype)).mp hx
      have hxq : K.mkQ (x : N) ∈ Q' := hx'
      have hxqpre : (x : N) ∈ Q'.comap K.mkQ := by
        change K.mkQ (x : N) ∈ Q'
        exact hxq
      rw [hpre] at hxqpre
      exact hmod ▸ ⟨x.property, hxqpre⟩
    · intro hx
      change (Q'.comap P'.subtype).mkQ (u x) = 0
      apply (Submodule.Quotient.mk_eq_zero (Q'.comap P'.subtype)).mpr
      have hx' : (x : N) ∈ P ⊓ (K ⊔ Q) := hmod.symm ▸ hx
      have hxq : (x : N) ∈ K ⊔ Q := hx'.2
      have hxq' : K.mkQ (x : N) ∈ Q' := by
        have hxqpre : (x : N) ∈ Q'.comap K.mkQ := by
          rw [hpre]
          exact hxq
        exact hxqpre
      exact hxq'
  change Nonempty (P ⧸ D.comap P.subtype ≃ₗ[R] P' ⧸ Q'.comap P'.subtype)
  refine ⟨?_⟩
  exact (Submodule.quotEquivOfEq (D.comap P.subtype) (LinearMap.ker v) hker.symm).trans
    (v.quotKerEquivOfSurjective hv)

/-- The intersection inclusion used to compare the degreewise cokernel
quotients of two congruent maps. -/
theorem approximate_complex_graded_intersection_le
    {A M N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (c : ℕ)
    (g : M →ₗ[A] N) (g' : M →ₗ[A] N)
    (hc : ArtinReesWorks I g c)
    (hg : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A N)) g' g) (n : ℕ) :
    LinearMap.range g ⊓ I ^ n • (⊤ : Submodule A N) ≤
      I ^ (n + 1) • (⊤ : Submodule A N) ⊔
        (LinearMap.range g' ⊓ I ^ n • (⊤ : Submodule A N)) := by
  sorry

/-- The equality of the two degreewise denominator submodules obtained by
applying the preceding inclusion in both directions. -/
theorem approximate_complex_graded_denominator_eq
    {A M N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (c : ℕ)
    (g : M →ₗ[A] N) (g' : M →ₗ[A] N)
    (hc : ArtinReesWorks I g c) (hc' : ArtinReesWorks I g' c)
    (hg : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A N)) g' g) (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule A N) ⊔
        (LinearMap.range g ⊓ I ^ n • (⊤ : Submodule A N)) =
      I ^ (n + 1) • (⊤ : Submodule A N) ⊔
        (LinearMap.range g' ⊓ I ^ n • (⊤ : Submodule A N)) := by
  sorry

/-- Congruent exact complexes have isomorphic associated graded cokernels as
graded `Gr_I(A)`-modules. -/
theorem approximate_complex_graded
    {A L M N : Type*} [CommRing A]
    [AddCommGroup L] [Module A L]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [IsNoetherianRing A]
    [Module.Finite A L] [Module.Finite A M] [Module.Finite A N]
    (I : Ideal A) (c : ℕ)
    (f : L →ₗ[A] M) (g : M →ₗ[A] N)
    (f' : L →ₗ[A] M) (g' : M →ₗ[A] N)
    (hS : Function.Exact f g) (hS' : g'.comp f' = 0)
    (hI : I ≤ Ring.jacobson A)
    (hc_f : ArtinReesWorks I f c)
    (hc_g : ArtinReesWorks I g c)
    (hf : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A M)) f' f)
    (hg : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A N)) g' g) :
    Nonempty (AssociatedGradedLinearEquiv I
      (M := linearMapCokernel g) (N := linearMapCokernel g')) := by
  sorry

/-! ## Flat base change -/

/-- Extension of scalars identifies the base change of `I^n M` with the
corresponding power of `IB` acting on `B ⊗[A] M`. -/
theorem submodule_baseChange_ideal_pow
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) :
    (I ^ n • (⊤ : Submodule A M)).baseChange B =
      (I.map (algebraMap A B)) ^ n •
        (⊤ : Submodule B (B ⊗[A] M)) := by
  sorry

/-- Flat base change commutes with the preimage of an ideal-power submodule.
This is the source's displayed kernel/preimage identity, with the tensor
submodule written using Mathlib's canonical `Submodule.baseChange`. -/
theorem flat_baseChange_preimage
    {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [Module.Flat A B]
    (I : Ideal A) (f : M →ₗ[A] N) (n : ℕ) :
    Submodule.comap (LinearMap.baseChange B f)
        ((I.map (algebraMap A B)) ^ n •
          (⊤ : Submodule B (B ⊗[A] N))) =
      (Submodule.comap f (I ^ n • (⊤ : Submodule A N))).baseChange B := by
  sorry

/-- A working Artin-Rees exponent remains valid after flat extension of the
Noetherian base ring.  `LinearMap.baseChange B f` uses the canonically
isomorphic convention `B ⊗[A] M` for the source's `M ⊗_A B`. -/
theorem artinReesWorks_baseChange
    {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Flat A B]
    (I : Ideal A) (f : M →ₗ[A] N) (c : ℕ)
    (hc : ArtinReesWorks I f c) :
    ArtinReesWorks (I.map (algebraMap A B))
      (LinearMap.baseChange B f) c := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit04
