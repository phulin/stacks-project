import Formalization.Books.Algebra.Unit51.MoreNoetherianRings
import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Commutative Algebra, Chapter 74: An application of Ext groups

The source's quotients `N / I^n N` and `M / I^n M` are represented by
submodule quotients.  Their induced map is Mathlib's canonical `Submodule.mapQ`,
and split injections are expressed by the categorical `IsSplitMono` predicate
in the module category.
-/

namespace Formalization.Books.Algebra.Unit74

open CategoryTheory
open CategoryTheory.Limits

universe u

/-! ## Quotient maps modulo powers of an ideal -/

/-- The map induced by a module homomorphism on quotients modulo `I ^ n`. -/
def adicQuotientMap {R N M : Type u} [CommRing R]
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
    (I : Ideal R) (φ : N →ₗ[R] M) (n : ℕ) :
    N ⧸ (I ^ n • (⊤ : Submodule R N)) →ₗ[R]
      M ⧸ (I ^ n • (⊤ : Submodule R M)) :=
  (I ^ n • (⊤ : Submodule R N)).mapQ
    (I ^ n • (⊤ : Submodule R M)) φ
    (Submodule.smul_top_le_comap_smul_top (I ^ n) φ)

/-! ## The application -/

/-- A module map that splits modulo arbitrarily large powers of a Jacobson-radical
ideal already splits. -/
theorem split_injection_after_completion
    {R N M : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) (φ : N →ₗ[R] M)
    (hφ : ∀ N₀ : ℕ, ∃ n ≥ N₀,
      IsSplitMono (ModuleCat.ofHom (adicQuotientMap I φ n))) :
    IsSplitMono (ModuleCat.ofHom φ) := by
  classical
  have hmono (n : ℕ) (hn : IsSplitMono (ModuleCat.ofHom (adicQuotientMap I φ n))) :
      Function.Injective (adicQuotientMap I φ n) := by
    let _ : IsSplitMono (ModuleCat.ofHom (adicQuotientMap I φ n)) := hn
    let _ : Mono (ModuleCat.ofHom (adicQuotientMap I φ n)) := inferInstance
    exact (ModuleCat.mono_iff_injective (ModuleCat.ofHom (adicQuotientMap I φ n))).mp inferInstance
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have hx : x - y ∈ Formalization.Books.Algebra.Unit51.powersIntersectionSubmodule I := by
      change x - y ∈ ⨅ n : ℕ, I ^ n • (⊤ : Submodule R N)
      rw [Submodule.mem_iInf]
      intro n
      obtain ⟨m, hmn, hm⟩ := hφ n
      have hzero : adicQuotientMap I φ m
          (Submodule.mkQ (I ^ m • (⊤ : Submodule R N)) (x - y)) = 0 := by
        change ((I ^ m • (⊤ : Submodule R N)).mapQ
          (I ^ m • (⊤ : Submodule R M)) φ _) ((I ^ m • (⊤ : Submodule R N)).mkQ (x-y)) = 0
        rw [← LinearMap.comp_apply, Submodule.mapQ_mkQ]
        simp [hxy]
      have hzero' :
          adicQuotientMap I φ m
              (Submodule.mkQ (I ^ m • (⊤ : Submodule R N)) (x-y)) =
            adicQuotientMap I φ m 0 := by
        rw [hzero, map_zero]
      have hmk := hmono m hm (a₁ := Submodule.mkQ
          (I ^ m • (⊤ : Submodule R N)) (x-y)) (a₂ := 0) hzero'
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmk
      exact (Submodule.pow_smul_top_le I N hmn) hmk
    have hz : x - y = 0 := by
      have hbot :=
        Formalization.Books.Algebra.Unit51.powersIntersectionSubmodule_eq_bot_of_le_jacobson
          (M := N) I hI
      rw [hbot] at hx
      exact hx
    exact sub_eq_zero.mp hz
  have map_mem_smul_top
      {A B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
      [Module.Free R A] [Module.Finite R A] (J : Ideal R) (v : A →ₗ[R] B)
      (hv : ∀ x, v x ∈ J • (⊤ : Submodule R B)) :
      v ∈ J • (⊤ : Submodule R (A →ₗ[R] B)) := by
    let ι := Module.Free.ChooseBasisIndex R A
    let b : Module.Basis ι R A := Module.Free.chooseBasis R A
    let _ : Fintype ι := Fintype.ofFinite ι
    have hterm (i : ι) :
        (b.coord i).smulRight (v (b i)) ∈
          J • (⊤ : Submodule R (A →ₗ[R] B)) := by
      refine Submodule.smul_induction_on (I := J) (N := (⊤ : Submodule R B))
        (p := fun y => (b.coord i).smulRight y ∈
          J • (⊤ : Submodule R (A →ₗ[R] B))) (hv (b i)) ?_ ?_
      · intro r hr z hz
        have heq :
            (b.coord i).smulRight (r • z) = r • (b.coord i).smulRight z := by
          ext x
          change (b.coord i x) • (r • z) = r • ((b.coord i x) • z)
          rw [smul_smul, smul_smul, mul_comm]
        rw [heq]
        exact Submodule.smul_mem_smul hr trivial
      · intro z₁ z₂ hz₁ hz₂
        have heq :
            (b.coord i).smulRight (z₁ + z₂) =
              (b.coord i).smulRight z₁ + (b.coord i).smulRight z₂ := by
          ext x
          simp
        rw [heq]
        exact add_mem hz₁ hz₂
    have hvsum :
        v = ∑ i : ι, (b.coord i).smulRight (v (b i)) := by
      apply b.ext
      intro i
      simp only [LinearMap.sum_apply]
      change v (b i) =
        ∑ j : ι, (b.coord j) (b i) • v (b j)
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
      · rw [b.coord_apply]
        simp
      · intro j hj hji
        rw [b.coord_apply]
        simp [hji]
    rw [hvsum]
    exact Submodule.sum_mem _ (fun i _ => hterm i)
  let Q : ModuleCat R := ModuleCat.of R (M ⧸ LinearMap.range φ)
  let q : M →ₗ[R] (M ⧸ LinearMap.range φ) := (LinearMap.range φ).mkQ
  have hq : Function.Surjective q := by
    exact Submodule.mkQ_surjective _
  have hexact : Function.Exact φ q := by
    rw [LinearMap.exact_iff]
    change LinearMap.ker ((LinearMap.range φ).mkQ) = LinearMap.range φ
    rw [Submodule.ker_mkQ]
  let _ : Epi (ModuleCat.ofHom q) :=
    (ModuleCat.epi_iff_surjective _).mpr hq
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (ModuleCat.ofHom φ) (ModuleCat.ofHom q) (by
      apply ModuleCat.hom_ext
      exact LinearMap.range_mkQ_comp φ)
  have hS : S.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · exact hexact
    · exact hφ_inj
    · exact hq
  obtain ⟨F⟩ :=
    Formalization.Books.Algebra.Unit71.exists_finite_free_resolution Q
  let F0 : ModuleCat R := F.complex.X 0
  let F1 : ModuleCat R := F.complex.X 1
  let d1 : (F1 : Type u) →ₗ[R] (F0 : Type u) := (F.complex.d 1 0).hom
  let eps : (F0 : Type u) →ₗ[R] (Q : Type u) :=
    F.resolution.resolution.augmentation.hom
  let _ : Module.Free R (F0 : Type u) := F.resolution.free 0
  let _ : Module.Finite R (F0 : Type u) := F.finite 0
  let _ : Module.Free R (F1 : Type u) := F.resolution.free 1
  let _ : Module.Finite R (F1 : Type u) := F.finite 1
  let _ : Projective F0 :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis R (F0 : Type u))
  let _ : Projective F1 :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis R (F1 : Type u))
  let alphaCat : F0 ⟶ ModuleCat.of R M :=
    Projective.factorThru F.resolution.resolution.augmentation (ModuleCat.ofHom q)
  let alpha : (F0 : Type u) →ₗ[R] M := alphaCat.hom
  have halpha : q.comp alpha = eps := by
    exact ModuleCat.hom_ext_iff.mp (Projective.factorThru_comp
      F.resolution.resolution.augmentation (ModuleCat.ofHom q))
  have hd1q : eps.comp d1 = 0 := by
    exact ModuleCat.hom_ext_iff.mp F.resolution.resolution.augmentation_condition
  have hda : q.comp (alpha.comp d1) = 0 := by
    rw [← LinearMap.comp_assoc, halpha]
    exact hd1q
  let betaCat : F1 ⟶ ModuleCat.of R N :=
    hS.exact.liftFromProjective (ModuleCat.ofHom (alpha.comp d1)) (by
      apply ModuleCat.hom_ext
      exact hda)
  let beta : (F1 : Type u) →ₗ[R] N := betaCat.hom
  have hbeta : φ.comp beta = alpha.comp d1 := by
    exact ModuleCat.hom_ext_iff.mp (hS.exact.liftFromProjective_comp
      (ModuleCat.ofHom (alpha.comp d1)) (by
        apply ModuleCat.hom_ext
        exact hda))
  let H := (F1 : Type u) →ₗ[R] N
  let precomp : ((F0 : Type u) →ₗ[R] N) →ₗ[R] H :=
    { toFun := fun g => g.comp d1
      map_add' := by intro g h; ext x <;> rfl
      map_smul' := by intro r g; ext x <;> rfl }
  let C := H ⧸ LinearMap.range precomp
  let c : H →ₗ[R] C := (LinearMap.range precomp).mkQ
  have hCfinite : Module.Finite R C := inferInstance
  have hquot (n : ℕ) (hn : IsSplitMono (ModuleCat.ofHom (adicQuotientMap I φ n))) :
      c beta ∈ I ^ n • (⊤ : Submodule R C) := by
    let qN : N →ₗ[R] (N ⧸ (I ^ n • (⊤ : Submodule R N))) :=
      (I ^ n • (⊤ : Submodule R N)).mkQ
    let qM : M →ₗ[R] (M ⧸ (I ^ n • (⊤ : Submodule R M))) :=
      (I ^ n • (⊤ : Submodule R M)).mkQ
    have hqN : Function.Surjective qN := Submodule.mkQ_surjective _
    let _ : Epi (ModuleCat.ofHom qN) :=
      (ModuleCat.epi_iff_surjective _).mpr hqN
    let a := adicQuotientMap I φ n
    let _ : IsSplitMono (ModuleCat.ofHom a) := hn
    let rCat := CategoryTheory.retraction (ModuleCat.ofHom a)
    let r : (M ⧸ (I ^ n • (⊤ : Submodule R M))) →ₗ[R]
        (N ⧸ (I ^ n • (⊤ : Submodule R N))) := rCat.hom
    have hretCat : ModuleCat.ofHom a ≫ rCat = 𝟙 _ :=
      CategoryTheory.IsSplitMono.id _
    have hret : r.comp a = LinearMap.id := by
      change rCat.hom.comp a = LinearMap.id
      exact ModuleCat.hom_ext_iff.mp hretCat
    have hcompat : a.comp qN = qM.comp φ := by
      simpa [a, qN, qM, adicQuotientMap] using
        (Submodule.mapQ_mkQ (I ^ n • (⊤ : Submodule R N))
          (I ^ n • (⊤ : Submodule R M)) φ)
    let gammaBar : (F0 : Type u) →ₗ[R]
        (N ⧸ (I ^ n • (⊤ : Submodule R N))) :=
      r.comp (qM.comp alpha)
    let gammaBarCat : F0 ⟶ ModuleCat.of R
        (N ⧸ (I ^ n • (⊤ : Submodule R N))) :=
      ModuleCat.ofHom gammaBar
    let gammaCat : F0 ⟶ ModuleCat.of R N :=
      Projective.factorThru (P := F0) (X := ModuleCat.of R
        (N ⧸ (I ^ n • (⊤ : Submodule R N)))) (E := ModuleCat.of R N)
        gammaBarCat (ModuleCat.ofHom qN)
    let gamma : (F0 : Type u) →ₗ[R] N := gammaCat.hom
    have hgamma : qN.comp gamma = gammaBar := by
      exact ModuleCat.hom_ext_iff.mp (Projective.factorThru_comp
        gammaBarCat (ModuleCat.ofHom qN))
    have hmod : qN.comp beta = gammaBar.comp d1 := by
      calc
        qN.comp beta = r.comp (a.comp (qN.comp beta)) := by
          rw [← LinearMap.comp_assoc, hret]
          simp
        _ = r.comp ((a.comp qN).comp beta) := by
          simp [LinearMap.comp_assoc]
        _ = r.comp (qM.comp (φ.comp beta)) := by
          rw [hcompat]
          simp only [LinearMap.comp_assoc]
        _ = r.comp (qM.comp (alpha.comp d1)) := by rw [hbeta]
        _ = gammaBar.comp d1 := by
          simp [gammaBar, LinearMap.comp_assoc]
    have hwq : qN.comp (beta - gamma.comp d1) = 0 := by
      ext x
      change qN (beta x) - qN (gamma (d1 x)) = 0
      have hm := congrArg (fun f => f x) hmod
      have hg := congrArg (fun f => f (d1 x)) hgamma
      dsimp at hm hg
      rw [hm, hg]
      simp
    have hwpoint : ∀ x, (beta - gamma.comp d1) x ∈
        I ^ n • (⊤ : Submodule R N) := by
      intro x
      have hz := congrArg (fun f => f x) hwq
      change qN ((beta - gamma.comp d1) x) = 0 at hz
      change (I ^ n • (⊤ : Submodule R N)).mkQ
        ((beta - gamma.comp d1) x) = 0 at hz
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
      exact hz
    have hw : beta - gamma.comp d1 ∈ I ^ n • (⊤ : Submodule R H) :=
      map_mem_smul_top (I ^ n) (beta - gamma.comp d1) hwpoint
    have hcw : c (beta - gamma.comp d1) ∈
        I ^ n • (⊤ : Submodule R C) := by
      refine Submodule.smul_induction_on (I := I ^ n) (N := (⊤ : Submodule R H))
        (p := fun z => c z ∈ I ^ n • (⊤ : Submodule R C)) hw ?_ ?_
      · intro r hr z hz
        rw [map_smul]
        exact Submodule.smul_mem_smul hr trivial
      · intro z₁ z₂ hz₁ hz₂
        rw [map_add]
        exact add_mem hz₁ hz₂
    have hcpre : c (gamma.comp d1) = 0 := by
      change (LinearMap.range precomp).mkQ (gamma.comp d1) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨gamma, by rfl⟩
    have hsum : beta = (beta - gamma.comp d1) + gamma.comp d1 := by
      rw [sub_add_cancel]
    rw [hsum, map_add, hcpre, add_zero]
    exact hcw
  have hc_inter : c beta ∈
      Formalization.Books.Algebra.Unit51.powersIntersectionSubmodule I := by
    change c beta ∈ ⨅ n : ℕ, I ^ n • (⊤ : Submodule R C)
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨m, hmn, hm⟩ := hφ n
    exact (Submodule.pow_smul_top_le I C hmn) (hquot m hm)
  have hc_zero : c beta = 0 := by
    have hbot :=
      Formalization.Books.Algebra.Unit51.powersIntersectionSubmodule_eq_bot_of_le_jacobson
        (M := C) I hI
    rw [hbot] at hc_inter
    exact hc_inter
  have hbeta_range : beta ∈ LinearMap.range precomp := by
    have hk : beta ∈ LinearMap.ker c := by
      exact (LinearMap.mem_ker).mpr hc_zero
    change beta ∈ (LinearMap.range precomp).mkQ.ker at hk
    rw [Submodule.ker_mkQ] at hk
    exact hk
  obtain ⟨gamma₀, hgamma₀⟩ := hbeta_range
  let epsCat : F0 ⟶ Q := F.resolution.resolution.augmentation
  let qCat : ModuleCat.of R M ⟶ Q := ModuleCat.ofHom q
  let _ : Epi epsCat := F.resolution.resolution.augmentation_epi
  let P := pullback epsCat qCat
  let p0 : P ⟶ F0 := pullback.fst epsCat qCat
  let pM : P ⟶ ModuleCat.of R M := pullback.snd epsCat qCat
  let _ : Epi pM := inferInstance
  let d1Cat : F1 ⟶ F0 := ModuleCat.ofHom d1
  let SF : ShortComplex (ModuleCat R) :=
    ShortComplex.mk d1Cat epsCat F.resolution.resolution.augmentation_condition
  have hSF : SF.Exact := F.resolution.resolution.exact_zero
  have hFfunc : Function.Exact d1 eps := by
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact SF).mp hSF
  have hbeta₀ : beta = gamma₀.comp d1 := by
    exact hgamma₀.symm
  have halphaCat : alphaCat ≫ qCat = epsCat :=
    Projective.factorThru_comp F.resolution.resolution.augmentation (ModuleCat.ofHom q)
  let _ : Mono S.f := hS.mono_f
  let k : P ⟶ ModuleCat.of R M := p0 ≫ alphaCat - pM
  have hk : k ≫ qCat = 0 := by
    dsimp [k]
    rw [Preadditive.sub_comp, Category.assoc, halphaCat, pullback.condition, sub_self]
  let l : P ⟶ ModuleCat.of R N := hS.exact.lift k hk
  have hl : l ≫ S.f = k := hS.exact.lift_f k hk
  let SK := LinearMap.shortComplexKer pM.hom
  have hSK : SK.ShortExact := by
    apply LinearMap.shortExact_shortComplexKer
    exact (ModuleCat.epi_iff_surjective pM).mp inferInstance
  let gammaCat₀ : F0 ⟶ ModuleCat.of R N := ModuleCat.ofHom gamma₀
  let hCat : P ⟶ ModuleCat.of R N := l - p0 ≫ gammaCat₀
  have hzero : SK.f ≫ hCat = 0 := by
    apply ModuleCat.hom_ext
    ext x
    have hl' : φ.comp l.hom = k.hom := by
      exact ModuleCat.hom_ext_iff.mp hl
    have hpcond : eps.comp (p0.hom.comp SK.f.hom) = 0 := by
      have hpcondCat : (SK.f ≫ p0) ≫ epsCat = 0 := by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        change (SK.f ≫ SK.g) ≫ qCat = 0
        rw [SK.zero, zero_comp]
      exact ModuleCat.hom_ext_iff.mp hpcondCat
    have hxeps : eps (p0.hom (SK.f.hom x)) = 0 := by
      exact congrArg (fun f => f x) hpcond
    have hy_range : p0.hom (SK.f.hom x) ∈ Set.range d1 :=
      (hFfunc _).mp hxeps
    obtain ⟨y, hy⟩ := hy_range
    have hpMzero : pM.hom (SK.f.hom x) = 0 := by
      have hz := congrArg (fun f => f x) (ModuleCat.hom_ext_iff.mp SK.zero)
      exact hz
    have hφzero : φ (l.hom (SK.f.hom x) -
        gamma₀ (p0.hom (SK.f.hom x))) = 0 := by
      rw [map_sub]
      apply sub_eq_zero.mpr
      calc
        φ (l.hom (SK.f.hom x)) = k.hom (SK.f.hom x) := by
          exact congrArg (fun f => f (SK.f.hom x)) hl'
        _ = alpha (p0.hom (SK.f.hom x)) - pM.hom (SK.f.hom x) := by
          rfl
        _ = alpha (p0.hom (SK.f.hom x)) := by rw [hpMzero, sub_zero]
        _ = alpha (d1 y) := by rw [hy]
        _ = φ (beta y) := by
          exact (congrArg (fun f => f y) hbeta).symm
        _ = φ (gamma₀ (p0.hom (SK.f.hom x))) := by
          rw [congrArg (fun f => f y) hbeta₀]
          change φ (gamma₀ (d1 y)) = _
          rw [hy]
    have hφeq : φ (l.hom (SK.f.hom x) -
        gamma₀ (p0.hom (SK.f.hom x))) = φ 0 := by
      simpa using hφzero
    have hdiff : l.hom (SK.f.hom x) -
        gamma₀ (p0.hom (SK.f.hom x)) = 0 := hφ_inj hφeq
    change l.hom (SK.f.hom x) - gamma₀ (p0.hom (SK.f.hom x)) = 0
    exact hdiff
  let _ : Epi SK.g := hSK.epi_g
  let s₀ : ModuleCat.of R M ⟶ ModuleCat.of R N :=
    hSK.exact.desc hCat hzero
  have hs₀ : pM ≫ s₀ = hCat := by
    exact hSK.exact.g_desc hCat hzero
  let φCat : ModuleCat.of R N ⟶ ModuleCat.of R M := ModuleCat.ofHom φ
  let j : ModuleCat.of R N ⟶ P :=
    pullback.lift (0 : ModuleCat.of R N ⟶ F0) φCat (by
      rw [zero_comp]
      exact S.zero.symm)
  have hj0 : j ≫ p0 = 0 := by
    exact pullback.lift_fst _ _ _
  have hjM : j ≫ pM = φCat := by
    exact pullback.lift_snd _ _ _
  have hsj : φCat ≫ s₀ = j ≫ l := by
    calc
      φCat ≫ s₀ = (j ≫ pM) ≫ s₀ := by rw [hjM]
      _ = j ≫ (pM ≫ s₀) := by simp [Category.assoc]
      _ = j ≫ hCat := by rw [hs₀]
      _ = j ≫ l := by
        dsimp [hCat]
        rw [Preadditive.comp_sub, ← Category.assoc, hj0, zero_comp, sub_zero]
  have hφs₀ : φCat ≫ s₀ = -𝟙 _ := by
    apply (cancel_mono φCat).1
    calc
      (φCat ≫ s₀) ≫ φCat = (j ≫ l) ≫ φCat := by rw [hsj]
      _ = j ≫ (l ≫ S.f) := by rfl
      _ = j ≫ k := by rw [hl]
      _ = -φCat := by
        dsimp [k]
        rw [Preadditive.comp_sub, ← Category.assoc, hj0, zero_comp, hjM]
        simp
      _ = (-𝟙 _) ≫ φCat := by simp
  apply CategoryTheory.IsSplitMono.mk'
  refine ⟨-s₀, ?_⟩
  rw [Preadditive.comp_neg, hφs₀, neg_neg]

end Formalization.Books.Algebra.Unit74
