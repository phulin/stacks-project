/-
# More on Algebra, Chapter 121: the short-exact-sequence formulas
-/

import Formalization.Books.MoreAlgebra.Unit121.Core
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

namespace Formalization.Books.MoreAlgebra.Unit121

noncomputable section

open CategoryTheory

universe u v

/-!
`ShortComplex.ShortExact` is Mathlib's canonical interface for a short exact sequence.  In
particular, the sequence below is a short complex in the abelian category of pairs, so the
commuting endomorphism data are retained by the morphisms themselves.
-/

/-!
The determinant definitions are expressed through the underlying modules, whereas the
short-exact hypothesis lives in the pair category.  This is the concrete bridge needed by
the module-level composition-series argument; it is kept as an interface so that the
categorical Abelian instance does not leak into downstream proofs.
-/

theorem shortExact_underlying_data
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (FiniteLengthEndomorphism.{u, v} R)}
    (hS : S.ShortExact) :
    Function.Exact S.f.hom.hom S.g.hom.hom ∧
      Function.Injective S.f.hom.hom ∧ Function.Surjective S.g.hom.hom := by
  let concreteZero : CategoryTheory.Limits.HasZeroMorphisms
      (FiniteLengthEndomorphism.{u, v} R) :=
    { zero := fun X Y =>
        { zero :=
            { hom := ModuleCat.ofHom 0
              comm := by
                apply ModuleCat.hom_ext
                simp } }
      comp_zero := by
        intro X Y f Z
        apply FiniteLengthEndomorphism.Morph.ext
        change f.hom ≫ ModuleCat.ofHom 0 = ModuleCat.ofHom 0
        apply ModuleCat.hom_ext
        simp
      zero_comp := by
        intro X Y Z f
        apply FiniteLengthEndomorphism.Morph.ext
        change ModuleCat.ofHom 0 ≫ f.hom = ModuleCat.ofHom 0
        apply ModuleCat.hom_ext
        simp }
  have underlying_injective {A B : FiniteLengthEndomorphism.{u, v} R}
      (f : A ⟶ B)
      (hf : ∀ {Z : FiniteLengthEndomorphism.{u, v} R} (g h : Z ⟶ A),
        g ≫ f = h ≫ f → g = h) : Function.Injective f.hom.hom := by
    intro x y hxy
    let K : Submodule R A.carrier := LinearMap.ker f.hom.hom
    have hcomm : ∀ z : A.carrier,
        f.hom.hom (A.endomorphism.hom z) =
          B.endomorphism.hom (f.hom.hom z) := by
      intro z
      have hz := congrArg (fun g : A.carrier ⟶ B.carrier => g z) f.comm
      simpa [ModuleCat.comp_apply] using hz
    have hstable : ∀ z : A.carrier, z ∈ K → A.endomorphism.hom z ∈ K := by
      intro z hz
      change f.hom.hom (A.endomorphism.hom z) = 0
      rw [hcomm, hz, map_zero]
    let phiK : Module.End R K :=
      A.endomorphism.hom.restrict hstable
    let A' : FiniteLengthEndomorphism.{u, v} R :=
      { carrier := ModuleCat.of R K
        finite_length := A.finite_length.of_injective K.injective_subtype
        endomorphism := ModuleCat.ofHom phiK }
    let i : A' ⟶ A :=
      { hom := ModuleCat.ofHom K.subtype
        comm := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          rfl }
    let z : A' ⟶ A :=
      { hom := ModuleCat.ofHom 0
        comm := by
          apply ModuleCat.hom_ext
          simp }
    have hcomp : i ≫ f = z ≫ f := by
      apply FiniteLengthEndomorphism.Morph.ext
      change i.hom ≫ f.hom = z.hom ≫ f.hom
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
      change f.hom.hom (K.subtype w) = f.hom.hom 0
      rw [show K.subtype w = (w : A.carrier) by rfl, w.property, map_zero]
    have hiz : i = z := hf i z hcomp
    have hxy' : f.hom.hom (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    let w : K := ⟨x - y, hxy'⟩
    have hw := congrArg (fun k : A' ⟶ A => k.hom.hom w) hiz
    have hzero : x - y = 0 := by
      change x - y = 0 at hw
      exact hw
    exact sub_eq_zero.mp hzero
  have underlying_surjective {A B : FiniteLengthEndomorphism.{u, v} R}
      (f : A ⟶ B)
      (hf : ∀ {Z : FiniteLengthEndomorphism.{u, v} R} (g h : B ⟶ Z),
        f ≫ g = f ≫ h → g = h) : Function.Surjective f.hom.hom := by
    let I : Submodule R B.carrier := LinearMap.range f.hom.hom
    have hstable : ∀ z : B.carrier, z ∈ I → B.endomorphism.hom z ∈ I := by
      intro z hz
      obtain ⟨y, hy⟩ := hz
      refine ⟨A.endomorphism.hom y, ?_⟩
      have hz' := congrArg (fun g : A.carrier ⟶ B.carrier => g y) f.comm
      simpa [ModuleCat.comp_apply, hy] using hz'
    let phiQ : Module.End R (B.carrier ⧸ I) :=
      I.mapQ I B.endomorphism.hom hstable
    let Q : FiniteLengthEndomorphism.{u, v} R :=
      { carrier := ModuleCat.of R (B.carrier ⧸ I)
        finite_length := B.finite_length.of_surjective (Submodule.mkQ_surjective _)
        endomorphism := ModuleCat.ofHom phiQ }
    let q : B ⟶ Q :=
      { hom := ModuleCat.ofHom I.mkQ
        comm := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          rfl }
    let z : B ⟶ Q :=
      { hom := ModuleCat.ofHom 0
        comm := by
          apply ModuleCat.hom_ext
          simp }
    have hcomp : f ≫ q = f ≫ z := by
      apply FiniteLengthEndomorphism.Morph.ext
      change f.hom ≫ q.hom = f.hom ≫ z.hom
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
      change I.mkQ (f.hom.hom y) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨y, rfl⟩
    have hqz : q = z := hf q z hcomp
    intro y
    have hy := congrArg (fun k : B ⟶ Q => k.hom.hom y) hqz
    have hyI : y ∈ I := by
      change I.mkQ y = 0 at hy
      exact (Submodule.Quotient.mk_eq_zero _).1 hy
    obtain ⟨x, hx⟩ := hyI
    exact ⟨x, hx⟩
  let : CategoryTheory.Limits.HasZeroMorphisms
      (FiniteLengthEndomorphism.{u, v} R) :=
    CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  have zero_hom {A B : FiniteLengthEndomorphism.{u, v} R} :
      (0 : A ⟶ B).hom = ModuleCat.ofHom 0 := by
    have hi : (inferInstance : CategoryTheory.Limits.HasZeroMorphisms
        (FiniteLengthEndomorphism.{u, v} R)) = concreteZero :=
      Subsingleton.elim _ _
    have hzero_eq : (0 : A ⟶ B) =
        @Zero.zero (A ⟶ B) (concreteZero.zero A B) := by
      change @Zero.zero (A ⟶ B)
          (@CategoryTheory.Limits.HasZeroMorphisms.zero
            (FiniteLengthEndomorphism.{u, v} R) _ (inferInstance) A B) =
        @Zero.zero (A ⟶ B) (concreteZero.zero A B)
      rw [hi]
    rw [hzero_eq]
    rfl
  have hmf : Mono S.f := hS.mono_f
  have heg : Epi S.g := hS.epi_g
  have hmono : Function.Injective S.f.hom.hom :=
    underlying_injective S.f (fun g h hgh => hmf.right_cancellation g h hgh)
  have hepi : Function.Surjective S.g.hom.hom :=
    underlying_surjective S.g (fun g h hgh => heg.left_cancellation g h hgh)
  have hexact : Function.Exact S.f.hom.hom S.g.hom.hom := by
    let : Mono S.f := hmf
    let K : Submodule R S.X₂.carrier := LinearMap.ker S.g.hom.hom
    have hcomm : ∀ z : S.X₂.carrier,
        S.g.hom.hom (S.X₂.endomorphism.hom z) =
          S.X₃.endomorphism.hom (S.g.hom.hom z) := by
      intro z
      have hz := congrArg (fun g : S.X₂.carrier ⟶ S.X₃.carrier => g z) S.g.comm
      simpa [ModuleCat.comp_apply] using hz
    have hstable : ∀ z : S.X₂.carrier, z ∈ K →
        S.X₂.endomorphism.hom z ∈ K := by
      intro z hz
      change S.g.hom.hom (S.X₂.endomorphism.hom z) = 0
      rw [hcomm, hz, map_zero]
    let phiK : Module.End R K := S.X₂.endomorphism.hom.restrict hstable
    let Kobj : FiniteLengthEndomorphism.{u, v} R :=
      { carrier := ModuleCat.of R K
        finite_length := S.X₂.finite_length.of_injective K.injective_subtype
        endomorphism := ModuleCat.ofHom phiK }
    let k : Kobj ⟶ S.X₂ :=
      { hom := ModuleCat.ofHom K.subtype
        comm := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          rfl }
    have hk : k ≫ S.g = 0 := by
      apply FiniteLengthEndomorphism.Morph.ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      rw [show (k ≫ S.g).hom = k.hom ≫ S.g.hom by rfl,
        ModuleCat.comp_apply, zero_hom]
      exact z.property
    intro x
    constructor
    · intro hx
      let w : K := ⟨x, hx⟩
      let l : Kobj ⟶ S.X₁ := hS.exact.lift k hk
      have hl : l ≫ S.f = k := hS.exact.lift_f k hk
      have hw := congrArg (fun q : Kobj ⟶ S.X₂ => q.hom.hom w) hl
      refine ⟨l.hom.hom w, ?_⟩
      change S.f.hom.hom (l.hom.hom w) = x at hw
      exact hw
    · rintro ⟨y, rfl⟩
      have hz' := congrArg (fun q : S.X₁ ⟶ S.X₃ => q.hom) S.zero
      rw [show (S.f ≫ S.g).hom = S.f.hom ≫ S.g.hom by rfl, zero_hom] at hz'
      have hz := congrArg (fun q : S.X₁.carrier ⟶ S.X₃.carrier => q.hom y) hz'
      simpa [ModuleCat.comp_apply] using hz
  exact ⟨hexact, hmono, hepi⟩

private theorem isSimplePair_transport
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    {φ : Module.End R M} {ψ : Module.End R N}
    (hφ : IsSimplePair φ) (e : M ≃ₗ[R] N)
    (he : ∀ x, e (φ x) = ψ (e x)) : IsSimplePair ψ := by
  constructor
  · rcases hφ.1 with ⟨x, y, hxy⟩
    refine ⟨e x, e y, ?_⟩
    intro h
    apply hxy
    apply e.injective
    simpa using h
  · intro P hP
    let Q : Submodule R M := P.comap (e : M →ₗ[R] N)
    have hQ : Submodule.map φ Q ≤ Q := by
      rintro _ ⟨x, hx, rfl⟩
      change e (φ x) ∈ P
      rw [he]
      exact hP ⟨e x, hx, rfl⟩
    rcases hφ.2 Q hQ with hQbot | hQtop
    · left
      ext y
      constructor
      · intro hy
        let x : M := e.symm y
        have hxQ : x ∈ Q := by
          change e x ∈ P
          simpa [x] using hy
        have hx0 : x = 0 := by
          apply (Submodule.mem_bot R).mp
          rw [← hQbot]
          exact hxQ
        simpa [x] using congrArg e hx0
      · intro hy
        exact (Submodule.mem_bot R).mp hy ▸ P.zero_mem
    · right
      apply top_unique
      intro y hy
      have hyQ : e.symm y ∈ Q := by
        rw [hQtop]
        exact Submodule.mem_top
      rw [← e.apply_symm_apply y]
      exact hyQ

private theorem simplePair_invariant_local
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    {φ : Module.End R M} {ψ : Module.End R N}
    (D : SimplePairData R M φ) (E : SimplePairData R N ψ)
    (e : M ≃ₗ[R] N)
    (he : ∀ x, e (φ x) = ψ (e x)) :
    simpleDeterminant D = simpleDeterminant E ∧
      simpleTrace D = simpleTrace E := by
  let _ : Module (IsLocalRing.ResidueField R) M := D.annihilated.module
  let _ : Module (IsLocalRing.ResidueField R) N := E.annihilated.module
  let _ : Module.Finite (IsLocalRing.ResidueField R) M := D.finite_dimensional
  let _ : Module.Finite (IsLocalRing.ResidueField R) N := E.finite_dimensional
  let eK : M ≃ₗ[IsLocalRing.ResidueField R] N :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro c x
        obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (R := R) c
        rw [← hr]
        change e (IsLocalRing.residue R r • x) =
          IsLocalRing.residue R r • e x
        have hM : IsLocalRing.residue R r • x = r • x :=
          D.annihilated.mk_smul r x
        have hN : IsLocalRing.residue R r • e x = r • e x :=
          E.annihilated.mk_smul r (e x)
        rw [hM, hN]
        exact e.map_smul r x }
  have heK :
      (eK : M →ₗ[IsLocalRing.ResidueField R] N) ∘ₗ
          (D.residue_endomorphism ∘ₗ
            (eK.symm : N →ₗ[IsLocalRing.ResidueField R] M)) =
        E.residue_endomorphism := by
    apply LinearMap.ext
    intro x
    change eK (D.residue_endomorphism.toFun (eK.symm x)) =
      E.residue_endomorphism.toFun x
    rw [D.residue_endomorphism_apply, E.residue_endomorphism_apply]
    simpa [eK] using he (e.symm x)
  have hdet := LinearMap.det_conj D.residue_endomorphism eK
  rw [heK] at hdet
  have heK' : eK.conj D.residue_endomorphism =
      E.residue_endomorphism := by
    apply LinearMap.ext
    intro x
    change eK (D.residue_endomorphism.toFun (eK.symm x)) =
      E.residue_endomorphism.toFun x
    rw [D.residue_endomorphism_apply, E.residue_endomorphism_apply]
    simpa [eK] using he (e.symm x)
  have htrace := LinearMap.trace_conj' D.residue_endomorphism eK
  rw [heK'] at htrace
  constructor
  · exact hdet.symm
  · exact htrace.symm

private theorem simpleCharacteristicPolynomial_iso
    {R M N : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    {φ : Module.End R M} {ψ : Module.End R N}
    (D : SimplePairData R M φ) (E : SimplePairData R N ψ)
    (e : M ≃ₗ[R] N)
    (he : ∀ x, e (φ x) = ψ (e x)) :
    simpleCharacteristicPolynomial D = simpleCharacteristicPolynomial E := by
  let _ : Module (IsLocalRing.ResidueField R) M := D.annihilated.module
  let _ : Module (IsLocalRing.ResidueField R) N := E.annihilated.module
  let _ : Module.Finite (IsLocalRing.ResidueField R) M := D.finite_dimensional
  let _ : Module.Finite (IsLocalRing.ResidueField R) N := E.finite_dimensional
  let eK : M ≃ₗ[IsLocalRing.ResidueField R] N :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro c x
        obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (R := R) c
        rw [← hr]
        change e (IsLocalRing.residue R r • x) =
          IsLocalRing.residue R r • e x
        have hM : IsLocalRing.residue R r • x = r • x :=
          D.annihilated.mk_smul r x
        have hN : IsLocalRing.residue R r • e x = r • e x :=
          E.annihilated.mk_smul r (e x)
        rw [hM, hN]
        exact e.map_smul r x }
  have heK :
      eK.conj D.residue_endomorphism = E.residue_endomorphism := by
    apply LinearMap.ext
    intro x
    change eK (D.residue_endomorphism.toFun (eK.symm x)) =
      E.residue_endomorphism.toFun x
    rw [D.residue_endomorphism_apply, E.residue_endomorphism_apply]
    simpa [eK] using he (e.symm x)
  have hchar := LinearEquiv.charpoly_conj eK D.residue_endomorphism
  rw [heK] at hchar
  exact hchar.symm

theorem lemma_ses_det
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (FiniteLengthEndomorphism.{u, v} R)}
    (hS : S.ShortExact) :
    determinant S.X₂ = determinant S.X₁ * determinant S.X₃ := by
  sorry

theorem lemma_ses_trace
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (FiniteLengthEndomorphism.{u, v} R)}
    (hS : S.ShortExact) :
    trace S.X₂ = trace S.X₁ + trace S.X₃ := by
  sorry

theorem lemma_ses_characteristicPolynomial
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (FiniteLengthEndomorphism.{u, v} R)}
    (hS : S.ShortExact) :
    characteristicPolynomial S.X₂ =
      characteristicPolynomial S.X₁ * characteristicPolynomial S.X₃ := by
  have hdata := shortExact_underlying_data hS
  have hcomm_f : ∀ x : S.X₁.carrier,
      S.f.hom.hom (S.X₁.endomorphism.hom x) =
        S.X₂.endomorphism.hom (S.f.hom.hom x) := by
    intro x
    have hx := congrArg (fun k : S.X₁.carrier ⟶ S.X₂.carrier => k x) S.f.comm
    simpa [ModuleCat.comp_apply] using hx
  have hcomm_g : ∀ x : S.X₂.carrier,
      S.g.hom.hom (S.X₂.endomorphism.hom x) =
        S.X₃.endomorphism.hom (S.g.hom.hom x) := by
    intro x
    have hx := congrArg (fun k : S.X₂.carrier ⟶ S.X₃.carrier => k x) S.g.comm
    simpa [ModuleCat.comp_apply] using hx
  let s₁ := stableCompositionSeries S.X₁
  let s₃ := stableCompositionSeries S.X₃
  let φ₁ := S.X₁.endomorphism.hom
  let φ₂ := S.X₂.endomorphism.hom
  let φ₃ := S.X₃.endomorphism.hom
  let mapStable (P : StableSubmodule φ₁) : StableSubmodule φ₂ :=
    { carrier := Submodule.map S.f.hom.hom P.carrier
      stable := by
        rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        refine ⟨φ₁ x, P.stable ⟨x, hx, rfl⟩, ?_⟩
        exact hcomm_f x }
  let comapStable (Q : StableSubmodule φ₃) : StableSubmodule φ₂ :=
    { carrier := Submodule.comap S.g.hom.hom Q.carrier
      stable := by
        rintro _ ⟨x, hx, rfl⟩
        change S.g.hom.hom (φ₂ x) ∈ Q.carrier
        change S.g.hom.hom x ∈ Q.carrier at hx
        rw [hcomm_g]
        exact Q.stable ⟨S.g.hom.hom x, hx, rfl⟩ }
  let mapRel :
      SetRel.Hom
        { (P, Q) : StableSubmodule φ₁ × StableSubmodule φ₁ | P.carrier < Q.carrier }
        { (P, Q) : StableSubmodule φ₂ × StableSubmodule φ₂ | P.carrier < Q.carrier } :=
    ⟨mapStable, by
      intro P Q hPQ
      change P.carrier < Q.carrier at hPQ
      apply Submodule.map_lt_map_of_le_of_sup_lt_sup hPQ.le
      rw [LinearMap.ker_eq_bot.mpr hdata.2.1]
      simpa only [sup_bot_eq] using hPQ⟩
  let comapRel :
      SetRel.Hom
        { (P, Q) : StableSubmodule φ₃ × StableSubmodule φ₃ | P.carrier < Q.carrier }
        { (P, Q) : StableSubmodule φ₂ × StableSubmodule φ₂ | P.carrier < Q.carrier } :=
    ⟨comapStable, by
      intro P Q hPQ
      change P.carrier < Q.carrier at hPQ
      exact Submodule.comap_strictMono_of_surjective hdata.2.2 hPQ⟩
  let p : StableSubmoduleSeries φ₂ := s₁.series.map mapRel
  let q : StableSubmoduleSeries φ₂ := s₃.series.map comapRel
  have stable_ext {P Q : StableSubmodule φ₂} (h : P.carrier = Q.carrier) : P = Q := by
    cases P
    cases Q
    cases h
    rfl
  have hjoin : p.last = q.head := by
    apply stable_ext
    simp only [p, q, RelSeries.last_map, RelSeries.head_map, mapRel, comapRel]
    change Submodule.map S.f.hom.hom s₁.series.last.carrier =
      Submodule.comap S.g.hom.hom s₃.series.head.carrier
    rw [s₁.last_eq_top, s₃.head_eq_bot]
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact (hdata.1 (S.f.hom.hom y)).2 ⟨y, rfl⟩
    · intro hx
      obtain ⟨y, hy⟩ := (hdata.1 x).1 hx
      exact ⟨y, Submodule.mem_top, hy⟩
  let r : StableSubmoduleSeries φ₂ := p.smash q hjoin
  have hr_head : r.head.carrier = ⊥ := by
    simp only [r, RelSeries.head_smash, RelSeries.head_map, mapRel]
    change Submodule.map S.f.hom.hom s₁.series.head.carrier = ⊥
    rw [s₁.head_eq_bot]
    simp
  have hr_last : r.last.carrier = ⊤ := by
    simp only [r, RelSeries.last_smash, RelSeries.last_map, comapRel]
    change Submodule.comap S.g.hom.hom s₃.series.last.carrier = ⊤
    rw [s₃.last_eq_top]
    simp
  let factor_map_iso (j : Fin s₁.series.length) :
      factorModule s₁.series j ≃ₗ[R] factorModule p j := by
    let fU : (s₁.series j.succ).carrier →ₗ[R] (p j.succ).carrier :=
      { toFun := fun x =>
          ⟨S.f.hom.hom x, by
            change S.f.hom.hom x ∈
              Submodule.map S.f.hom.hom (s₁.series j.succ).carrier
            exact ⟨x, x.property, rfl⟩⟩
        map_add' := by
          intro x y
          apply Subtype.ext
          simp
        map_smul' := by
          intro a x
          apply Subtype.ext
          simp }
    have hfU_inj : Function.Injective fU := by
      intro x y hxy
      apply Subtype.ext
      apply hdata.2.1
      exact congrArg Subtype.val hxy
    have hfU_surj : Function.Surjective fU := by
      intro z
      have hz : (z : S.X₂.carrier) ∈
          Submodule.map S.f.hom.hom (s₁.series j.succ).carrier := by
        change (z : S.X₂.carrier) ∈ (p j.succ).carrier
        exact z.property
      obtain ⟨x, hx, hzx⟩ := hz
      exact ⟨⟨x, hx⟩, Subtype.ext hzx⟩
    let fUe := LinearEquiv.ofBijective fU ⟨hfU_inj, hfU_surj⟩
    let L₁ : Submodule R (s₁.series j.succ).carrier :=
      Submodule.comap (s₁.series j.succ).carrier.subtype
        (s₁.series j.castSucc).carrier
    let L₂ : Submodule R (p j.succ).carrier :=
      Submodule.comap (p j.succ).carrier.subtype (p j.castSucc).carrier
    have hL : L₁.map fUe.toLinearMap = L₂ := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        change (S.f.hom.hom x : S.X₂.carrier) ∈
          Submodule.map S.f.hom.hom (s₁.series j.castSucc).carrier
        exact ⟨x, hx, rfl⟩
      · intro hz
        change (z : S.X₂.carrier) ∈
          Submodule.map S.f.hom.hom (s₁.series j.castSucc).carrier at hz
        obtain ⟨x, hx, hzx⟩ := z.property
        obtain ⟨y, hy, hyz⟩ := hz
        have hxy : x = y := hdata.2.1 (hzx.trans hyz.symm)
        refine ⟨⟨x, hx⟩, ?_, ?_⟩
        · change (x : S.X₁.carrier) ∈ (s₁.series j.castSucc).carrier
          simpa [hxy] using hy
        · apply Subtype.ext
          exact hzx
    exact Submodule.Quotient.equiv L₁ L₂ fUe hL
  let factor_comap_iso (j : Fin s₃.series.length) :
      factorModule q j ≃ₗ[R] factorModule s₃.series j := by
    let gU : (q j.succ).carrier →ₗ[R] (s₃.series j.succ).carrier :=
      { toFun := fun x =>
          ⟨S.g.hom.hom x, by
            change S.g.hom.hom x ∈ (s₃.series j.succ).carrier
            exact x.property⟩
        map_add' := by
          intro x y
          apply Subtype.ext
          simp
        map_smul' := by
          intro a x
          apply Subtype.ext
          simp }
    have hgU_surj : Function.Surjective gU := by
      intro y
      obtain ⟨x, hxy⟩ := hdata.2.2 (y : S.X₃.carrier)
      refine ⟨⟨x, ?_⟩, ?_⟩
      · change S.g.hom.hom x ∈ (s₃.series j.succ).carrier
        simpa [hxy] using y.property
      · apply Subtype.ext
        exact hxy
    let L₂ : Submodule R (q j.succ).carrier :=
      Submodule.comap (q j.succ).carrier.subtype (q j.castSucc).carrier
    let L₃ : Submodule R (s₃.series j.succ).carrier :=
      Submodule.comap (s₃.series j.succ).carrier.subtype
        (s₃.series j.castSucc).carrier
    have hL : L₂ ≤ L₃.comap gU := by
      intro x hx
      change S.g.hom.hom x ∈ (s₃.series j.castSucc).carrier
      change S.g.hom.hom x ∈ (s₃.series j.castSucc).carrier at hx
      exact hx
    let gQ := L₂.mapQ L₃ gU hL
    have hgQ_inj : Function.Injective gQ := by
      intro a b hab
      obtain ⟨x, rfl⟩ := L₂.mkQ_surjective a
      obtain ⟨y, rfl⟩ := L₂.mkQ_surjective b
      apply (Submodule.Quotient.eq L₂).2
      apply (Submodule.Quotient.eq L₃).1 at hab
      change S.g.hom.hom (x - y) ∈ (s₃.series j.castSucc).carrier
      simpa [L₃, gU] using hab
    have hgQ_surj : Function.Surjective gQ := by
      intro z
      obtain ⟨y, rfl⟩ := L₃.mkQ_surjective z
      obtain ⟨x, hxy⟩ := hdata.2.2 (y : S.X₃.carrier)
      let x' : (q j.succ).carrier := ⟨x, by
        change S.g.hom.hom x ∈ (s₃.series j.succ).carrier
        simpa [hxy] using y.property⟩
      refine ⟨L₂.mkQ x', ?_⟩
      change L₃.mkQ (gU x') = L₃.mkQ y
      exact congrArg L₃.mkQ (Subtype.ext hxy)
    exact LinearEquiv.ofBijective gQ ⟨hgQ_inj, hgQ_surj⟩
  have factor_map_comm (j : Fin s₁.series.length) (x : factorModule s₁.series j) :
      factor_map_iso j (factorEnd s₁.series j x) =
        factorEnd p (Fin.cast (by simp [p]) j) (factor_map_iso j x) := by
    refine Submodule.Quotient.induction_on _ x ?_
    intro x
    change factor_map_iso j (factorEnd s₁.series j (Submodule.Quotient.mk x)) =
      factorEnd p (Fin.cast (by simp [p]) j)
        (factor_map_iso j (Submodule.Quotient.mk x))
    simp [factor_map_iso, factorEnd, Submodule.Quotient.equiv_apply,
      Submodule.mapQ_apply]
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    exact hcomm_f x
  have factor_comap_comm (j : Fin s₃.series.length)
      (x : factorModule q j) :
      factor_comap_iso j (factorEnd q (Fin.cast (by simp [q]) j) x) =
        factorEnd s₃.series j (factor_comap_iso j x) := by
    refine Submodule.Quotient.induction_on _ x ?_
    intro x
    change factor_comap_iso j
        (factorEnd q (Fin.cast (by simp [q]) j) (Submodule.Quotient.mk x)) =
      factorEnd s₃.series j (factor_comap_iso j (Submodule.Quotient.mk x))
    simp [factor_comap_iso, factorEnd, Submodule.Quotient.equiv_apply,
      Submodule.mapQ_apply]
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    exact hcomm_g x
  let factor_smash_left (j : Fin p.length) :
      factorModule (p.smash q hjoin)
          (Fin.cast (by simp [p, q]) (j.castAdd q.length)) ≃ₗ[R] factorModule p j := by
    let i : Fin (p.smash q hjoin).length :=
      Fin.cast (by simp [p, q]) (j.castAdd q.length)
    change factorModule (p.smash q hjoin) i ≃ₗ[R] factorModule p j
    have hi_succ_idx : i.succ = (j.castAdd q.length).succ := by
      apply Fin.ext
      rfl
    have hi_castSucc_idx : i.castSucc = (j.castAdd q.length).castSucc := by
      apply Fin.ext
      rfl
    have hi_succ : (p.smash q hjoin) i.succ = p j.succ := by
      rw [hi_succ_idx]
      exact RelSeries.smash_succ_castAdd hjoin j
    have hi_castSucc : (p.smash q hjoin) i.castSucc = p j.castSucc := by
      rw [hi_castSucc_idx]
      exact RelSeries.smash_castAdd hjoin j
    have hcar_succ :
        ((p.smash q hjoin) i.succ).carrier = (p j.succ).carrier :=
      congrArg StableSubmodule.carrier hi_succ
    have hcar_castSucc :
        ((p.smash q hjoin) i.castSucc).carrier = (p j.castSucc).carrier :=
      congrArg StableSubmodule.carrier hi_castSucc
    let eU : ((p.smash q hjoin) i.succ).carrier ≃ₗ[R] (p j.succ).carrier :=
      LinearEquiv.ofEq _ _ hcar_succ
    let L := Submodule.comap ((p.smash q hjoin) i.succ).carrier.subtype
      ((p.smash q hjoin) i.castSucc).carrier
    let L' := Submodule.comap (p j.succ).carrier.subtype (p j.castSucc).carrier
    have hL : L.map eU.toLinearMap = L' := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        change (eU y : S.X₂.carrier) ∈ (p j.castSucc).carrier
        change (y : S.X₂.carrier) ∈ ((p.smash q hjoin) i.castSucc).carrier at hy
        have hy' : (y : S.X₂.carrier) ∈ (p j.castSucc).carrier := by
          rw [← hcar_castSucc]
          exact hy
        simpa [eU] using hy'
      · intro hx
        change (x : S.X₂.carrier) ∈ (p j.castSucc).carrier at hx
        let y : ((p.smash q hjoin) i.succ).carrier :=
          ⟨x, by
            change (x : S.X₂.carrier) ∈ ((p.smash q hjoin) i.succ).carrier
            rw [hcar_succ]
            exact x.property⟩
        refine ⟨y, ?_, ?_⟩
        · change (y : S.X₂.carrier) ∈ ((p.smash q hjoin) i.castSucc).carrier
          rw [hcar_castSucc]
          exact hx
        · apply Subtype.ext
          rfl
    simpa only [factorModule, L, L'] using
      (Submodule.Quotient.equiv L L' eU hL)
  let factor_smash_right (j : Fin q.length) :
      factorModule (p.smash q hjoin)
          (Fin.cast (by simp [p, q]) (j.natAdd p.length)) ≃ₗ[R] factorModule q j := by
    let i : Fin (p.smash q hjoin).length :=
      Fin.cast (by simp [p, q]) (j.natAdd p.length)
    change factorModule (p.smash q hjoin) i ≃ₗ[R] factorModule q j
    have hi_succ_idx : i.succ = (j.natAdd p.length).succ := by
      apply Fin.ext
      rfl
    have hi_castSucc_idx : i.castSucc = (j.natAdd p.length).castSucc := by
      apply Fin.ext
      rfl
    have hi_succ : (p.smash q hjoin) i.succ = q j.succ := by
      rw [hi_succ_idx]
      exact RelSeries.smash_succ_natAdd hjoin j
    have hi_castSucc : (p.smash q hjoin) i.castSucc = q j.castSucc := by
      rw [hi_castSucc_idx]
      exact RelSeries.smash_natAdd hjoin j
    have hcar_succ :
        ((p.smash q hjoin) i.succ).carrier = (q j.succ).carrier :=
      congrArg StableSubmodule.carrier hi_succ
    have hcar_castSucc :
        ((p.smash q hjoin) i.castSucc).carrier = (q j.castSucc).carrier :=
      congrArg StableSubmodule.carrier hi_castSucc
    let eU : ((p.smash q hjoin) i.succ).carrier ≃ₗ[R] (q j.succ).carrier :=
      LinearEquiv.ofEq _ _ hcar_succ
    let L := Submodule.comap ((p.smash q hjoin) i.succ).carrier.subtype
      ((p.smash q hjoin) i.castSucc).carrier
    let L' := Submodule.comap (q j.succ).carrier.subtype (q j.castSucc).carrier
    have hL : L.map eU.toLinearMap = L' := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        change (eU y : S.X₂.carrier) ∈ (q j.castSucc).carrier
        change (y : S.X₂.carrier) ∈ ((p.smash q hjoin) i.castSucc).carrier at hy
        have hy' : (y : S.X₂.carrier) ∈ (q j.castSucc).carrier := by
          rw [← hcar_castSucc]
          exact hy
        simpa [eU] using hy'
      · intro hx
        change (x : S.X₂.carrier) ∈ (q j.castSucc).carrier at hx
        let y : ((p.smash q hjoin) i.succ).carrier :=
          ⟨x, by
            change (x : S.X₂.carrier) ∈ ((p.smash q hjoin) i.succ).carrier
            rw [hcar_succ]
            exact x.property⟩
        refine ⟨y, ?_, ?_⟩
        · change (y : S.X₂.carrier) ∈ ((p.smash q hjoin) i.castSucc).carrier
          rw [hcar_castSucc]
          exact hx
        · apply Subtype.ext
          rfl
    simpa only [factorModule, L, L'] using
      (Submodule.Quotient.equiv L L' eU hL)
  have factor_smash_left_comm (j : Fin p.length)
      (x : factorModule (p.smash q hjoin)
        (Fin.cast (by simp [p, q]) (j.castAdd q.length))) :
      factor_smash_left j (factorEnd (p.smash q hjoin)
          (Fin.cast (by simp [p, q]) (j.castAdd q.length)) x) =
        factorEnd p j (factor_smash_left j x) := by
    refine Submodule.Quotient.induction_on _ x ?_
    intro x
    simp [factor_smash_left, factorEnd, Submodule.Quotient.equiv_apply,
      Submodule.mapQ_apply]
    all_goals
      congr 1 <;> apply Subtype.ext <;> rfl
  have factor_smash_right_comm (j : Fin q.length)
      (x : factorModule (p.smash q hjoin)
        (Fin.cast (by simp [p, q]) (j.natAdd p.length))) :
      factor_smash_right j (factorEnd (p.smash q hjoin)
          (Fin.cast (by simp [p, q]) (j.natAdd p.length)) x) =
        factorEnd q j (factor_smash_right j x) := by
    refine Submodule.Quotient.induction_on _ x ?_
    intro x
    simp [factor_smash_right, factorEnd, Submodule.Quotient.equiv_apply,
      Submodule.mapQ_apply]
    all_goals
      congr 1 <;> apply Subtype.ext <;> rfl
  let pIndex (j : Fin s₁.series.length) : Fin p.length :=
    Fin.cast (by simp [p]) j
  let qIndex (j : Fin s₃.series.length) : Fin q.length :=
    Fin.cast (by simp [q]) j
  let leftIndex (j : Fin s₁.series.length) : Fin (p.smash q hjoin).length :=
    Fin.cast (by rfl) ((pIndex j).castAdd q.length)
  let rightIndex (j : Fin s₃.series.length) : Fin (p.smash q hjoin).length :=
    Fin.cast (by rfl) ((qIndex j).natAdd p.length)
  let leftEquiv (j : Fin s₁.series.length) :
      factorModule s₁.series j ≃ₗ[R]
        factorModule (p.smash q hjoin) (leftIndex j) := by
    exact (factor_map_iso j).trans (factor_smash_left (pIndex j)).symm
  have left_comm (j : Fin s₁.series.length)
      (x : factorModule s₁.series j) :
      leftEquiv j (factorEnd s₁.series j x) =
        factorEnd (p.smash q hjoin) (leftIndex j) (leftEquiv j x) := by
    let jp := pIndex j
    let e₂ := factor_smash_left jp
    have he₂ (y : factorModule p jp) :
        e₂.symm (factorEnd p jp y) =
          factorEnd (p.smash q hjoin) (leftIndex j) (e₂.symm y) := by
      apply e₂.injective
      calc
        e₂ (e₂.symm (factorEnd p jp y)) = factorEnd p jp y :=
          e₂.apply_symm_apply _
        _ = e₂ (factorEnd (p.smash q hjoin) (leftIndex j) (e₂.symm y)) := by
          symm
          simpa [e₂, leftIndex, jp, pIndex] using
            factor_smash_left_comm jp (e₂.symm y)
    change e₂.symm (factor_map_iso j (factorEnd s₁.series j x)) =
      factorEnd (p.smash q hjoin) (leftIndex j)
        (e₂.symm (factor_map_iso j x))
    have hm := factor_map_comm j x
    have h1 := congrArg e₂.symm (by simpa [jp, pIndex] using hm)
    exact h1.trans (he₂ (factor_map_iso j x))
  let rightEquiv (j : Fin s₃.series.length) :
      factorModule (p.smash q hjoin) (rightIndex j) ≃ₗ[R]
        factorModule s₃.series j := by
    exact (factor_smash_right (qIndex j)).trans (factor_comap_iso j)
  have right_comm (j : Fin s₃.series.length)
      (x : factorModule (p.smash q hjoin) (rightIndex j)) :
      rightEquiv j (factorEnd (p.smash q hjoin) (rightIndex j) x) =
        factorEnd s₃.series j (rightEquiv j x) := by
    let e₁ := factor_smash_right (qIndex j)
    let e₂ := factor_comap_iso j
    change e₂ (e₁ (factorEnd (p.smash q hjoin) (rightIndex j) x)) =
      factorEnd s₃.series j (e₂ (e₁ x))
    rw [factor_smash_right_comm]
    exact factor_comap_comm j (e₁ x)
  let leftData (j : Fin s₁.series.length) :
      SimplePairData R (factorModule (p.smash q hjoin) (leftIndex j))
        (factorEnd (p.smash q hjoin) (leftIndex j)) := by
    exact simplePairData
      ((S.X₂.finite_length.of_injective
        (Submodule.injective_subtype _)).of_surjective
      (Submodule.mkQ_surjective _))
      (factorEnd (p.smash q hjoin) (leftIndex j))
      (isSimplePair_transport (s₁.simple_factor j).simple (leftEquiv j)
        (left_comm j))
  let rightData (j : Fin s₃.series.length) :
      SimplePairData R (factorModule (p.smash q hjoin) (rightIndex j))
        (factorEnd (p.smash q hjoin) (rightIndex j)) := by
    have he_inv (y : factorModule s₃.series j) :
        (rightEquiv j).symm (factorEnd s₃.series j y) =
          factorEnd (p.smash q hjoin) (rightIndex j) ((rightEquiv j).symm y) := by
      apply (rightEquiv j).injective
      rw [(rightEquiv j).apply_symm_apply]
      symm
      simpa only [LinearEquiv.apply_symm_apply] using right_comm j ((rightEquiv j).symm y)
    exact simplePairData
      ((S.X₂.finite_length.of_injective
        (Submodule.injective_subtype _)).of_surjective
      (Submodule.mkQ_surjective _))
      (factorEnd (p.smash q hjoin) (rightIndex j))
      (isSimplePair_transport (s₃.simple_factor j).simple (rightEquiv j).symm he_inv)
  let s1Index (j : Fin p.length) : Fin s₁.series.length :=
    Fin.cast (by simp [p]) j
  let s3Index (j : Fin q.length) : Fin s₃.series.length :=
    Fin.cast (by simp [q]) j
  have leftIndex_raw (j : Fin p.length) :
      leftIndex (s1Index j) = Fin.castAdd q.length j := by
    apply Fin.ext
    rfl
  have rightIndex_raw (j : Fin q.length) :
      rightIndex (s3Index j) = Fin.natAdd p.length j := by
    apply Fin.ext
    rfl
  let simpleFactor₂ : ∀ i : Fin (p.length + q.length),
      SimplePairData R (factorModule (p.smash q hjoin) i)
        (factorEnd (p.smash q hjoin) i) :=
    fun i =>
      Fin.addCases
        (fun j => (leftIndex_raw j) ▸ leftData (s1Index j))
        (fun j => (rightIndex_raw j) ▸ rightData (s3Index j)) i
  let s₂ : StableCompositionSeries S.X₂ :=
    { series := p.smash q hjoin
      head_eq_bot := by simpa [r] using hr_head
      last_eq_top := by simpa [r] using hr_last
      simple_factor := simpleFactor₂ }
  have hleft_char (j : Fin s₁.series.length) :
      simpleCharacteristicPolynomial (s₁.simple_factor j) =
        simpleCharacteristicPolynomial (leftData j) := by
    exact simpleCharacteristicPolynomial_iso (s₁.simple_factor j) (leftData j)
      (leftEquiv j) (left_comm j)
  have hright_char (j : Fin s₃.series.length) :
      simpleCharacteristicPolynomial (rightData j) =
        simpleCharacteristicPolynomial (s₃.simple_factor j) := by
    exact simpleCharacteristicPolynomial_iso (rightData j) (s₃.simple_factor j)
      (rightEquiv j) (right_comm j)
  rw [characteristicPolynomial_eq_stableCompositionSeries_product S.X₂ s₂,
    characteristicPolynomial_eq_stableCompositionSeries_product S.X₁ s₁,
    characteristicPolynomial_eq_stableCompositionSeries_product S.X₃ s₃]
  change (∏ i : Fin (p.length + q.length),
      simpleCharacteristicPolynomial (s₂.simple_factor i)) =
    (∏ i : Fin s₁.series.length,
      simpleCharacteristicPolynomial (s₁.simple_factor i)) *
      ∏ i : Fin s₃.series.length,
        simpleCharacteristicPolynomial (s₃.simple_factor i)
  rw [Fin.prod_univ_add]
  congr 1
  · apply Fintype.prod_congr
    intro j
    have hsj : s1Index j = j := by
      apply Fin.ext
      rfl
    have hsource :
        simpleCharacteristicPolynomial (s₁.simple_factor (s1Index j)) =
          simpleCharacteristicPolynomial (s₁.simple_factor j) := by
      cases hsj
      rfl
    have hchar :
        simpleCharacteristicPolynomial (leftData (s1Index j)) =
          simpleCharacteristicPolynomial (s₁.simple_factor j) := by
      calc
        simpleCharacteristicPolynomial (leftData (s1Index j)) =
            simpleCharacteristicPolynomial (s₁.simple_factor (s1Index j)) :=
          (hleft_char (s1Index j)).symm
        _ = simpleCharacteristicPolynomial (s₁.simple_factor j) := hsource
    have hsf : s₂.simple_factor (j.castAdd q.length) =
        (leftIndex_raw j) ▸ leftData (s1Index j) := by
      simp only [s₂, simpleFactor₂, Fin.addCases_left]
    have htransport :
        simpleCharacteristicPolynomial ((leftIndex_raw j) ▸ leftData (s1Index j)) =
          simpleCharacteristicPolynomial (leftData (s1Index j)) := by
      cases leftIndex_raw j
      rfl
    rw [hsf]
    exact htransport.trans hchar
  · apply Fintype.prod_congr
    intro j
    have hsj : s3Index j = j := by
      apply Fin.ext
      rfl
    have hsource :
        simpleCharacteristicPolynomial (s₃.simple_factor (s3Index j)) =
          simpleCharacteristicPolynomial (s₃.simple_factor j) := by
      cases hsj
      rfl
    have hchar :
        simpleCharacteristicPolynomial (rightData (s3Index j)) =
          simpleCharacteristicPolynomial (s₃.simple_factor j) := by
      calc
        simpleCharacteristicPolynomial (rightData (s3Index j)) =
            simpleCharacteristicPolynomial (s₃.simple_factor (s3Index j)) :=
          hright_char (s3Index j)
        _ = simpleCharacteristicPolynomial (s₃.simple_factor j) := hsource
    have hsf : s₂.simple_factor (j.natAdd p.length) =
        (rightIndex_raw j) ▸ rightData (s3Index j) := by
      simp only [s₂, simpleFactor₂, Fin.addCases_right]
    have htransport :
        simpleCharacteristicPolynomial ((rightIndex_raw j) ▸ rightData (s3Index j)) =
          simpleCharacteristicPolynomial (rightData (s3Index j)) := by
      cases rightIndex_raw j
      rfl
    rw [hsf]
    exact htransport.trans hchar

/-- The three identities of the source lemma collected in one interface. -/
theorem lemma_ses
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (FiniteLengthEndomorphism.{u, v} R)}
    (hS : S.ShortExact) :
    determinant S.X₂ = determinant S.X₁ * determinant S.X₃ ∧
      trace S.X₂ = trace S.X₁ + trace S.X₃ ∧
        characteristicPolynomial S.X₂ =
          characteristicPolynomial S.X₁ * characteristicPolynomial S.X₃ := by
  exact ⟨lemma_ses_det hS, lemma_ses_trace hS, lemma_ses_characteristicPolynomial hS⟩

end
