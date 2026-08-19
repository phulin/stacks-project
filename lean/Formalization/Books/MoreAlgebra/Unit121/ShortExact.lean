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
  sorry

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
