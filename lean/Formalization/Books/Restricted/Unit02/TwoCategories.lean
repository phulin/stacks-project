import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets
import Formalization.Books.Algebra.Unit98.TakingLimits
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Data.PNat.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Algebraization of Formal Spaces, Chapter 2: Two categories

This file formalizes the two categories used in the chapter.  The category
`AdicSystemCategory` is modeled as a full subcategory of structured arrows
from the canonical system of quotients `A / I^n`; this records both the
`A_n`-algebra structures and the compatibility of all transition maps.  The
category `CompleteAlgebraCategory` is the full subcategory of `CommAlgCat A`
cut out by adic completeness and finite type of the residue algebra.

The source section is statement-heavy.  The construction-level definitions
below use Mathlib's canonical quotient, tensor-product, and completion APIs;
the longer algebraic and categorical proofs are left as theorem interfaces
for the proof stage.
-/

namespace Formalization.Books.Restricted.Unit02

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21
open scoped TensorProduct

universe u v

noncomputable section

/-! ## The canonical quotient systems -/

/-- The `n`th quotient in the `J`-adic inverse system, indexed by `ℕ+`. -/
abbrev powerQuotient (R : Type u) [CommRing R] (J : Ideal R) (n : ℕ+) : Type u :=
  R ⧸ J ^ (n : ℕ)

/-- The transition map `R / J^m → R / J^n` for `n ≤ m`. -/
def powerQuotientTransition {R : Type u} [CommRing R] (J : Ideal R)
    {m n : ℕ+} (h : n ≤ m) :
    powerQuotient R J m →+* powerQuotient R J n :=
  Ideal.Quotient.factorPow J ((PNat.coe_le_coe n m).mpr h)

/- The identities and composition law for the quotient transitions are the
   ordinary quotient-factor identities in Mathlib. -/
theorem powerQuotientTransition_id {R : Type u} [CommRing R] (J : Ideal R)
    (n : ℕ+) :
    powerQuotientTransition J (m := n) (n := n) le_rfl = RingHom.id _ := by
  ext x
  simp [powerQuotientTransition]

theorem powerQuotientTransition_comp {R : Type u} [CommRing R] (J : Ideal R)
    {m n k : ℕ+} (hnm : n ≤ m) (hkn : k ≤ n) :
    (powerQuotientTransition J hkn).comp (powerQuotientTransition J hnm) =
      powerQuotientTransition J (hkn.trans hnm) := by
  simp only [powerQuotientTransition]
  exact Ideal.Quotient.factor_comp _ _

/-- The canonical inverse system of powers of an ideal. -/
def powerQuotientSystem {R : Type u} [CommRing R] (J : Ideal R) :
    InverseSystem ℕ+ CommRingCat.{u} where
  obj i := CommRingCat.of (powerQuotient R J i.unop)
  map f :=
    CommRingCat.ofHom
      (powerQuotientTransition J (CategoryTheory.leOfHom f.unop))
  map_id := by
    intro i
    apply CommRingCat.hom_ext
    exact powerQuotientTransition_id J i.unop
  map_comp := by
    intro i j k f g
    apply CommRingCat.hom_ext
    simpa using
      (powerQuotientTransition_comp J
        (CategoryTheory.leOfHom f.unop) (CategoryTheory.leOfHom g.unop)).symm

/-! ## The category `𝓒` of compatible finite-type systems -/

/-- The book's notation `A_n = A / I^n`. -/
abbrev adicQuotient (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ+) : Type u :=
  powerQuotient A I n

/-- The canonical inverse system `(A_n)`. -/
abbrev adicQuotientSystem (A : Type u) [CommRing A] (I : Ideal A) :
    InverseSystem ℕ+ CommRingCat.{u} :=
  powerQuotientSystem I

/-- Mathlib's canonical `I`-adic completion of `A`. -/
abbrev adicCompletionRing (A : Type u) [CommRing A] (I : Ideal A) : Type u :=
  AdicCompletion I A

/-- The source's display `A^ = lim A_n`, with the positive-index quotient system. -/
theorem adicCompletion_is_powerQuotientLimit {A : Type u} [CommRing A]
    (I : Ideal A) :
    Nonempty
      (adicCompletionRing A I ≃+*
        ((limit (adicQuotientSystem A I) : CommRingCat.{u}) : Type u)) := by
  let F := adicQuotientSystem A I
  have heval : ∀ {m n : ℕ} (hmn : m ≤ n)
      (x : AdicCompletion I A),
      Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
        AdicCompletion.evalₐ I m x := by
    intro m n hmn x
    let hn : (I ^ n • ⊤ : Submodule A A) ≤ I ^ n :=
      le_of_eq (Ideal.mul_top _)
    let hm : (I ^ m • ⊤ : Submodule A A) ≤ I ^ m :=
      le_of_eq (Ideal.mul_top _)
    have hfac : ∀ (y : A ⧸ (I ^ n • ⊤ : Submodule A A)),
        Ideal.Quotient.factorPow I hmn (Submodule.factor hn y) =
          Submodule.factor hm (AdicCompletion.transitionMap I A hmn y) := by
      intro y
      induction y using Quotient.inductionOn' with
      | _ a => rfl
    rw [← AdicCompletion.factor_eval_eq_evalₐ I x hn]
    rw [← AdicCompletion.factor_eval_eq_evalₐ I x hm]
    rw [hfac]
    exact congrArg (fun z => Submodule.factor hm z)
      (AdicCompletion.transitionMap_comp_eval_apply I A hmn x)
  let c : Cone F :=
    { pt := CommRingCat.of (AdicCompletion I A)
      π :=
        { app := fun i =>
            CommRingCat.ofHom
              (AdicCompletion.evalₐ I (i.unop : ℕ)).toRingHom
          naturality := by
            intro i j f
            apply CommRingCat.hom_ext
            apply RingHom.ext
            intro x
            have hmn : (j.unop : ℕ) ≤ (i.unop : ℕ) := by
              exact (PNat.coe_le_coe _ _).mpr (CategoryTheory.le_of_op_hom f)
            change AdicCompletion.evalₐ I (j.unop : ℕ) x =
              powerQuotientTransition I (CategoryTheory.le_of_op_hom f)
                (AdicCompletion.evalₐ I (i.unop : ℕ) x)
            simpa [powerQuotientTransition] using (heval hmn x).symm }
      }
  let φ : AdicCompletion I A →+*
      ((limit F : CommRingCat) : Type u) :=
    (limit.lift F c).hom
  let pos : ℕ → ℕ+ := fun n => ⟨n + 1, Nat.succ_pos n⟩
  let g : ∀ n : ℕ,
      ((limit F : CommRingCat) : Type u) →+* A ⧸ I ^ n := fun n =>
    (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp
      (limit.π F (Opposite.op (pos n))).hom
  have hg : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow I hmn).comp (g n) = g m := by
    intro m n hmn
    apply RingHom.ext
    intro x
    have hpos : pos m ≤ pos n := by
      change m + 1 ≤ n + 1
      exact Nat.succ_le_succ hmn
    have hlim := limit.w F (CategoryTheory.homOfLE hpos).op
    have hlim' := congrArg (fun q => q.hom x) hlim
    change
      Ideal.Quotient.factorPow I hmn
          (Ideal.Quotient.factorPow I (Nat.le_succ n)
            ((limit.π F (Opposite.op (pos n))).hom x)) =
        Ideal.Quotient.factorPow I (Nat.le_succ m)
          ((limit.π F (Opposite.op (pos m))).hom x)
    change powerQuotientTransition I hpos
        ((limit.π F (Opposite.op (pos n))).hom x) =
      (limit.π F (Opposite.op (pos m))).hom x at hlim'
    rw [← hlim']
    obtain ⟨a, ha⟩ :=
      Ideal.Quotient.mk_surjective
        ((limit.π F (Opposite.op (pos n))).hom x)
    rw [← ha]
    rfl
  let ψ : ((limit F : CommRingCat) : Type u) →+* AdicCompletion I A :=
    AdicCompletion.liftRingHom I g hg
  have hφ : ∀ (n : ℕ) (x : AdicCompletion I A),
      (limit.π F (Opposite.op (pos n))).hom (φ x) =
        AdicCompletion.evalₐ I (n + 1) x := by
    intro n x
    have hπ := limit.lift_π c (Opposite.op (pos n))
    have hπ' := congrArg (fun q => q.hom x) hπ
    change (limit.π F (Opposite.op (pos n))).hom (φ x) =
      AdicCompletion.evalₐ I (n + 1) x
    exact hπ'
  have hψφ : ψ.comp φ = RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ I n (ψ (φ x)) =
      AdicCompletion.evalₐ I n x
    rw [AdicCompletion.evalₐ_liftRingHom]
    change Ideal.Quotient.factorPow I (Nat.le_succ n)
        ((limit.π F (Opposite.op (pos n))).hom (φ x)) =
      AdicCompletion.evalₐ I n x
    rw [hφ n x]
    exact heval (Nat.le_succ n) x
  have hφψ : φ.comp ψ = RingHom.id _ := by
    have hD : IsLimit ((forget CommRingCat).mapCone (limit.cone F)) :=
      isLimitOfPreserves (forget CommRingCat) (limit.isLimit F)
    apply RingHom.ext
    intro x
    apply (Types.isLimitEquivSections hD).injective
    ext i
    cases i with
    | op i =>
      have hstep : i ≤ pos (i : ℕ) := by
        change (i : ℕ) ≤ (i : ℕ) + 1
        exact Nat.le_succ _
      have hπ := congrArg (fun q => q.hom (ψ x))
        (limit.lift_π c (Opposite.op i))
      have hlim := limit.w F (CategoryTheory.homOfLE hstep).op
      have hlim' := congrArg (fun q => q.hom x) hlim
      change
        (limit.π F (Opposite.op i)).hom (φ (ψ x)) =
          AdicCompletion.evalₐ I (i : ℕ) (ψ x) at hπ
      change
        (limit.π F (Opposite.op i)).hom (φ (ψ x)) =
          (limit.π F (Opposite.op i)).hom x
      rw [hπ]
      rw [AdicCompletion.evalₐ_liftRingHom]
      change
        Ideal.Quotient.factorPow I (Nat.le_succ (i : ℕ))
            ((limit.π F (Opposite.op (pos (i : ℕ)))).hom x) =
          (limit.π F (Opposite.op i)).hom x
      change
        powerQuotientTransition I hstep
            ((limit.π F (Opposite.op (pos (i : ℕ)))).hom x) =
          (limit.π F (Opposite.op i)).hom x
      exact hlim'
  refine ⟨RingEquiv.ofBijective φ ?_⟩
  refine ⟨?_, ?_⟩
  · intro x y hxy
    calc
      x = (ψ.comp φ) x := by rw [hψφ]; rfl
      _ = (ψ.comp φ) y := congrArg ψ hxy
      _ = y := by rw [hψφ]; rfl
  · intro y
    exact ⟨ψ y, by
      simpa only [RingHom.comp_apply, RingHom.id_apply] using
        congrArg (fun q => q y) hφψ⟩

/-- The image of `I^n` in `A_{n+1}`. -/
def adicStagePowerIdeal {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+) :
    Ideal (adicQuotient A I (n + 1)) :=
  Ideal.map
    (Ideal.Quotient.mk (I ^ ((n + 1 : ℕ+) : ℕ)))
    (I ^ (n : ℕ))

/-- A system equipped with its compatible maps from the quotient system `(A_n)`. -/
abbrev AdicSystemArrow (A : Type u) [CommRing A] (I : Ideal A) :=
  StructuredArrow (adicQuotientSystem A I)
    (𝟭 (InverseSystem ℕ+ CommRingCat.{u}))

/-- The `I^n`-part of the `(n+1)`st stage of a structured system. -/
def adicSystemPowerIdeal {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemArrow A I) (n : ℕ+) :
    Ideal (X.right.obj (Opposite.op (n + 1))) :=
  Ideal.map
    (X.hom.app (Opposite.op (n + 1))).hom
    (adicStagePowerIdeal I n)

/-- The transition map of a structured inverse system. -/
def adicSystemTransition {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemArrow A I) {m n : ℕ+} (h : n ≤ m) :
    X.right.obj (Opposite.op m) →+* X.right.obj (Opposite.op n) :=
  (X.right.map (CategoryTheory.homOfLE h).op).hom

/-- The quotient presentation of one successive transition in `𝓒`. -/
structure AdicSystemStep {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemArrow A I) (n : ℕ+) where
  equivalence :
    (X.right.obj (Opposite.op (n + 1)) ⧸ adicSystemPowerIdeal I X n) ≃+*
      X.right.obj (Opposite.op n)
  transition_eq :
    equivalence.toRingHom.comp
        (Ideal.Quotient.mk (adicSystemPowerIdeal I X n)) =
      adicSystemTransition I X (PNat.lt_add_right n 1).le

/-- The object property defining the chapter's category `𝓒`. -/
def AdicSystemProperty {A : Type u} [CommRing A] (I : Ideal A) :
    ObjectProperty (AdicSystemArrow A I) :=
  fun X =>
    (∀ n : ℕ+, RingHom.FiniteType
      (X.hom.app (Opposite.op n)).hom) ∧
      (∀ n : ℕ+, Nonempty (AdicSystemStep I X n))

/-- The category `𝓒` of compatible finite-type inverse systems. -/
abbrev AdicSystemCategory (A : Type u) [CommRing A] (I : Ideal A) :=
  (AdicSystemProperty I).FullSubcategory

/-- The stagewise `A_n`-algebra structure carried by a structured system. -/
abbrev adicSystemStageAlgebra {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemArrow A I) (n : ℕ+) :
    Algebra (adicQuotient A I n) (X.right.obj (Opposite.op n)) :=
  (X.hom.app (Opposite.op n)).hom.toAlgebra

/-- The scalar map from `A_{n+1}` to the lower stage, through `A_n`. -/
def adicSystemLowerStageScalarMap {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemArrow A I) (n : ℕ+) :
    adicQuotient A I (n + 1) →+*
      X.right.obj (Opposite.op n) :=
  (X.hom.app (Opposite.op n)).hom.comp
    (powerQuotientTransition I
      (m := n + 1) (n := n) (PNat.lt_add_right n 1).le)

/-- The transition in `𝓒` is an `A_{n+1}`-algebra map. -/
theorem adicSystemTransition_is_algebraMap {A : Type u} [CommRing A]
    (I : Ideal A) (X : AdicSystemArrow A I) (n : ℕ+) :
    (adicSystemTransition I X (PNat.lt_add_right n 1).le).comp
        (X.hom.app (Opposite.op (n + 1))).hom =
      adicSystemLowerStageScalarMap I X n := by
  apply RingHom.ext
  intro x
  have h := congrArg
    (fun q : ((adicQuotientSystem A I).obj (Opposite.op (n + 1)) ⟶
      X.right.obj (Opposite.op n)) => q.hom x)
    (X.hom.naturality (CategoryTheory.homOfLE (PNat.lt_add_right n 1).le).op)
  change
    (X.hom.app (Opposite.op n)).hom
        (powerQuotientTransition I
          (m := n + 1) (n := n) (PNat.lt_add_right n 1).le x) =
      (X.right.map (CategoryTheory.homOfLE (PNat.lt_add_right n 1).le).op).hom
        ((X.hom.app (Opposite.op (n + 1))).hom x) at h
  change
    (X.right.map (CategoryTheory.homOfLE (PNat.lt_add_right n 1).le).op).hom
        ((X.hom.app (Opposite.op (n + 1))).hom x) =
      (X.hom.app (Opposite.op n)).hom
        (powerQuotientTransition I
          (m := n + 1) (n := n) (PNat.lt_add_right n 1).le x)
  exact h.symm

/-! ## The category `𝓒'` of complete algebras -/

/-- The extension `IB` of `I` to an `A`-algebra `B`. -/
def cprimeIdeal {A : Type u} [CommRing A] (I : Ideal A) (B : CommAlgCat A) :
    Ideal B :=
  Ideal.map (algebraMap A B) I

/-- The residue algebra `B / IB` over `A / I`. -/
def cprimeResidueAlgebra {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) : CommAlgCat (A ⧸ I) := by
  letI : Algebra (A ⧸ I) (B ⧸ cprimeIdeal I B) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := A) (A := B) (p := I) (P := cprimeIdeal I B)
      Ideal.le_comap_map
  exact CommAlgCat.of (A ⧸ I) (B ⧸ cprimeIdeal I B)

/-- The object property defining `𝓒'`. -/
def CompleteAlgebraProperty {A : Type u} [CommRing A] (I : Ideal A) :
    ObjectProperty (CommAlgCat.{u} A) :=
  fun B =>
    IsAdicComplete (cprimeIdeal I B) B ∧
      Algebra.FiniteType (A ⧸ I) (cprimeResidueAlgebra I B)

/-- The category `𝓒'` of `I`-adically complete algebras with finite residue algebra. -/
abbrev CompleteAlgebraCategory (A : Type u) [CommRing A] (I : Ideal A) :=
  (CompleteAlgebraProperty I).FullSubcategory

/-- Put the canonical `A`-algebra structure on a quotient of an `A`-algebra. -/
def quotientCommAlg {A : Type u} [CommRing A] (B : CommAlgCat A) (J : Ideal B) :
    CommAlgCat A := by
  letI : Algebra A (B ⧸ J) :=
    ((Ideal.Quotient.mk J).comp (algebraMap A B)).toAlgebra
  exact CommAlgCat.of A (B ⧸ J)

/-! ## The quotient functor `𝓒' → 𝓒` -/

/-- The `n`th stage of the quotient system attached to an algebra. -/
abbrev cprimeQuotientStage {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) (n : ℕ+) : Type u :=
  B ⧸ (cprimeIdeal I B) ^ (n : ℕ)

/-- The transition map in the quotient system attached to `B`. -/
abbrev cprimeQuotientTransition {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) {m n : ℕ+} (h : n ≤ m) :
    cprimeQuotientStage I B m →+* cprimeQuotientStage I B n :=
  powerQuotientTransition (cprimeIdeal I B) h

/-- The quotient inverse system attached to an `A`-algebra. -/
abbrev cprimeQuotientSystem {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) : InverseSystem ℕ+ CommRingCat.{u} :=
  powerQuotientSystem (cprimeIdeal I B)

/-- The ideal inclusion needed for the map `A/I^n → B/(IB)^n`. -/
theorem cprimeBaseIdeal_le {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) (n : ℕ+) :
    I ^ (n : ℕ) ≤
      ((cprimeIdeal I B) ^ (n : ℕ)).comap (algebraMap A B) := by
  rw [cprimeIdeal, ← Ideal.map_pow]
  exact Ideal.le_comap_map

/-- The stagewise quotient map from `A_n` to `B/(IB)^n`. -/
def cprimeBaseComponent {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) (n : ℕ+) :
    adicQuotient A I n →+* cprimeQuotientStage I B n :=
  Ideal.quotientMap
    ((cprimeIdeal I B) ^ (n : ℕ)) (algebraMap A B)
    (cprimeBaseIdeal_le I B n)

private theorem finiteType_of_finiteType_quotient
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (K : Ideal R) (hK : IsNilpotent K) :
    RingHom.FiniteType
        (Ideal.quotientMap (K.map f) f Ideal.le_comap_map) →
      RingHom.FiniteType f := by
  let : Algebra R S := f.toAlgebra
  let J : Ideal S := K.map f
  let π : S →ₐ[R] (S ⧸ J) := Ideal.Quotient.mkₐ R J
  let : Algebra (R ⧸ K) (S ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  intro h
  have h' : RingHom.FiniteType
      (algebraMap (R ⧸ K) (S ⧸ J)) := by
    have he : algebraMap (R ⧸ K) (S ⧸ J) =
        Ideal.quotientMap J f Ideal.le_comap_map := by
      apply RingHom.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    exact he ▸ h
  change Algebra.FiniteType R S
  let q : R →+* (S ⧸ J) := (Ideal.Quotient.mk J).comp f
  have hq : RingHom.FiniteType q := by
    have hmk : RingHom.FiniteType (Ideal.Quotient.mk K) :=
      RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective
    have hcomp : RingHom.FiniteType
        ((algebraMap (R ⧸ K) (S ⧸ J)).comp (Ideal.Quotient.mk K)) :=
      h'.comp hmk
    convert hcomp using 1
    ext r
    rfl
  let : Algebra R (S ⧸ J) := q.toAlgebra
  have hq' : Algebra.FiniteType R (S ⧸ J) := hq
  obtain ⟨s, hs⟩ := hq'.out
  classical
  let lift : (S ⧸ J) → S := fun x => (Ideal.Quotient.mk_surjective x).choose
  have hlift (x : S ⧸ J) : Ideal.Quotient.mk J (lift x) = x :=
    (Ideal.Quotient.mk_surjective x).choose_spec
  let T : Set S := lift '' (s : Set (S ⧸ J))
  let C : Subalgebra R S := Algebra.adjoin R T
  have hT : T.Finite := s.finite_toSet.image lift
  have hπ : Function.Surjective (π.comp C.val) := by
    apply (AlgHom.range_eq_top _).mp
    apply Algebra.eq_top_iff.mpr
    intro x
    have hle : Algebra.adjoin R (s : Set (S ⧸ J)) ≤ (π.comp C.val).range := by
      apply Algebra.adjoin_le
      intro y hy
      exact ⟨⟨lift y, Algebra.subset_adjoin ⟨y, hy, rfl⟩⟩, by
        simpa [π] using hlift y⟩
    exact hle (by rw [hs]; trivial)
  have hbase : ∀ x : S, ∃ a : C, x - a.1 ∈ J := by
    intro x
    obtain ⟨a, ha⟩ := hπ (π x)
    refine ⟨a, ?_⟩
    have hz : π (x - a.1) = 0 := by
      simpa [map_sub, Function.comp_apply] using sub_eq_zero.mpr ha.symm
    simpa [π] using Ideal.Quotient.eq_zero_iff_mem.mp hz
  obtain ⟨N, hKN⟩ := hK
  have hN : J ^ N = ⊥ := by
    change (Ideal.map f K) ^ N = ⊥
    rw [← Ideal.map_pow, hKN]
    simp
  have hdecomp (n : ℕ) (x : S) (hx : x ∈ J ^ n) :
      ∃ a : C, a.1 ∈ J ^ n ∧ x - a.1 ∈ J ^ (n + 1) := by
    have hx' : x ∈ Ideal.map f (K ^ n) := by
      simpa [J, Ideal.map_pow] using hx
    rw [Ideal.map] at hx'
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx'
    · rintro y ⟨r, hr, rfl⟩
      let a : C := ⟨f r, C.algebraMap_mem r⟩
      refine ⟨a, ?_, ?_⟩
      · rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hr
      · simp [a]
    · exact ⟨0, Ideal.zero_mem _, by simp⟩
    · rintro x y _ _ ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
      refine ⟨a + b, add_mem ha hb, ?_⟩
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using add_mem hxa hyb
    · rintro c x _ ⟨a, ha, hxa⟩
      obtain ⟨b, hb⟩ := hbase c
      refine ⟨b * a, ?_, ?_⟩
      · exact Ideal.mul_mem_left _ _ ha
      · have h₁ : c * (x - a.1) ∈ J ^ (n + 1) :=
          Ideal.mul_mem_left _ _ hxa
        have h₂ : (c - b.1) * a.1 ∈ J ^ (n + 1) := by
          have hmul := Ideal.mul_mem_mul hb ha
          simpa [pow_succ', mul_comm] using hmul
        have hres := add_mem h₁ h₂
        change c * x - b.1 * a.1 ∈ J ^ (n + 1)
        convert hres using 1
        ring
  have hgen : ∀ n : ℕ, ∀ x : S, ∃ a : C, x - a.1 ∈ J ^ n := by
    intro n
    induction n with
    | zero => intro x; exact ⟨0, by simp⟩
    | succ n ih =>
      intro x
      obtain ⟨a, ha⟩ := ih x
      obtain ⟨b, hb, hxb⟩ := hdecomp n (x - a.1) ha
      refine ⟨a + b, ?_⟩
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxb
  have hCtop : C = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨a, ha⟩ := hgen N x
    have hzero : x - a.1 = 0 := by simpa [hN] using ha
    have hxa : x = a.1 := sub_eq_zero.mp hzero
    rw [hxa]
    exact a.property
  have hCfinite : Algebra.FiniteType R C := Algebra.FiniteType.adjoin_of_finite hT
  apply hCfinite.of_surjective C.val
  intro x
  have hx : x ∈ C := by rw [hCtop]; trivial
  exact ⟨⟨x, hx⟩, rfl⟩

private theorem finiteType_cprime_stage_quotient {A : Type u} [CommRing A]
    (I : Ideal A) (B : CommAlgCat A) (n : ℕ+)
    (hres : RingHom.FiniteType
      (Ideal.quotientMap (cprimeIdeal I B) (algebraMap A B)
        Ideal.le_comap_map)) :
    RingHom.FiniteType
      (Ideal.quotientMap
        ((Ideal.map (Ideal.Quotient.mk (I ^ (n : ℕ))) I).map
          (cprimeBaseComponent I B n))
        (cprimeBaseComponent I B n) Ideal.le_comap_map) := by
  let p : Ideal A := I ^ (n : ℕ)
  let J : Ideal B := (cprimeIdeal I B) ^ (n : ℕ)
  let K : Ideal (A ⧸ p) := Ideal.map (Ideal.Quotient.mk p) I
  let f := cprimeBaseComponent I B n
  let : Algebra (A ⧸ p) (B ⧸ J) := f.toAlgebra
  let L : Ideal (B ⧸ J) := (cprimeIdeal I B).map (Ideal.Quotient.mk J)
  have hL : K.map (algebraMap (A ⧸ p) (B ⧸ J)) = L := by
    dsimp [L, K]
    rw [Ideal.map_map]
    change Ideal.map ((Ideal.Quotient.mk J).comp (algebraMap A B)) I = _
    rw [cprimeIdeal, ← Ideal.map_map]
  let : Algebra (A ⧸ I) (B ⧸ cprimeIdeal I B) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have hres' : RingHom.FiniteType
      (algebraMap (A ⧸ I) (B ⧸ cprimeIdeal I B)) := by
    have he : algebraMap (A ⧸ I) (B ⧸ cprimeIdeal I B) =
        Ideal.quotientMap (cprimeIdeal I B) (algebraMap A B)
          Ideal.le_comap_map := by
      apply RingHom.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    exact he ▸ hres
  let : Algebra A (B ⧸ J) :=
    ((Ideal.Quotient.mk J).comp (algebraMap A B)).toAlgebra
  let q : (A ⧸ p) →+* ((B ⧸ J) ⧸ L) :=
    (Ideal.Quotient.mk L).comp f
  let : Algebra (A ⧸ p) ((B ⧸ J) ⧸ L) :=
    q.toAlgebra
  have hIL : I ≤ L.comap (algebraMap A (B ⧸ J)) := by
    intro x hx
    change algebraMap A (B ⧸ J) x ∈ L
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx)
  let : Algebra (A ⧸ I) ((B ⧸ J) ⧸ L) :=
    Ideal.Quotient.algebraQuotientOfLEComap hIL
  have hKq : ∀ x : A ⧸ p, x ∈ K → q x = 0 := by
    intro x hx
    change (Ideal.Quotient.mk L) (f x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [← hL]
    exact Ideal.mem_map_of_mem _ hx
  let q' : ((A ⧸ p) ⧸ K) →+* ((B ⧸ J) ⧸ L) :=
    Ideal.Quotient.lift K q hKq
  let : Algebra ((A ⧸ p) ⧸ K) ((B ⧸ J) ⧸ L) := q'.toAlgebra
  have hJ : J ≤ cprimeIdeal I B := by
    dsimp [J]
    exact Ideal.pow_le_self (by exact_mod_cast n.ne_zero)
  let e : ((B ⧸ J) ⧸ L) ≃+* (B ⧸ cprimeIdeal I B) :=
    DoubleQuot.quotQuotEquivQuotOfLE hJ
  have hAIT' : RingHom.FiniteType
      (e.symm.toRingHom.comp
        (algebraMap (A ⧸ I) (B ⧸ cprimeIdeal I B))) :=
    hres'.comp_surjective e.symm.surjective
  have hAIT : RingHom.FiniteType
      (algebraMap (A ⧸ I) ((B ⧸ J) ⧸ L)) := by
    convert hAIT' using 1
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  let hq : A ⧸ I →+* (A ⧸ p) ⧸ K :=
    Ideal.quotientMap K (Ideal.Quotient.mk p) Ideal.le_comap_map
  have hcomp : RingHom.FiniteType
      (algebraMap (A ⧸ I) ((B ⧸ J) ⧸ L)) := hAIT
  have heq :
      (algebraMap ((A ⧸ p) ⧸ K) ((B ⧸ J) ⧸ L)).comp hq =
        algebraMap (A ⧸ I) ((B ⧸ J) ⧸ L) := by
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change q' (Ideal.Quotient.mk K (Ideal.Quotient.mk p x)) =
      Ideal.Quotient.mk L (algebraMap A (B ⧸ J) x)
    rw [Ideal.Quotient.lift_mk]
    change q (Ideal.Quotient.mk p x) =
      Ideal.Quotient.mk L (algebraMap A (B ⧸ J) x)
    dsimp [q, f, cprimeBaseComponent]
    rw [Ideal.quotientMap_mk]
    change Ideal.Quotient.mk L
        (Ideal.Quotient.mk J (algebraMap A B x)) =
      Ideal.Quotient.mk L (Ideal.Quotient.mk J (algebraMap A B x))
    rfl
  have hq' : RingHom.FiniteType
      (algebraMap ((A ⧸ p) ⧸ K) ((B ⧸ J) ⧸ L)) :=
    RingHom.FiniteType.of_comp_finiteType (heq ▸ hcomp)
  have hLf : K.map f = L := by
    change K.map (algebraMap (A ⧸ p) (B ⧸ J)) = L
    exact hL
  let eLf : ((B ⧸ J) ⧸ L) ≃+*
      ((B ⧸ J) ⧸ K.map f) := Ideal.quotEquivOfEq hLf.symm
  have hq'' : RingHom.FiniteType
      (eLf.toRingHom.comp
        (algebraMap ((A ⧸ p) ⧸ K) ((B ⧸ J) ⧸ L))) :=
    hq'.comp_surjective eLf.surjective
  have heq' :
      eLf.toRingHom.comp
          (algebraMap ((A ⧸ p) ⧸ K) ((B ⧸ J) ⧸ L)) =
        Ideal.quotientMap (K.map f) f Ideal.le_comap_map := by
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change eLf (q' (Ideal.Quotient.mk K x)) =
      Ideal.Quotient.mk (K.map f) (f x)
    rw [Ideal.Quotient.lift_mk]
    change eLf (q x) = Ideal.Quotient.mk (K.map f) (f x)
    dsimp [eLf, q]
  exact heq' ▸ hq''

/-- The finite-type assertion used to show that the quotient functor lands in `𝓒`. -/
theorem cprimeBaseComponent_finiteType {A : Type u} [CommRing A]
    (I : Ideal A) (B : CompleteAlgebraCategory A I) (n : ℕ+) :
    RingHom.FiniteType (cprimeBaseComponent I B.obj n) := by
  let p : Ideal A := I ^ (n : ℕ)
  let K : Ideal (A ⧸ p) := Ideal.map (Ideal.Quotient.mk p) I
  let f := cprimeBaseComponent I B.obj n
  have hK : IsNilpotent K := by
    refine ⟨n, ?_⟩
    dsimp [K]
    rw [← Ideal.map_pow]
    simp [p]
  change RingHom.FiniteType f
  apply finiteType_of_finiteType_quotient f K hK
  let : Algebra (A ⧸ I) (B.obj ⧸ cprimeIdeal I B.obj) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have hres : RingHom.FiniteType
      (Ideal.quotientMap (cprimeIdeal I B.obj) (algebraMap A B.obj)
        Ideal.le_comap_map) := by
    change RingHom.FiniteType (algebraMap (A ⧸ I)
      (B.obj ⧸ cprimeIdeal I B.obj))
    rw [RingHom.finiteType_algebraMap]
    exact B.property.2
  simpa [p, K, f] using finiteType_cprime_stage_quotient I B.obj n hres

theorem cprimeBaseMap_naturality {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) {i j : ℕ+ᵒᵖ} (f : i ⟶ j) :
    (adicQuotientSystem A I).map f ≫
        CommRingCat.ofHom (cprimeBaseComponent I B j.unop) =
      CommRingCat.ofHom (cprimeBaseComponent I B i.unop) ≫
        (cprimeQuotientSystem I B).map f := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The natural transformation from `(A_n)` to the quotient system of `B`. -/
def cprimeBaseMap {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) :
    adicQuotientSystem A I ⟶ cprimeQuotientSystem I B where
  app n := CommRingCat.ofHom (cprimeBaseComponent I B n.unop)
  naturality := by
    intro i j f
    exact cprimeBaseMap_naturality I B f

/-- The structured arrow underlying the quotient system of `B`. -/
def cprimeQuotientArrow {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) : AdicSystemArrow A I :=
  StructuredArrow.mk (cprimeBaseMap I B)

/-- The quotient system of a complete algebra satisfies the defining system conditions. -/
theorem cprimeQuotientArrow_property {A : Type u} [CommRing A] (I : Ideal A)
    (B : CompleteAlgebraCategory A I) :
    AdicSystemProperty I (cprimeQuotientArrow I B.obj) := by
  change
    (∀ n : ℕ+, RingHom.FiniteType (cprimeBaseComponent I B.obj n)) ∧
      (∀ n : ℕ+, Nonempty (AdicSystemStep I (cprimeQuotientArrow I B.obj) n))
  constructor
  · intro n
    exact cprimeBaseComponent_finiteType I B n
  · intro n
    refine ⟨{ equivalence := ?_, transition_eq := ?_ }⟩
    · change
        (B.obj ⧸ (cprimeIdeal I B.obj) ^ ((n + 1 : ℕ+) : ℕ)) ⧸
            Ideal.map (cprimeBaseComponent I B.obj (n + 1))
              (adicStagePowerIdeal I n) ≃+*
          B.obj ⧸ (cprimeIdeal I B.obj) ^ (n : ℕ)
      let p : Ideal A := I ^ ((n + 1 : ℕ+) : ℕ)
      let J : Ideal B.obj :=
        (cprimeIdeal I B.obj) ^ ((n + 1 : ℕ+) : ℕ)
      let K : Ideal (A ⧸ p) :=
        Ideal.map (Ideal.Quotient.mk p) (I ^ (n : ℕ))
      let f := cprimeBaseComponent I B.obj (n + 1)
      let L : Ideal (B.obj ⧸ J) :=
        ((cprimeIdeal I B.obj) ^ (n : ℕ)).map (Ideal.Quotient.mk J)
      have hL : K.map f = L := by
        dsimp [K, L]
        rw [Ideal.map_map]
        change Ideal.map ((Ideal.Quotient.mk J).comp (algebraMap A B.obj))
          (I ^ (n : ℕ)) = _
        rw [cprimeIdeal, ← Ideal.map_pow, ← Ideal.map_map]
      have hJ : J ≤ (cprimeIdeal I B.obj) ^ (n : ℕ) := by
        dsimp [J]
        exact Ideal.pow_le_pow_right (I := cprimeIdeal I B.obj) (Nat.le_succ (n : ℕ))
      let e0 : ((B.obj ⧸ J) ⧸ L) ≃+*
          (B.obj ⧸ (cprimeIdeal I B.obj) ^ (n : ℕ)) :=
        DoubleQuot.quotQuotEquivQuotOfLE hJ
      have e : (cprimeQuotientStage I B.obj (n + 1) ⧸ L) ≃+*
          (B.obj ⧸ (cprimeIdeal I B.obj) ^ (n : ℕ)) := by
        simpa [cprimeQuotientStage, J] using e0
      let q : (cprimeQuotientStage I B.obj (n + 1) ⧸ K.map f) ≃+*
          (cprimeQuotientStage I B.obj (n + 1) ⧸ L) :=
        Ideal.quotEquivOfEq hL
      change (B.obj ⧸ J) ⧸ K.map f ≃+*
        B.obj ⧸ (cprimeIdeal I B.obj) ^ (n : ℕ)
      exact q.trans e
    · apply RingHom.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl

/-- The object part of the canonical functor `𝓒' → 𝓒`. -/
def completeAlgebraSystemObject {A : Type u} [CommRing A] (I : Ideal A)
    (B : CompleteAlgebraCategory A I) : AdicSystemCategory A I :=
  ⟨cprimeQuotientArrow I B.obj, cprimeQuotientArrow_property I B⟩

/-- The ideal inclusion needed for the quotient map induced by an algebra map. -/
theorem cprimeQuotientMapIdeal_le {A : Type u} [CommRing A] (I : Ideal A)
    {B C : CommAlgCat A} (f : B ⟶ C) (n : ℕ+) :
    (cprimeIdeal I B) ^ (n : ℕ) ≤
      ((cprimeIdeal I C) ^ (n : ℕ)).comap f.hom.toRingHom := by
  have hf : f.hom.toRingHom.comp (algebraMap A B) = algebraMap A C := by
    ext x
    exact f.hom.commutes x
  have hmap :
      Ideal.map f.hom.toRingHom ((cprimeIdeal I B) ^ (n : ℕ)) =
        (cprimeIdeal I C) ^ (n : ℕ) := by
    simp only [cprimeIdeal]
    rw [← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map, hf]
  rw [← hmap]
  exact Ideal.le_comap_map

/-- The map on quotient stages induced by an `A`-algebra map. -/
def cprimeQuotientMapComponent {A : Type u} [CommRing A] (I : Ideal A)
    {B C : CommAlgCat A} (f : B ⟶ C) (n : ℕ+) :
    cprimeQuotientStage I B n →+* cprimeQuotientStage I C n :=
  Ideal.quotientMap
    ((cprimeIdeal I C) ^ (n : ℕ)) f.hom.toRingHom
    (cprimeQuotientMapIdeal_le I f n)

theorem cprimeQuotientMap_naturality {A : Type u} [CommRing A] (I : Ideal A)
    {B C : CommAlgCat A} (f : B ⟶ C) {i j : ℕ+ᵒᵖ} (g : i ⟶ j) :
    (cprimeQuotientSystem I B).map g ≫
        CommRingCat.ofHom (cprimeQuotientMapComponent I f j.unop) =
      CommRingCat.ofHom (cprimeQuotientMapComponent I f i.unop) ≫
        (cprimeQuotientSystem I C).map g := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The natural transformation induced on quotient systems by an algebra map. -/
def cprimeQuotientMap {A : Type u} [CommRing A] (I : Ideal A)
    {B C : CommAlgCat A} (f : B ⟶ C) :
    cprimeQuotientSystem I B ⟶ cprimeQuotientSystem I C where
  app n := CommRingCat.ofHom (cprimeQuotientMapComponent I f n.unop)
  naturality := by
    intro i j g
    exact cprimeQuotientMap_naturality I f g

theorem cprimeBaseMap_map_compatibility {A : Type u} [CommRing A]
    (I : Ideal A) {B C : CommAlgCat A} (f : B ⟶ C) :
    cprimeBaseMap I B ≫ cprimeQuotientMap I f = cprimeBaseMap I C := by
  apply CategoryTheory.NatTrans.ext
  funext n
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change cprimeQuotientMapComponent I f n.unop
      (cprimeBaseComponent I B n.unop x) =
    cprimeBaseComponent I C n.unop x
  dsimp [cprimeQuotientMapComponent, cprimeBaseComponent]
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk _) (f.hom.commutes x)

/-- The morphism part of the canonical functor `𝓒' → 𝓒`. -/
def completeAlgebraSystemMap {A : Type u} [CommRing A] (I : Ideal A)
    {B C : CompleteAlgebraCategory A I} (f : B ⟶ C) :
    completeAlgebraSystemObject I B ⟶ completeAlgebraSystemObject I C :=
  ObjectProperty.homMk <|
    StructuredArrow.homMk (cprimeQuotientMap I f.hom)
      (cprimeBaseMap_map_compatibility I f.hom)

theorem completeAlgebraSystemMap_id {A : Type u} [CommRing A]
    (I : Ideal A) (B : CompleteAlgebraCategory A I) :
    completeAlgebraSystemMap I (𝟙 B) = 𝟙 (completeAlgebraSystemObject I B) := by
  apply ObjectProperty.hom_ext
  apply StructuredArrow.hom_ext
  apply CategoryTheory.NatTrans.ext
  funext n
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change cprimeQuotientMapComponent I (𝟙 B.obj) n.unop x = x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem completeAlgebraSystemMap_comp {A : Type u} [CommRing A]
    (I : Ideal A) {B C D : CompleteAlgebraCategory A I}
    (f : B ⟶ C) (g : C ⟶ D) :
    completeAlgebraSystemMap I (f ≫ g) =
      completeAlgebraSystemMap I f ≫ completeAlgebraSystemMap I g := by
  have hfg : (f ≫ g).hom.hom =
      g.hom.hom.comp f.hom.hom := rfl
  apply ObjectProperty.hom_ext
  apply StructuredArrow.hom_ext
  change cprimeQuotientMap I (f ≫ g).hom =
    cprimeQuotientMap I f.hom ≫ cprimeQuotientMap I g.hom
  apply CategoryTheory.NatTrans.ext
  funext n
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change cprimeQuotientMapComponent I (f ≫ g).hom n.unop x =
      cprimeQuotientMapComponent I g.hom n.unop
      (cprimeQuotientMapComponent I f.hom n.unop x)
  dsimp [cprimeQuotientMapComponent]
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The canonical functor `𝓒' → 𝓒`, sending `B` to `(B/I^nB)_n`. -/
def completeAlgebraSystemFunctor {A : Type u} [CommRing A] (I : Ideal A) :
    CompleteAlgebraCategory A I ⥤ AdicSystemCategory A I where
  obj := completeAlgebraSystemObject I
  map f := completeAlgebraSystemMap I f
  map_id := completeAlgebraSystemMap_id I
  map_comp := completeAlgebraSystemMap_comp I

/-! ## The inverse limit and the quasi-inverse statement -/

/-- The underlying inverse-limit ring of an object of `𝓒`. -/
abbrev adicSystemLimitRing {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemCategory A I) : CommRingCat.{u} :=
  limit X.obj.right

/-- The complete algebra supplied by the inverse limit construction. -/
structure AdicSystemLimitData {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemCategory A I) where
  algebra : CommAlgCat A
  comparison : (algebra : Type u) ≃+* adicSystemLimitRing I X
  comparison_stage : ∀ (a : A) (n : ℕ+),
    (limit.π X.obj.right (Opposite.op n)).hom
        (comparison (algebraMap A algebra a)) =
      (X.obj.hom.app (Opposite.op n)).hom
        (Ideal.Quotient.mk (I ^ (n : ℕ)) a)
  complete : IsAdicComplete (cprimeIdeal I algebra) algebra
  residue_finite : Algebra.FiniteType (A ⧸ I) (cprimeResidueAlgebra I algebra)

private theorem adicSystemPowerIdeal_eq_map
    {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemArrow A I) (n : ℕ+) :
    let q : A →+* ((adicQuotientSystem A I).obj
        (Opposite.op (n + 1)) : Type u) :=
      Ideal.Quotient.mk (I ^ ((n + 1 : ℕ+) : ℕ))
    adicSystemPowerIdeal I X n =
      Ideal.map (X.hom.app (Opposite.op (n + 1))).hom
        (Ideal.map q (I ^ (n : ℕ))) := by
  dsimp
  rfl

private theorem ideal_restrictScalars_eq_smul_top_of_map
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal A) (K : Ideal B)
    (hK : K = Ideal.map (algebraMap A B) J) :
    (K.restrictScalars A : Submodule A B) = J • (⊤ : Submodule A B) := by
  rw [hK, Ideal.smul_top_eq_map]

private theorem isAdicComplete_of_linearEquiv
    {A M N : Type u} [CommRing A] (I : Ideal A)
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (hM : IsAdicComplete I M) :
    IsAdicComplete I N := by
  refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
  · refine ⟨?_⟩
    intro x hx
    apply e.symm.injective
    have hzero : e.symm x = 0 := by
      apply hM.toIsHausdorff.haus (e.symm x)
      intro n
      have h := SModEq.map (hx n) e.symm.toLinearMap
      have hm :
          Submodule.map e.symm.toLinearMap
              (I ^ n • (⊤ : Submodule A N)) ≤
            I ^ n • (⊤ : Submodule A M) := by
        rw [Submodule.map_smul'', Submodule.map_top]
        exact smul_mono_right _ le_top
      exact SModEq.mono hm (by simpa using h)
    simpa using hzero
  · refine ⟨?_⟩
    intro f hf
    let g : ℕ → M := fun n => e.symm (f n)
    have hg : ∀ {m n}, m ≤ n →
        g m ≡ g n [SMOD (I ^ m • (⊤ : Submodule A M))] := by
      intro m n hmn
      have h := SModEq.map (hf hmn) e.symm.toLinearMap
      have hm :
          Submodule.map e.symm.toLinearMap
              (I ^ m • (⊤ : Submodule A N)) ≤
            I ^ m • (⊤ : Submodule A M) := by
        rw [Submodule.map_smul'', Submodule.map_top]
        exact smul_mono_right _ le_top
      exact SModEq.mono hm (by simpa [g] using h)
    obtain ⟨L, hL⟩ := hM.toIsPrecomplete.prec' g hg
    refine ⟨e L, ?_⟩
    intro n
    have h := SModEq.map (hL n) e.toLinearMap
    have hm :
        Submodule.map e.toLinearMap
            (I ^ n • (⊤ : Submodule A M)) ≤
          I ^ n • (⊤ : Submodule A N) := by
      rw [Submodule.map_smul'', Submodule.map_top]
      exact smul_mono_right _ le_top
    exact SModEq.mono hm (by simpa [g] using h)

private def adicSystemModuleSystem {A : Type u} [CommRing A]
    (I : Ideal A) (X : AdicSystemArrow A I) :
    Formalization.Books.Algebra.Unit87.NaturalInverseSystem A :=
  let aMap : ∀ n : ℕ+ᵒᵖ, A →+* (X.right.obj n) :=
    fun n => (X.hom.app n).hom.comp
      (Ideal.Quotient.mk (I ^ (n.unop : ℕ)))
  { obj := fun n =>
      letI : Algebra A (X.right.obj n) := (aMap n).toAlgebra
      ModuleCat.of A (X.right.obj n)
    map := fun {i j} f =>
      letI : Algebra A (X.right.obj i) := (aMap i).toAlgebra
      letI : Algebra A (X.right.obj j) := (aMap j).toAlgebra
      ModuleCat.ofHom
        { toFun := (X.right.map f).hom
          map_add' := by intro x y; simp
          map_smul' := by
            intro a x
            change (X.right.map f).hom (aMap i a * x) =
              aMap j a * (X.right.map f).hom x
            rw [map_mul]
            have h := congrArg
              (fun q => q.hom (Ideal.Quotient.mk (I ^ (i.unop : ℕ)) a))
              (X.hom.naturality f)
            change (X.hom.app j).hom
                (((adicQuotientSystem A I).map f).hom
                  (Ideal.Quotient.mk (I ^ (i.unop : ℕ)) a)) =
              (X.right.map f).hom
                ((X.hom.app i).hom
                  (Ideal.Quotient.mk (I ^ (i.unop : ℕ)) a)) at h
            have hs : (X.right.map f).hom (aMap i a) = aMap j a := by
              change (X.right.map f).hom
                  ((X.hom.app i).hom
                    (Ideal.Quotient.mk (I ^ (i.unop : ℕ)) a)) =
                (X.hom.app j).hom
                  (Ideal.Quotient.mk (I ^ (j.unop : ℕ)) a)
              calc
                _ = (X.hom.app j).hom
                    (((adicQuotientSystem A I).map f).hom
                      (Ideal.Quotient.mk (I ^ (i.unop : ℕ)) a)) := h.symm
                _ = _ := by rfl
            exact congrArg
              (fun z => z * (X.right.map f).hom x) hs }
    map_id := by
      intro i
      let : Algebra A (X.right.obj i) := (aMap i).toAlgebra
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp
    map_comp := by
      intro i j k f g
      let : Algebra A (X.right.obj i) := (aMap i).toAlgebra
      let : Algebra A (X.right.obj j) := (aMap j).toAlgebra
      let : Algebra A (X.right.obj k) := (aMap k).toAlgebra
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp }

private theorem adicSystemModuleSystem_isQuotient
    {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemArrow A I) (hX : AdicSystemProperty I X) :
    Formalization.Books.Algebra.Unit98.IsQuotientInverseSystem I
      (adicSystemModuleSystem I X) := by
  intro n
  rcases hX.2 n with ⟨s⟩
  let B := X.right.obj (Opposite.op (n + 1))
  let K : Ideal B := adicSystemPowerIdeal I X n
  let q : A →+* ((adicQuotientSystem A I).obj
      (Opposite.op (n + 1)) : Type u) :=
    Ideal.Quotient.mk (I ^ ((n + 1 : ℕ+) : ℕ))
  let : Algebra A B :=
    ((X.hom.app (Opposite.op (n + 1))).hom.comp q).toAlgebra
  let : Algebra A (X.right.obj (Opposite.op n)) :=
    ((X.hom.app (Opposite.op n)).hom.comp
      (Ideal.Quotient.mk (I ^ (n : ℕ)))).toAlgebra
  let P : Submodule A B := I ^ (n : ℕ) • (⊤ : Submodule A B)
  have hK' : K = Ideal.map (X.hom.app (Opposite.op (n + 1))).hom
      (Ideal.map q (I ^ (n : ℕ))) := by
    dsimp [K]
    change adicSystemPowerIdeal I X n =
      Ideal.map (X.hom.app (Opposite.op (n + 1))).hom
        (Ideal.map q (I ^ (n : ℕ)))
    exact adicSystemPowerIdeal_eq_map I X n
  have hK : K = Ideal.map (algebraMap A B) (I ^ (n : ℕ)) := by
    calc
      K = Ideal.map (X.hom.app (Opposite.op (n + 1))).hom
          (Ideal.map q (I ^ (n : ℕ))) := hK'
      _ = Ideal.map
          ((X.hom.app (Opposite.op (n + 1))).hom.comp q)
          (I ^ (n : ℕ)) := Ideal.map_map q
            (X.hom.app (Opposite.op (n + 1))).hom
      _ = Ideal.map (algebraMap A B) (I ^ (n : ℕ)) := by rfl
  have hP : P = (K.restrictScalars A : Submodule A B) := by
    exact (ideal_restrictScalars_eq_smul_top_of_map
      (I ^ (n : ℕ)) K hK).symm
  let e₁ :
      (B ⧸ P) ≃ₗ[A] (B ⧸ K) :=
    Submodule.quotEquivOfEq P (K.restrictScalars A) hP
  let e₂ :
    (B ⧸ K) ≃ₗ[A] X.right.obj (Opposite.op n) :=
      { toFun := s.equivalence
        invFun := s.equivalence.symm
        left_inv := s.equivalence.left_inv
        right_inv := s.equivalence.right_inv
        map_add' := s.equivalence.map_add
        map_smul' := by
          intro a x
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
          change s.equivalence
              (Ideal.Quotient.mk K (algebraMap A B a * x)) =
            algebraMap A (X.right.obj (Opposite.op n)) a *
              s.equivalence (Ideal.Quotient.mk K x)
          rw [map_mul]
          have hscalar :
              s.equivalence (Ideal.Quotient.mk K (algebraMap A B a)) =
                algebraMap A (X.right.obj (Opposite.op n)) a := by
            calc
              _ = (adicSystemTransition I X
                    (PNat.lt_add_right n 1).le)
                    (algebraMap A B a) := by
                exact congrArg (fun q => q (algebraMap A B a))
                  s.transition_eq
              _ = _ := by
                have h := congrArg
                  (fun q => q (Ideal.Quotient.mk
                    (I ^ ((n + 1 : ℕ+) : ℕ)) a))
                  (adicSystemTransition_is_algebraMap I X n)
                change (adicSystemTransition I X
                    (PNat.lt_add_right n 1).le)
                    ((X.hom.app (Opposite.op (n + 1))).hom
                      (Ideal.Quotient.mk
                        (I ^ ((n + 1 : ℕ+) : ℕ)) a)) =
                  (X.hom.app (Opposite.op n)).hom
                    (powerQuotientTransition I
                      (m := n + 1) (n := n)
                      (PNat.lt_add_right n 1).le
                      (Ideal.Quotient.mk
                        (I ^ ((n + 1 : ℕ+) : ℕ)) a)) at h
                convert h using 1
                · rfl
                · rfl
          rw [s.equivalence.map_mul, hscalar] }
  refine ⟨{ equivalence := (e₁.trans e₂).toModuleIso, transition_eq := ?_ }⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change B at x
  dsimp [e₁, e₂, B, K, P]
  change s.equivalence
      ((Submodule.quotEquivOfEq P (K.restrictScalars A) hP)
        (Submodule.Quotient.mk x)) =
    (X.right.map (CategoryTheory.homOfLE
      (PNat.lt_add_right n 1).le).op).hom x
  rw [Submodule.quotEquivOfEq_mk P (K.restrictScalars A) hP x]
  exact congrArg (fun z => z x) s.transition_eq

/-- The completeness lemma supplies an `A`-algebra structure on the limit. -/
theorem adicSystemLimitData_exists {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (X : AdicSystemCategory A I) :
    Nonempty (AdicSystemLimitData I X) := by
  let F := adicSystemModuleSystem I X.obj
  have hF := adicSystemModuleSystem_isQuotient I X.obj X.property
  have hlimit := Formalization.Books.Algebra.Unit98.limit_complete I hI F hF
  let c : Cone X.obj.right :=
    { pt := CommRingCat.of A
      π :=
        { app := fun i =>
            CommRingCat.ofHom
              ((X.obj.hom.app i).hom.comp
                (Ideal.Quotient.mk (I ^ (i.unop : ℕ))))
          naturality := by
            intro i j f
            apply CommRingCat.hom_ext
            apply RingHom.ext
            intro a
            have h := congrArg
              (fun q => q.hom
                (Ideal.Quotient.mk (I ^ (i.unop : ℕ)) a))
              (X.obj.hom.naturality f)
            change (X.obj.hom.app j).hom
                (((adicQuotientSystem A I).map f).hom
                  (Ideal.Quotient.mk (I ^ (i.unop : ℕ)) a)) =
              (X.obj.right.map f).hom
                ((X.obj.hom.app i).hom
                  (Ideal.Quotient.mk (I ^ (i.unop : ℕ)) a)) at h
            exact h } }
  let φ : A →+* ((limit X.obj.right : CommRingCat.{u}) : Type u) :=
    (limit.lift X.obj.right c).hom
  let : Algebra A ((limit X.obj.right : CommRingCat.{u}) : Type u) :=
    φ.toAlgebra
  have hFG :
      F ⋙ forget₂ (ModuleCat A) AddCommGrpCat =
        X.obj.right ⋙ forget₂ CommRingCat RingCat ⋙
          forget₂ RingCat AddCommGrpCat := by
    rfl
  let eStage :
      limit (F ⋙ forget₂ (ModuleCat A) AddCommGrpCat) ≅
        limit (X.obj.right ⋙ forget₂ CommRingCat RingCat ⋙
          forget₂ RingCat AddCommGrpCat) :=
    eqToIso (congrArg (fun G => limit G) hFG)
  let eAddIso :
      (forget₂ (ModuleCat A) AddCommGrpCat).obj
          (limit F) ≅
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj
          (limit X.obj.right) :=
    preservesLimitIso (forget₂ (ModuleCat A) AddCommGrpCat) F ≪≫
        eStage ≪≫
        (preservesLimitIso
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
          X.obj.right).symm
  let eAdd :
      ((limit F : ModuleCat A) : Type u) ≃+
        ((limit X.obj.right : CommRingCat.{u}) : Type u) :=
    CategoryTheory.Iso.addCommGroupIsoToAddEquiv eAddIso
  have hproj (y : ((limit F : ModuleCat A) : Type u))
      (n : ℕ+) :
      (limit.π X.obj.right (Opposite.op n)).hom (eAdd y) =
        (limit.π F (Opposite.op n)).hom y := by
    change (((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
      (limit.π X.obj.right (Opposite.op n))).hom (eAddIso.hom.hom y)) =
      ((forget₂ (ModuleCat A) AddCommGrpCat).map
        (limit.π F (Opposite.op n))).hom y
    dsimp [eAddIso]
    have hπ := preservesLimitIso_inv_π
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
      X.obj.right (Opposite.op n)
    have hπy := congrArg
      (fun q => q.hom
        (eStage.hom.hom
          ((preservesLimitIso (forget₂ (ModuleCat A) AddCommGrpCat) F).hom.hom y)))
      hπ
    have hπy' :
        ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          (limit.π X.obj.right (Opposite.op n))).hom
            ((preservesLimitIso
              (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
              X.obj.right).inv.hom
              (eStage.hom.hom
                ((preservesLimitIso
                  (forget₂ (ModuleCat A) AddCommGrpCat) F).hom.hom y))) =
          (limit.π
            (X.obj.right ⋙ forget₂ CommRingCat RingCat ⋙
              forget₂ RingCat AddCommGrpCat) (Opposite.op n)).hom
            (eStage.hom.hom
              ((preservesLimitIso
                (forget₂ (ModuleCat A) AddCommGrpCat) F).hom.hom y)) := by
      simpa only [ConcreteCategory.comp_apply] using hπy
    have hstageproj : HEq
        ((limit.π
            (F ⋙ forget₂ (ModuleCat A) AddCommGrpCat) (Opposite.op n)).hom
          (eStage.hom.hom
            ((preservesLimitIso (forget₂ (ModuleCat A) AddCommGrpCat) F).hom.hom y)))
        ((limit.π
            (X.obj.right ⋙ forget₂ CommRingCat RingCat ⋙
              forget₂ RingCat AddCommGrpCat) (Opposite.op n)).hom
          ((preservesLimitIso (forget₂ (ModuleCat A) AddCommGrpCat) F).hom.hom y)) := by
      dsimp [eStage]
      cases hFG
      rfl
    have hpfy := congrArg (fun q => q.hom y)
      (preservesLimitIso_hom_π
        (forget₂ (ModuleCat A) AddCommGrpCat) F (Opposite.op n))
    have hmap : HEq
        ((limit.π
            (X.obj.right ⋙ forget₂ CommRingCat RingCat ⋙
              forget₂ RingCat AddCommGrpCat) (Opposite.op n)).hom
          (eStage.hom.hom
            ((preservesLimitIso (forget₂ (ModuleCat A) AddCommGrpCat) F).hom.hom y)))
        (((forget₂ (ModuleCat A) AddCommGrpCat).map
          (limit.π F (Opposite.op n))).hom y) :=
      hstageproj.symm.trans (heq_of_eq hpfy)
    have hfull : HEq
        (((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          (limit.π X.obj.right (Opposite.op n))).hom
          ((preservesLimitIso
            (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
            X.obj.right).inv.hom
            (eStage.hom.hom
              ((preservesLimitIso
                (forget₂ (ModuleCat A) AddCommGrpCat) F).hom.hom y))))
        (((forget₂ (ModuleCat A) AddCommGrpCat).map
          (limit.π F (Opposite.op n))).hom y) := by
      exact (heq_of_eq hπy').trans hmap
    exact eq_of_heq hfull
  let eLin :
      ((limit F : ModuleCat A) : Type u) ≃ₗ[A]
        ((limit X.obj.right : CommRingCat.{u}) : Type u) :=
    { eAdd with
      map_smul' := by
        intro a y
        apply Concrete.limit_ext X.obj.right
        intro n
        change (limit.π X.obj.right n).hom (eAdd (a • y)) =
          (limit.π X.obj.right n).hom (φ a * eAdd y)
        rw [hproj (a • y) n.unop, map_mul]
        have hφn := congrArg (fun q => q.hom a)
          (limit.lift_π c n)
        change (limit.π X.obj.right n).hom (φ a) =
          (X.obj.hom.app n).hom
            (Ideal.Quotient.mk (I ^ (n.unop : ℕ)) a) at hφn
        rw [hφn, hproj y n.unop]
        change (limit.π F n).hom (a • y) =
          a • (limit.π F n).hom y
        rw [map_smul]
        }
  have hcomplete :
      IsAdicComplete I ((limit F : ModuleCat A) : Type u) :=
    hlimit.2
  have hcomplete' :
      IsAdicComplete I ((limit X.obj.right : CommRingCat.{u}) : Type u) :=
    isAdicComplete_of_linearEquiv I eLin hcomplete
  let B : CommAlgCat A :=
    CommAlgCat.of A ((limit X.obj.right : CommRingCat.{u}) : Type u)
  refine ⟨AdicSystemLimitData.mk B (RingEquiv.refl _) ?_ ?_ ?_⟩
  · intro a n
    change (limit.π X.obj.right (Opposite.op n)).hom (φ a) = _
    rw [← ConcreteCategory.comp_apply, limit.lift_π]
    rfl
  · change IsAdicComplete (Ideal.map (algebraMap A B) I) B
    exact (IsAdicComplete.map_algebraMap_iff
      (I := I) (M := ((limit X.obj.right : CommRingCat.{u}) : Type u))).mpr
      hcomplete'
  · let L : Type u := ((limit X.obj.right : CommRingCat.{u}) : Type u)
    let S : Type u := X.obj.right.obj (Opposite.op (1 : ℕ+))
    let J : Ideal L := cprimeIdeal I B
    let p : L →+* S := (limit.π X.obj.right (Opposite.op (1 : ℕ+))).hom
    let lp := Classical.choice (hlimit.1 (1 : ℕ+))
    have hp_surj : Function.Surjective p := by
      intro z
      obtain ⟨q, hq⟩ := lp.equivalence.surjective z
      obtain ⟨y, hy⟩ := Submodule.mkQ_surjective
        (I ^ (1 : ℕ) • (⊤ : Submodule A
          (Formalization.Books.Algebra.Unit87.inverseLimitModule F : Type u))) q
      refine ⟨eLin y, ?_⟩
      have hproj' := congrArg (fun q => q.hom y) lp.projection_eq
      change lp.equivalence
          ((I ^ (1 : ℕ) • (⊤ : Submodule A
            (Formalization.Books.Algebra.Unit87.inverseLimitModule F : Type u))).mkQ y) =
        (limit.π F (Opposite.op (1 : ℕ+))).hom y at hproj'
      have hpe : p (eLin y) =
          (limit.π F (Opposite.op (1 : ℕ+))).hom y := by
        change (limit.π X.obj.right (Opposite.op (1 : ℕ+))).hom
            (eAdd y) = _
        simpa using hproj y (1 : ℕ+)
      have hprojz := hproj'.symm.trans ((congrArg lp.equivalence hy).trans hq)
      rw [hpe]
      exact hprojz
    have hp_kernel : J ≤ RingHom.ker p := by
      dsimp [J, cprimeIdeal]
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change p (algebraMap A B a) = 0
      have hpa := congrArg (fun q => q.hom a)
        (limit.lift_π c (Opposite.op (1 : ℕ+)))
      change p (φ a) =
        (X.obj.hom.app (Opposite.op (1 : ℕ+))).hom
          (Ideal.Quotient.mk (I ^ (1 : ℕ)) a) at hpa
      rw [show algebraMap A B a = φ a by rfl, hpa]
      have ha0 : Ideal.Quotient.mk (I ^ (1 : ℕ)) a = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using ha)
      rw [ha0]
      change (X.obj.hom.app (Opposite.op (1 : ℕ+))).hom
          (0 : ((adicQuotientSystem A I).obj
            (Opposite.op (1 : ℕ+)) : Type u)) = 0
      exact (X.obj.hom.app (Opposite.op (1 : ℕ+))).hom.map_zero
    let qres : (L ⧸ J) →+* S := Ideal.Quotient.lift J p (by
      intro x hx
      exact hp_kernel hx)
    have qres_surj : Function.Surjective qres := by
      intro z
      obtain ⟨b, hb⟩ := hp_surj z
      refine ⟨Ideal.Quotient.mk J b, ?_⟩
      change p b = z
      exact hb
    have qres_inj : Function.Injective qres := by
      intro z₁ z₂ hz
      obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective z₁
      obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective z₂
      change p b₁ = p b₂ at hz
      have hp : p (b₁ - b₂) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact hz
      let y := eLin.symm (b₁ - b₂)
      have hpy : (limit.π F (Opposite.op (1 : ℕ+))).hom y = 0 := by
        rw [← hproj y 1]
        change p (eLin y) = 0
        rw [eLin.apply_symm_apply]
        exact hp
      have hproj' := congrArg (fun q => q.hom y) lp.projection_eq
      change lp.equivalence
          ((I ^ (1 : ℕ) • (⊤ : Submodule A
            (Formalization.Books.Algebra.Unit87.inverseLimitModule F : Type u))).mkQ y) =
        (limit.π F (Opposite.op (1 : ℕ+))).hom y at hproj'
      have hmk :
          (I ^ (1 : ℕ) • (⊤ : Submodule A
            (Formalization.Books.Algebra.Unit87.inverseLimitModule F : Type u))).mkQ y = 0 := by
        apply lp.equivalence.injective
        rw [hproj', hpy]
        exact (lp.equivalence.map_zero).symm
      have hy : y ∈ I ^ (1 : ℕ) • (⊤ : Submodule A
        (Formalization.Books.Algebra.Unit87.inverseLimitModule F : Type u)) := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmk
        exact hmk
      have hmap :
          Submodule.map eLin.toLinearMap
              (I ^ (1 : ℕ) • (⊤ : Submodule A
                (Formalization.Books.Algebra.Unit87.inverseLimitModule F : Type u))) ≤
            (J.restrictScalars A : Submodule A L) := by
        rw [ideal_restrictScalars_eq_smul_top_of_map
          (I ^ (1 : ℕ)) J (by
            dsimp [J, cprimeIdeal]
            rw [pow_one])]
        rw [Submodule.map_smul'', Submodule.map_top]
        exact smul_mono_right _ le_top
      have hmem : eLin y ∈ J := hmap
        (Submodule.mem_map_of_mem hy)
      rw [← sub_eq_zero]
      change Ideal.Quotient.mk J (b₁ - b₂) = 0
      rw [show b₁ - b₂ = eLin y by
        dsimp [y]
        rw [eLin.apply_symm_apply]]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    let eRes : (L ⧸ J) ≃+* S := RingEquiv.ofBijective qres
      ⟨qres_inj, qres_surj⟩
    let : Algebra (A ⧸ I) (L ⧸ J) :=
      Ideal.Quotient.algebraQuotientOfLEComap
        (R := A) (A := L) (p := I) (P := J) Ideal.le_comap_map
    let eI : (A ⧸ I) ≃+*
        ((adicQuotientSystem A I).obj
          (Opposite.op (1 : ℕ+)) : Type u) :=
      Ideal.quotEquivOfEq (by simp)
    let fstage0 : ((adicQuotientSystem A I).obj
        (Opposite.op (1 : ℕ+)) : Type u) →+* S :=
      (X.obj.hom.app (Opposite.op (1 : ℕ+))).hom
    let fstage : A ⧸ I →+* S := fstage0.comp eI.toRingHom
    have hbase : eRes.toRingHom.comp (algebraMap (A ⧸ I) (L ⧸ J)) =
        fstage := by
      apply RingHom.ext
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      change eRes (Ideal.Quotient.mk J (algebraMap A L a)) =
        fstage (Ideal.Quotient.mk I a)
      rw [show eRes (Ideal.Quotient.mk J (algebraMap A L a)) =
          p (algebraMap A L a) by rfl]
      change p (φ a) = fstage (Ideal.Quotient.mk I a)
      dsimp [p, φ]
      rw [← ConcreteCategory.comp_apply, limit.lift_π]
      change (c.π.app (Opposite.op (1 : ℕ+))).hom a =
        fstage0 (eI (Ideal.Quotient.mk I a))
      dsimp [c]
      change fstage0 (Ideal.Quotient.mk (I ^ (1 : ℕ)) a) =
        fstage0 (eI (Ideal.Quotient.mk I a))
      rw [show eI (Ideal.Quotient.mk I a) =
          Ideal.Quotient.mk (I ^ (1 : ℕ)) a by
            simp only [eI, Ideal.quotEquivOfEq]
            have hpow : I = I ^ ((1 : ℕ+) : ℕ) := by simp
            change (Submodule.quotEquivOfEq I (I ^ ((1 : ℕ+) : ℕ)) hpow
              (Submodule.Quotient.mk a)) = Submodule.Quotient.mk a
            rw [Submodule.quotEquivOfEq_mk I (I ^ ((1 : ℕ+) : ℕ)) hpow a]
        ]
    have hfinite : RingHom.FiniteType
        (eRes.symm.toRingHom.comp fstage) := by
      have hg0 : RingHom.FiniteType
          (eRes.symm.toRingHom.comp fstage0) :=
        (X.property.1 (1 : ℕ+)).comp_surjective eRes.symm.surjective
      have hcomp : RingHom.FiniteType
          ((eRes.symm.toRingHom.comp fstage).comp eI.symm.toRingHom) := by
        convert hg0 using 1
        ext x
        change eRes.symm (fstage0 (eI (eI.symm x))) = eRes.symm (fstage0 x)
        rw [eI.apply_symm_apply]
      exact RingHom.FiniteType.of_comp_finiteType hcomp
    have heq : eRes.symm.toRingHom.comp fstage =
        algebraMap (A ⧸ I) (L ⧸ J) := by
      apply RingHom.ext
      intro x
      apply eRes.injective
      simpa using congrArg (fun q => q x) hbase.symm
    have hfinal : RingHom.FiniteType (algebraMap (A ⧸ I) (L ⧸ J)) := by
      rw [← heq]
      exact hfinite
    have hfinal' : RingHom.FiniteType
        (algebraMap (A ⧸ I)
          ((cprimeResidueAlgebra I B : CommAlgCat (A ⧸ I)) : Type u)) := by
      convert hfinal using 1
      · rfl
      · exact HEq.rfl
      · exact HEq.rfl
    rw [RingHom.finiteType_algebraMap] at hfinal'
    exact hfinal'

private noncomputable def adicSystemLimitCone {A : Type u} [CommRing A]
    (I : Ideal A) (X : AdicSystemCategory A I) : Cone X.obj.right :=
  { pt := CommRingCat.of A
    π :=
      { app := fun i =>
          CommRingCat.ofHom
            ((X.obj.hom.app i).hom.comp
              (Ideal.Quotient.mk (I ^ (i.unop : ℕ))))
        naturality := by
          intro i j f
          apply CommRingCat.hom_ext
          apply RingHom.ext
          intro a
          have h := congrArg
            (fun q => q.hom
              (Ideal.Quotient.mk (I ^ (i.unop : ℕ)) a))
            (X.obj.hom.naturality f)
          change (X.obj.hom.app j).hom
              (((adicQuotientSystem A I).map f).hom
                (Ideal.Quotient.mk (I ^ (i.unop : ℕ)) a)) =
            (X.obj.right.map f).hom
              ((X.obj.hom.app i).hom
                (Ideal.Quotient.mk (I ^ (i.unop : ℕ)) a)) at h
          exact h } }

private noncomputable def adicSystemLimitAlgebraMap {A : Type u} [CommRing A]
    (I : Ideal A) (X : AdicSystemCategory A I) :
    A →+* ((limit X.obj.right : CommRingCat.{u}) : Type u) :=
  (limit.lift X.obj.right (adicSystemLimitCone I X)).hom

private noncomputable instance adicSystemLimitAlgebra {A : Type u} [CommRing A]
    (I : Ideal A) (X : AdicSystemCategory A I) :
    Algebra A ((limit X.obj.right : CommRingCat.{u}) : Type u) :=
  (adicSystemLimitAlgebraMap I X).toAlgebra

private theorem adicSystemLimitModuleEquiv {A : Type u} [CommRing A]
    (I : Ideal A) (X : AdicSystemCategory A I) :
    ∃ e :
        ((Formalization.Books.Algebra.Unit87.inverseLimitModule
            (adicSystemModuleSystem I X.obj) : ModuleCat A) : Type u) ≃ₗ[A]
          ((limit X.obj.right : CommRingCat.{u}) : Type u),
      ∀ y n,
        (limit.π X.obj.right (Opposite.op n)).hom (e y) =
          (limit.π (adicSystemModuleSystem I X.obj)
            (Opposite.op n)).hom y := by
  let F := adicSystemModuleSystem I X.obj
  have hFG :
      F ⋙ forget₂ (ModuleCat A) AddCommGrpCat =
        X.obj.right ⋙ forget₂ CommRingCat RingCat ⋙
          forget₂ RingCat AddCommGrpCat := by
    rfl
  let eStage :
      limit (F ⋙ forget₂ (ModuleCat A) AddCommGrpCat) ≅
        limit (X.obj.right ⋙ forget₂ CommRingCat RingCat ⋙
          forget₂ RingCat AddCommGrpCat) :=
    eqToIso (congrArg (fun G => limit G) hFG)
  let eAddIso :
      (forget₂ (ModuleCat A) AddCommGrpCat).obj
          (limit F) ≅
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj
          (limit X.obj.right) :=
    preservesLimitIso (forget₂ (ModuleCat A) AddCommGrpCat) F ≪≫
        eStage ≪≫
        (preservesLimitIso
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
          X.obj.right).symm
  let eAdd :
      ((limit F : ModuleCat A) : Type u) ≃+
        ((limit X.obj.right : CommRingCat.{u}) : Type u) :=
    CategoryTheory.Iso.addCommGroupIsoToAddEquiv eAddIso
  have hproj (y : ((limit F : ModuleCat A) : Type u))
      (n : ℕ+) :
      (limit.π X.obj.right (Opposite.op n)).hom (eAdd y) =
        (limit.π F (Opposite.op n)).hom y := by
    change (((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
      (limit.π X.obj.right (Opposite.op n))).hom (eAddIso.hom.hom y)) =
      ((forget₂ (ModuleCat A) AddCommGrpCat).map
        (limit.π F (Opposite.op n))).hom y
    dsimp [eAddIso]
    have hπ := preservesLimitIso_inv_π
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
      X.obj.right (Opposite.op n)
    have hπy := congrArg
      (fun q => q.hom
        (eStage.hom.hom
          ((preservesLimitIso (forget₂ (ModuleCat A) AddCommGrpCat) F).hom.hom y)))
      hπ
    have hπy' :
        ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          (limit.π X.obj.right (Opposite.op n))).hom
            ((preservesLimitIso
              (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
              X.obj.right).inv.hom
              (eStage.hom.hom
                ((preservesLimitIso
                  (forget₂ (ModuleCat A) AddCommGrpCat) F).hom.hom y))) =
          (limit.π
            (X.obj.right ⋙ forget₂ CommRingCat RingCat ⋙
              forget₂ RingCat AddCommGrpCat) (Opposite.op n)).hom
            (eStage.hom.hom
              ((preservesLimitIso
                (forget₂ (ModuleCat A) AddCommGrpCat) F).hom.hom y)) := by
      simpa only [ConcreteCategory.comp_apply] using hπy
    have hstageproj : HEq
        ((limit.π
            (F ⋙ forget₂ (ModuleCat A) AddCommGrpCat) (Opposite.op n)).hom
          (eStage.hom.hom
            ((preservesLimitIso (forget₂ (ModuleCat A) AddCommGrpCat) F).hom.hom y)))
        ((limit.π
            (X.obj.right ⋙ forget₂ CommRingCat RingCat ⋙
              forget₂ RingCat AddCommGrpCat) (Opposite.op n)).hom
          ((preservesLimitIso (forget₂ (ModuleCat A) AddCommGrpCat) F).hom.hom y)) := by
      dsimp [eStage]
      cases hFG
      rfl
    have hpfy := congrArg (fun q => q.hom y)
      (preservesLimitIso_hom_π
        (forget₂ (ModuleCat A) AddCommGrpCat) F (Opposite.op n))
    have hmap : HEq
        ((limit.π
            (X.obj.right ⋙ forget₂ CommRingCat RingCat ⋙
              forget₂ RingCat AddCommGrpCat) (Opposite.op n)).hom
          (eStage.hom.hom
            ((preservesLimitIso (forget₂ (ModuleCat A) AddCommGrpCat) F).hom.hom y)))
        (((forget₂ (ModuleCat A) AddCommGrpCat).map
          (limit.π F (Opposite.op n))).hom y) := by
      exact hstageproj.symm.trans (heq_of_eq hpfy)
    have hfull : HEq
        (((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          (limit.π X.obj.right (Opposite.op n))).hom
          ((preservesLimitIso
            (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
            X.obj.right).inv.hom
            (eStage.hom.hom
              ((preservesLimitIso
                (forget₂ (ModuleCat A) AddCommGrpCat) F).hom.hom y))))
        (((forget₂ (ModuleCat A) AddCommGrpCat).map
          (limit.π F (Opposite.op n))).hom y) := by
      exact (heq_of_eq hπy').trans hmap
    exact eq_of_heq hfull
  let eLin :
      ((limit F : ModuleCat A) : Type u) ≃ₗ[A]
        ((limit X.obj.right : CommRingCat.{u}) : Type u) :=
    { eAdd with
      map_smul' := by
        intro a y
        apply Concrete.limit_ext X.obj.right
        intro n
        change (limit.π X.obj.right n).hom (eAdd (a • y)) =
          (limit.π X.obj.right n).hom
            (adicSystemLimitAlgebraMap I X a * eAdd y)
        rw [hproj (a • y) n.unop, map_mul]
        have hφn := congrArg (fun q => q.hom a)
          (limit.lift_π (adicSystemLimitCone I X) n)
        change (limit.π X.obj.right n).hom
            (adicSystemLimitAlgebraMap I X a) =
          (X.obj.hom.app n).hom
            (Ideal.Quotient.mk (I ^ (n.unop : ℕ)) a) at hφn
        rw [hφn, hproj y n.unop]
        change (limit.π F n).hom (a • y) =
          a • (limit.π F n).hom y
        rw [map_smul] }
  exact ⟨eLin, hproj⟩

noncomputable def adicSystemLimitData {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (X : AdicSystemCategory A I) : AdicSystemLimitData I X :=
  Classical.choice (adicSystemLimitData_exists I hI X)

def adicSystemLimitObject {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (X : AdicSystemCategory A I) : CompleteAlgebraCategory A I :=
  let d := adicSystemLimitData I hI X
  ⟨d.algebra, ⟨d.complete, d.residue_finite⟩⟩

private theorem adicSystemLimitData_stage_equiv {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (X : AdicSystemCategory A I)
    (d : AdicSystemLimitData I X) (n : ℕ+) :
    Nonempty
      (((d.algebra : Type u) ⧸ (cprimeIdeal I d.algebra) ^ (n : ℕ)) ≃+*
        X.obj.right.obj (Opposite.op n)) := by
  let F := adicSystemModuleSystem I X.obj
  have hF := adicSystemModuleSystem_isQuotient I X.obj X.property
  have hlimit := Formalization.Books.Algebra.Unit98.limit_complete I hI F hF
  obtain ⟨eLin, hproj⟩ := adicSystemLimitModuleEquiv I X
  let L : Type u := ((limit X.obj.right : CommRingCat.{u}) : Type u)
  let B : Type u := d.algebra
  let J : Ideal B := cprimeIdeal I d.algebra
  let P : Submodule A (Formalization.Books.Algebra.Unit87.inverseLimitModule F : Type u) :=
    I ^ (n : ℕ) • (⊤ : Submodule A
      (Formalization.Books.Algebra.Unit87.inverseLimitModule F : Type u))
  let p : B →+* X.obj.right.obj (Opposite.op n) :=
    (limit.π X.obj.right (Opposite.op n)).hom.comp d.comparison.toRingHom
  have hcomparison_smul (a : A) (b : B) :
      d.comparison (algebraMap A B a * b) =
        adicSystemLimitAlgebraMap I X a * d.comparison b := by
    apply Concrete.limit_ext X.obj.right
    intro k
    have hstage :
        (limit.π X.obj.right k).hom
            (d.comparison (algebraMap A B a)) =
          (X.obj.hom.app k).hom
            (Ideal.Quotient.mk (I ^ (k.unop : ℕ)) a) := by
      simpa only [Opposite.unop_op] using d.comparison_stage a k.unop
    have hscalar' :
        (limit.π X.obj.right k).hom
            (adicSystemLimitAlgebraMap I X a) =
          (X.obj.hom.app k).hom
            (Ideal.Quotient.mk (I ^ (k.unop : ℕ)) a) := by
      have hscalar := congrArg (fun q => q.hom a)
        (limit.lift_π (adicSystemLimitCone I X) k)
      change (limit.π X.obj.right k).hom
          (adicSystemLimitAlgebraMap I X a) =
        (X.obj.hom.app k).hom
          (Ideal.Quotient.mk (I ^ (k.unop : ℕ)) a)
      exact hscalar
    change (limit.π X.obj.right k).hom
        (d.comparison (algebraMap A B a * b)) =
      (limit.π X.obj.right k).hom
        (adicSystemLimitAlgebraMap I X a * d.comparison b)
    simp only [map_mul]
    rw [hstage, ← hscalar']
  let eComp : B ≃ₗ[A] L :=
    { toFun := d.comparison
      invFun := d.comparison.symm
      left_inv := d.comparison.left_inv
      right_inv := d.comparison.right_inv
      map_add' := d.comparison.map_add
      map_smul' := by
        intro a b
        rw [Algebra.smul_def, Algebra.smul_def]
        change d.comparison (algebraMap A B a * b) =
          adicSystemLimitAlgebraMap I X a * d.comparison b
        exact hcomparison_smul a b }
  have hp_surj : Function.Surjective p := by
    let lp := Classical.choice (hlimit.1 n)
    intro z
    obtain ⟨q, hq⟩ := lp.equivalence.surjective z
    obtain ⟨y, hy⟩ := Submodule.mkQ_surjective P q
    refine ⟨d.comparison.symm (eLin y), ?_⟩
    have hproj' := congrArg (fun q => q.hom y) lp.projection_eq
    change lp.equivalence (P.mkQ y) =
      (limit.π F (Opposite.op n)).hom y at hproj'
    have hpe : p (d.comparison.symm (eLin y)) =
        (limit.π F (Opposite.op n)).hom y := by
      dsimp [p]
      rw [d.comparison.apply_symm_apply]
      simpa using hproj y n
    have hprojz := hproj'.symm.trans ((congrArg lp.equivalence hy).trans hq)
    rw [hpe]
    exact hprojz
  have hJK : J ^ (n : ℕ) ≤ RingHom.ker p := by
    dsimp [J, cprimeIdeal]
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro a ha
    change p (algebraMap A B a) = 0
    change (limit.π X.obj.right (Opposite.op n)).hom
        (d.comparison (algebraMap A B a)) = 0
    rw [d.comparison_stage]
    have ha0 : Ideal.Quotient.mk (I ^ (n : ℕ)) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rw [ha0]
    exact (X.obj.hom.app (Opposite.op n)).hom.map_zero
  have hKJ : RingHom.ker p ≤ J ^ (n : ℕ) := by
    intro b hb
    let y := eLin.symm (d.comparison b)
    have hycomp : eLin y = d.comparison b := by
      dsimp [y]
      rw [eLin.apply_symm_apply]
    have hpy : (limit.π F (Opposite.op n)).hom y = 0 := by
      rw [← hproj y n, hycomp]
      exact hb
    let lp := Classical.choice (hlimit.1 n)
    have hproj' := congrArg (fun q => q.hom y) lp.projection_eq
    change lp.equivalence (P.mkQ y) =
      (limit.π F (Opposite.op n)).hom y at hproj'
    have hmk : P.mkQ y = 0 := by
      apply lp.equivalence.injective
      rw [hproj', hpy]
      exact (lp.equivalence.map_zero).symm
    have hyP : y ∈ P := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmk
      exact hmk
    have hmapLin :
        Submodule.map eLin.toLinearMap P ≤
          (I ^ (n : ℕ) • (⊤ : Submodule A L)) := by
      rw [Submodule.map_smul'', Submodule.map_top]
      exact smul_mono_right _ le_top
    have hJpow : J ^ (n : ℕ) =
        Ideal.map (algebraMap A B) (I ^ (n : ℕ)) := by
      dsimp [J, cprimeIdeal]
      rw [← Ideal.map_pow]
    have hmapComp :
        Submodule.map eComp.symm.toLinearMap
            (I ^ (n : ℕ) • (⊤ : Submodule A L)) ≤
          ((J ^ (n : ℕ)).restrictScalars A : Submodule A B) := by
      rw [ideal_restrictScalars_eq_smul_top_of_map
        (I ^ (n : ℕ)) (J ^ (n : ℕ)) hJpow]
      rw [Submodule.map_smul'', Submodule.map_top]
      exact smul_mono_right _ le_top
    have hmem : eComp.symm (eLin y) ∈ J ^ (n : ℕ) := by
      apply hmapComp
      exact Submodule.mem_map_of_mem
        (hmapLin (Submodule.mem_map_of_mem hyP))
    rw [hycomp] at hmem
    change d.comparison.symm (d.comparison b) ∈ J ^ (n : ℕ) at hmem
    simpa using hmem
  have hker : J ^ (n : ℕ) = RingHom.ker p :=
    le_antisymm hJK hKJ
  let e₀ := RingHom.quotientKerEquivOfSurjective hp_surj
  exact ⟨(Ideal.quotEquivOfEq hker).trans e₀⟩

/-- The limit algebra has the prescribed quotient at every positive stage. -/
theorem adicSystemLimit_quotient_presentation {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (X : AdicSystemCategory A I) (n : ℕ+) :
    Nonempty
      (((adicSystemLimitObject I hI X).obj : Type u) ⧸
          (cprimeIdeal I (adicSystemLimitObject I hI X).obj) ^ (n : ℕ) ≃+*
        X.obj.right.obj (Opposite.op n)) := by
  let d := adicSystemLimitData I hI X
  change Nonempty
    (((d.algebra : Type u) ⧸ (cprimeIdeal I d.algebra) ^ (n : ℕ)) ≃+*
      X.obj.right.obj (Opposite.op n))
  exact adicSystemLimitData_stage_equiv I hI X d n

/-- A map of systems induces a map between the chosen complete limit algebras. -/
private noncomputable def adicSystemLimitRingHom {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) {X Y : AdicSystemCategory A I} (f : X ⟶ Y) :
    ((adicSystemLimitObject I hI X).obj : Type u) →+*
      (adicSystemLimitObject I hI Y).obj :=
  let dX := adicSystemLimitData I hI X
  let dY := adicSystemLimitData I hI Y
  dY.comparison.symm.toRingHom.comp
    ((lim.map f.hom.right).hom.comp dX.comparison.toRingHom)

private theorem adicSystemLimitRingHom_commutes {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) {X Y : AdicSystemCategory A I} (f : X ⟶ Y)
    (a : A) :
    adicSystemLimitRingHom I hI f
        (algebraMap A (adicSystemLimitObject I hI X).obj a) =
      algebraMap A (adicSystemLimitObject I hI Y).obj a := by
  let dX := adicSystemLimitData I hI X
  let dY := adicSystemLimitData I hI Y
  let q : ((dX.algebra : Type u) : Type u) →+*
      (dY.algebra : Type u) :=
    dY.comparison.symm.toRingHom.comp
      ((lim.map f.hom.right).hom.comp dX.comparison.toRingHom)
  change q (algebraMap A dX.algebra a) = algebraMap A dY.algebra a
  apply dY.comparison.injective
  apply Concrete.limit_ext Y.obj.right
  intro n
  change (limit.π Y.obj.right n).hom
      (dY.comparison (q (algebraMap A dX.algebra a))) =
    (limit.π Y.obj.right n).hom
      (dY.comparison (algebraMap A dY.algebra a))
  dsimp [q]
  rw [dY.comparison.apply_symm_apply]
  rw [← ConcreteCategory.comp_apply, limMap_π]
  change (f.hom.right.app n).hom
      ((limit.π X.obj.right n).hom
        (dX.comparison (algebraMap A dX.algebra a))) =
    (limit.π Y.obj.right n).hom
      (dY.comparison (algebraMap A dY.algebra a))
  have hX := dX.comparison_stage a n.unop
  have hY := dY.comparison_stage a n.unop
  have hf := congrArg (fun z => z.hom
      (Ideal.Quotient.mk (I ^ (n.unop : ℕ)) a))
    (congrArg (fun z => z.app n) f.hom.w)
  change (f.hom.right.app n).hom
      ((X.obj.hom.app n).hom
        (Ideal.Quotient.mk (I ^ (n.unop : ℕ)) a)) =
    (Y.obj.hom.app n).hom
      (Ideal.Quotient.mk (I ^ (n.unop : ℕ)) a) at hf
  rw [hX, hY]
  exact hf

private noncomputable def adicSystemLimitAlgHom {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) {X Y : AdicSystemCategory A I} (f : X ⟶ Y) :
    (adicSystemLimitObject I hI X).obj →ₐ[A]
      (adicSystemLimitObject I hI Y).obj :=
  { toRingHom := adicSystemLimitRingHom I hI f
    commutes' := adicSystemLimitRingHom_commutes I hI f }

private noncomputable def adicSystemLimitMap {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) {X Y : AdicSystemCategory A I} (f : X ⟶ Y) :
    adicSystemLimitObject I hI X ⟶ adicSystemLimitObject I hI Y :=
  ObjectProperty.homMk
    (CommAlgCat.ofHom (adicSystemLimitAlgHom I hI f))

private theorem adicSystemLimitRingHom_apply {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) {X Y : AdicSystemCategory A I} (f : X ⟶ Y)
    (b : (adicSystemLimitObject I hI X).obj) :
    adicSystemLimitRingHom I hI f b =
      (adicSystemLimitData I hI Y).comparison.symm
        ((lim.map f.hom.right).hom
          ((adicSystemLimitData I hI X).comparison b)) := by
  rfl

private theorem adicSystemLimitMap_id {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (X : AdicSystemCategory A I) :
    adicSystemLimitMap I hI (𝟙 X) = 𝟙 (adicSystemLimitObject I hI X) := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro b
  dsimp [adicSystemLimitMap, adicSystemLimitAlgHom, adicSystemLimitObject]
  change adicSystemLimitRingHom I hI (𝟙 X) b = b
  rw [adicSystemLimitRingHom_apply]
  apply (adicSystemLimitData I hI X).comparison.injective
  have hlimid : (lim.map (𝟙 X.obj.right)).hom =
      RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply Concrete.limit_ext X.obj.right
    intro m
    rw [← ConcreteCategory.comp_apply, ← limMap_eq, limMap_π]
    simp
  have hlimid' :
      (lim.map (𝟙 X : X ⟶ X).hom.right).hom = RingHom.id _ := by
    rw [show (𝟙 X : X ⟶ X).hom.right = 𝟙 X.obj.right by rfl]
    exact hlimid
  rw [hlimid']
  change (adicSystemLimitData I hI X).comparison
      ((adicSystemLimitData I hI X).comparison.invFun
        ((adicSystemLimitData I hI X).comparison.toFun b)) =
    (adicSystemLimitData I hI X).comparison b
  exact congrArg (fun z => (adicSystemLimitData I hI X).comparison z)
    ((adicSystemLimitData I hI X).comparison.left_inv b)

private theorem adicSystemLimitMap_comp {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG)
    {X Y Z : AdicSystemCategory A I} (f : X ⟶ Y) (g : Y ⟶ Z) :
    adicSystemLimitMap I hI (f ≫ g) =
      adicSystemLimitMap I hI f ≫ adicSystemLimitMap I hI g := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro b
  dsimp [adicSystemLimitMap, adicSystemLimitAlgHom, adicSystemLimitObject]
  change adicSystemLimitRingHom I hI (f ≫ g) b =
    adicSystemLimitRingHom I hI g
      (adicSystemLimitRingHom I hI f b)
  rw [adicSystemLimitRingHom_apply, adicSystemLimitRingHom_apply,
    adicSystemLimitRingHom_apply]
  apply (adicSystemLimitData I hI Z).comparison.injective
  rw [(adicSystemLimitData I hI Z).comparison.apply_symm_apply]
  rw [(adicSystemLimitData I hI Z).comparison.apply_symm_apply]
  rw [(adicSystemLimitData I hI Y).comparison.apply_symm_apply]
  apply Concrete.limit_ext Z.obj.right
  intro n
  simp

theorem adicSystemLimitMap_exists {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) {X Y : AdicSystemCategory A I} (f : X ⟶ Y) :
    Nonempty (adicSystemLimitObject I hI X ⟶ adicSystemLimitObject I hI Y) := by
  exact ⟨adicSystemLimitMap I hI f⟩

/-- The functor from `𝓒` to `𝓒'` defined by inverse limit. -/
noncomputable def systemLimitFunctor {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) : AdicSystemCategory A I ⥤ CompleteAlgebraCategory A I :=
  { obj := fun X => adicSystemLimitObject I hI X
    map := fun f => adicSystemLimitMap I hI f
    map_id := by
      intro X
      exact adicSystemLimitMap_id I hI X
    map_comp := by
      intro X Y Z f g
      exact adicSystemLimitMap_comp I hI f g }

theorem systemLimitFunctor_exists {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) :
    Nonempty (AdicSystemCategory A I ⥤ CompleteAlgebraCategory A I) := by
  exact ⟨systemLimitFunctor I hI⟩

/-- The two constructions are quasi-inverse equivalences of categories. -/
theorem quotient_limit_quasiInverse {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) :
    Nonempty
        (completeAlgebraSystemFunctor I ⋙ systemLimitFunctor I hI ≅
          𝟭 (CompleteAlgebraCategory A I)) ∧
      Nonempty
        (systemLimitFunctor I hI ⋙ completeAlgebraSystemFunctor I ≅
          𝟭 (AdicSystemCategory A I)) := by
  sorry

/-- Conversely, completeness identifies an algebra with the limit of its quotients. -/
theorem completeAlgebra_limit_presentation {A : Type u} [CommRing A]
    (I : Ideal A) (B : CompleteAlgebraCategory A I) :
    Nonempty
      (B.obj ≃+*
        ((limit (cprimeQuotientSystem I B.obj) : CommRingCat.{u}) : Type u)) := by
  let _ : IsAdicComplete (cprimeIdeal I B.obj) (B.obj : Type u) := B.property.1
  obtain ⟨e⟩ := adicCompletion_is_powerQuotientLimit (cprimeIdeal I B.obj)
  exact ⟨(AdicCompletion.ofAlgEquiv (cprimeIdeal I B.obj)).toRingEquiv.trans e⟩

/-! ## Presentations by completed polynomial algebras -/

/-- The completion of a finite-type `A`-algebra for the extended ideal. -/
def adicCompletionAlgebra {A : Type u} [CommRing A] (I : Ideal A)
    (C : CommAlgCat A) : CommAlgCat A :=
  CommAlgCat.of A (AdicCompletion (cprimeIdeal I C) C)

/-- Every finite-type `A`-algebra has a complete finite-type completion. -/
theorem adicCompletionAlgebra_property {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (C : CommAlgCat A)
    (hC : Algebra.FiniteType A C) :
    CompleteAlgebraProperty I (adicCompletionAlgebra I C) := by
  constructor
  · let J : Ideal (C : Type u) := cprimeIdeal I C
    let _ : IsNoetherianRing (C : Type u) :=
      Algebra.FiniteType.isNoetherianRing A (C : Type u)
    have hJ : J.FG := Ideal.FG.of_isNoetherianRing J
    have hmap :
        IsAdicComplete
          (J.map (algebraMap (C : Type u) (AdicCompletion J (C : Type u))))
          (AdicCompletion J (C : Type u)) :=
      (IsAdicComplete.map_algebraMap_iff
        (I := J) (M := AdicCompletion J (C : Type u))).mpr
        (AdicCompletion.isAdicComplete hJ)
    change IsAdicComplete
      (Ideal.map (algebraMap A (AdicCompletion J (C : Type u))) I)
      (AdicCompletion J (C : Type u))
    have hAlg : algebraMap A (AdicCompletion J (C : Type u)) =
        (algebraMap (C : Type u) (AdicCompletion J (C : Type u))).comp
          (algebraMap A (C : Type u)) :=
      (IsScalarTower.algebraMap_eq A (C : Type u)
        (AdicCompletion J (C : Type u))).symm
    rw [hAlg, ← Ideal.map_map]
    exact hmap
  · let J : Ideal (C : Type u) := cprimeIdeal I C
    let _ : IsNoetherianRing (C : Type u) :=
      Algebra.FiniteType.isNoetherianRing A (C : Type u)
    have hJ : J.FG := Ideal.FG.of_isNoetherianRing J
    let Q := AdicCompletion J (C : Type u)
    let K : Ideal Q := Ideal.map (algebraMap A Q) I
    let _ : Algebra (A ⧸ I) ((C : Type u) ⧸ J) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    let _ : Algebra (A ⧸ I) (Q ⧸ K) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    have hC' : RingHom.FiniteType (algebraMap A (C : Type u)) := by
      rw [RingHom.finiteType_algebraMap]
      exact hC
    have hqC : RingHom.FiniteType
        ((Ideal.Quotient.mk J).comp (algebraMap A (C : Type u))) :=
      hC'.comp_surjective (fun x => Ideal.Quotient.mk_surjective x)
    have hq' : RingHom.FiniteType
        (algebraMap (A ⧸ I) ((C : Type u) ⧸ J)) := by
      apply RingHom.FiniteType.of_comp_finiteType
        (f := Ideal.Quotient.mk I)
      convert hqC using 1
      ext x
      rfl
    have hker : K = RingHom.ker (AdicCompletion.evalOneₐ J).toRingHom := by
      rw [show RingHom.ker (AdicCompletion.evalOneₐ J).toRingHom =
          J.map (algebraMap (C : Type u) Q) from
        AdicCompletion.ker_evalOneₐ_eq_map J hJ]
      change Ideal.map (algebraMap A Q) I =
        J.map (algebraMap (C : Type u) Q)
      dsimp [K, Q]
      have hAlg : algebraMap A (AdicCompletion J (C : Type u)) =
          (algebraMap (C : Type u) (AdicCompletion J (C : Type u))).comp
            (algebraMap A (C : Type u)) :=
        (IsScalarTower.algebraMap_eq A (C : Type u)
          (AdicCompletion J (C : Type u))).symm
      rw [hAlg, ← Ideal.map_map]
      simp [J, cprimeIdeal]
    let e : (Q ⧸ K) ≃+* ((C : Type u) ⧸ J) :=
      (Ideal.quotEquivOfEq hker).trans
        (RingHom.quotientKerEquivOfSurjective
          (f := (AdicCompletion.evalOneₐ J).toRingHom)
          (AdicCompletion.evalOneₐ_surjective J))
    have hq'' : RingHom.FiniteType
        (e.symm.toRingHom.comp
          (algebraMap (A ⧸ I) ((C : Type u) ⧸ J))) :=
      hq'.comp_surjective e.symm.surjective
    have heq : e.symm.toRingHom.comp
          (algebraMap (A ⧸ I) ((C : Type u) ⧸ J)) =
        algebraMap (A ⧸ I) (Q ⧸ K) := by
      apply RingHom.ext
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      apply e.injective
      simp only [RingHom.coe_comp, Function.comp_apply]
      change e (e.symm
          (algebraMap (A ⧸ I) ((C : Type u) ⧸ J)
            (Ideal.Quotient.mk I a))) =
        e (algebraMap (A ⧸ I) (Q ⧸ K) (Ideal.Quotient.mk I a))
      rw [e.apply_symm_apply]
      rfl
    have hfinal : RingHom.FiniteType (algebraMap (A ⧸ I) (Q ⧸ K)) := by
      rw [← heq]
      exact hq''
    change Algebra.FiniteType (A ⧸ I) (Q ⧸ K)
    exact RingHom.finiteType_algebraMap.mp hfinal

/-- A polynomial algebra in `r` variables over `A`. -/
def polynomialAlgebra {A : Type u} [CommRing A] (r : ℕ) : CommAlgCat A :=
  CommAlgCat.of A (MvPolynomial (Fin r) A)

/-- The completed polynomial algebra `A⟦x₁, ..., xᵣ⟧`. -/
def polynomialCompletion {A : Type u} [CommRing A] (I : Ideal A) (r : ℕ) :
    CommAlgCat A :=
  adicCompletionAlgebra I (polynomialAlgebra r)

theorem polynomialCompletion_property {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (r : ℕ) :
    CompleteAlgebraProperty I (polynomialCompletion I r) := by
  have h : Algebra.FiniteType A (MvPolynomial (Fin r) A) := by infer_instance
  simpa [polynomialCompletion, adicCompletionAlgebra, polynomialAlgebra] using
    adicCompletionAlgebra_property I (polynomialAlgebra r) h

/-- Every complete algebra in `𝓒'` is a quotient of a completed polynomial algebra. -/
theorem exists_polynomialCompletion_quotient {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (B : CompleteAlgebraCategory A I) :
    ∃ (r : ℕ) (J : Ideal (polynomialCompletion I r)),
        Nonempty
        (B.obj ≃ₐ[A]
          (polynomialCompletion I r : Type u) ⧸ J) := by
  sorry

/-! ## The four Noetherian assertions -/

/-- A complete algebra in `𝓒'` is Noetherian when `A` is Noetherian. -/
theorem completeAlgebra_isNoetherian {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (B : CompleteAlgebraCategory A I) :
    IsNoetherianRing B.obj := by
  sorry

/-- A quotient of an object of `𝓒'` is again an object of `𝓒'` over a Noetherian base. -/
theorem quotient_completeAlgebra_property {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (B : CompleteAlgebraCategory A I)
    (J : Ideal B.obj) :
    CompleteAlgebraProperty I (quotientCommAlg B.obj J) := by
  sorry

/-- The quotient construction used in the second Noetherian assertion. -/
def quotientCompleteAlgebra {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (B : CompleteAlgebraCategory A I)
    (J : Ideal B.obj) : CompleteAlgebraCategory A I :=
  ⟨quotientCommAlg B.obj J, quotient_completeAlgebra_property I B J⟩

/-- The completion of a finite-type algebra is in `𝓒'`. -/
theorem finiteType_completion_completeAlgebra_property {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (C : CommAlgCat A)
    (hC : Algebra.FiniteType A C) :
    CompleteAlgebraProperty I (adicCompletionAlgebra I C) := by
  exact adicCompletionAlgebra_property I C hC

/-! ## The warning without Noetherian hypotheses -/

/-- Data witnessing that quotient closure for `𝓒'` is not a general-ring fact. -/
structure CPrimeQuotientFailure where
  base : Type u
  [commRing : CommRing base]
  ideal : Ideal base
  algebra : CommAlgCat base
  quotientIdeal : Ideal algebra
  base_complete : CompleteAlgebraProperty ideal algebra
  quotient_not_complete :
    ¬ CompleteAlgebraProperty ideal (quotientCommAlg algebra quotientIdeal)

/-- The non-Noetherian quotient warning from the source. -/
theorem exists_cprime_quotient_failure : Nonempty CPrimeQuotientFailure := by
  sorry

/-! ## Base change -/

/-- Data for a base change `A₁ → A₂` carrying `I₁^c` into `I₂`. -/
structure AdicBaseChangeData (A₁ A₂ : Type u) [CommRing A₁] [CommRing A₂] where
  map : A₁ →+* A₂
  I₁ : Ideal A₁
  I₂ : Ideal A₂
  exponent : ℕ+
  ideal_le : Ideal.map map (I₁ ^ (exponent : ℕ)) ≤ I₂

theorem baseChange_power_le {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (D : AdicBaseChangeData A₁ A₂) (n : ℕ+) :
    D.I₁ ^ ((D.exponent * n : ℕ+) : ℕ) ≤
      (D.I₂ ^ (n : ℕ)).comap D.map := by
  sorry

/-- The induced map `A₁/I₁^(cn) → A₂/I₂^n`. -/
def baseChangeQuotientComponent {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (D : AdicBaseChangeData A₁ A₂) (n : ℕ+) :
    adicQuotient A₁ D.I₁ (D.exponent * n) →+*
      adicQuotient A₂ D.I₂ n :=
  Ideal.quotientMap (D.I₂ ^ (n : ℕ)) D.map
    (baseChange_power_le D n)

/-- The stagewise tensor product appearing in base change of systems. -/
def systemBaseChangeStage {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (D : AdicBaseChangeData A₁ A₂) (X : AdicSystemCategory A₁ D.I₁)
    (n : ℕ+) : CommRingCat.{u} := by
  let R := adicQuotient A₁ D.I₁ (D.exponent * n)
  letI : Algebra R (X.obj.right.obj (Opposite.op (D.exponent * n))) :=
    (X.obj.hom.app (Opposite.op (D.exponent * n))).hom.toAlgebra
  letI : Algebra R (adicQuotient A₂ D.I₂ n) :=
    (baseChangeQuotientComponent D n).toAlgebra
  exact CommRingCat.of
    (X.obj.right.obj (Opposite.op (D.exponent * n)) ⊗[R]
      adicQuotient A₂ D.I₂ n)

/-- The system base-change functor supplied by the stagewise tensor products. -/
theorem systemBaseChangeFunctor_exists {A₁ A₂ : Type u}
    [CommRing A₁] [CommRing A₂] (D : AdicBaseChangeData A₁ A₂) :
    Nonempty
      (AdicSystemCategory A₁ D.I₁ ⥤ AdicSystemCategory A₂ D.I₂) := by
  sorry

noncomputable def systemBaseChangeFunctor {A₁ A₂ : Type u}
    [CommRing A₁] [CommRing A₂] (D : AdicBaseChangeData A₁ A₂) :
    AdicSystemCategory A₁ D.I₁ ⥤ AdicSystemCategory A₂ D.I₂ :=
  Classical.choice (systemBaseChangeFunctor_exists D)

/-- The system base-change functor has the source's tensor-product stages. -/
theorem systemBaseChangeFunctor_stage_spec {A₁ A₂ : Type u}
    [CommRing A₁] [CommRing A₂] (D : AdicBaseChangeData A₁ A₂)
    (X : AdicSystemCategory A₁ D.I₁) (n : ℕ+) :
    Nonempty
      (((systemBaseChangeFunctor D).obj X).obj.right.obj (Opposite.op n) ≃+*
        (systemBaseChangeStage D X n : Type u)) := by
  sorry

/-- The completed tensor product appearing in base change of complete algebras. -/
def completeBaseChangeAlgebra {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (D : AdicBaseChangeData A₁ A₂) (B : CompleteAlgebraCategory A₁ D.I₁) :
    CommAlgCat A₂ := by
  letI : Algebra A₁ A₂ := D.map.toAlgebra
  let T := B.obj ⊗[A₁] A₂
  letI : Algebra A₂ T := Algebra.TensorProduct.rightAlgebra
  exact CommAlgCat.of A₂
    (AdicCompletion (Ideal.map (algebraMap A₂ T) D.I₂) T)

theorem completeBaseChangeAlgebra_property {A₁ A₂ : Type u}
    [CommRing A₁] [CommRing A₂] (D : AdicBaseChangeData A₁ A₂)
    (hI₂ : D.I₂.FG) (B : CompleteAlgebraCategory A₁ D.I₁) :
    CompleteAlgebraProperty D.I₂ (completeBaseChangeAlgebra D B) := by
  sorry

/-- The object part of completed tensor-product base change. -/
def completeBaseChangeObject {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (D : AdicBaseChangeData A₁ A₂) (hI₂ : D.I₂.FG)
    (B : CompleteAlgebraCategory A₁ D.I₁) :
    CompleteAlgebraCategory A₂ D.I₂ :=
  ⟨completeBaseChangeAlgebra D B, completeBaseChangeAlgebra_property D hI₂ B⟩

/-- Base change on `𝓒'`, after completing the tensor product. -/
theorem completeBaseChangeFunctor_exists {A₁ A₂ : Type u}
    [CommRing A₁] [CommRing A₂] (D : AdicBaseChangeData A₁ A₂)
    (hI₂ : D.I₂.FG) :
    Nonempty
      (CompleteAlgebraCategory A₁ D.I₁ ⥤ CompleteAlgebraCategory A₂ D.I₂) := by
  sorry

noncomputable def completeBaseChangeFunctor {A₁ A₂ : Type u}
    [CommRing A₁] [CommRing A₂] (D : AdicBaseChangeData A₁ A₂)
    (hI₂ : D.I₂.FG) :
    CompleteAlgebraCategory A₁ D.I₁ ⥤ CompleteAlgebraCategory A₂ D.I₂ :=
  Classical.choice (completeBaseChangeFunctor_exists D hI₂)

/-- The completed base-change functor has the displayed completed tensor product as its object. -/
theorem completeBaseChangeFunctor_obj_spec {A₁ A₂ : Type u}
    [CommRing A₁] [CommRing A₂] (D : AdicBaseChangeData A₁ A₂)
    (hI₂ : D.I₂.FG) (B : CompleteAlgebraCategory A₁ D.I₁) :
    Nonempty
      ((completeBaseChangeFunctor D hI₂).obj B ≅ completeBaseChangeObject D hI₂ B) := by
  sorry

/-- The two base-change constructions agree through the equivalences `𝓒 ≃ 𝓒'`. -/
theorem baseChange_functors_agree {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (D : AdicBaseChangeData A₁ A₂) (hI₁ : D.I₁.FG) (hI₂ : D.I₂.FG) :
    Nonempty
      (completeBaseChangeFunctor D hI₂ ≅
        completeAlgebraSystemFunctor D.I₁ ⋙
          systemBaseChangeFunctor D ⋙
          systemLimitFunctor D.I₂ hI₂) := by
  sorry

/-! ## Closed immersions and the final base-change identity -/

/-- The data for the closed-immersion base change in the source. -/
structure ClosedImmersionData (A : Type u) [CommRing A] where
  I : Ideal A
  a : Ideal A
  Ibar : Ideal (A ⧸ a)
  c : ℕ+
  d : ℕ+
  I_power_le :
    Ideal.map (Ideal.Quotient.mk a) (I ^ (c : ℕ)) ≤ Ibar
  Ibar_power_le :
    Ibar ^ (d : ℕ) ≤ Ideal.map (Ideal.Quotient.mk a) I

theorem closedImmersion_Ibar_fg {A : Type u} [CommRing A]
    [IsNoetherianRing A] (D : ClosedImmersionData A) : D.Ibar.FG := by
  sorry

/-- The quotient `B/aB`, as an algebra over `A/a`. -/
def closedImmersionQuotient {A : Type u} [CommRing A]
    (D : ClosedImmersionData A) (B : CompleteAlgebraCategory A D.I) :
    CommAlgCat (A ⧸ D.a) := by
  let J : Ideal B.obj := Ideal.map (algebraMap A B.obj) D.a
  letI : Algebra (A ⧸ D.a) (B.obj ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := A) (A := B.obj) (p := D.a) (P := J) Ideal.le_comap_map
  exact CommAlgCat.of (A ⧸ D.a) (B.obj ⧸ J)

/-- The tensor product with `A/a` is canonically the quotient `B/aB`. -/
def closedImmersionTensorAlgebra {A : Type u} [CommRing A]
    (D : ClosedImmersionData A) (B : CompleteAlgebraCategory A D.I) :
    CommAlgCat (A ⧸ D.a) := by
  letI : Algebra A (A ⧸ D.a) :=
    (Ideal.Quotient.mk D.a).toAlgebra
  let T := (A ⧸ D.a) ⊗[A] B.obj
  letI : Semiring T := Algebra.TensorProduct.instSemiring
  letI : CommRing T := Algebra.TensorProduct.instCommRing
  letI : Algebra (A ⧸ D.a) T := Algebra.TensorProduct.leftAlgebra
  exact CommAlgCat.of (A ⧸ D.a) T

theorem closedImmersion_tensor_quotient_equiv {A : Type u} [CommRing A]
    (D : ClosedImmersionData A) (B : CompleteAlgebraCategory A D.I) :
    Nonempty
      ((closedImmersionTensorAlgebra D B : Type u) ≃ₐ[A ⧸ D.a]
        (closedImmersionQuotient D B : Type u)) := by
  sorry

/-- The closed-immersion completion is the completed tensor product from base change. -/
def closedImmersionBaseChangeData {A : Type u} [CommRing A]
    (D : ClosedImmersionData A) :
    AdicBaseChangeData A (A ⧸ D.a) where
  map := Ideal.Quotient.mk D.a
  I₁ := D.I
  I₂ := D.Ibar
  exponent := D.c
  ideal_le := D.I_power_le

def closedImmersionBaseChangeAlgebra {A : Type u} [CommRing A]
    (D : ClosedImmersionData A) (B : CompleteAlgebraCategory A D.I) :
    CommAlgCat (A ⧸ D.a) :=
  completeBaseChangeAlgebra (closedImmersionBaseChangeData D) B

/-- The quotient `B/aB` is complete for the induced `Ibar`-adic topology. -/
theorem closedImmersion_quotient_complete {A : Type u} [CommRing A]
    [IsNoetherianRing A] (D : ClosedImmersionData A)
    (B : CompleteAlgebraCategory A D.I) :
    CompleteAlgebraProperty D.Ibar (closedImmersionQuotient D B) := by
  sorry

/-- The closed-immersion quotient as an object of the target complete-algebra category. -/
def closedImmersionQuotientObject {A : Type u} [CommRing A]
    [IsNoetherianRing A] (D : ClosedImmersionData A)
    (B : CompleteAlgebraCategory A D.I) :
    CompleteAlgebraCategory (A ⧸ D.a) D.Ibar :=
  ⟨closedImmersionQuotient D B, closedImmersion_quotient_complete D B⟩

/-- The source's identity `(B ⊗ Abar)^ = (B/aB)^ = B/aB`, expressed canonically. -/
theorem closedImmersion_completion_identity {A : Type u} [CommRing A]
    [IsNoetherianRing A] (D : ClosedImmersionData A)
    (B : CompleteAlgebraCategory A D.I) :
    Nonempty
      (closedImmersionBaseChangeAlgebra D B ≅ closedImmersionQuotient D B) := by
  sorry

/-- The target base-change functor is the quotient functor `B ↦ B/aB`. -/
theorem closedImmersion_baseChangeFunctor_obj {A : Type u} [CommRing A]
    [IsNoetherianRing A] (D : ClosedImmersionData A)
    (B : CompleteAlgebraCategory A D.I) :
    Nonempty
      ((completeBaseChangeFunctor (closedImmersionBaseChangeData D)
          (closedImmersion_Ibar_fg D)).obj B ≅
        closedImmersionQuotientObject D B) := by
  sorry

end

end Formalization.Books.Restricted.Unit02
