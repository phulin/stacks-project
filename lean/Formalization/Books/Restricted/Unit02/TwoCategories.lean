import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets
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
  sorry

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
  sorry

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
  sorry

/-- The stagewise quotient map from `A_n` to `B/(IB)^n`. -/
def cprimeBaseComponent {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) (n : ℕ+) :
    adicQuotient A I n →+* cprimeQuotientStage I B n :=
  Ideal.quotientMap
    ((cprimeIdeal I B) ^ (n : ℕ)) (algebraMap A B)
    (cprimeBaseIdeal_le I B n)

/-- The finite-type assertion used to show that the quotient functor lands in `𝓒`. -/
theorem cprimeBaseComponent_finiteType {A : Type u} [CommRing A]
    (I : Ideal A) (B : CompleteAlgebraCategory A I) (n : ℕ+) :
    RingHom.FiniteType (cprimeBaseComponent I B.obj n) := by
  sorry

theorem cprimeBaseMap_naturality {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) {i j : ℕ+ᵒᵖ} (f : i ⟶ j) :
    (adicQuotientSystem A I).map f ≫
        CommRingCat.ofHom (cprimeBaseComponent I B j.unop) =
      CommRingCat.ofHom (cprimeBaseComponent I B i.unop) ≫
        (cprimeQuotientSystem I B).map f := by
  sorry

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
  sorry

/-- The object part of the canonical functor `𝓒' → 𝓒`. -/
def completeAlgebraSystemObject {A : Type u} [CommRing A] (I : Ideal A)
    (B : CompleteAlgebraCategory A I) : AdicSystemCategory A I :=
  ⟨cprimeQuotientArrow I B.obj, cprimeQuotientArrow_property I B⟩

/-- The ideal inclusion needed for the quotient map induced by an algebra map. -/
theorem cprimeQuotientMapIdeal_le {A : Type u} [CommRing A] (I : Ideal A)
    {B C : CommAlgCat A} (f : B ⟶ C) (n : ℕ+) :
    (cprimeIdeal I B) ^ (n : ℕ) ≤
      ((cprimeIdeal I C) ^ (n : ℕ)).comap f.hom.toRingHom := by
  sorry

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
  sorry

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
  sorry

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
  sorry

theorem completeAlgebraSystemMap_comp {A : Type u} [CommRing A]
    (I : Ideal A) {B C D : CompleteAlgebraCategory A I}
    (f : B ⟶ C) (g : C ⟶ D) :
    completeAlgebraSystemMap I (f ≫ g) =
      completeAlgebraSystemMap I f ≫ completeAlgebraSystemMap I g := by
  sorry

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
  complete : IsAdicComplete (cprimeIdeal I algebra) algebra
  residue_finite : Algebra.FiniteType (A ⧸ I) (cprimeResidueAlgebra I algebra)

/-- The completeness lemma supplies an `A`-algebra structure on the limit. -/
theorem adicSystemLimitData_exists {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (X : AdicSystemCategory A I) :
    Nonempty (AdicSystemLimitData I X) := by
  sorry

noncomputable def adicSystemLimitData {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (X : AdicSystemCategory A I) : AdicSystemLimitData I X :=
  Classical.choice (adicSystemLimitData_exists I hI X)

def adicSystemLimitObject {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (X : AdicSystemCategory A I) : CompleteAlgebraCategory A I :=
  let d := adicSystemLimitData I hI X
  ⟨d.algebra, ⟨d.complete, d.residue_finite⟩⟩

/-- The limit algebra has the prescribed quotient at every positive stage. -/
theorem adicSystemLimit_quotient_presentation {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (X : AdicSystemCategory A I) (n : ℕ+) :
    Nonempty
      (((adicSystemLimitObject I hI X).obj : Type u) ⧸
          (cprimeIdeal I (adicSystemLimitObject I hI X).obj) ^ (n : ℕ) ≃+*
        X.obj.right.obj (Opposite.op n)) := by
  sorry

/-- A map of systems induces a map between the chosen complete limit algebras. -/
theorem adicSystemLimitMap_exists {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) {X Y : AdicSystemCategory A I} (f : X ⟶ Y) :
    Nonempty (adicSystemLimitObject I hI X ⟶ adicSystemLimitObject I hI Y) := by
  sorry

/-- The functor from `𝓒` to `𝓒'` defined by inverse limit. -/
theorem systemLimitFunctor_exists {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) :
    Nonempty (AdicSystemCategory A I ⥤ CompleteAlgebraCategory A I) := by
  sorry

noncomputable def systemLimitFunctor {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) : AdicSystemCategory A I ⥤ CompleteAlgebraCategory A I :=
  Classical.choice (systemLimitFunctor_exists I hI)

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
  sorry

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
  sorry

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
  sorry

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
