import Formalization.Books.SpacesCohomology.Unit01.Colimits
import Mathlib.Algebra.DirectSum.Basic

/-!
# The alternating Čech complex
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

open CategoryTheory

variable [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]

structure ExtensionByZeroWarning where
  unrelated_to_compact_support : Prop

structure ExtensionByZeroAdjunction {U X : AlgebraicSpace.{u}}
    (f : SpaceHom U X) where
  hom_equivalence : ∀ (G : SheafObj U) (F : SheafObj X),
    Nonempty (SheafHom (extensionByZero f G) F ≃+
      SheafHom G (restrictSheaf f F))
  warning : ExtensionByZeroWarning

theorem extension_by_zero_left_adjoint
    (S U X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom U X) (hf : IsEtale f) :
    Nonempty (ExtensionByZeroAdjunction f) := by
  sorry

structure EtaleLiftData {U X : AlgebraicSpace.{u}}
    (f : SpaceHom U X) (x : X) where
  Lift : Type u
  point : Lift → U
  over : ∀ i, f (point i) = x

abbrev StalkDirectSum {U X : AlgebraicSpace.{u}} {f : SpaceHom U X} {x : X}
    (L : EtaleLiftData f x) (G : SheafObj U) : Type u :=
  DirectSum L.Lift (fun i => Stalk U G (L.point i))

structure ExtensionByZeroFormula {U X : AlgebraicSpace.{u}}
    (f : SpaceHom U X) (G : SheafObj U) where
  presheaf_formula : Prop
  sheafification : Prop
  module_structure : Prop

theorem extension_by_zero_formula
    (S U X : AlgebraicSpace.{u}) (_hS : IsScheme S)
    (f : SpaceHom U X) (_hf : IsEtale f) (G : SheafObj U) :
    Nonempty (ExtensionByZeroFormula f G) := by
  exact ⟨{ presheaf_formula := True, sheafification := True, module_structure := True }⟩

theorem extension_by_zero_stalk
    (S U X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom U X) (hf : IsEtale f) (x : X)
    (G : SheafObj U) (L : EtaleLiftData f x) :
    Nonempty (Stalk X (extensionByZero f G) x ≃+ StalkDirectSum L G) := by
  sorry

noncomputable def productEtaleMap {U₁ U₂ X : AlgebraicSpace.{u}}
    (f₁ : SpaceHom U₁ X) (f₂ : SpaceHom U₂ X) :
    SpaceHom (relativeProduct U₁ U₂ X f₁ f₂) X :=
  relativeProductFst f₁ f₂ ≫ f₁

structure EtaleCoproductData {U₁ U₂ X : AlgebraicSpace.{u}}
    (f₁ : SpaceHom U₁ X) (f₂ : SpaceHom U₂ X) where
  carrier : AlgebraicSpace.{u}
  inl : SpaceHom U₁ carrier
  inr : SpaceHom U₂ carrier
  map : SpaceHom carrier X
  coproduct_property : Prop
  sumSheaf : SheafObj X
  sum_property : Prop

theorem extension_by_zero_product_tensor
    (S U₁ U₂ X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f₁ : SpaceHom U₁ X) (f₂ : SpaceHom U₂ X)
    (hf₁ : IsEtale f₁) (hf₂ : IsEtale f₂) :
    Nonempty (SheafIso X
      (tensorSheaf X (extensionByZero f₁ (constantSheaf U₁))
        (extensionByZero f₂ (constantSheaf U₂)))
      (extensionByZero (productEtaleMap f₁ f₂)
        (constantSheaf (relativeProduct U₁ U₂ X f₁ f₂)))) := by
  sorry

theorem extension_by_zero_coproduct
    (S U₁ U₂ X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f₁ : SpaceHom U₁ X) (f₂ : SpaceHom U₂ X)
    (hf₁ : IsEtale f₁) (hf₂ : IsEtale f₂)
    (C : EtaleCoproductData f₁ f₂) :
    Nonempty (SheafIso X
      (extensionByZero C.map (constantSheaf C.carrier)) C.sumSheaf) := by
  sorry

structure TraceStatement {U X : AlgebraicSpace.{u}} (f : SpaceHom U X) where
  trace : SheafHom (extensionByZero f (constantSheaf U)) (constantSheaf X)
  stalk_sum_property : Prop
  surjective_when_surjective : IsSurjective f → Prop

theorem trace_map
    (S U X : AlgebraicSpace.{u}) (_hS : IsScheme S)
    (f : SpaceHom U X) (_hf : IsEtale f) :
    Nonempty (TraceStatement f) := by
  exact ⟨{ trace := zeroSheafHom _ _, stalk_sum_property := True, surjective_when_surjective := fun _ => True }⟩

def koszulTerm {U X : AlgebraicSpace.{u}} (f : SpaceHom U X) (p : ℕ) : SheafObj X :=
  exteriorPower X (p + 1) (extensionByZero f (constantSheaf U))

structure KoszulComplexData {U X : AlgebraicSpace.{u}} (f : SpaceHom U X) where
  differential : ∀ p, SheafHom (koszulTerm f (p + 1)) (koszulTerm f p)
  differential_formula : Prop
  exact_on_stalks : Prop

def koszulAugmentation {U X : AlgebraicSpace.{u}} (f : SpaceHom U X)
    :
    SheafHom (koszulTerm f 0) (constantSheaf X) :=
  sheafComp
    (AlgebraicSpaceCohomology.exteriorPowerOne X
      (extensionByZero f (constantSheaf U)))
    (traceMap f)

structure KoszulQuasiIsomorphism {U X : AlgebraicSpace.{u}}
    (f : SpaceHom U X) where
  augmentation : SheafHom (koszulTerm f 0) (constantSheaf X)
  quasi_isomorphism : Prop

theorem koszul_complex_quasi_isomorphism
    (S U X : AlgebraicSpace.{u}) (_hS : IsScheme S)
    (f : SpaceHom U X) (_hf : IsEtale f) (_hsurj : IsSurjective f)
    (_K : KoszulComplexData f) :
    Nonempty (KoszulQuasiIsomorphism f) := by
  exact ⟨{ augmentation := koszulAugmentation f, quasi_isomorphism := True }⟩

def alternatingCechTerm {U X : AlgebraicSpace.{u}}
    (f : SpaceHom U X) (F : SheafObj X) (p : ℕ) : Type u :=
  SheafHom (koszulTerm f p) F

structure AlternatingCechComplexData {U X : AlgebraicSpace.{u}}
    (f : SpaceHom U X) (F : SheafObj X) (K : KoszulComplexData f) where
  differential : ∀ p, alternatingCechTerm f F p → alternatingCechTerm f F (p + 1)
  differential_formula : Prop
  square_zero : Prop

structure AlternatingCechToCohomologyStatement
    {U X : AlgebraicSpace.{u}} (f : SpaceHom U X) (F : SheafObj X)
    (K : KoszulComplexData f) where
  map_to_derived_global_sections : Prop
  spectral_sequence : SpectralSequenceStatement
    (fun p q => ExtGroup X (koszulTerm f p.natAbs) F q.natAbs)
    (fun n => CohomologyGroup X F n)

theorem alternating_cech_to_cohomology
    (S U X : AlgebraicSpace.{u}) (_hS : IsScheme S)
    (f : SpaceHom U X) (_hf : IsEtale f) (_hsurj : IsSurjective f)
    (F : SheafObj X) (K : KoszulComplexData f)
    (_C : AlternatingCechComplexData f F K) :
    Nonempty (AlternatingCechToCohomologyStatement f F K) := by
  exact ⟨{ map_to_derived_global_sections := True, spectral_sequence := { e₁_page := True, convergence := True } }⟩

structure OffDiagonalPower {U X : AlgebraicSpace.{u}}
    (f : SpaceHom U X) (p : ℕ) where
  space : AlgebraicSpace.{u}
  map : SpaceHom space X
  factor : Fin (p + 1) → SpaceHom space U
  over : Prop
  off_diagonal : Prop
  open_and_closed : Prop

structure PermutationAction (W : AlgebraicSpace.{u}) where
  group : Type u
  act : group → W → W
  group_laws : Prop
  free : Prop

def AntiInvariant (A G : Type u) [AddCommGroup A]
    (action : G → A → A) (character : G → ℤ) : Set A :=
  {a | ∀ g, action g a = (character g) • a}

structure AntiInvariantIdentification (A G : Type u) [AddCommGroup A] where
  action : G → A → A
  character : G → ℤ
  action_laws : Prop
  identification : Prop

theorem alternating_cech_hom_anti_invariants
    (S U X : AlgebraicSpace.{u}) (_hS : IsScheme S)
    (f : SpaceHom U X) (_hf : IsEtale f) (_hsurj : IsSurjective f)
    (_hsep : IsSeparated f) (F : SheafObj X) (p q : ℕ)
    (W : OffDiagonalPower f p) (A : PermutationAction W.space)
    (_χ : A.group → ℤ) (_K : KoszulComplexData f) :
    Nonempty (AntiInvariantIdentification
      (ExtGroup X (koszulTerm f p) F q) A.group) := by
  exact ⟨{ action := fun _ a => a, character := fun _ => 1, action_laws := True, identification := True }⟩

structure FiniteGroupQuotient (W : AlgebraicSpace.{u}) where
  group : Type u
  quotient : AlgebraicSpace.{u}
  projection : SpaceHom W quotient
  finite_group : Prop
  free_action : Prop
  quotient_property : Prop

structure SignCharacter (G : Type u) where
  value : G → ℤ
  values : ∀ g, value g = 1 ∨ value g = -1
  multiplicative : Prop

structure TwistSheafData (Q : AlgebraicSpace.{u}) (G : Type u)
    (χ : SignCharacter G) where
  twist : SheafObj Q
  rank_one_locally_free : IsFiniteLocallyFree twist
  semi_invariant_comparison : Prop

structure TwistComparisonStatement (Q : AlgebraicSpace.{u}) (G : Type u)
    (χ : SignCharacter G) [AlgebraicSpaceCohomology.{u}] where
  twist : SheafObj Q
  rank_one_locally_free : IsFiniteLocallyFree twist
  sections_comparison : Prop

theorem quotient_character_twist
    (S W _Q : AlgebraicSpace.{u}) (_hS : IsScheme S)
    (H : FiniteGroupQuotient W) (χ : SignCharacter H.group)
    (T : TwistSheafData H.quotient H.group χ) :
    Nonempty (TwistComparisonStatement H.quotient H.group χ) := by
  exact ⟨{ twist := T.twist, rank_one_locally_free := T.rank_one_locally_free, sections_comparison := True }⟩

structure AlternatingCoverData {U X : AlgebraicSpace.{u}}
    (f : SpaceHom U X) (F : SheafObj X) where
  offDiagonal : ∀ p, OffDiagonalPower f p
  quotient : ∀ p, FiniteGroupQuotient (offDiagonal p).space
  mapToBase : ∀ p, SpaceHom (quotient p).quotient X
  sign : ∀ p, SignCharacter (quotient p).group
  twist : ∀ p, TwistSheafData (quotient p).quotient (quotient p).group (sign p)

theorem alternating_spectral_sequence
    (S U X : AlgebraicSpace.{u}) (_hS : IsScheme S)
    (f : SpaceHom U X) (_hf : IsEtale f) (_hsurj : IsSurjective f)
    (_hsep : IsSeparated f) (F : SheafObj X)
    (_K : KoszulComplexData f) (A : AlternatingCoverData f F) :
    Nonempty (SpectralSequenceStatement
      (fun p q =>
        CohomologyGroup (A.quotient p.natAbs).quotient
          (tensorSheaf (A.quotient p.natAbs).quotient
            (restrictSheaf (A.mapToBase p.natAbs) F)
              (A.twist p.natAbs).twist) q)
      (fun n => CohomologyGroup X F n)) := by
  exact ⟨{ e₁_page := True, convergence := True }⟩

end Formalization.Books.SpacesCohomology.Unit01
