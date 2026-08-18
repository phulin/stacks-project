import Formalization.Books.Homology.Unit06.Extensions
import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.Data.List.TFAE

/-!
# Homological Algebra, Chapter 28: Projectives

The source's projective objects and categories with enough projectives are
Mathlib's canonical `Projective`, `ProjectivePresentation`, and
`EnoughProjectives` interfaces.  Short exact sequences are represented by
`ShortComplex.ShortExact`, and their splittings by `ShortComplex.Splitting`.
The extension group in the characterization is the extension-class group
constructed in Chapter 6.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

universe v u w

namespace Formalization.Books.Homology.Unit28

/-! ## Projective objects -/

/-- The four conditions in the source's characterization of a projective
object.  The second condition uses the chapter's exact-functor interface for
the preadditive co-Yoneda functor, whose value at `B` is the group of
morphisms `P ⟶ B`. -/
def projectiveConditions
    {C : Type u} [Category.{v} C] [Abelian C] (P : C) : List Prop :=
  [ Projective P,
    Formalization.Books.Categories.Unit23.IsExact
      (preadditiveCoyoneda.obj (Opposite.op P)),
    ∀ (A B : C) (f : A ⟶ B) (g : B ⟶ P) (h : f ≫ g = 0),
      (ShortComplex.mk f g h).ShortExact →
        Nonempty (ShortComplex.mk f g h).Splitting,
    ∀ (A : C) (ξ : Formalization.Books.Homology.Unit06.Ext P A), ξ = 0 ]

/-- Projectivity is equivalent to exactness of the covariant Hom functor,
splitting of every short exact sequence ending in `P`, and vanishing of all
extension classes with first argument `P`. -/
theorem projective_characterization
    {C : Type u} [Category.{v} C] [Abelian C] (P : C) :
    List.TFAE (projectiveConditions P) := by
  unfold projectiveConditions
  have h12 : Projective P ↔
      Formalization.Books.Categories.Unit23.IsExact
        (preadditiveCoyoneda.obj (Opposite.op P)) := by
    let F := preadditiveCoyoneda.obj (Opposite.op P)
    have hiff : Projective P ↔ F.PreservesEpimorphisms :=
      Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj P
    have hlim : PreservesFiniteLimits F := by infer_instance
    constructor
    · intro hP
      let : F.PreservesEpimorphisms := hiff.mp hP
      let : PreservesFiniteLimits F := hlim
      let : F.PreservesHomology :=
        Functor.preservesHomology_of_preservesEpis_and_kernels F
      have hcol : PreservesFiniteColimits F :=
        Functor.preservesFiniteColimits_of_preservesHomology F
      exact ⟨hlim, hcol⟩
    · intro hF
      change PreservesFiniteLimits F ∧ PreservesFiniteColimits F at hF
      apply hiff.mpr
      exact Functor.preservesEpimorphisms_of_preserves_shortExact_right F
        ((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).mp hF.2)
  have h13_forward :
      Projective P →
        (∀ (A B : C) (f : A ⟶ B) (g : B ⟶ P) (h : f ≫ g = 0),
          (ShortComplex.mk f g h).ShortExact →
            Nonempty (ShortComplex.mk f g h).Splitting) := by
    intro hP A B f g h hS
    let : Projective P := hP
    let : Epi g := hS.epi_g
    let : Mono f := hS.mono_f
    obtain ⟨s, hs⟩ := Projective.factors (𝟙 P) g
    let k : B ⟶ B := 𝟙 B - g ≫ s
    have hk : k ≫ g = 0 := by
      simp [k, Category.assoc, hs]
    let r : B ⟶ A := hS.fIsKernel.lift (KernelFork.ofι k hk)
    have hr : r ≫ f = k := by
      exact hS.fIsKernel.fac (KernelFork.ofι k hk) WalkingParallelPair.zero
    refine ⟨{ r := r, s := s, f_r := ?_, s_g := hs, id := ?_ }⟩
    · rw [← cancel_mono f]
      simp [Category.assoc, hr, k]
      rw [← Category.assoc, h, zero_comp]
    · simp [hr, k]
  have h31 :
      (∀ (A B : C) (f : A ⟶ B) (g : B ⟶ P) (h : f ≫ g = 0),
        (ShortComplex.mk f g h).ShortExact →
          Nonempty (ShortComplex.mk f g h).Splitting) → Projective P := by
    intro hS
    refine ⟨fun {E X} f e _ => ?_⟩
    let E' : Formalization.Books.Homology.Unit06.Extension C (kernel e) X :=
      { middle := E
        inclusion := kernel.ι e
        projection := e
        zero := kernel.condition e
        shortExact := { exact := ShortComplex.exact_kernel e } }
    let pb := Formalization.Books.Homology.Unit06.pullbackExtension E' f
    obtain ⟨spl⟩ := hS (kernel e) pb.middle pb.inclusion pb.projection pb.zero
      pb.shortExact
    refine ⟨spl.s ≫ pullback.fst E'.projection f, ?_⟩
    dsimp [pb, Formalization.Books.Homology.Unit06.pullbackExtension] at spl ⊢
    rw [Category.assoc, pullback.condition, ← Category.assoc, spl.s_g,
      Category.id_comp]
  have h13 :
      Projective P ↔
        (∀ (A B : C) (f : A ⟶ B) (g : B ⟶ P) (h : f ≫ g = 0),
          (ShortComplex.mk f g h).ShortExact →
            Nonempty (ShortComplex.mk f g h).Splitting) :=
    ⟨h13_forward, h31⟩
  have h14 : Projective P ↔
      (∀ (A : C) (ξ : Formalization.Books.Homology.Unit06.Ext P A), ξ = 0) := by
    constructor
    · intro hP A ξ
      refine Quotient.inductionOn ξ ?_
      intro E
      change Formalization.Books.Homology.Unit06.extensionClass E =
        Formalization.Books.Homology.Unit06.zeroExtClass
      apply Quotient.sound
      let s : E.toShortComplex.Splitting :=
        (h13_forward hP A E.middle E.inclusion E.projection E.zero
          E.shortExact).some
      dsimp [Formalization.Books.Homology.Unit06.Extension.toShortComplex] at s
      let i : E.middle ≅ A ⊞ P := s.isoBinaryBiproduct
      let f : Formalization.Books.Homology.Unit06.ExtensionHom E
          (Formalization.Books.Homology.Unit06.splitExtension A P) :=
        { middle := by
            simpa [Formalization.Books.Homology.Unit06.splitExtension] using i.hom
          comm_left := by
            dsimp [Formalization.Books.Homology.Unit06.splitExtension]
            apply biprod.hom_ext
            · dsimp [i, ShortComplex.Splitting.isoBinaryBiproduct]
              simp only [Category.assoc, biprod.lift_fst]
              simpa using s.f_r
            · dsimp [i, ShortComplex.Splitting.isoBinaryBiproduct]
              simp [E.zero]
          comm_right := by
            dsimp [Formalization.Books.Homology.Unit06.splitExtension]
            simp [i, s] }
      let g : Formalization.Books.Homology.Unit06.ExtensionHom
          (Formalization.Books.Homology.Unit06.splitExtension A P) E :=
        { middle := by
            simpa [Formalization.Books.Homology.Unit06.splitExtension] using i.inv
          comm_left := by
            dsimp [Formalization.Books.Homology.Unit06.splitExtension]
            dsimp [i, ShortComplex.Splitting.isoBinaryBiproduct]
            simp
          comm_right := by
            dsimp [Formalization.Books.Homology.Unit06.splitExtension]
            apply biprod.hom_ext'
            · dsimp [i, ShortComplex.Splitting.isoBinaryBiproduct]
              simp [E.zero]
            · dsimp [i, ShortComplex.Splitting.isoBinaryBiproduct]
              simpa using s.s_g }
      let e : E ≅ Formalization.Books.Homology.Unit06.splitExtension A P :=
        { hom := f
          inv := g
          hom_inv_id := by
            apply Formalization.Books.Homology.Unit06.ExtensionHom.ext
            change i.hom ≫ i.inv = 𝟙 E.middle
            exact i.hom_inv_id
          inv_hom_id := by
            apply Formalization.Books.Homology.Unit06.ExtensionHom.ext
            change i.inv ≫ i.hom = 𝟙 (A ⊞ P)
            exact i.inv_hom_id }
      exact ⟨e⟩
    · intro hE
      refine ⟨fun {E X} f e _ => ?_⟩
      let E' : Formalization.Books.Homology.Unit06.Extension C (kernel e) X :=
        { middle := E
          inclusion := kernel.ι e
          projection := e
          zero := kernel.condition e
          shortExact := { exact := ShortComplex.exact_kernel e } }
      let pb := Formalization.Books.Homology.Unit06.pullbackExtension E' f
      have hz : Formalization.Books.Homology.Unit06.extensionClass pb =
          Formalization.Books.Homology.Unit06.zeroExtClass :=
        hE (kernel e) (Formalization.Books.Homology.Unit06.extensionClass pb)
      change Formalization.Books.Homology.Unit06.extensionClass pb =
        Formalization.Books.Homology.Unit06.extensionClass
          (Formalization.Books.Homology.Unit06.splitExtension (kernel e) P) at hz
      obtain ⟨iso⟩ := Quotient.exact hz
      let inr : P ⟶
          (Formalization.Books.Homology.Unit06.splitExtension (kernel e) P).middle := by
        simpa [Formalization.Books.Homology.Unit06.splitExtension] using
          (biprod.inr : P ⟶ (kernel e) ⊞ P)
      let s : P ⟶ pb.middle := inr ≫ iso.inv.middle
      let fst : pb.middle ⟶ E := by
        change pullback E'.projection f ⟶ E
        exact pullback.fst E'.projection f
      have hcond : fst ≫ e = pb.projection ≫ f := by
        change pullback.fst E'.projection f ≫ e =
          pullback.snd E'.projection f ≫ f
        exact pullback.condition
      refine ⟨s ≫ fst, ?_⟩
      have hproj := iso.inv.comm_right
      dsimp [s]
      rw [Category.assoc, hcond]
      calc
        (inr ≫ iso.inv.middle) ≫ pb.projection ≫ f =
            inr ≫ (iso.inv.middle ≫ pb.projection) ≫ f := by
              simp [Category.assoc]
        _ = inr ≫
            (Formalization.Books.Homology.Unit06.splitExtension (kernel e) P).projection ≫ f := by
              rw [hproj]
        _ = f := by
          simp [inr, Formalization.Books.Homology.Unit06.splitExtension]
  tfae_have 1 ↔ 2 := by exact h12
  tfae_have 1 ↔ 3 := by exact h13
  tfae_have 1 ↔ 4 := by exact h14
  tfae_finish

/-! ## Coproducts and enough projectives -/

/-- A coproduct of a family of projective objects is projective whenever the
coproduct exists.  The proof uses the coproduct universal property and
projective factorization for each summand. -/
theorem projective_coproduct
    {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} (P : ι → C) [HasCoproduct P]
    [∀ i, Projective (P i)] :
    Projective (∐ P) := by
  refine Projective.mk (fun {E X} f e _ => ?_)
  refine ⟨Sigma.desc (fun i => Projective.factorThru (Sigma.ι P i ≫ f) e), ?_⟩
  apply Sigma.hom_ext
  intro i
  simp

/- The source's “enough projectives” definition is exactly Mathlib's
   `EnoughProjectives C`, whose presentations are
   `ProjectivePresentation X`. -/

/-! ## Functorial projective surjections -/

/-- The source's functorial choice of projective epimorphisms.  The functor
lands in the canonical arrow category; `Arrow.rightFunc` records the target,
`Arrow.left` the source, and `Arrow.hom` the chosen morphism. -/
def HasFunctorialProjectiveSurjections
    {C : Type u} [Category.{v} C] [Abelian C] : Prop :=
  ∃ P : C ⥤ Arrow C,
    P ⋙ Arrow.rightFunc = 𝟭 C ∧
      (∀ A : C, Epi (Arrow.hom (P.obj A))) ∧
        ∀ A : C, Projective (Arrow.left (P.obj A))

end Formalization.Books.Homology.Unit28
