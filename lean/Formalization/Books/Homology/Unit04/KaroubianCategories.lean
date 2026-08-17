import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Yoneda

/-!
# Homological Algebra, Chapter 4: Karoubian categories

Mathlib's `IsIdempotentComplete` is the canonical interface for the
Karoubian condition.  In a preadditive category, Mathlib identifies it with
the existence of kernels for all idempotent endomorphisms.  The declarations
below record the source statements using that interface, together with the
countable-product argument's explicit presheaf and abelian-group maps.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive

universe v u

namespace Formalization.Books.Homology.Unit04

/-! ## Karoubian categories and the equivalent formulations -/

/- The source definition is Mathlib's `IsIdempotentComplete`; the following
   theorem exposes its preadditive kernel formulation under a chapter-local
   name. -/

theorem karoubian_iff_idempotents_have_kernels
    {C : Type u} [Category.{v} C] [Preadditive C] :
    IsIdempotentComplete C ↔
      ∀ (X : C) (p : X ⟶ X), p ≫ p = p → HasKernel p :=
  Idempotents.isIdempotentComplete_iff_idempotents_have_kernels C

theorem karoubian_iff_idempotents_have_cokernels
    {C : Type u} [Category.{v} C] [Preadditive C] :
    IsIdempotentComplete C ↔
      ∀ (X : C) (p : X ⟶ X), p ≫ p = p → HasCokernel p := by
  constructor
  · intro h X p hp
    have hkp : HasKernel p :=
      (karoubian_iff_idempotents_have_kernels (C := C)).mp h X p hp
    have hkc : HasKernel (Formalization.Books.Homology.Unit03.idempotentComplement p) :=
      (karoubian_iff_idempotents_have_kernels (C := C)).mp h X
        (Formalization.Books.Homology.Unit03.idempotentComplement p)
        (Formalization.Books.Homology.Unit03.idempotent_complement_relations p hp).2.2
    exact
      (Formalization.Books.Homology.Unit03.idempotent_splitting_has_all_kernels_and_cokernels
        p hp ⟨Or.inl hkp, Or.inl hkc⟩).2.1
  · intro h
    apply (karoubian_iff_idempotents_have_kernels (C := C)).mpr
    intro X p hp
    have hcp : HasCokernel p := h X p hp
    have hcc : HasCokernel (Formalization.Books.Homology.Unit03.idempotentComplement p) :=
      h X (Formalization.Books.Homology.Unit03.idempotentComplement p)
        (Formalization.Books.Homology.Unit03.idempotent_complement_relations p hp).2.2
    exact
      (Formalization.Books.Homology.Unit03.idempotent_splitting_has_all_kernels_and_cokernels
        p hp ⟨Or.inr hcp, Or.inr hcc⟩).1

/- In the decomposition below `b.bicone.snd ≫ b.bicone.inr` is the projection
   onto the second summand.  The displayed equation says that `p` becomes this
   projection after transporting along `e : Z ≅ b.bicone.pt`. -/

theorem karoubian_iff_idempotent_direct_sum_decomposition
    {C : Type u} [Category.{v} C] [Preadditive C] :
    IsIdempotentComplete C ↔
      ∀ (Z : C) (p : Z ⟶ Z), p ≫ p = p →
        ∃ (X Y : C) (b : BinaryBiproductData X Y) (e : Z ≅ b.bicone.pt),
          p ≫ e.hom = e.hom ≫ b.bicone.snd ≫ b.bicone.inr := by
  constructor
  · intro h Z p hp
    letI : HasKernel p :=
      (karoubian_iff_idempotents_have_kernels (C := C)).mp h Z p hp
    letI : HasKernel (Formalization.Books.Homology.Unit03.idempotentComplement p) :=
      (karoubian_iff_idempotents_have_kernels (C := C)).mp h Z
        (Formalization.Books.Homology.Unit03.idempotentComplement p)
        (Formalization.Books.Homology.Unit03.idempotent_complement_relations p hp).2.2
    letI : HasCokernel p :=
      (karoubian_iff_idempotents_have_cokernels (C := C)).mp h Z p hp
    letI : HasCokernel (Formalization.Books.Homology.Unit03.idempotentComplement p) :=
      (karoubian_iff_idempotents_have_cokernels (C := C)).mp h Z
        (Formalization.Books.Homology.Unit03.idempotentComplement p)
        (Formalization.Books.Homology.Unit03.idempotent_complement_relations p hp).2.2
    obtain ⟨b₁, b₂, b₃, b₄, e₁, e₂, e₃, e₄, hh⟩ :=
      Formalization.Books.Homology.Unit03.idempotent_splitting_decompositions p hp
    have h₁ := hh.1
    have h₂ := hh.2.1
    have h₃ := hh.2.2.1
    have h₄ := hh.2.2.2.1
    have hzero : p ≫ Formalization.Books.Homology.Unit03.idempotent_kernel_projection p hp = 0 := by
      apply (cancel_mono (kernel.ι p)).1
      simp only [Category.assoc, Formalization.Books.Homology.Unit03.idempotent_kernel_projection,
        kernel.lift_ι, zero_comp]
      simpa using (Formalization.Books.Homology.Unit03.idempotent_complement_relations p hp).1
    have hone : p ≫ Formalization.Books.Homology.Unit03.idempotent_complement_kernel_projection p hp =
        Formalization.Books.Homology.Unit03.idempotent_complement_kernel_projection p hp := by
      apply (cancel_mono (kernel.ι (Formalization.Books.Homology.Unit03.idempotentComplement p))).1
      simp only [Category.assoc,
        Formalization.Books.Homology.Unit03.idempotent_complement_kernel_projection,
        kernel.lift_ι]
      exact hp
    refine ⟨kernel p, kernel (Formalization.Books.Homology.Unit03.idempotentComplement p), b₁, e₁, ?_⟩
    apply b₁.isBilimit.isLimit.hom_ext
    intro j
    rcases j with ⟨⟨⟩⟩
    · change (p ≫ e₁.hom) ≫ b₁.bicone.fst =
        (e₁.hom ≫ b₁.bicone.snd ≫ b₁.bicone.inr) ≫ b₁.bicone.fst
      rw [Category.assoc, h₃]
      simp only [Category.assoc, BinaryBicone.inr_fst, comp_zero]
      exact hzero
    · change (p ≫ e₁.hom) ≫ b₁.bicone.snd =
        (e₁.hom ≫ b₁.bicone.snd ≫ b₁.bicone.inr) ≫ b₁.bicone.snd
      rw [Category.assoc, h₄]
      simp only [Category.assoc, BinaryBicone.inr_snd, Category.comp_id]
      exact hone.trans h₄.symm
  · intro h
    apply (karoubian_iff_idempotents_have_kernels (C := C)).mpr
    intro Z p hp
    obtain ⟨X, Y, b, e, he⟩ := h Z p hp
    letI : HasKernel b.bicone.snd :=
      ⟨⟨{
        cone := BinaryBicone.sndKernelFork b.bicone
        isLimit := BinaryBicone.isLimitSndKernelFork b.isBilimit.isLimit
      }⟩⟩
    letI : HasKernel (b.bicone.snd ≫ b.bicone.inr) := inferInstance
    letI : HasKernel (e.hom ≫ b.bicone.snd ≫ b.bicone.inr) := inferInstance
    let kcone : KernelFork p :=
      KernelFork.ofι (f := p) (kernel.ι (e.hom ≫ b.bicone.snd ≫ b.bicone.inr))
        (by
          apply (cancel_mono e.hom).1
          rw [Category.assoc, he]
          simp)
    let klimit : IsLimit kcone := by
      simpa only [kcone] using
        (kernel.ofCompIso (e.hom ≫ b.bicone.snd ≫ b.bicone.inr) p e he)
    exact ⟨⟨{ cone := kcone, isLimit := klimit }⟩⟩

/-! ## The representability observation in the product argument -/

/- For `W : C`, this is the subgroup of morphisms `W ⟶ X` killed by `e`.
   Contravariance is implemented by precomposition. -/

def idempotentKernelPresheaf
    {C : Type u} [Category.{v} C] [Preadditive C]
    (X : C) (e : X ⟶ X) : Cᵒᵖ ⥤ Type v where
  obj W := {f : W.unop ⟶ X // f ≫ e = 0}
  map := fun {W V} g =>
    TypeCat.ofHom (fun f : {f : W.unop ⟶ X // f ≫ e = 0} =>
      ⟨g.unop ≫ f.1, by
        simp only [Category.assoc, f.2, comp_zero]⟩)
  map_id := by
    intro W
    ext f
    simp
  map_comp := by
    intro W V U f g
    ext h
    simp [Category.assoc]

theorem idempotent_kernel_presheaf_isRepresentable_iff
    {C : Type u} [Category.{v} C] [Preadditive C]
    (X : C) (e : X ⟶ X) :
    (idempotentKernelPresheaf X e).IsRepresentable ↔ HasKernel e := by
  constructor
  · intro hr
    rcases hr.has_representation with ⟨Y, ⟨r⟩⟩
    let i : Y ⟶ X := (r.homEquiv (𝟙 Y)).1
    have hi : i ≫ e = 0 := (r.homEquiv (𝟙 Y)).2
    let kfork : KernelFork e := KernelFork.ofι i hi
    let klimit : IsLimit kfork := by
      refine KernelFork.IsLimit.ofι i hi
        (fun {W} f hf => r.homEquiv.symm ⟨f, hf⟩) ?_ ?_
      · intro W f hf
        let g := r.homEquiv.symm ⟨f, hf⟩
        have hg : r.homEquiv g = ⟨f, hf⟩ := r.homEquiv.apply_symm_apply _
        have hc := r.homEquiv_comp g (𝟙 Y)
        have hm : (⟨f, hf⟩ : (idempotentKernelPresheaf X e).obj (Opposite.op W)) =
            (idempotentKernelPresheaf X e).map g.op (r.homEquiv (𝟙 Y)) := by
          rw [← hg]
          rw [Category.comp_id] at hc
          exact hc
        change g ≫ i = f
        have hval := congrArg Subtype.val hm
        change f = g ≫ i at hval
        exact hval.symm
      · intro W f hf m hm
        apply r.homEquiv.injective
        let g := r.homEquiv.symm ⟨f, hf⟩
        have hg : r.homEquiv g = ⟨f, hf⟩ := r.homEquiv.apply_symm_apply _
        have hc := r.homEquiv_comp m (𝟙 Y)
        have hm' : r.homEquiv m =
            (idempotentKernelPresheaf X e).map m.op (r.homEquiv (𝟙 Y)) := by
          simpa only [Category.comp_id] using hc
        apply Subtype.ext
        change (r.homEquiv m).1 = (r.homEquiv g).1
        have hval := congrArg Subtype.val hm'
        change (r.homEquiv m).1 = m ≫ i at hval
        exact (hval.trans hm).trans (congrArg Subtype.val hg).symm
    exact ⟨⟨{ cone := kfork, isLimit := klimit }⟩⟩
  · intro hk
    letI : HasKernel e := hk
    apply Functor.RepresentableBy.isRepresentable
    refine
      { homEquiv :=
          { toFun := fun f => ⟨f ≫ kernel.ι e, by simp⟩
            invFun := fun f => kernel.lift e f.1 f.2
            left_inv := by
              intro f
              apply (cancel_mono (kernel.ι e)).1
              simp
            right_inv := by
              intro f
              apply Subtype.ext
              simp }
        homEquiv_comp := ?_ }
    intro W V f g
    apply Subtype.ext
    change (f ≫ g) ≫ kernel.ι e = f ≫ (g ≫ kernel.ι e)
    simp [Category.assoc]

/-! ## The explicit countable-product maps on abelian groups -/

/- The product indexed by `ℕ` is represented by the function type `ℕ → A`. -/

def projectorPhi
    {A : Type u} [AddCommGroup A] (e : A →+ A) :
    (ℕ → A) →+ (ℕ → A) where
  toFun a n := e (a n) + (a (n + 1) - e (a (n + 1)))
  map_zero' := by
    funext n
    simp
  map_add' a b := by
    funext n
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

def projectorPsi
    {A : Type u} [AddCommGroup A] (e : A →+ A) :
    (ℕ → A) →+ (ℕ → A) where
  toFun a n :=
    match n with
    | 0 => a 0
    | n + 1 => (a n - e (a n)) + e (a (n + 1))
  map_zero' := by
    funext n
    cases n <;> simp
  map_add' a b := by
    funext n
    cases n <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/- The textbook writes an equality between kernels living in different
   ambient groups.  The source-faithful correction is the canonical additive
   isomorphism between them. -/

theorem projector_kernel_equiv
    {A : Type u} [AddCommGroup A] (e : A →+ A)
    (he : e.comp e = e) :
    Nonempty (e.ker ≃+ (projectorPhi e).ker) := by
  have he' (x : A) : e (e x) = e x := by
    simpa using congrArg (fun f : A →+ A => f x) he
  refine ⟨
    { toEquiv :=
        { toFun := fun x =>
            ⟨fun n => if n = 0 then x.1 else 0, by
              funext n
              cases n with
              | zero =>
                  change e x.1 + ((0 : A) - e 0) = 0
                  have hx : e x.1 = 0 := x.2
                  simpa only [map_zero, sub_zero, add_zero] using hx
              | succ n => simp [projectorPhi]⟩
          invFun := fun a =>
            ⟨a.1 0, by
              have h0 := congrArg (fun f : ℕ → A => e (f 0)) a.2
              simpa [projectorPhi, he', sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h0⟩
          left_inv := by
            intro x
            apply Subtype.ext
            simp
          right_inv := by
            intro a
            apply Subtype.ext
            funext n
            cases n with
            | zero => simp
            | succ n =>
                have hn : e (a.1 n) = 0 := by
                  have h := congrArg (fun f : ℕ → A => e (f n)) a.2
                  simpa [projectorPhi, he', sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
                have hn1 : e (a.1 (n + 1)) = 0 := by
                  have h := congrArg (fun f : ℕ → A => e (f (n + 1))) a.2
                  simpa [projectorPhi, he', sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
                have h := congrArg (fun f : ℕ → A => f n) a.2
                have hnext : a.1 (n + 1) = 0 := by
                  simpa [projectorPhi, hn, hn1] using h
                simp [hnext] }
      map_add' := by
        intro x y
        apply Subtype.ext
        funext n
        cases n <;> simp }⟩

theorem projectorPhi_has_right_inverse
    {A : Type u} [AddCommGroup A] (e : A →+ A)
    (he : e.comp e = e) :
    Function.RightInverse (projectorPsi e) (projectorPhi e) := by
  have he' (x : A) : e (e x) = e x := by
    simpa using congrArg (fun f : A →+ A => f x) he
  intro a
  funext n
  cases n with
  | zero =>
      simp [projectorPhi, projectorPsi, he', sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  | succ n =>
      simp [projectorPhi, projectorPsi, he', sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-! ## Countable products/coproducts force the Karoubian condition -/

theorem karoubian_of_countable_products_of_kernels_of_split_epimorphisms
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCountableProducts C]
    (h : ∀ {X Y : C} (f : X ⟶ Y) [IsSplitEpi f], HasKernel f) :
    IsIdempotentComplete C := by
  apply (karoubian_iff_idempotents_have_kernels (C := C)).mpr
  intro X e he
  let P : C := ∏ᶜ (fun _ : ℕ => X)
  let phi : P ⟶ P :=
    Pi.lift (fun n =>
      Pi.π (fun _ : ℕ => X) n ≫ e +
        Pi.π (fun _ : ℕ => X) (n + 1) ≫ (𝟙 X - e))
  let psi : P ⟶ P :=
    Pi.lift (fun n =>
      match n with
      | 0 => Pi.π (fun _ : ℕ => X) 0
      | n + 1 =>
          Pi.π (fun _ : ℕ => X) n ≫ (𝟙 X - e) +
            Pi.π (fun _ : ℕ => X) (n + 1) ≫ e)
  have hpsi : psi ≫ phi = 𝟙 P := by
    apply Pi.hom_ext
    intro n
    cases n with
    | zero =>
        simp [psi, phi, Category.assoc, he, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm]
    | succ n =>
        simp [psi, phi, Category.assoc, he, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm]
  letI : IsSplitEpi phi :=
    IsSplitEpi.mk' { section_ := psi, id := hpsi }
  letI : HasKernel phi := h phi
  let i : kernel phi ⟶ X := kernel.ι phi ≫ Pi.π (fun _ : ℕ => X) 0
  let lift0 (W : C) (f : W ⟶ X) : W ⟶ P :=
    Pi.lift (fun n => if n = 0 then f else 0)
  have lift0_phi {W : C} (f : W ⟶ X) (hf : f ≫ e = 0) :
      lift0 W f ≫ phi = 0 := by
    apply Pi.hom_ext
    intro n
    cases n with
    | zero =>
        simp [lift0, phi, hf, Category.assoc, sub_eq_add_neg, add_comm]
    | succ n =>
        simp [lift0, phi, Category.assoc, sub_eq_add_neg, add_left_comm, add_comm]
  have hkill {W : C} (m : W ⟶ kernel phi) (n : ℕ) :
      m ≫ kernel.ι phi ≫ Pi.π (fun _ : ℕ => X) n ≫ e = 0 := by
    have hm : m ≫ kernel.ι phi ≫ phi = 0 := by
      simp
    have hn := congrArg
      (fun q : W ⟶ P => q ≫ Pi.π (fun _ : ℕ => X) n ≫ e) hm
    simpa [phi, Category.assoc, he, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hn
  have hzero {W : C} (m : W ⟶ kernel phi) (n : ℕ) :
      m ≫ kernel.ι phi ≫ Pi.π (fun _ : ℕ => X) (n + 1) = 0 := by
    have hm : m ≫ kernel.ι phi ≫ phi = 0 := by
      simp
    have hn := congrArg (fun q : W ⟶ P => q ≫ Pi.π (fun _ : ℕ => X) n) hm
    have hn' :
        m ≫ kernel.ι phi ≫ Pi.π (fun _ : ℕ => X) n ≫ e +
            m ≫ kernel.ι phi ≫ Pi.π (fun _ : ℕ => X) (n + 1) ≫ (𝟙 X - e) = 0 := by
      simpa [phi, Category.assoc] using hn
    simpa [comp_sub, Category.assoc, hkill m n, hkill m (n + 1)] using hn'
  have hi : i ≫ e = 0 := by
    have h0 := congrArg
      (fun q : kernel phi ⟶ P => q ≫ Pi.π (fun _ : ℕ => X) 0 ≫ e)
      (kernel.condition phi)
    simpa [i, phi, Category.assoc, he, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h0
  let kfork : KernelFork e := KernelFork.ofι i hi
  let klimit : IsLimit kfork := by
    refine KernelFork.IsLimit.ofι i hi
      (fun {W} f hf => kernel.lift phi (lift0 W f) (lift0_phi f hf)) ?_ ?_
    · intro W f hf
      simp [i, lift0]
    · intro W f hf m hm
      apply (cancel_mono (kernel.ι phi)).1
      rw [kernel.lift_ι]
      apply Pi.hom_ext
      intro n
      cases n with
      | zero =>
          simpa [i, lift0, Category.assoc] using hm
      | succ n =>
          simp [lift0, hzero m n, Category.assoc]
  exact ⟨⟨{ cone := kfork, isLimit := klimit }⟩⟩

theorem karoubian_of_countable_coproducts_of_cokernels_of_split_monomorphisms
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCountableCoproducts C]
    (h : ∀ {X Y : C} (f : X ⟶ Y) [IsSplitMono f], HasCokernel f) :
    IsIdempotentComplete C := by
  letI : HasCountableProducts Cᵒᵖ :=
    { out := fun J _ => inferInstance }
  apply Idempotents.isIdempotentComplete_of_isIdempotentComplete_opposite
  apply karoubian_of_countable_products_of_kernels_of_split_epimorphisms (C := Cᵒᵖ)
  intro X Y f hf
  letI : IsSplitEpi f := hf
  letI : IsSplitMono f.unop :=
    IsSplitMono.mk' {
      retraction := (section_ f).unop
      id := by
        apply Quiver.Hom.op_inj
        simp }
  letI : HasCokernel f.unop := h f.unop
  exact ⟨⟨{
    cone := KernelFork.ofι (cokernel.π f.unop).op (by
      apply Quiver.Hom.unop_inj
      exact cokernel.condition f.unop)
    isLimit := CokernelCofork.IsColimit.ofπOp (cokernel.π f.unop)
      (cokernel.condition f.unop) (cokernelIsCokernel f.unop)
  }⟩⟩

end Formalization.Books.Homology.Unit04
