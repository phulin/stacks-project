import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Subobject

/-!
# Dualizing Complexes, Chapter 2: Essential surjections and injections

The source defines essential extensions and essential surjections in an
abelian category, records their elementary closure properties, and then
specializes the extension notion to modules.  Categorical subobjects,
intersections, images, kernels, and cokernels below are the canonical
Mathlib constructions.
-/

namespace Formalization.Books.Dualizing.Unit02

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

universe u v w

noncomputable section

/-! ## Essential morphisms in an abelian category -/

/-- A monomorphism is an essential extension when every nonzero subobject of
the target meets its image nontrivially. -/
def EssentialExtension {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B : 𝒜} (f : A ⟶ B) : Prop :=
  ∃ (hf : Mono f),
    letI := hf
    ∀ P : Subobject B, P ≠ ⊥ → Subobject.mk f ⊓ P ≠ ⊥

/-- An epimorphism is essential when no proper subobject of its source maps
onto the target. -/
def EssentialSurjection {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B : 𝒜} (f : A ⟶ B) : Prop :=
  Epi f ∧ ∀ P : Subobject A, P ≠ ⊤ → (Subobject.«exists» f).obj P ≠ ⊤

/-! The four assertions in the source's first elementary lemma. -/

/-- Essential extensions are transitive. -/
theorem essentialExtension_trans {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) (g : B ⟶ D)
    (hf : EssentialExtension f) (hg : EssentialExtension g) :
    EssentialExtension (f ≫ g) := by
  unfold EssentialExtension
  rcases hf with ⟨hf, hfe⟩
  rcases hg with ⟨hg, hge⟩
  letI := hf
  letI := hg
  refine ⟨inferInstance, ?_⟩
  intro P hP
  have hpull :
      (Subobject.mk g ⊓ P) =
        (Subobject.map g).obj ((Subobject.pullback g).obj P) := by
    exact Subobject.inf_eq_map_pullback' (MonoOver.mk g) P
  have hQ : (Subobject.pullback g).obj P ≠ (⊥ : Subobject B) := by
    intro hQ
    apply hge P hP
    rw [hpull, hQ, Subobject.map_bot]
  have hR : Subobject.mk f ⊓ (Subobject.pullback g).obj P ≠ (⊥ : Subobject B) :=
    hfe _ hQ
  have hmapR :
      (Subobject.map g).obj (Subobject.mk f ⊓ (Subobject.pullback g).obj P) ≠
        (⊥ : Subobject D) := by
    intro hzero
    apply hR
    have hzero' := congrArg (fun Q => (Subobject.pullback g).obj Q) hzero
    simpa only [Subobject.pullback_map_self, ← Subobject.map_bot g] using hzero'
  have hleComp :
      (Subobject.map g).obj (Subobject.mk f ⊓ (Subobject.pullback g).obj P) ≤
        Subobject.mk (f ≫ g) := by
    calc
      (Subobject.map g).obj (Subobject.mk f ⊓ (Subobject.pullback g).obj P) ≤
          (Subobject.map g).obj (Subobject.mk f) :=
        (Functor.monotone (Subobject.map g)) (Subobject.inf_le_left _ _)
      _ = Subobject.mk (f ≫ g) := by simp [Subobject.map_mk]
  have hleP :
      (Subobject.map g).obj (Subobject.mk f ⊓ (Subobject.pullback g).obj P) ≤ P := by
    calc
      (Subobject.map g).obj (Subobject.mk f ⊓ (Subobject.pullback g).obj P) ≤
          (Subobject.map g).obj ((Subobject.pullback g).obj P) :=
        (Functor.monotone (Subobject.map g)) (Subobject.inf_le_right _ _)
      _ = Subobject.mk g ⊓ P := hpull.symm
      _ ≤ P := Subobject.inf_le_right _ _
  have hle := Subobject.le_inf _ _ _ hleComp hleP
  intro hzero
  apply hmapR
  exact le_antisymm (hzero ▸ hle) bot_le

/-- Pulling an essential extension back along a monomorphism gives an
essential intersection extension. -/
noncomputable def essentialIntersectionArrow
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) [Mono f] (g : D ⟶ B) [Mono g] :
    ((Subobject.mk f ⊓ Subobject.mk g : Subobject B) : 𝒜) ⟶ D :=
  Subobject.ofLEMk (Subobject.mk f ⊓ Subobject.mk g) g (by simp)

/-- The intersection of an essential subobject with any subobject is
essential in that subobject. -/
theorem essentialExtension_intersection
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) [Mono f] (g : D ⟶ B) [Mono g]
    (hf : EssentialExtension f) :
    EssentialExtension (essentialIntersectionArrow f g) := by
  letI : Mono (essentialIntersectionArrow f g) := by
    dsimp [essentialIntersectionArrow]
    infer_instance
  have hle :
      Subobject.mk (essentialIntersectionArrow f g) ≤
        (Subobject.pullback g).obj (Subobject.mk f) := by
    apply Subobject.le_of_factors
    have hp : ((Subobject.pullback g).obj (Subobject.mk f)).Factors
        (essentialIntersectionArrow f g) :=
      CategoryTheory.Limits.pullback_factors g (Subobject.mk f)
        (essentialIntersectionArrow f g) (by
          simpa [essentialIntersectionArrow] using
            (Subobject.inf_arrow_factors_left (Subobject.mk f) (Subobject.mk g)))
    simpa only [Subobject.underlyingIso_hom_comp_eq_mk] using
      (Subobject.factors_of_factors_right (Subobject.underlyingIso
        (essentialIntersectionArrow f g)).hom hp)
  have hrev :
      (Subobject.pullback g).obj (Subobject.mk f) ≤
        Subobject.mk (essentialIntersectionArrow f g) := by
    apply Subobject.le_of_factors
    rw [Subobject.mk_factors_iff]
    let p := (Subobject.pullback g).obj (Subobject.mk f)
    have hFf : (Subobject.mk f).Factors (p.arrow ≫ g) := by
      apply (CategoryTheory.Limits.pullback_factors_iff g (Subobject.mk f) p.arrow).mp
      exact Subobject.factors_self p
    have hFg : (Subobject.mk g).Factors (p.arrow ≫ g) := by
      exact ⟨p.arrow, rfl⟩
    have hFi : ((Subobject.mk f) ⊓ (Subobject.mk g)).Factors (p.arrow ≫ g) :=
      (Subobject.inf_factors (p.arrow ≫ g)).2 ⟨hFf, hFg⟩
    let q := ((Subobject.mk f) ⊓ (Subobject.mk g)).factorThru (p.arrow ≫ g) hFi
    have hq : q ≫ essentialIntersectionArrow f g = p.arrow := by
      apply (cancel_mono g).1
      dsimp [q, essentialIntersectionArrow]
      simp [Subobject.factorThru_arrow]
    refine ⟨q, ?_⟩
    change q ≫ essentialIntersectionArrow f g = p.arrow
    exact hq
  have hmk :
      Subobject.mk (essentialIntersectionArrow f g) =
        (Subobject.pullback g).obj (Subobject.mk f) :=
    le_antisymm hle hrev
  unfold EssentialExtension at hf ⊢
  rcases hf with ⟨hf, hfe⟩
  letI := hf
  refine ⟨inferInstance, ?_⟩
  intro P hP
  have hmapg : (Subobject.map g).obj P ≤ Subobject.mk g := by
    induction P using Subobject.ind with
    | _ p =>
      rw [Subobject.map_mk]
      apply Subobject.mk_le_mk_of_comm p
      simp
  have hPmap : (Subobject.map g).obj P ≠ (⊥ : Subobject B) := by
    intro hbot
    apply hP
    calc
      P = (Subobject.pullback g).obj ((Subobject.map g).obj P) :=
        (Subobject.pullback_map_self g P).symm
      _ = (Subobject.pullback g).obj (⊥ : Subobject B) := congrArg _ hbot
      _ = (⊥ : Subobject D) := by
        rw [← Subobject.pullback_map_self g (⊥ : Subobject D), Subobject.map_bot]
  have hR : Subobject.mk f ⊓ (Subobject.map g).obj P ≠ (⊥ : Subobject B) :=
    hfe _ hPmap
  have hRle : Subobject.mk f ⊓ (Subobject.map g).obj P ≤ Subobject.mk g :=
    (Subobject.inf_le_right _ _).trans hmapg
  let R : Subobject B := Subobject.mk f ⊓ (Subobject.map g).obj P
  have hmapR : (Subobject.map g).obj ((Subobject.pullback g).obj R) = R := by
    calc
      (Subobject.map g).obj ((Subobject.pullback g).obj R) = Subobject.mk g ⊓ R := by
        exact (Subobject.inf_eq_map_pullback' (MonoOver.mk g) R).symm
      _ = R := by
        apply inf_eq_right.mpr
        exact hRle
  have hmapR' :
      (Subobject.map g).obj ((Subobject.pullback g).obj
        (Subobject.mk f ⊓ (Subobject.map g).obj P)) =
        Subobject.mk f ⊓ (Subobject.map g).obj P := by
    simpa only [R] using hmapR
  intro hzero
  have hpullzero :
      (Subobject.pullback g).obj
          (Subobject.mk f ⊓ (Subobject.map g).obj P) = (⊥ : Subobject D) := by
    rw [Subobject.inf_pullback, Subobject.pullback_map_self, ← hmk, hzero]
  apply hR
  rw [← hmapR', hpullzero, Subobject.map_bot]

/-- Essential surjections are closed under composition. -/
theorem essentialSurjection_comp {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) (g : B ⟶ D)
    (hf : EssentialSurjection f) (hg : EssentialSurjection g) :
    EssentialSurjection (f ≫ g) := by
  rcases hf with ⟨hf, hfess⟩
  rcases hg with ⟨hg, hgess⟩
  constructor
  · infer_instance
  · intro P hP
    have hQ : (Subobject.«exists» f).obj P ≠ (⊤ : Subobject B) := hfess P hP
    have hR : (Subobject.«exists» g).obj ((Subobject.«exists» f).obj P) ≠
        (⊤ : Subobject D) := hgess _ hQ
    intro hzero
    apply hR
    apply top_unique
    have hle :
        (Subobject.«exists» (f ≫ g)).obj P ≤
          (Subobject.«exists» g).obj ((Subobject.«exists» f).obj P) := by
      let Ff := Subobject.imageFactorisation f P
      let Fg := Subobject.imageFactorisation g ((Subobject.«exists» f).obj P)
      let Fc := Subobject.imageFactorisation (f ≫ g) P
      have hIf : Ff.F.I = ((Subobject.«exists» f).obj P : 𝒜) := rfl
      have hIg : Fg.F.I =
          ((Subobject.«exists» g).obj ((Subobject.«exists» f).obj P) : 𝒜) := rfl
      let F' : MonoFactorisation (P.arrow ≫ f ≫ g) :=
        { I := ((Subobject.«exists» g).obj ((Subobject.«exists» f).obj P) : 𝒜)
          m := ((Subobject.«exists» g).obj ((Subobject.«exists» f).obj P)).arrow
          m_mono := inferInstance
          e := Ff.F.e ≫ eqToHom hIf ≫ Fg.F.e ≫ eqToHom hIg
          fac := by
            have hmf : Ff.F.m = ((Subobject.«exists» f).obj P).arrow := by
              exact Subobject.imageFactorisation_F_m f P
            have hmg : Fg.F.m =
                ((Subobject.«exists» g).obj ((Subobject.«exists» f).obj P)).arrow := by
              exact Subobject.imageFactorisation_F_m g ((Subobject.«exists» f).obj P)
            have hIfcomp : eqToHom hIf ≫ ((Subobject.«exists» f).obj P).arrow = Ff.F.m := by
              rw [eqToHom_comp_iff]
              exact hmf.symm.trans (eq_of_heq (eqToHom_comp_heq Ff.F.m hIf.symm).symm)
            have hIgcomp : eqToHom hIg ≫
                ((Subobject.«exists» g).obj ((Subobject.«exists» f).obj P)).arrow = Fg.F.m := by
              rw [eqToHom_comp_iff]
              exact hmg.symm.trans (eq_of_heq (eqToHom_comp_heq Fg.F.m hIg.symm).symm)
            calc
              (Ff.F.e ≫ eqToHom hIf ≫ Fg.F.e ≫ eqToHom hIg) ≫
                  ((Subobject.«exists» g).obj ((Subobject.«exists» f).obj P)).arrow =
                  Ff.F.e ≫ eqToHom hIf ≫ (Fg.F.e ≫ Fg.F.m) := by
                    simp only [Category.assoc]
                    rw [hIgcomp]
              _ = Ff.F.e ≫
                  eqToHom hIf ≫ (((Subobject.«exists» f).obj P).arrow ≫ g) := by
                    rw [Fg.F.fac]
              _ = Ff.F.e ≫ Ff.F.m ≫ g := by
                    rw [← Category.assoc (eqToHom hIf)
                      ((Subobject.«exists» f).obj P).arrow g, hIfcomp]
              _ = P.arrow ≫ f ≫ g := by
                simp only [← Category.assoc, Ff.F.fac] }
      let q := Fc.isImage.lift F'
      refine Subobject.le_of_comm q ?_
      dsimp [q]
      change Fc.isImage.lift F' ≫ F'.m = Fc.F.m
      exact Fc.isImage.lift_fac F'
    calc
      (⊤ : Subobject D) = (Subobject.«exists» (f ≫ g)).obj P := hzero.symm
      _ ≤ (Subobject.«exists» g).obj ((Subobject.«exists» f).obj P) := hle

/-! The quotient appearing in the fourth assertion. -/

/-- The quotient of `B` by the image of the kernel of `g` under `f`.
The cokernel of the displayed composite is canonically the quotient by that
image. -/
abbrev quotientByImageOfKernel
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) (g : A ⟶ D) : 𝒜 :=
  cokernel (kernel.ι g ≫ f)

/-- The quotient projection `B → B / f(ker(g))`. -/
noncomputable def quotientByImageOfKernelProjection
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) (g : A ⟶ D) :
    B ⟶ quotientByImageOfKernel f g :=
  cokernel.π (kernel.ι g ≫ f)

/-- The map induced from `g : A → D` to the quotient by `f(ker(g))`. -/
noncomputable def essentialQuotientMap
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) (g : A ⟶ D) [Epi g] :
    D ⟶ quotientByImageOfKernel f g :=
  Abelian.epiDesc g (f ≫ quotientByImageOfKernelProjection f g) (by
    dsimp [quotientByImageOfKernelProjection]
    simpa only [Category.assoc] using (cokernel.condition (kernel.ι g ≫ f)))

/-- The quotient map in the fourth assertion of the source's lemma is an
essential surjection. -/
theorem essentialSurjection_quotient
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) (g : A ⟶ D)
    (hf : EssentialSurjection f) [Epi g] :
    EssentialSurjection (essentialQuotientMap f g) := by
  rcases hf with ⟨hf, hfess⟩
  let e := essentialQuotientMap f g
  let q := quotientByImageOfKernelProjection f g
  letI : Epi q := by
    dsimp [q, quotientByImageOfKernelProjection]
    infer_instance
  have heq : g ≫ e = f ≫ q := by
    dsimp [e, essentialQuotientMap, q]
    exact Abelian.comp_epiDesc g (f ≫ cokernel.π (kernel.ι g ≫ f)) _
  haveI : Epi e := by
    haveI : Epi (f ≫ q) := by infer_instance
    haveI : Epi (g ≫ e) := by rw [heq]; infer_instance
    exact epi_of_epi g e
  constructor
  · infer_instance
  · intro P hP
    let Q : Subobject A := (Subobject.pullback g).obj P
    let a := Subobject.pullbackπ g P
    have hcond : a ≫ P.arrow = Q.arrow ≫ g := by
      dsimp [a, Q]
      exact (Subobject.isPullback g P).w
    haveI : Epi a := by
      dsimp [a]
      exact Abelian.epi_fst_of_isLimit P.arrow g (Subobject.isPullback g P).isLimit
    have hQ : Q ≠ (⊤ : Subobject A) := by
      intro hQ
      apply hP
      letI : IsIso Q.arrow := (Subobject.isIso_arrow_iff_eq_top Q).2 hQ
      haveI : Epi (Q.arrow ≫ g) := inferInstance
      haveI : Epi (a ≫ P.arrow) := by
        rw [hcond]
        infer_instance
      haveI : Epi P.arrow :=
        epi_of_epi_fac (f := a) (g := P.arrow) (h := a ≫ P.arrow) rfl
      haveI : IsIso P.arrow := isIso_of_mono_of_epi _
      exact (Subobject.isIso_arrow_iff_eq_top P).mp inferInstance
    intro hzero
    have hpe : Epi (P.arrow ≫ e) := by
      let Fx := Subobject.imageFactorisation e P
      have hmx : Fx.F.m = ((Subobject.«exists» e).obj P).arrow := by
        exact Subobject.imageFactorisation_F_m e P
      have htop : Subobject.mk Fx.F.m = (⊤ : Subobject (quotientByImageOfKernel f g)) := by
        have hmk : Subobject.mk Fx.F.m =
            Subobject.mk ((Subobject.«exists» e).obj P).arrow := by
          apply Subobject.mk_eq_mk_of_comm Fx.F.m
            ((Subobject.«exists» e).obj P).arrow (Iso.refl _)
          change (𝟙 _ ≫ ((Subobject.«exists» e).obj P).arrow) = Fx.F.m
          rw [Category.id_comp]
          exact hmx.symm
        rw [hmk, Subobject.mk_arrow, hzero]
      haveI : IsIso Fx.F.m := (Subobject.isIso_iff_mk_eq_top _).2 htop
      haveI : Epi Fx.F.e := by
        have h := IsImage.e_isoExt_hom
          (Abelian.imageStrongEpiMonoFactorisation (P.arrow ≫ e)).toMonoIsImage
          Fx.isImage
        rw [← h]
        infer_instance
      rw [← Fx.F.fac]
      infer_instance
    have hrel : Q.arrow ≫ f ≫ q = a ≫ (P.arrow ≫ e) := by
      rw [← heq, ← Category.assoc Q.arrow g e, ← hcond]
      exact Category.assoc _ _ _
    haveI : Epi (Q.arrow ≫ f ≫ q) := by
      rw [hrel]
      infer_instance
    have hQf : Epi (Q.arrow ≫ f) := by
      apply Preadditive.epi_of_cancel_zero
      intro Z d hd
      let k := kernel.ι g ≫ f
      have hk : k ≫ d = 0 := by
        let l := (Subobject.isPullback g P).lift (0 : kernel g ⟶ (P : 𝒜))
          (kernel.ι g) (by simp)
        have hl : l ≫ Q.arrow = kernel.ι g := by
          dsimp [l, Q]
          simp
        dsimp [k]
        calc
          k ≫ d = (l ≫ Q.arrow) ≫ f ≫ d := by
            change (kernel.ι g ≫ f) ≫ d = (l ≫ Q.arrow) ≫ f ≫ d
            simpa only [Category.assoc] using
              (congrArg (fun x => x ≫ f ≫ d) hl).symm
          _ = l ≫ ((Q.arrow ≫ f) ≫ d) := by simp only [Category.assoc]
          _ = 0 := by rw [hd, comp_zero]
      let l := cokernel.desc (kernel.ι g ≫ f) d (by simpa [k] using hk)
      have hld : q ≫ l = d := by
        dsimp [l, q, quotientByImageOfKernelProjection, quotientByImageOfKernel]
        exact cokernel.π_desc _ _ _
      have hlzero : l = 0 := by
        apply zero_of_epi_comp (Q.arrow ≫ f ≫ q)
        have h' : (Q.arrow ≫ f) ≫ (q ≫ l) = 0 := by
          rw [hld, hd]
        simpa [Category.assoc] using h'
      rw [← hld, hlzero, comp_zero]
    have htop : (Subobject.«exists» f).obj Q = (⊤ : Subobject B) := by
      let Fq := Subobject.imageFactorisation f Q
      haveI : Epi (Fq.F.e ≫ Fq.F.m) := by
        rw [Fq.F.fac]
        infer_instance
      haveI : Epi Fq.F.m := epi_of_epi Fq.F.e Fq.F.m
      haveI : IsIso Fq.F.m := isIso_of_mono_of_epi _
      have hm : Subobject.mk Fq.F.m = (⊤ : Subobject B) :=
        (Subobject.isIso_iff_mk_eq_top _).mp inferInstance
      have hmf : Fq.F.m = ((Subobject.«exists» f).obj Q).arrow := by
        exact Subobject.imageFactorisation_F_m f Q
      have hmk : Subobject.mk Fq.F.m =
          Subobject.mk ((Subobject.«exists» f).obj Q).arrow := by
        apply Subobject.mk_eq_mk_of_comm Fq.F.m
          ((Subobject.«exists» f).obj Q).arrow (Iso.refl _)
        change (𝟙 _ ≫ ((Subobject.«exists» f).obj Q).arrow) = Fq.F.m
        rw [Category.id_comp]
        exact hmf.symm
      rw [hmk, Subobject.mk_arrow] at hm
      exact hm
    exact hfess Q hQ htop

/-! ## Filtered unions of essential extensions -/

/-- A compatible system of essential injections from `M` into a filtered
diagram of modules. -/
def CompatibleEssentialSystem
    {R : Type u} [Ring R] {I : Type v} [SmallCategory I] [IsFiltered I]
    (M : ModuleCat.{w} R) (F : I ⥤ ModuleCat.{w} R)
    (u : ∀ i : I, M ⟶ F.obj i) : Prop :=
  (∀ i : I, EssentialExtension (u i)) ∧
    ∀ {i j : I} (f : i ⟶ j), u i ≫ F.map f = u j

/-- The map from `M` to a chosen filtered-colimit cocone point induced by a
compatible system. -/
noncomputable def filteredColimitMap
    {R : Type u} [Ring R] {I : Type v} [SmallCategory I] [IsFiltered I]
    (M : ModuleCat.{w} R) (F : I ⥤ ModuleCat.{w} R)
    (t : Cocone F) (u : ∀ i : I, M ⟶ F.obj i) : M ⟶ t.pt :=
  let i : I := IsFiltered.nonempty.some
  u i ≫ t.ι.app i

/-- Every stage gives the same map to the filtered-colimit cocone point. -/
theorem filteredColimitMap_eq
    {R : Type u} [Ring R] {I : Type v} [SmallCategory I] [IsFiltered I]
    (M : ModuleCat.{w} R) (F : I ⥤ ModuleCat.{w} R)
    (t : Cocone F) (u : ∀ i : I, M ⟶ F.obj i)
    (hu : CompatibleEssentialSystem M F u) (i : I) :
    u i ≫ t.ι.app i = filteredColimitMap M F t u := by
  dsimp [filteredColimitMap]
  let j : I := IsFiltered.nonempty.some
  let k : I := IsFiltered.max i j
  let fi : i ⟶ k := IsFiltered.leftToMax i j
  let fj : j ⟶ k := IsFiltered.rightToMax i j
  calc
    u i ≫ t.ι.app i = u i ≫ (F.map fi ≫ t.ι.app k) := by rw [t.w fi]
    _ = (u i ≫ F.map fi) ≫ t.ι.app k := by simp only [Category.assoc]
    _ = u k ≫ t.ι.app k := by rw [hu.2 fi]
    _ = (u j ≫ F.map fj) ≫ t.ι.app k := by rw [hu.2 fj]
    _ = u j ≫ (F.map fj ≫ t.ι.app k) := by simp only [Category.assoc]
    _ = u j ≫ t.ι.app j := by rw [t.w fj]

/-- A filtered colimit of a compatible system of essential extensions is an
essential extension. -/
theorem essentialExtension_filteredColimit
    {R : Type u} [Ring R] {I : Type v} [SmallCategory I] [IsFiltered I]
    (M : ModuleCat.{w} R) (F : I ⥤ ModuleCat.{w} R)
    (t : Cocone F) (ht : IsColimit t) (u : ∀ i : I, M ⟶ F.obj i)
    (hu : CompatibleEssentialSystem M F u) :
    EssentialExtension (filteredColimitMap M F t u) := by
  sorry

/-! ## The module criterion -/

/-- A submodule is essential in a module when it meets every nonzero
submodule nontrivially.  This is the module realization of an essential
extension `S ↪ N`. -/
def EssentialSubmodule {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    (S : Submodule R N) : Prop :=
  ∀ T : Submodule R N, T ≠ ⊥ → S ⊓ T ≠ ⊥

/-- The submodule formulation agrees with the categorical essential
extension predicate through the canonical `ModuleCat` subobject API. -/
theorem essentialSubmodule_iff_essentialExtension
    {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    (S : Submodule R N) :
    EssentialSubmodule S ↔
      EssentialExtension (ModuleCat.ofHom S.subtype) := by
  haveI : Mono (ModuleCat.ofHom S.subtype) :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  let e := ModuleCat.subobjectModule (ModuleCat.of R N)
  have hS : e (Subobject.mk (ModuleCat.ofHom S.subtype)) = S := by
    change e (e.symm S) = S
    exact e.apply_symm_apply S
  constructor
  · intro h
    unfold EssentialExtension
    refine ⟨inferInstance, ?_⟩
    intro P hP
    have hP' : e P ≠ (⊥ : Submodule R N) := by
      intro hbot
      apply hP
      apply e.injective
      rw [hbot, e.map_bot]
    intro hbot
    apply h (e P) hP'
    rw [← hS, ← e.map_inf, hbot, e.map_bot]
  · intro h
    unfold EssentialExtension at h
    obtain ⟨hf, hess⟩ := h
    haveI := hf
    unfold EssentialSubmodule
    intro T hT
    have hT' : e.symm T ≠ (⊥ : Subobject (ModuleCat.of R N)) := by
      intro hbot
      apply hT
      apply e.symm.injective
      rw [hbot, e.symm.map_bot]
    have hcat := hess (e.symm T) hT'
    intro hbot
    apply hcat
    apply e.injective
    rw [e.map_inf, hS, e.apply_symm_apply, hbot, e.map_bot]

/-- Elementwise characterization of an essential submodule. -/
theorem essentialSubmodule_iff_smul
    {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    (S : Submodule R N) :
    EssentialSubmodule S ↔
      ∀ x : N, x ≠ 0 → ∃ r : R, r • x ∈ S ∧ r • x ≠ 0 := by
  unfold EssentialSubmodule
  constructor
  · intro h x hx
    have hT : Submodule.span R ({x} : Set N) ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      exact ⟨x, Submodule.mem_span_singleton_self x, hx⟩
    obtain ⟨y, hy, hy0⟩ :=
      (S ⊓ Submodule.span R ({x} : Set N)).ne_bot_iff.mp (h _ hT)
    rw [Submodule.mem_inf] at hy
    have hyT := hy.2
    rw [Submodule.mem_span_singleton] at hyT
    obtain ⟨r, hyr⟩ := hyT
    subst y
    exact ⟨r, hy.1, hy0⟩
  · intro h T hT
    obtain ⟨x, hxT, hx0⟩ := T.ne_bot_iff.mp hT
    obtain ⟨r, hrs, hrs0⟩ := h x hx0
    rw [Submodule.ne_bot_iff]
    exact ⟨r • x, ⟨hrs, T.smul_mem r hxT⟩, hrs0⟩

end

end Formalization.Books.Dualizing.Unit02
