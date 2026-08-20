import Formalization.Books.Homology.Unit19.Filtrations.Pullbacks

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open scoped ZeroObject

universe v u

namespace Formalization.Books.Homology.Unit19

/-! ## Associated graded objects -/

/-- The `p`th graded piece `F^p A / F^(p+1) A`. -/
def gradedPiece {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (p : ℤ) : C :=
  cokernel (Subobject.ofLE (A.filtration.obj (p + 1)) (A.filtration.obj p)
    (A.filtration.antitone (by omega)))

def gradedPieceπ {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (p : ℤ) :
    (A.filtration.obj p : C) ⟶ gradedPiece A p :=
  cokernel.π _

noncomputable def gradedPieceMap {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    gradedPiece A p ⟶ gradedPiece B p := by
  let a : (A.filtration.obj (p + 1) : C) ⟶ (A.filtration.obj p : C) :=
    Subobject.ofLE (A.filtration.obj (p + 1)) (A.filtration.obj p)
      (A.filtration.antitone (by omega))
  let b : (B.filtration.obj (p + 1) : C) ⟶ (B.filtration.obj p : C) :=
    Subobject.ofLE (B.filtration.obj (p + 1)) (B.filtration.obj p)
      (B.filtration.antitone (by omega))
  let u : (A.filtration.obj p : C) ⟶ (B.filtration.obj p : C) :=
    (B.filtration.obj p).factorThru
      ((A.filtration.obj p).arrow ≫ f.hom) (f.map_filtration p)
  change cokernel a ⟶ cokernel b
  refine cokernel.desc a (u ≫ cokernel.π b) ?_
  let v : (A.filtration.obj (p + 1) : C) ⟶
      (B.filtration.obj (p + 1) : C) :=
    (B.filtration.obj (p + 1)).factorThru
      ((A.filtration.obj (p + 1)).arrow ≫ f.hom)
      (f.map_filtration (p + 1))
  have huv : a ≫ u = v ≫ b := by
    apply (cancel_mono (B.filtration.obj p).arrow).mp
    dsimp [a, b, u, v]
    simp [Category.assoc]
  rw [← Category.assoc, huv, Category.assoc, cokernel.condition, comp_zero]

theorem gradedPiece_map_id {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (p : ℤ) :
    gradedPieceMap (𝟙 A) p = 𝟙 (gradedPiece A p) := by
  let : Epi (gradedPieceπ A p) := by
    change Epi (cokernel.π _)
    infer_instance
  apply (cancel_epi (gradedPieceπ A p)).mp
  simp only [Category.comp_id]
  dsimp [gradedPieceMap, gradedPieceπ]
  change cokernel.π _ ≫ cokernel.desc _ _ _ = cokernel.π _
  simp

theorem gradedPiece_map_comp {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D) (p : ℤ) :
    gradedPieceMap (f ≫ g) p = gradedPieceMap f p ≫ gradedPieceMap g p := by
  have hπ {E F : FilteredObject C} (h : E ⟶ F) :
      gradedPieceπ E p ≫ gradedPieceMap h p =
        (F.filtration.obj p).factorThru
            ((E.filtration.obj p).arrow ≫ h.hom) (h.map_filtration p) ≫
          gradedPieceπ F p := by
    dsimp [gradedPieceMap, gradedPieceπ]
    change cokernel.π _ ≫ cokernel.desc _ _ _ = _ ≫ cokernel.π _
    simp
  have hfg :
      (D.filtration.obj p).factorThru
          ((A.filtration.obj p).arrow ≫ (f ≫ g).hom)
          ((f ≫ g).map_filtration p) =
        (B.filtration.obj p).factorThru
            ((A.filtration.obj p).arrow ≫ f.hom) (f.map_filtration p) ≫
          (D.filtration.obj p).factorThru
            ((B.filtration.obj p).arrow ≫ g.hom) (g.map_filtration p) := by
    apply (cancel_mono (D.filtration.obj p).arrow).mp
    simp [Category.assoc]
  let : Epi (gradedPieceπ A p) := by
    change Epi (cokernel.π _)
    infer_instance
  apply (cancel_epi (gradedPieceπ A p)).mp
  calc
    gradedPieceπ A p ≫ gradedPieceMap (f ≫ g) p =
        (D.filtration.obj p).factorThru
            ((A.filtration.obj p).arrow ≫ (f ≫ g).hom)
            ((f ≫ g).map_filtration p) ≫ gradedPieceπ D p := hπ (f ≫ g)
    _ = ((B.filtration.obj p).factorThru
            ((A.filtration.obj p).arrow ≫ f.hom) (f.map_filtration p) ≫
          (D.filtration.obj p).factorThru
            ((B.filtration.obj p).arrow ≫ g.hom) (g.map_filtration p)) ≫
          gradedPieceπ D p := by rw [hfg]
    _ = (B.filtration.obj p).factorThru
            ((A.filtration.obj p).arrow ≫ f.hom) (f.map_filtration p) ≫
          (gradedPieceπ B p ≫ gradedPieceMap g p) := by rw [hπ g, Category.assoc]
    _ = (gradedPieceπ A p ≫ gradedPieceMap f p) ≫
          gradedPieceMap g p := by rw [hπ f, ← Category.assoc]
    _ = gradedPieceπ A p ≫ (gradedPieceMap f p ≫ gradedPieceMap g p) :=
      Category.assoc _ _ _

/-- The associated-graded-piece functor. -/
def gradedPieceFunctor {C : Type u} [Category.{v} C] [Abelian C] (p : ℤ) :
    FilteredObject C ⥤ C where
  obj A := gradedPiece A p
  map f := gradedPieceMap (C := C) f p
  map_id := by
    intro A
    exact gradedPiece_map_id A p
  map_comp := by
    intro A B D f g
    exact gradedPiece_map_comp f g p

theorem gradedPieceFunctor_is_additive {C : Type u} [Category.{v} C] [Abelian C]
    (p : ℤ) :
    (gradedPieceFunctor (C := C) p).Additive := by
  constructor
  intro A B f g
  have hπ {E F : FilteredObject C} (h : E ⟶ F) :
      gradedPieceπ E p ≫ gradedPieceMap h p =
        (F.filtration.obj p).factorThru
            ((E.filtration.obj p).arrow ≫ h.hom) (h.map_filtration p) ≫
          gradedPieceπ F p := by
    dsimp [gradedPieceMap, gradedPieceπ]
    change cokernel.π _ ≫ cokernel.desc _ _ _ = _ ≫ cokernel.π _
    simp
  have hadd :
      (B.filtration.obj p).factorThru
          ((A.filtration.obj p).arrow ≫ (f + g).hom)
          ((f + g).map_filtration p) =
        (B.filtration.obj p).factorThru
            ((A.filtration.obj p).arrow ≫ f.hom) (f.map_filtration p) +
          (B.filtration.obj p).factorThru
            ((A.filtration.obj p).arrow ≫ g.hom) (g.map_filtration p) := by
    apply (cancel_mono (B.filtration.obj p).arrow).mp
    simp only [Subobject.factorThru_arrow, Preadditive.add_comp]
    change (A.filtration.obj p).arrow ≫ (f.hom + g.hom) = _
    simp [Preadditive.comp_add]
  let : Epi (gradedPieceπ A p) := by
    change Epi (cokernel.π _)
    infer_instance
  apply (cancel_epi (gradedPieceπ A p)).mp
  calc
    gradedPieceπ A p ≫ gradedPieceMap (f + g) p =
        (B.filtration.obj p).factorThru
            ((A.filtration.obj p).arrow ≫ (f + g).hom)
            ((f + g).map_filtration p) ≫ gradedPieceπ B p := hπ (f + g)
    _ = ((B.filtration.obj p).factorThru
            ((A.filtration.obj p).arrow ≫ f.hom) (f.map_filtration p) +
          (B.filtration.obj p).factorThru
            ((A.filtration.obj p).arrow ≫ g.hom) (g.map_filtration p)) ≫
          gradedPieceπ B p := by rw [hadd]
    _ = (B.filtration.obj p).factorThru
            ((A.filtration.obj p).arrow ≫ f.hom) (f.map_filtration p) ≫
          gradedPieceπ B p +
        (B.filtration.obj p).factorThru
            ((A.filtration.obj p).arrow ≫ g.hom) (g.map_filtration p) ≫
          gradedPieceπ B p := by rw [Preadditive.add_comp]
    _ = (gradedPieceπ A p ≫ gradedPieceMap f p) +
          (gradedPieceπ A p ≫ gradedPieceMap g p) := by rw [hπ f, hπ g]
    _ = gradedPieceπ A p ≫ (gradedPieceMap f p + gradedPieceMap g p) :=
      by rw [Preadditive.comp_add]

/-- The full associated graded functor, valued in Mathlib's graded objects. -/
def associatedGraded {C : Type u} [Category.{v} C] [Abelian C] :
    FilteredObject C ⥤ GradedObject ℤ C where
  obj A := fun p => gradedPiece A p
  map f := fun p => gradedPieceMap (C := C) f p
  map_id := by
    intro A
    apply GradedObject.hom_ext
    intro p
    exact gradedPiece_map_id A p
  map_comp := by
    intro A B D f g
    ext p
    exact gradedPiece_map_comp f g p

theorem associatedGraded_is_additive {C : Type u} [Category.{v} C] [Abelian C] :
    (associatedGraded (C := C)).Additive := by
  let e : GradedObject ℤ C ≌ (Discrete ℤ ⥤ C) :=
    piEquivalenceFunctorDiscrete ℤ C
  have he : e.functor.Additive :=
    e.fullyFaithfulFunctor.additive_ofFullyFaithful
  refine ⟨?_⟩
  intro A B f g
  apply e.fullyFaithfulFunctor.map_injective
  ext ⟨p⟩
  rw [he.map_add]
  change gradedPieceMap (f + g) p =
    gradedPieceMap f p + gradedPieceMap g p
  let : (gradedPieceFunctor (C := C) p).Additive :=
    gradedPieceFunctor_is_additive p
  exact Functor.map_add (F := gradedPieceFunctor (C := C) p) (f := f) (g := g)

theorem associatedGraded_piece {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (p : ℤ) :
    (associatedGraded (C := C)).obj A p = gradedPiece A p := rfl

theorem associatedGraded_direct_sum_description {C : Type u} [Category.{v} C]
    [Abelian C] [HasCountableCoproducts C] (A : FilteredObject C) :
    (Formalization.Books.Homology.Unit16.gradedTotal C).obj
        ((associatedGraded (C := C)).obj A) =
      ∐ fun p : ℤ => gradedPiece A p := rfl

def filteredCoimage {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) : FilteredObject C :=
  Abelian.coimage f

def filteredCoimageπ {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) : A ⟶ filteredCoimage f :=
  Abelian.coimage.π f

def filteredImage {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) : FilteredObject C :=
  Abelian.image f

def filteredImageι {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) : filteredImage f ⟶ B :=
  Abelian.image.ι f

/-! ### Exact sequences on associated graded pieces -/

def filteredSubobjectShortExact {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    ShortComplex C :=
  ShortComplex.mk
    (gradedPieceMap (C := C) (inducedFilteredHom A X) p)
    (gradedPieceMap (C := C)
      (quotientFilteredHom A (cokernel.π X.arrow)) p) (by
    rw [← gradedPiece_map_comp]
    have hzero :
        inducedFilteredHom A X ≫ quotientFilteredHom A (cokernel.π X.arrow) = 0 := by
      apply FilteredHom.ext _ _
      change X.arrow ≫ cokernel.π X.arrow = 0
      exact cokernel.condition _
    rw [hzero]
    let : (gradedPieceFunctor (C := C) p).Additive :=
      gradedPieceFunctor_is_additive p
    change (gradedPieceFunctor (C := C) p).map (0 :
      inducedFilteredObject A X ⟶ quotientFilteredObject A (cokernel.π X.arrow)) = 0
    exact Functor.map_zero (F := gradedPieceFunctor (C := C) p) _ _)

/-!
The proof is organized around the following diagram, where
\`Q = F^(p+1) A\` and \`P = F^p A\`:

\`\`\`
0 ──→ X ∩ Q ──→ Q ──→ im(Q → A/X) ──→ 0
      │          │            │
0 ──→ X ∩ P ──→ P ──→ im(P → A/X) ──→ 0
      │          │            │
0 ──→ grᵖ X  ──→ grᵖ A ──→ grᵖ(A/X) ──→ 0
\`\`\`

The first two rows are elementary pullback/image short exact sequences.
The bottom row is their componentwise cokernel.  A snake-lemma argument
then supplies its exactness.
-/

private noncomputable abbrev filteredSubobjectRow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier)
    (P : Subobject A.carrier) : ShortComplex C :=
  ShortComplex.mk
    (Subobject.pullbackπ X.arrow P)
    (Subobject.imageFactorisation (cokernel.π X.arrow) P).F.e
    (by
      apply (cancel_mono
        (Subobject.imageFactorisation (cokernel.π X.arrow) P).F.m).mp
      rw [Category.assoc,
        (Subobject.imageFactorisation (cokernel.π X.arrow) P).F.fac,
        zero_comp, ← Category.assoc, (Subobject.isPullback X.arrow P).w,
        Category.assoc, cokernel.condition, comp_zero])

private theorem imageFactorisation_e_epi
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : C} {f : U ⟶ V} (H : ImageFactorisation f) : Epi H.F.e := by
  constructor
  intro Z g h w
  let e' := equalizer.lift _ w
  let F' : MonoFactorisation f :=
    { I := equalizer g h
      m := equalizer.ι g h ≫ H.F.m
      m_mono := mono_comp _ _
      e := e'
      fac := by
        dsimp [e']
        rw [← Category.assoc, equalizer.lift_ι, H.F.fac] }
  let v := H.isImage.lift F'
  have hv₀ : v ≫ equalizer.ι g h ≫ H.F.m = H.F.m :=
    H.isImage.lift_fac F'
  have hv : v ≫ equalizer.ι g h = 𝟙 H.F.I := by
    apply (cancel_mono H.F.m).mp
    simpa only [Category.assoc, Category.comp_id, Category.id_comp] using hv₀
  calc
    g = 𝟙 _ ≫ g := by rw [Category.id_comp]
    _ = v ≫ equalizer.ι g h ≫ g := by rw [← hv, Category.assoc]
    _ = v ≫ equalizer.ι g h ≫ h := by rw [equalizer.condition]
    _ = 𝟙 _ ≫ h := by rw [← Category.assoc, hv]
    _ = h := by rw [Category.id_comp]

private noncomputable def filteredSubobjectRow_isKernel
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier)
    (P : Subobject A.carrier) :
    IsLimit (KernelFork.ofι (filteredSubobjectRow A X P).f
      (filteredSubobjectRow A X P).zero) := by
  let q : A.carrier ⟶ cokernel X.arrow := cokernel.π X.arrow
  let K := (Subobject.pullback X.arrow).obj P
  let H := Subobject.imageFactorisation q P
  let a := Subobject.pullbackπ X.arrow P
  let b := H.F.e
  have hX : IsLimit (KernelFork.ofι X.arrow (cokernel.condition X.arrow)) :=
    Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ q (cokernel.condition X.arrow))
      (cokernelIsCokernel X.arrow)
  have ha : Mono a := by
    constructor
    intro Z f g hfg
    apply (cancel_mono K.arrow).mp
    apply (cancel_mono X.arrow).mp
    have hw := (Subobject.isPullback X.arrow P).w
    calc
      (f ≫ K.arrow) ≫ X.arrow = f ≫ (K.arrow ≫ X.arrow) :=
        Category.assoc _ _ _
      _ = f ≫ (a ≫ P.arrow) := congrArg (fun z => f ≫ z) hw.symm
      _ = (f ≫ a) ≫ P.arrow := (Category.assoc _ _ _).symm
      _ = (g ≫ a) ≫ P.arrow := congrArg (fun z => z ≫ P.arrow) hfg
      _ = g ≫ (a ≫ P.arrow) := Category.assoc _ _ _
      _ = g ≫ (K.arrow ≫ X.arrow) := congrArg (fun z => g ≫ z) hw
      _ = (g ≫ K.arrow) ≫ X.arrow := (Category.assoc _ _ _).symm
  let _ : Mono a := ha
  change IsLimit (KernelFork.ofι a _)
  apply KernelFork.IsLimit.ofι'
  intro W k hk
  have hkq : (k ≫ P.arrow) ≫ q = 0 := by
    calc
      (k ≫ P.arrow) ≫ q = k ≫ (P.arrow ≫ q) := Category.assoc _ _ _
      _ = k ≫ (H.F.e ≫ H.F.m) := by rw [H.F.fac]
      _ = (k ≫ H.F.e) ≫ H.F.m := (Category.assoc _ _ _).symm
      _ = 0 := by rw [hk, zero_comp]
  let u := hX.lift (KernelFork.ofι (k ≫ P.arrow) hkq)
  have hu : u ≫ X.arrow = k ≫ P.arrow :=
    hX.fac (KernelFork.ofι (k ≫ P.arrow) hkq) WalkingParallelPair.zero
  let l := (Subobject.isPullback X.arrow P).lift k u hu.symm
  exact ⟨l, (Subobject.isPullback X.arrow P).lift_fst k u hu.symm⟩

private theorem filteredSubobjectRow_epi
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier)
    (P : Subobject A.carrier) : Epi (filteredSubobjectRow A X P).g := by
  exact imageFactorisation_e_epi
    (Subobject.imageFactorisation (cokernel.π X.arrow) P)

private theorem filteredSubobjectRow_shortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier)
    (P : Subobject A.carrier) :
    (filteredSubobjectRow A X P).ShortExact := by
  let hK := filteredSubobjectRow_isKernel A X P
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.exact_of_f_is_kernel _ hK
  · exact mono_of_isLimit_fork hK
  · exact filteredSubobjectRow_epi A X P

private noncomputable abbrev filteredSubobjectRowTransition
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    filteredSubobjectRow A X (A.filtration.obj (p + 1)) ⟶
      filteredSubobjectRow A X (A.filtration.obj p) := by
  let q := cokernel.π X.arrow
  let Q := A.filtration.obj (p + 1)
  let P := A.filtration.obj p
  have hQP : Q ≤ P := A.filtration.antitone (by omega)
  let Hq := Subobject.imageFactorisation q Q
  let Hp := Subobject.imageFactorisation q P
  let F' : MonoFactorisation (Q.arrow ≫ q) :=
    { I := Hp.F.I
      m := Hp.F.m
      m_mono := Hp.F.m_mono
      e := Subobject.ofLE Q P hQP ≫ Hp.F.e
      fac := by
        rw [Category.assoc, Hp.F.fac, ← Category.assoc, Subobject.ofLE_arrow] }
  exact
    { τ₁ := Subobject.ofLE
        ((Subobject.pullback X.arrow).obj Q)
        ((Subobject.pullback X.arrow).obj P)
        ((Subobject.pullback X.arrow).monotone hQP)
      τ₂ := Subobject.ofLE Q P hQP
      τ₃ := Hq.isImage.lift F'
      comm₁₂ := by
        apply (cancel_mono P.arrow).mp
        rw [Category.assoc, (Subobject.isPullback X.arrow P).w,
          ← Category.assoc, Subobject.ofLE_arrow,
          Category.assoc, Subobject.ofLE_arrow,
          (Subobject.isPullback X.arrow Q).w]
      comm₂₃ := by
        apply (cancel_mono Hp.F.m).mp
        simp only [Category.assoc]
        rw [Hp.F.fac, Hq.isImage.lift_fac F',
          ← Category.assoc, Subobject.ofLE_arrow, Hq.F.fac] }

private theorem filteredSubobjectRowTransition_image_fac
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectRowTransition A X p).τ₃ ≫
        (Subobject.imageFactorisation (cokernel.π X.arrow)
          (A.filtration.obj p)).F.m =
      (Subobject.imageFactorisation (cokernel.π X.arrow)
        (A.filtration.obj (p + 1))).F.m := by
  dsimp [filteredSubobjectRowTransition]
  exact (Subobject.imageFactorisation (cokernel.π X.arrow)
    (A.filtration.obj (p + 1))).isImage.lift_fac _

private theorem filteredSubobjectRowTransition_mono_τ₃
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    Mono (filteredSubobjectRowTransition A X p).τ₃ := by
  constructor
  intro Z a b hab
  apply (cancel_mono (Subobject.imageFactorisation (cokernel.π X.arrow)
    (A.filtration.obj (p + 1))).F.m).mp
  rw [← filteredSubobjectRowTransition_image_fac A X p]
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ (Subobject.imageFactorisation (cokernel.π X.arrow)
      (A.filtration.obj p)).F.m) hab

private theorem gradedPieceπ_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {E F : FilteredObject C} (h : E ⟶ F) (p : ℤ) :
    gradedPieceπ E p ≫ gradedPieceMap h p =
      (F.filtration.obj p).factorThru
          ((E.filtration.obj p).arrow ≫ h.hom) (h.map_filtration p) ≫
        gradedPieceπ F p := by
  dsimp [gradedPieceMap, gradedPieceπ]
  change cokernel.π _ ≫ cokernel.desc _ _ _ = _ ≫ cokernel.π _
  simp

private noncomputable abbrev filteredSubobjectInducedStepIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    ((inducedFilteredObject A X).filtration.obj p : C) ≅
      ((Subobject.pullback X.arrow).obj (A.filtration.obj p) : C) :=
  eqToIso rfl

private noncomputable abbrev filteredSubobjectQuotientStepIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p : C) ≅
      (Subobject.imageFactorisation (cokernel.π X.arrow)
        (A.filtration.obj p)).F.I :=
  eqToIso rfl

private theorem filteredSubobjectInducedStepIso_inv_comp_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectInducedStepIso A X p).inv ≫
        ((inducedFilteredObject A X).filtration.obj p).arrow =
      ((Subobject.pullback X.arrow).obj (A.filtration.obj p)).arrow := by
  dsimp [filteredSubobjectInducedStepIso, inducedFilteredObject, inducedFiltration]
  exact Subobject.arrow_congr
    ((Subobject.pullback X.arrow).obj (A.filtration.obj p))
    ((inducedFilteredObject A X).filtration.obj p) rfl

private theorem filteredSubobjectInducedStepIso_hom_comp_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectInducedStepIso A X p).hom ≫
        ((inducedFilteredObject A X).filtration.obj p).arrow =
      ((Subobject.pullback X.arrow).obj (A.filtration.obj p)).arrow := by
  dsimp [filteredSubobjectInducedStepIso, inducedFilteredObject, inducedFiltration]
  exact Subobject.arrow_congr
    ((inducedFilteredObject A X).filtration.obj p)
    ((Subobject.pullback X.arrow).obj (A.filtration.obj p)) rfl

private theorem filteredSubobjectInducedStepIso_hom_comp_pullback_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectInducedStepIso A X p).hom ≫
        ((Subobject.pullback X.arrow).obj (A.filtration.obj p)).arrow =
      ((inducedFilteredObject A X).filtration.obj p).arrow := by
  dsimp [filteredSubobjectInducedStepIso, inducedFilteredObject, inducedFiltration]
  exact Subobject.arrow_congr
    ((inducedFilteredObject A X).filtration.obj p)
    ((Subobject.pullback X.arrow).obj (A.filtration.obj p)) rfl

private theorem filteredSubobjectPullbackTransition_comp_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    ((Subobject.pullback X.arrow).obj (A.filtration.obj (p + 1))).ofLE
        ((Subobject.pullback X.arrow).obj (A.filtration.obj p))
        ((Subobject.pullback X.arrow).monotone
          (A.filtration.antitone (by omega))) ≫
      ((Subobject.pullback X.arrow).obj (A.filtration.obj p)).arrow =
    ((Subobject.pullback X.arrow).obj (A.filtration.obj (p + 1))).arrow :=
  Subobject.ofLE_arrow _

private theorem filteredSubobjectRowTransition_τ₁_comp_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectRowTransition A X p).τ₁ ≫
        ((Subobject.pullback X.arrow).obj (A.filtration.obj p)).arrow =
      ((Subobject.pullback X.arrow).obj (A.filtration.obj (p + 1))).arrow := by
  change
    ((Subobject.pullback X.arrow).obj (A.filtration.obj (p + 1))).ofLE
        ((Subobject.pullback X.arrow).obj (A.filtration.obj p))
        ((Subobject.pullback X.arrow).monotone
          (A.filtration.antitone (by omega))) ≫
      ((Subobject.pullback X.arrow).obj (A.filtration.obj p)).arrow = _
  exact filteredSubobjectPullbackTransition_comp_arrow A X p

private theorem filteredSubobjectInducedStepIso_transition_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectInducedStepIso A X (p + 1)).hom ≫
        (filteredSubobjectRowTransition A X p).τ₁ =
      Subobject.ofLE
          ((inducedFilteredObject A X).filtration.obj (p + 1))
          ((inducedFilteredObject A X).filtration.obj p)
          ((inducedFilteredObject A X).filtration.antitone (by omega)) ≫
        (filteredSubobjectInducedStepIso A X p).hom := by
  apply (cancel_mono
    ((Subobject.pullback X.arrow).obj (A.filtration.obj p)).arrow).mp
  rw [Category.assoc, filteredSubobjectRowTransition_τ₁_comp_arrow,
    filteredSubobjectInducedStepIso_hom_comp_pullback_arrow,
    Category.assoc,
    filteredSubobjectInducedStepIso_hom_comp_pullback_arrow]
  apply eq_of_heq
  exact (heq_of_eq (Subobject.ofLE_arrow _)).symm

private theorem filteredSubobjectInducedTransition_comp_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    Subobject.ofLE
        ((inducedFilteredObject A X).filtration.obj (p + 1))
        ((inducedFilteredObject A X).filtration.obj p)
        ((inducedFilteredObject A X).filtration.antitone (by omega)) ≫
      ((inducedFilteredObject A X).filtration.obj p).arrow =
    ((inducedFilteredObject A X).filtration.obj (p + 1)).arrow :=
  Subobject.ofLE_arrow _

private theorem filteredSubobjectRowTransition_τ₁_left_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (((filteredSubobjectRowTransition A X p).τ₁ ≫
        (filteredSubobjectInducedStepIso A X p).inv) ≫
      ((inducedFilteredObject A X).filtration.obj p).arrow) ≍
    ((Subobject.pullback X.arrow).obj (A.filtration.obj (p + 1))).arrow := by
  rw [Category.assoc]
  have htransport := heq_of_eq
    (filteredSubobjectInducedStepIso_inv_comp_arrow A X p)
  exact (heq_comp rfl rfl rfl (by rfl) htransport).trans
    (heq_of_eq (filteredSubobjectPullbackTransition_comp_arrow A X p))

private theorem filteredSubobjectRowTransition_τ₁_right_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (((filteredSubobjectInducedStepIso A X (p + 1)).hom ≫
        Subobject.ofLE
          ((inducedFilteredObject A X).filtration.obj (p + 1))
          ((inducedFilteredObject A X).filtration.obj p)
          ((inducedFilteredObject A X).filtration.antitone (by omega))) ≫
      ((inducedFilteredObject A X).filtration.obj p).arrow) ≍
    ((Subobject.pullback X.arrow).obj (A.filtration.obj (p + 1))).arrow := by
  have htransition :=
    (filteredSubobjectInducedTransition_comp_arrow A X p)
  have hcomp := congrArg
    (fun z => (filteredSubobjectInducedStepIso A X (p + 1)).hom ≫ z)
    htransition
  exact (heq_of_eq ((Category.assoc _ _ _).trans hcomp)).trans
    (heq_of_eq (filteredSubobjectInducedStepIso_hom_comp_arrow A X (p + 1)))

private theorem filteredSubobjectRowTransition_τ₁_transport
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectRowTransition A X p).τ₁ ≫
        (filteredSubobjectInducedStepIso A X p).inv =
      (filteredSubobjectInducedStepIso A X (p + 1)).hom ≫
        Subobject.ofLE
          ((inducedFilteredObject A X).filtration.obj (p + 1))
          ((inducedFilteredObject A X).filtration.obj p)
          ((inducedFilteredObject A X).filtration.antitone (by omega)) := by
  change
    ((Subobject.pullback X.arrow).obj (A.filtration.obj (p + 1))).ofLE
          ((Subobject.pullback X.arrow).obj (A.filtration.obj p))
          ((Subobject.pullback X.arrow).monotone
            (A.filtration.antitone (by omega))) ≫
        (filteredSubobjectInducedStepIso A X p).inv =
      (filteredSubobjectInducedStepIso A X (p + 1)).hom ≫
        Subobject.ofLE
          ((inducedFilteredObject A X).filtration.obj (p + 1))
          ((inducedFilteredObject A X).filtration.obj p)
          ((inducedFilteredObject A X).filtration.antitone (by omega))
  apply (cancel_mono
    ((inducedFilteredObject A X).filtration.obj p).arrow).mp
  apply eq_of_heq
  exact (filteredSubobjectRowTransition_τ₁_left_arrow A X p).trans
    (filteredSubobjectRowTransition_τ₁_right_arrow A X p).symm

private theorem filteredSubobjectInducedTransition_comp_gradedPieceπ
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    Subobject.ofLE
        ((inducedFilteredObject A X).filtration.obj (p + 1))
        ((inducedFilteredObject A X).filtration.obj p)
        ((inducedFilteredObject A X).filtration.antitone (by omega)) ≫
      gradedPieceπ (inducedFilteredObject A X) p = 0 := by
  change _ ≫ cokernel.π _ = 0
  exact cokernel.condition _

private theorem filteredSubobjectInducedTransition_fromIso_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    ((filteredSubobjectInducedStepIso A X (p + 1)).hom ≫
        Subobject.ofLE
          ((inducedFilteredObject A X).filtration.obj (p + 1))
          ((inducedFilteredObject A X).filtration.obj p)
          ((inducedFilteredObject A X).filtration.antitone (by omega))) ≫
      gradedPieceπ (inducedFilteredObject A X) p = 0 := by
  exact (Category.assoc _ _ _).trans
    ((congrArg
      (fun z => (filteredSubobjectInducedStepIso A X (p + 1)).hom ≫ z)
      (filteredSubobjectInducedTransition_comp_gradedPieceπ A X p)).trans comp_zero)

private theorem filteredSubobjectQuotientStepIso_inv_comp_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectQuotientStepIso A X p).inv ≫
        ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p).arrow ≍
      (Subobject.imageFactorisation (cokernel.π X.arrow)
        (A.filtration.obj p)).F.m := by
  have harrow :
      ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p).arrow ≍
        (Subobject.imageFactorisation (cokernel.π X.arrow)
          (A.filtration.obj p)).F.m := by
    rfl
  exact (eqToHom_comp_heq
    ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p).arrow
    (by rfl :
      ((Subobject.imageFactorisation (cokernel.π X.arrow)
        (A.filtration.obj p)).F.I : C) =
      ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p : C))).trans
    harrow

private theorem filteredSubobjectQuotientStepIso_hom_comp_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectQuotientStepIso A X p).hom ≫
        ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p).arrow ≍
      (Subobject.imageFactorisation (cokernel.π X.arrow)
        (A.filtration.obj p)).F.m := by
  have harrow :
      ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p).arrow ≍
        (Subobject.imageFactorisation (cokernel.π X.arrow)
          (A.filtration.obj p)).F.m := by
    rfl
  exact (eqToHom_comp_heq
    ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p).arrow
    (by rfl :
      ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p : C) =
      ((Subobject.imageFactorisation (cokernel.π X.arrow)
        (A.filtration.obj p)).F.I : C))).trans harrow

private theorem filteredSubobjectQuotientStepIso_hom_comp_image_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectQuotientStepIso A X p).hom ≫
        (Subobject.imageFactorisation (cokernel.π X.arrow)
          (A.filtration.obj p)).F.m ≍
      ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p).arrow := by
  have harrow :
      ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p).arrow ≍
        (Subobject.imageFactorisation (cokernel.π X.arrow)
          (A.filtration.obj p)).F.m := by
    rfl
  exact (eqToHom_comp_heq
    (Subobject.imageFactorisation (cokernel.π X.arrow)
      (A.filtration.obj p)).F.m
    (by rfl :
      ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p : C) =
      ((Subobject.imageFactorisation (cokernel.π X.arrow)
        (A.filtration.obj p)).F.I : C))).trans harrow.symm

private theorem filteredSubobjectQuotientTransition_comp_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    Subobject.ofLE
        ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj (p + 1))
        ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p)
        ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.antitone
          (by omega)) ≫
      ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p).arrow =
    ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj (p + 1)).arrow :=
  Subobject.ofLE_arrow _

private theorem filteredSubobjectQuotientStepIso_transition_left_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (((filteredSubobjectQuotientStepIso A X (p + 1)).hom ≫
        (filteredSubobjectRowTransition A X p).τ₃) ≫
      (Subobject.imageFactorisation (cokernel.π X.arrow)
        (A.filtration.obj p)).F.m) ≍
    ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj (p + 1)).arrow := by
  rw [Category.assoc, filteredSubobjectRowTransition_image_fac]
  exact filteredSubobjectQuotientStepIso_hom_comp_image_arrow A X (p + 1)

private theorem filteredSubobjectQuotientStepIso_transition_right_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (((Subobject.ofLE
        ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj (p + 1))
        ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p)
        ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.antitone
          (by omega)) ≫
      (filteredSubobjectQuotientStepIso A X p).hom) ≫
      (Subobject.imageFactorisation (cokernel.π X.arrow)
        (A.filtration.obj p)).F.m)) ≍
    ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj (p + 1)).arrow := by
  rw [Category.assoc]
  exact (heq_comp rfl rfl rfl (by rfl)
    (filteredSubobjectQuotientStepIso_hom_comp_image_arrow A X p)).trans
    (heq_of_eq (filteredSubobjectQuotientTransition_comp_arrow A X p))

private theorem filteredSubobjectQuotientStepIso_transition_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectQuotientStepIso A X (p + 1)).hom ≫
        (filteredSubobjectRowTransition A X p).τ₃ =
      Subobject.ofLE
          ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj (p + 1))
          ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p)
          ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.antitone
            (by omega)) ≫
        (filteredSubobjectQuotientStepIso A X p).hom := by
  apply (cancel_mono
    (Subobject.imageFactorisation (cokernel.π X.arrow)
      (A.filtration.obj p)).F.m).mp
  apply eq_of_heq
  exact (filteredSubobjectQuotientStepIso_transition_left_arrow A X p).trans
    (filteredSubobjectQuotientStepIso_transition_right_arrow A X p).symm

private theorem filteredSubobjectRowTransition_τ₃_left_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (((filteredSubobjectRowTransition A X p).τ₃ ≫
        (filteredSubobjectQuotientStepIso A X p).inv) ≫
      ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p).arrow) ≍
    (Subobject.imageFactorisation (cokernel.π X.arrow)
      (A.filtration.obj (p + 1))).F.m := by
  rw [Category.assoc]
  exact (heq_comp rfl rfl rfl (by rfl)
    (filteredSubobjectQuotientStepIso_inv_comp_arrow A X p)).trans
    (heq_of_eq (filteredSubobjectRowTransition_image_fac A X p))

private theorem filteredSubobjectRowTransition_τ₃_right_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (((filteredSubobjectQuotientStepIso A X (p + 1)).hom ≫
        Subobject.ofLE
          ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj (p + 1))
          ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p)
          ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.antitone
            (by omega))) ≫
      ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p).arrow) ≍
    (Subobject.imageFactorisation (cokernel.π X.arrow)
      (A.filtration.obj (p + 1))).F.m := by
  have htransition := filteredSubobjectQuotientTransition_comp_arrow A X p
  have hcomp := congrArg
    (fun z => (filteredSubobjectQuotientStepIso A X (p + 1)).hom ≫ z)
    htransition
  exact (heq_of_eq ((Category.assoc _ _ _).trans hcomp)).trans
    (filteredSubobjectQuotientStepIso_hom_comp_arrow A X (p + 1))

private theorem filteredSubobjectRowTransition_τ₃_transport
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectRowTransition A X p).τ₃ ≫
        (filteredSubobjectQuotientStepIso A X p).inv =
      (filteredSubobjectQuotientStepIso A X (p + 1)).hom ≫
        Subobject.ofLE
          ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj (p + 1))
          ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p)
          ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.antitone
            (by omega)) := by
  apply (cancel_mono
    ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p).arrow).mp
  apply eq_of_heq
  exact (filteredSubobjectRowTransition_τ₃_left_arrow A X p).trans
    (filteredSubobjectRowTransition_τ₃_right_arrow A X p).symm

private theorem filteredSubobjectQuotientTransition_comp_gradedPieceπ
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    Subobject.ofLE
        ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj (p + 1))
        ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p)
        ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.antitone
          (by omega)) ≫
      gradedPieceπ (quotientFilteredObject A (cokernel.π X.arrow)) p = 0 := by
  change _ ≫ cokernel.π _ = 0
  exact cokernel.condition _

private theorem filteredSubobjectQuotientTransition_fromIso_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    ((filteredSubobjectQuotientStepIso A X (p + 1)).hom ≫
        Subobject.ofLE
          ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj (p + 1))
          ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p)
          ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.antitone
            (by omega))) ≫
      gradedPieceπ (quotientFilteredObject A (cokernel.π X.arrow)) p = 0 := by
  exact (Category.assoc _ _ _).trans
    ((congrArg
      (fun z => (filteredSubobjectQuotientStepIso A X (p + 1)).hom ≫ z)
      (filteredSubobjectQuotientTransition_comp_gradedPieceπ A X p)).trans comp_zero)

private noncomputable abbrev filteredSubobjectRowComparison
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    filteredSubobjectRow A X (A.filtration.obj p) ⟶
      filteredSubobjectShortExact A X p := by
  let q := cokernel.π X.arrow
  let P := A.filtration.obj p
  let eX : ((inducedFilteredObject A X).filtration.obj p : C) =
      ((Subobject.pullback X.arrow).obj P : C) := rfl
  let eQ : ((quotientFilteredObject A q).filtration.obj p : C) =
      (Subobject.imageFactorisation q P).F.I := rfl
  exact
    { τ₁ := eqToHom eX.symm ≫ gradedPieceπ (inducedFilteredObject A X) p
      τ₂ := gradedPieceπ A p
      τ₃ := eqToHom eQ.symm ≫ gradedPieceπ (quotientFilteredObject A q) p
      comm₁₂ := by
        have hfactor :
            eqToHom eX.symm ≫
                (A.filtration.obj p).factorThru
                  (((inducedFilteredObject A X).filtration.obj p).arrow ≫
                    (inducedFilteredHom A X).hom)
                  ((inducedFilteredHom A X).map_filtration p) =
              Subobject.pullbackπ X.arrow P := by
          apply (cancel_mono (A.filtration.obj p).arrow).mp
          rw [Category.assoc, Subobject.factorThru_arrow]
          have htransport :
              eqToHom eX.symm ≫
                  (((inducedFilteredObject A X).filtration.obj p).arrow ≫
                    (inducedFilteredHom A X).hom) ≍
                ((Subobject.pullback X.arrow).obj P).arrow ≫ X.arrow := by
            simpa only [inducedFilteredObject, inducedFiltration,
              inducedFilteredHom] using
              (eqToHom_comp_heq
                (((inducedFilteredObject A X).filtration.obj p).arrow ≫
                  (inducedFilteredHom A X).hom) eX.symm)
          exact (eq_of_heq htransport).trans
            (Subobject.isPullback X.arrow P).w.symm
        dsimp only [filteredSubobjectShortExact]
        change (eqToHom eX.symm ≫
            gradedPieceπ (inducedFilteredObject A X) p) ≫
              gradedPieceMap (inducedFilteredHom A X) p =
          Subobject.pullbackπ X.arrow P ≫ gradedPieceπ A p
        rw [Category.assoc, gradedPieceπ_naturality,
          ← Category.assoc, hfactor]
      comm₂₃ := by
        have hfactor :
            ((quotientFilteredObject A q).filtration.obj p).factorThru
                ((A.filtration.obj p).arrow ≫
                  (quotientFilteredHom A q).hom)
                ((quotientFilteredHom A q).map_filtration p) =
              (Subobject.imageFactorisation q P).F.e ≫ eqToHom eQ.symm := by
          apply (cancel_mono
            ((quotientFilteredObject A q).filtration.obj p).arrow).mp
          rw [Subobject.factorThru_arrow]
          have htransport :
              (Subobject.imageFactorisation q P).F.e ≫ eqToHom eQ.symm ≫
                  ((quotientFilteredObject A q).filtration.obj p).arrow ≍
                (Subobject.imageFactorisation q P).F.e ≫
                  (Subobject.imageFactorisation q P).F.m := by
            have harrow :
                ((quotientFilteredObject A q).filtration.obj p).arrow ≍
                  (Subobject.imageFactorisation q P).F.m := by rfl
            have hmap :
                eqToHom eQ.symm ≫
                    ((quotientFilteredObject A q).filtration.obj p).arrow ≍
                  (Subobject.imageFactorisation q P).F.m :=
              (eqToHom_comp_heq
                ((quotientFilteredObject A q).filtration.obj p).arrow
                eQ.symm).trans harrow
            simpa only [Category.assoc] using
              heq_comp (f := (Subobject.imageFactorisation q P).F.e)
                (g := eqToHom eQ.symm ≫
                  ((quotientFilteredObject A q).filtration.obj p).arrow)
                (f' := (Subobject.imageFactorisation q P).F.e)
                (g' := (Subobject.imageFactorisation q P).F.m)
                rfl rfl rfl (by rfl) hmap
          change P.arrow ≫ q =
            ((Subobject.imageFactorisation q P).F.e ≫ eqToHom eQ.symm) ≫
              ((quotientFilteredObject A q).filtration.obj p).arrow
          simpa only [Category.assoc] using
            (Subobject.imageFactorisation q P).F.fac.symm.trans
              (eq_of_heq htransport).symm
        dsimp only [filteredSubobjectShortExact]
        change gradedPieceπ A p ≫
            gradedPieceMap (quotientFilteredHom A q) p =
          (Subobject.imageFactorisation q P).F.e ≫
            (eqToHom eQ.symm ≫
              gradedPieceπ (quotientFilteredObject A q) p)
        rw [gradedPieceπ_naturality]
        simp [hfactor, Category.assoc] }

private theorem filteredSubobjectRowComparison_τ₁_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectRowTransition A X p).τ₁ ≫
      (filteredSubobjectRowComparison A X p).τ₁ = 0 := by
  change (filteredSubobjectRowTransition A X p).τ₁ ≫
      (filteredSubobjectInducedStepIso A X p).inv ≫
        gradedPieceπ (inducedFilteredObject A X) p = 0
  rw [← Category.assoc, filteredSubobjectRowTransition_τ₁_transport]
  exact filteredSubobjectInducedTransition_fromIso_zero A X p

private theorem filteredSubobjectRowComparison_τ₂_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectRowTransition A X p).τ₂ ≫
      (filteredSubobjectRowComparison A X p).τ₂ = 0 := by
  change (A.filtration.obj (p + 1)).ofLE (A.filtration.obj p)
      (A.filtration.antitone (by omega)) ≫ gradedPieceπ A p = 0
  change _ ≫ cokernel.π _ = 0
  exact cokernel.condition _

private theorem filteredSubobjectRowComparison_τ₃_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectRowTransition A X p).τ₃ ≫
      (filteredSubobjectRowComparison A X p).τ₃ = 0 := by
  change (filteredSubobjectRowTransition A X p).τ₃ ≫
      (filteredSubobjectQuotientStepIso A X p).inv ≫
        gradedPieceπ (quotientFilteredObject A (cokernel.π X.arrow)) p = 0
  rw [← Category.assoc, filteredSubobjectRowTransition_τ₃_transport]
  exact filteredSubobjectQuotientTransition_fromIso_zero A X p

private theorem filteredSubobjectRowTransition_comp_comparison
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    filteredSubobjectRowTransition A X p ≫
      filteredSubobjectRowComparison A X p = 0 := by
  ext
  · exact filteredSubobjectRowComparison_τ₁_zero A X p
  · exact filteredSubobjectRowComparison_τ₂_zero A X p
  · exact filteredSubobjectRowComparison_τ₃_zero A X p

private theorem filteredSubobjectRowComparison_epi_τ₃
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    Epi (filteredSubobjectRowComparison A X p).τ₃ := by
  dsimp [filteredSubobjectRowComparison]
  apply epi_comp'
  · infer_instance
  · dsimp [gradedPieceπ]
    change Epi (cokernel.π _)
    infer_instance

private noncomputable abbrev filteredSubobjectComparisonCofork
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :=
  CokernelCofork.ofπ
    (filteredSubobjectRowComparison A X p)
    (filteredSubobjectRowTransition_comp_comparison A X p)

private noncomputable def filteredSubobjectComparisonCofork_isColimit_τ₁
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    IsColimit (ShortComplex.π₁.mapCocone
      (filteredSubobjectComparisonCofork A X p)) := by
  apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2
  refine Cofork.isColimitOfIsos
    (c := CokernelCofork.ofπ
      (f := Subobject.ofLE
        ((inducedFilteredObject A X).filtration.obj (p + 1))
        ((inducedFilteredObject A X).filtration.obj p)
        ((inducedFilteredObject A X).filtration.antitone (by omega)))
      (gradedPieceπ (inducedFilteredObject A X) p)
      (cokernel.condition _))
    (cokernelIsCokernel _)
    (c' := _)
    (filteredSubobjectInducedStepIso A X (p + 1))
    (filteredSubobjectInducedStepIso A X p)
    (Iso.refl _)
    (filteredSubobjectInducedStepIso_transition_naturality A X p)
    (by simp)
    (by
      change (filteredSubobjectInducedStepIso A X p).inv ≫
          gradedPieceπ (inducedFilteredObject A X) p ≫
            𝟙 (gradedPiece (inducedFilteredObject A X) p) =
        (filteredSubobjectRowComparison A X p).τ₁
      dsimp [filteredSubobjectRowComparison,
        filteredSubobjectInducedStepIso]
      rw [Category.comp_id]
      rfl)

private noncomputable def filteredSubobjectComparisonCofork_isColimit_τ₂
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    IsColimit (ShortComplex.π₂.mapCocone
      (filteredSubobjectComparisonCofork A X p)) := by
  apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2
  dsimp [filteredSubobjectComparisonCofork, filteredSubobjectRowComparison]
  exact cokernelIsCokernel _

private noncomputable def filteredSubobjectComparisonCofork_isColimit_τ₃
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    IsColimit (ShortComplex.π₃.mapCocone
      (filteredSubobjectComparisonCofork A X p)) := by
  apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2
  refine Cofork.isColimitOfIsos
    (c := CokernelCofork.ofπ
      (f := Subobject.ofLE
        ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj (p + 1))
        ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.obj p)
        ((quotientFilteredObject A (cokernel.π X.arrow)).filtration.antitone
          (by omega)))
      (gradedPieceπ (quotientFilteredObject A (cokernel.π X.arrow)) p)
      (cokernel.condition _))
    (cokernelIsCokernel _)
    (c' := _)
    (filteredSubobjectQuotientStepIso A X (p + 1))
    (filteredSubobjectQuotientStepIso A X p)
    (Iso.refl _)
    (filteredSubobjectQuotientStepIso_transition_naturality A X p)
    (by simp)
    (by
      change (filteredSubobjectQuotientStepIso A X p).inv ≫
          gradedPieceπ (quotientFilteredObject A (cokernel.π X.arrow)) p ≫
            𝟙 (gradedPiece
              (quotientFilteredObject A (cokernel.π X.arrow)) p) =
        (filteredSubobjectRowComparison A X p).τ₃
      dsimp [filteredSubobjectRowComparison,
        filteredSubobjectQuotientStepIso]
      rw [Category.comp_id]
      rfl)

private noncomputable def filteredSubobjectRowComparison_isCokernel
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    IsColimit (CokernelCofork.ofπ
      (filteredSubobjectRowComparison A X p)
      (filteredSubobjectRowTransition_comp_comparison A X p)) := by
  apply ShortComplex.isColimitOfIsColimitπ
  · exact filteredSubobjectComparisonCofork_isColimit_τ₁ A X p
  · exact filteredSubobjectComparisonCofork_isColimit_τ₂ A X p
  · exact filteredSubobjectComparisonCofork_isColimit_τ₃ A X p

private theorem shortExact_of_cokernel_between_shortExact_rows
    {C : Type u} [Category.{v} C] [Abelian C]
    {L₁ L₂ L₃ : ShortComplex C} (v : L₁ ⟶ L₂) (w : L₂ ⟶ L₃)
    (hvw : v ≫ w = 0) (h₁ : L₁.ShortExact) (h₂ : L₂.ShortExact)
    (hv₃ : Mono v.τ₃) (hw₃ : Epi w.τ₃)
    (h₃ : IsColimit (CokernelCofork.ofπ w hvw)) : L₃.ShortExact := by
  let S : ShortComplex.SnakeInput C :=
    { L₀ := kernel v
      L₁ := L₁
      L₂ := L₂
      L₃ := L₃
      v₀₁ := kernel.ι v
      v₁₂ := v
      v₂₃ := w
      h₀ := kernelIsKernel v
      h₃ := h₃
      L₁_exact := h₁.exact
      epi_L₁_g := h₁.epi_g
      L₂_exact := h₂.exact
      mono_L₂_f := h₂.mono_f }
  have hzero : IsZero S.L₀.X₃ := by
    let _ : Mono v.τ₃ := hv₃
    exact KernelFork.IsLimit.isZero_of_mono S.h₀τ₃
  have hδ : S.δ = 0 := hzero.eq_of_src _ _
  have hmono : Mono S.L₃.f := by
    exact (S.L₂'.exact_iff_mono hδ).1 S.L₂'_exact
  have hepi : Epi S.L₃.g := by
    let _ : Epi w.τ₃ := hw₃
    have hcomp : Epi (L₂.g ≫ w.τ₃) := by
      let _ := h₂.epi_g
      infer_instance
    rw [← w.comm₂₃] at hcomp
    exact epi_of_epi w.τ₂ L₃.g
  exact ShortComplex.ShortExact.mk' S.L₃_exact hmono hepi

theorem graded_piece_subobject_short_exact {C : Type u} [Category.{v} C]
    [Abelian C] (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectShortExact A X p).ShortExact := by
  exact shortExact_of_cokernel_between_shortExact_rows
    (filteredSubobjectRowTransition A X p)
    (filteredSubobjectRowComparison A X p)
    (filteredSubobjectRowTransition_comp_comparison A X p)
    (filteredSubobjectRow_shortExact A X (A.filtration.obj (p + 1)))
    (filteredSubobjectRow_shortExact A X (A.filtration.obj p))
    (filteredSubobjectRowTransition_mono_τ₃ A X p)
    (filteredSubobjectRowComparison_epi_τ₃ A X p)
    (filteredSubobjectRowComparison_isCokernel A X p)


def filteredKernelCoimageGradedShortComplex {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk
    (gradedPieceMap (C := C) (filteredKernelι f) p)
    (gradedPieceMap (C := C) (filteredCoimageπ f) p) (by
      rw [← gradedPiece_map_comp]
      have hzero : filteredKernelι f ≫ filteredCoimageπ f = 0 := by
        let k := (kernelIsKernel f).lift
          (KernelFork.ofι (filteredKernelι f) (filteredKernelι_comp f))
        have hk : k ≫ kernel.ι f = filteredKernelι f :=
          (kernelIsKernel f).fac
            (KernelFork.ofι (filteredKernelι f) (filteredKernelι_comp f))
            WalkingParallelPair.zero
        rw [← hk]
        dsimp [filteredCoimageπ, filteredCoimage]
        rw [Category.assoc, cokernel.condition, comp_zero]
        rfl
      rw [hzero]
      let : (gradedPieceFunctor (C := C) p).Additive :=
        gradedPieceFunctor_is_additive p
      change (gradedPieceFunctor (C := C) p).map (0 :
        filteredKernel f ⟶ filteredCoimage f) = 0
      exact Functor.map_zero (F := gradedPieceFunctor (C := C) p) _ _)

theorem graded_piece_kernel_coimage_short_exact {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    (filteredKernelCoimageGradedShortComplex f p).ShortExact := by
  sorry

def filteredImageCokernelGradedShortComplex {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk
    (gradedPieceMap (C := C) (filteredImageι f) p)
    (gradedPieceMap (C := C) (filteredCokernelπ f) p) (by
      rw [← gradedPiece_map_comp]
      have hzero : filteredImageι f ≫ filteredCokernelπ f = 0 := by
        change kernel.ι (cokernel.π f) ≫ filteredCokernelπ f = 0
        let c := CokernelCofork.ofπ (filteredCokernelπ f)
          (filteredCokernel_comp f)
        let k := (cokernelIsCokernel f).desc c
        have hk : cokernel.π f ≫ k = filteredCokernelπ f :=
          (cokernelIsCokernel f).fac c WalkingParallelPair.one
        rw [← hk, ← Category.assoc, kernel.condition, zero_comp]
      rw [hzero]
      let : (gradedPieceFunctor (C := C) p).Additive :=
        gradedPieceFunctor_is_additive p
      change (gradedPieceFunctor (C := C) p).map (0 :
        filteredImage f ⟶ filteredCokernel f) = 0
      exact Functor.map_zero (F := gradedPieceFunctor (C := C) p) _ _)

theorem graded_piece_image_cokernel_short_exact {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    (filteredImageCokernelGradedShortComplex f p).ShortExact := by
  sorry

def filteredKernelGradedShortComplex {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk
    (gradedPieceMap (C := C) (filteredKernelι f) p)
    (gradedPieceMap (C := C) f p) (by sorry)

def filteredCokernelGradedShortComplex {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk
    (gradedPieceMap (C := C) f p)
    (gradedPieceMap (C := C) (filteredCokernelπ f) p) (by sorry)

theorem graded_piece_kernel_exact {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ)
    (hf : Strict f) :
    (filteredKernelGradedShortComplex f p).Exact := by
  sorry

theorem graded_piece_cokernel_exact {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ)
    (hf : Strict f) :
    (filteredCokernelGradedShortComplex f p).Exact := by
  sorry

/-! ### Strictness detected by the associated graded -/

def FourTermExact {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0) : Prop :=
  (ShortComplex.mk f g hfg).Exact ∧ (ShortComplex.mk g h hgh).Exact ∧ Mono f ∧ Epi h

theorem strict_iff_associated_graded {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B)
    (hfiniteA : A.IsFinite) (hfiniteB : B.IsFinite) :
    Strict f ↔
      IsIso (Abelian.coimageImageComparison f) ∧
      IsIso ((associatedGraded (C := C)).map
        (Abelian.coimageImageComparison f)) ∧
      (∀ p, (filteredKernelGradedShortComplex f p).Exact) ∧
      (∀ p, (filteredCokernelGradedShortComplex f p).Exact) ∧
      (∀ p, FourTermExact
        (gradedPieceMap (C := C) (filteredKernelι f) p)
        (gradedPieceMap (C := C) f p)
        (gradedPieceMap (C := C) (filteredCokernelπ f) p)
        (by sorry) (by sorry)) := by
  sorry

/-! ## Filtered complexes -/

def filteredComplex {C : Type u} [Category.{v} C] [Preadditive C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hfg : f ≫ g = 0) : ShortComplex (FilteredObject C) :=
  ShortComplex.mk f g hfg

def filteredImageToKernel {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hfg : f ≫ g = 0) :
    Abelian.image f ⟶ kernel g :=
  kernel.lift g (Abelian.image.ι f) (by sorry)

def filteredComplexHomology {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hfg : f ≫ g = 0) : FilteredObject C :=
  cokernel (filteredImageToKernel f g hfg)

def gradedImageToKernel {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hfg : f ≫ g = 0) (p : ℤ) :
    Abelian.image (gradedPieceMap (C := C) f p) ⟶
      kernel (gradedPieceMap (C := C) g p) :=
  kernel.lift (gradedPieceMap (C := C) g p)
    (Abelian.image.ι (gradedPieceMap (C := C) f p)) (by sorry)

def gradedComplexHomology {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hfg : f ≫ g = 0) (p : ℤ) : C :=
  cokernel (gradedImageToKernel f g hfg p)

def gradedComplexHomologyObject {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hfg : f ≫ g = 0) : GradedObject ℤ C :=
  fun p => gradedComplexHomology f g hfg p

theorem filtered_complex_gr_homology_iso {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hfg : f ≫ g = 0) (hf : Strict f) (hg : Strict g) :
    Nonempty ((associatedGraded (C := C)).obj (filteredComplexHomology f g hfg) ≅
      gradedComplexHomologyObject f g hfg) := by
  sorry

/-! ### Filtered acyclicity -/

def filtrationStep {C : Type u} [Category.{v} C]
    (A : FilteredObject C) (p : ℤ) : C := (A.filtration.obj p : C)

def filtrationStepMap {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    filtrationStep A p ⟶ filtrationStep B p := by
  exact (Subobject.factorThru (B.filtration.obj p)
    ((A.filtration.obj p).arrow ≫ f.hom) (f.map_filtration p))

def filtrationStepComplex {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hfg : f ≫ g = 0) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (filtrationStepMap f p) (filtrationStepMap g p) (by sorry)

def filtrationQuotient {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (p : ℤ) : C :=
  cokernel (A.filtration.obj p).arrow

def filtrationQuotientMap {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    filtrationQuotient A p ⟶ filtrationQuotient B p := by
  change cokernel (A.filtration.obj p).arrow ⟶ cokernel (B.filtration.obj p).arrow
  refine cokernel.desc (A.filtration.obj p).arrow
    (f.hom ≫ cokernel.π (B.filtration.obj p).arrow) ?_
  let u := (B.filtration.obj p).factorThru
    ((A.filtration.obj p).arrow ≫ f.hom) (f.map_filtration p)
  rw [← Category.assoc, ← Subobject.factorThru_arrow
    (B.filtration.obj p) ((A.filtration.obj p).arrow ≫ f.hom)
    (f.map_filtration p)]
  rw [Category.assoc, cokernel.condition, comp_zero]

def filtrationQuotientComplex {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hfg : f ≫ g = 0) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (filtrationQuotientMap f p) (filtrationQuotientMap g p) (by sorry)

def gradedPieceComplex {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hfg : f ≫ g = 0) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (gradedPieceMap (C := C) f p) (gradedPieceMap (C := C) g p) (by sorry)

def gradedComplex {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hfg : f ≫ g = 0) :
  GradedObject ℤ C :=
  (associatedGraded (C := C)).obj (filteredComplexHomology f g hfg)

theorem filtered_acyclic {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hfg : f ≫ g = 0)
    (hfiniteA : A.IsFinite) (hfiniteB : B.IsFinite) (hfiniteD : D.IsFinite)
    (hgraded : ∀ p, (gradedPieceComplex f g hfg p).Exact) :
    (∀ p, (gradedPieceComplex f g hfg p).Exact) ∧
    (∀ p, (filtrationStepComplex f g hfg p).Exact) ∧
    (∀ p, (filtrationQuotientComplex f g hfg p).Exact) ∧
    Strict f ∧ Strict g ∧
    (ShortComplex.mk f.hom g.hom (by sorry)).Exact := by
  sorry

end Formalization.Books.Homology.Unit19
