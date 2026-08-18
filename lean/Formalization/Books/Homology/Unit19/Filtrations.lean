import Formalization.Books.Homology.Unit16.GradedObjects
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Subobject.FactorThru
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Homological Algebra, Chapter 19: Filtrations

The source develops filtrations on objects of an abelian category.  The
underlying category, subobjects, images, kernels, cokernels, and graded
objects below use Mathlib's canonical interfaces.  A filtered morphism keeps
the underlying morphism together with the factorization expressing
preservation of every filtration step.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open scoped ZeroObject

universe v u

namespace Formalization.Books.Homology.Unit19

/-! ## Filtered objects -/

/-- A decreasing `ℤ`-indexed family of subobjects of an object. -/
structure DecreasingFiltration (C : Type u) [Category.{v} C] (A : C) where
  obj : ℤ → Subobject A
  antitone : Antitone obj

/-- An object together with a decreasing filtration. -/
structure FilteredObject (C : Type u) [Category.{v} C] where
  carrier : C
  filtration : DecreasingFiltration C carrier

/-- The category of filtered objects of `C`. -/
abbrev Fil (C : Type u) [Category.{v} C] := FilteredObject C

/-- A morphism of filtered objects, with its stepwise factorization data. -/
abbrev FilteredHom {C : Type u} [Category.{v} C]
    (A B : FilteredObject C) :=
  { f : A.carrier ⟶ B.carrier //
    ∀ i : ℤ, (B.filtration.obj i).Factors ((A.filtration.obj i).arrow ≫ f) }

namespace FilteredHom

abbrev hom {C : Type u} [Category.{v} C] {A B : FilteredObject C}
    (f : FilteredHom A B) : A.carrier ⟶ B.carrier := f.1

abbrev map_filtration {C : Type u} [Category.{v} C] {A B : FilteredObject C}
    (f : FilteredHom A B) (i : ℤ) :
    (B.filtration.obj i).Factors ((A.filtration.obj i).arrow ≫ f.hom) := f.2 i

@[ext]
theorem ext {C : Type u} [Category.{v} C] {A B : FilteredObject C}
    (f g : FilteredHom A B) (h : f.hom = g.hom) : f = g := by
  apply Subtype.ext
  exact h

end FilteredHom

instance filteredCategory {C : Type u} [Category.{v} C] : Category (FilteredObject C) where
  Hom A B := FilteredHom A B
  id A :=
    ⟨𝟙 A.carrier, fun i => by
      simpa using (Subobject.factors_self (A.filtration.obj i))⟩
  comp {A B D} f g :=
    ⟨f.hom ≫ g.hom, fun i => by
      have h := Subobject.factors_of_factors_right
        ((B.filtration.obj i).factorThru
          ((A.filtration.obj i).arrow ≫ f.hom) (f.map_filtration i))
        (g := (B.filtration.obj i).arrow ≫ g.hom) (g.map_filtration i)
      rw [← Category.assoc, Subobject.factorThru_arrow] at h
      simpa only [Category.assoc] using h⟩
  id_comp := by
    intro A B f
    apply FilteredHom.ext _ _
    change (𝟙 A.carrier) ≫ f.hom = f.hom
    exact Category.id_comp _
  comp_id := by
    intro A B f
    apply FilteredHom.ext _ _
    change f.hom ≫ (𝟙 B.carrier) = f.hom
    exact Category.comp_id _
  assoc := by
    intro A B D E f g h
    apply FilteredHom.ext _ _
    change (f.hom ≫ g.hom) ≫ h.hom = f.hom ≫ (g.hom ≫ h.hom)
    exact Category.assoc _ _ _

@[simp]
theorem filteredHom_id_hom {C : Type u} [Category.{v} C]
    (A : FilteredObject C) : (𝟙 A : A ⟶ A).hom = 𝟙 A.carrier := rfl

@[simp]
theorem filteredHom_comp_hom {C : Type u} [Category.{v} C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-! ### Induced and quotient filtrations -/

/-- The induced filtration on a subobject, expressed by pullback of subobjects. -/
def inducedFiltration {C : Type u} [Category.{v} C] [HasPullbacks C]
    {A : C} (F : DecreasingFiltration C A) (X : Subobject A) :
    DecreasingFiltration C (X : C) where
  obj i := (Subobject.pullback X.arrow).obj (F.obj i)
  antitone := by
    intro i j hij
    exact (Subobject.pullback X.arrow).monotone (F.antitone hij)

/-- The filtered object obtained from a filtered object and a subobject. -/
def inducedFilteredObject {C : Type u} [Category.{v} C] [HasPullbacks C]
    (A : FilteredObject C) (X : Subobject A.carrier) : FilteredObject C where
  carrier := (X : C)
  filtration := inducedFiltration A.filtration X

/-- The quotient filtration associated to a morphism, using categorical images. -/
def quotientFiltration {C : Type u} [Category.{v} C] [HasImages C]
    {A Y : C} (F : DecreasingFiltration C A) (π : A ⟶ Y) [Epi π] :
    DecreasingFiltration C Y where
  obj i := (Subobject.«exists» π).obj (F.obj i)
  antitone := by
    intro i j hij
    exact (Subobject.«exists» π).monotone (F.antitone hij)

/-- The filtered object with quotient filtration along `π`. -/
def quotientFilteredObject {C : Type u} [Category.{v} C] [HasImages C]
    (A : FilteredObject C) {Y : C} (π : A.carrier ⟶ Y) [Epi π] : FilteredObject C where
  carrier := Y
  filtration := quotientFiltration A.filtration π

/-- The inclusion of an induced filtered object is a filtered morphism. -/
def inducedFilteredHom {C : Type u} [Category.{v} C] [HasPullbacks C]
    (A : FilteredObject C) (X : Subobject A.carrier) :
    inducedFilteredObject A X ⟶ A :=
  ⟨X.arrow, fun i => by
    apply (Subobject.factors_iff _ _).mpr
    exact ⟨Subobject.pullbackπ X.arrow (A.filtration.obj i),
      (Subobject.isPullback X.arrow (A.filtration.obj i)).w⟩⟩

/-- The quotient map is a filtered morphism for the quotient filtration. -/
def quotientFilteredHom {C : Type u} [Category.{v} C] [HasImages C]
    (A : FilteredObject C) {Y : C} (π : A.carrier ⟶ Y) [Epi π] :
    A ⟶ quotientFilteredObject A π :=
  ⟨π, fun i => by
    let h := Subobject.imageFactorisation π (A.filtration.obj i)
    apply (Subobject.factors_iff _ _).mpr
    exact ⟨h.F.e, h.F.fac⟩⟩

/-! ### Finiteness, intersection, union, separation, and exhaustiveness -/

/-- A finite decreasing filtration has a top and a bottom step. -/
def FiniteFiltration {C : Type u} [Category.{v} C] [HasZeroObject C]
    {A : C} (F : DecreasingFiltration C A) : Prop :=
  ∃ n m : ℤ, F.obj n = ⊤ ∧ F.obj m = ⊥

/-- The assertion that the intersection of all filtration steps exists. -/
def HasIntersection {C : Type u} [Category.{v} C]
    {A : C} (F : DecreasingFiltration C A) : Prop :=
  ∃ X : Subobject A, (∀ i, X ≤ F.obj i) ∧
    ∀ Y : Subobject A, (∀ i, Y ≤ F.obj i) → Y ≤ X

/-- A chosen intersection of the filtration steps. -/
noncomputable def intersection {C : Type u} [Category.{v} C]
    {A : C} {F : DecreasingFiltration C A} (hF : HasIntersection F) :
    Subobject A :=
  Classical.choose hF

theorem intersection_le {C : Type u} [Category.{v} C]
    {A : C} {F : DecreasingFiltration C A} (hF : HasIntersection F) (i : ℤ) :
    intersection hF ≤ F.obj i :=
  (Classical.choose_spec hF).1 i

theorem le_intersection {C : Type u} [Category.{v} C]
    {A : C} {F : DecreasingFiltration C A} (hF : HasIntersection F)
    (X : Subobject A) (hX : ∀ i, X ≤ F.obj i) :
    X ≤ intersection hF :=
  (Classical.choose_spec hF).2 X hX

/-- The assertion that the union of all filtration steps exists. -/
def HasUnion {C : Type u} [Category.{v} C]
    {A : C} (F : DecreasingFiltration C A) : Prop :=
  ∃ X : Subobject A, (∀ i, F.obj i ≤ X) ∧
    ∀ Y : Subobject A, (∀ i, F.obj i ≤ Y) → X ≤ Y

/-- A chosen union of the filtration steps. -/
noncomputable def union {C : Type u} [Category.{v} C]
    {A : C} {F : DecreasingFiltration C A} (hF : HasUnion F) :
    Subobject A :=
  Classical.choose hF

theorem union_le {C : Type u} [Category.{v} C]
    {A : C} {F : DecreasingFiltration C A} (hF : HasUnion F) (i : ℤ) :
    F.obj i ≤ union hF :=
  (Classical.choose_spec hF).1 i

theorem union_le_of_le {C : Type u} [Category.{v} C]
    {A : C} {F : DecreasingFiltration C A} (hF : HasUnion F)
    (X : Subobject A) (hX : ∀ i, F.obj i ≤ X) :
    union hF ≤ X :=
  (Classical.choose_spec hF).2 X hX

/-- Separation and exhaustiveness are stated only when the corresponding
    lattice extremum exists, exactly as in the source. -/
def Separated {C : Type u} [Category.{v} C] [HasZeroObject C]
    {A : C} (F : DecreasingFiltration C A) : Prop :=
  ∃ hF : HasIntersection F, intersection hF = ⊥

def Exhaustive {C : Type u} [Category.{v} C] [HasZeroObject C]
    {A : C} (F : DecreasingFiltration C A) : Prop :=
  ∃ hF : HasUnion F, union hF = ⊤

def FilteredObject.IsFinite {C : Type u} [Category.{v} C]
    [HasZeroObject C] (A : FilteredObject C) : Prop :=
  FiniteFiltration A.filtration

def FilteredObject.IsSeparated {C : Type u} [Category.{v} C]
    [HasZeroObject C] (A : FilteredObject C) : Prop :=
  Separated A.filtration

def FilteredObject.IsExhaustive {C : Type u} [Category.{v} C]
    [HasZeroObject C] (A : FilteredObject C) : Prop :=
  Exhaustive A.filtration

/-! ### Additivity and kernels/cokernels of filtered morphisms -/

def filteredHomAddSubgroup {C : Type u} [Category.{v} C] [Preadditive C]
    (A B : FilteredObject C) : AddSubgroup (A.carrier ⟶ B.carrier) where
  carrier f := ∀ i : ℤ,
    (B.filtration.obj i).Factors ((A.filtration.obj i).arrow ≫ f)
  zero_mem' := by
    intro i
    simpa using
      (Subobject.factors_zero :
        (B.filtration.obj i).Factors
          (0 : (A.filtration.obj i : C) ⟶ B.carrier))
  add_mem' := by
    intro f g hf hg i
    simpa only [Preadditive.comp_add] using
      (Subobject.factors_add
        ((A.filtration.obj i).arrow ≫ f)
        ((A.filtration.obj i).arrow ≫ g)
        (hf i) (hg i))
  neg_mem' := by
    intro f hf i
    rcases (Subobject.factors_iff _ _).mp (hf i) with ⟨u, hu⟩
    apply (Subobject.factors_iff _ _).mpr
    refine ⟨-u, ?_⟩
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, hu]

instance filteredHomAddCommGroup {C : Type u} [Category.{v} C] [Preadditive C]
    (A B : FilteredObject C) : AddCommGroup (FilteredHom A B) := by
  change AddCommGroup (filteredHomAddSubgroup A B)
  infer_instance

instance filteredPreadditive {C : Type u} [Category.{v} C] [Preadditive C] :
    Preadditive (FilteredObject C) where
  homGroup A B := filteredHomAddCommGroup A B
  add_comp := by
    intro A B D f g h
    apply FilteredHom.ext _ _
    change (f.hom + g.hom) ≫ h.hom = f.hom ≫ h.hom + g.hom ≫ h.hom
    exact Preadditive.add_comp _ _ _ _ _ _
  comp_add := by
    intro A B D f g h
    apply FilteredHom.ext _ _
    change f.hom ≫ (g.hom + h.hom) = f.hom ≫ g.hom + f.hom ≫ h.hom
    exact Preadditive.comp_add _ _ _ _ _ _

def zeroFilteredObject {C : Type u} [Category.{v} C] [HasZeroObject C] :
    FilteredObject C where
  carrier := 0
  filtration :=
    { obj := fun _ => Subobject.mk (𝟙 (0 : C))
      antitone := by intro i j hij; rfl }

theorem zeroFilteredObject_isZero {C : Type u} [Category.{v} C]
    [Preadditive C] [HasZeroObject C] : IsZero (zeroFilteredObject (C := C)) where
  unique_to A := ⟨⟨⟨(0 : zeroFilteredObject (C := C) ⟶ A)⟩, by
    intro f
    apply FilteredHom.ext _ _
    exact (isZero_zero C).eq_of_src _ _⟩⟩
  unique_from A := ⟨⟨⟨(0 : A ⟶ zeroFilteredObject (C := C))⟩, by
    intro f
    apply FilteredHom.ext _ _
    exact (isZero_zero C).eq_of_tgt _ _⟩⟩

instance filteredHasZeroObject {C : Type u} [Category.{v} C]
    [Preadditive C] [HasZeroObject C] : HasZeroObject (FilteredObject C) :=
  ⟨⟨zeroFilteredObject (C := C), zeroFilteredObject_isZero (C := C)⟩⟩

/-- The source's assertion that `Fil(C)` is additive.  The project-wide
    additive-category interface is used rather than a parallel definition. -/
theorem filteredCategory_additive_exists {C : Type u} [Category.{v} C] [Abelian C] :
    Nonempty (Formalization.Books.Homology.Unit03.AdditiveCategory (FilteredObject C)) := by
  letI : HasFiniteProducts (FilteredObject C) := by
      refine { out := ?_ }
      intro n
      refine ⟨fun F => ?_⟩
      let q : Fin n → C := fun j => (F.obj (Discrete.mk j)).carrier
      let p : C := ∏ᶜ q
      let π : ∀ j : Fin n, p ⟶ q j := fun j => Limits.Pi.π q j
      let Pfil : ℤ → Subobject p := fun i =>
        Finset.univ.inf fun j =>
          (Subobject.pullback (π j)).obj ((F.obj (Discrete.mk j)).filtration.obj i)
      let P : FilteredObject C :=
        { carrier := p
          filtration :=
            { obj := Pfil
              antitone := by
                intro i j hij
                apply Finset.le_inf
                intro k hk
                exact (Finset.inf_le hk).trans
                  ((Subobject.pullback (π k)).monotone
                    ((F.obj (Discrete.mk k)).filtration.antitone hij)) } }
      let t : Fan (fun j : Fin n => F.obj (Discrete.mk j)) :=
        Fan.mk P (fun j => by
          refine ⟨π j, ?_⟩
          intro i
          let X := (Subobject.pullback (π j)).obj
            ((F.obj (Discrete.mk j)).filtration.obj i)
          let hX := Subobject.finset_inf_arrow_factors Finset.univ
            (fun k => (Subobject.pullback (π k)).obj
              ((F.obj (Discrete.mk k)).filtration.obj i)) j (Finset.mem_univ j)
          let v := X.factorThru (Pfil i).arrow hX
          have hv := X.factorThru_arrow (Pfil i).arrow hX
          let hpb := Subobject.isPullback (π j)
            ((F.obj (Discrete.mk j)).filtration.obj i)
          have hfj : ((F.obj (Discrete.mk j)).filtration.obj i).Factors
              (X.arrow ≫ π j) := by
            apply (Subobject.factors_iff _ _).mpr
            exact ⟨Subobject.pullbackπ (π j)
              ((F.obj (Discrete.mk j)).filtration.obj i), hpb.w⟩
          have hfac := Subobject.factors_of_factors_right v hfj
          rw [← Category.assoc, hv] at hfac
          simpa [X, P, Pfil] using hfac)
      let ht : IsLimit t :=
        Fan.IsLimit.mk t
          (fun s => by
            let l : s.pt ⟶ P := by
              let h : s.pt.carrier ⟶ p := Limits.Pi.lift
                (fun j => (s.proj j).hom)
              refine ⟨h, ?_⟩
              intro i
              apply (Subobject.factors_iff _ _).mpr
              have hP : (Pfil i).Factors
                  ((s.pt.filtration.obj i).arrow ≫ h) := by
                dsimp [Pfil]
                apply (Subobject.finset_inf_factors _).mpr
                intro j hj
                let u := ((F.obj (Discrete.mk j)).filtration.obj i).factorThru
                  ((s.pt.filtration.obj i).arrow ≫ (s.proj j).hom)
                  ((s.proj j).map_filtration i)
                let hpb := Subobject.isPullback (π j)
                  ((F.obj (Discrete.mk j)).filtration.obj i)
                apply (Subobject.factors_iff _ _).mpr
                refine ⟨hpb.lift u
                  ((s.pt.filtration.obj i).arrow ≫ h) ?_,
                  hpb.lift_snd _ _ _⟩
                rw [Subobject.factorThru_arrow]
                have hp := Limits.Pi.lift_π (fun k => (s.proj k).hom) j
                simpa [h, π, p, q, Category.assoc] using
                  congrArg (fun z => (s.pt.filtration.obj i).arrow ≫ z) hp
              simpa [P] using (Subobject.factors_iff _ _).mp hP
            simpa [t] using l)
          (fun s j => by
            apply FilteredHom.ext _ _
            change (Limits.Pi.lift (fun k => (s.proj k).hom) ≫ π j) =
              (s.proj j).hom
            simpa [π, p, q] using
              (Limits.Pi.lift_π (fun k => (s.proj k).hom) j))
          (fun s m hm => by
            apply FilteredHom.ext _ _
            apply Limits.Pi.hom_ext _ _
            intro j
            have hm' : FilteredHom.hom m ≫ π j = (s.proj j).hom := by
              have h := congrArg FilteredHom.hom (hm j)
              simpa [t, π] using h
            change FilteredHom.hom m ≫ π j =
              Limits.Pi.lift (fun k => (s.proj k).hom) ≫ π j
            rw [Limits.Pi.lift_π]
            exact hm')
      let e := (Discrete.natIsoFunctor (F := F)).symm
      let coneF : Cone F := (Cone.postcompose e.hom).obj t
      let htF : IsLimit coneF :=
        (IsLimit.postcomposeHomEquiv e t).symm ht
      exact ⟨⟨coneF, htF⟩⟩
  exact ⟨{ toPreadditive := inferInstance, toHasFiniteProducts := inferInstance }⟩

noncomputable instance filteredCategory_additive {C : Type u} [Category.{v} C]
    [Abelian C] :
    Formalization.Books.Homology.Unit03.AdditiveCategory (FilteredObject C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts :=
      (Classical.choice (filteredCategory_additive_exists (C := C))).toHasFiniteProducts }

/-- The filtered kernel object uses the induced filtration on the kernel
    subobject. -/
def filteredKernel {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) : FilteredObject C :=
  inducedFilteredObject A (Subobject.mk (kernel.ι f.hom))

def filteredKernelι {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) : filteredKernel f ⟶ A :=
  inducedFilteredHom A (Subobject.mk (kernel.ι f.hom))

theorem filteredKernelι_comp {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) :
    filteredKernelι f ≫ f = 0 := by
  apply FilteredHom.ext _ _
  change (Subobject.mk (kernel.ι f.hom)).arrow ≫ f.hom = 0
  rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc, kernel.condition]
  simp

def filteredKernelFork {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) : KernelFork f :=
  KernelFork.ofι (filteredKernelι f) (filteredKernelι_comp f)

theorem filteredKernelFork_isLimit_exists {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) :
    Nonempty (IsLimit (filteredKernelFork f)) := by
  have underlying_zero : ∀ {W : FilteredObject C} (g : W ⟶ A),
      g ≫ f = 0 → g.hom ≫ f.hom = 0 := by
    intro W g hg
    have h := congrArg FilteredHom.hom hg
    change g.hom ≫ f.hom = (0 : filteredHomAddSubgroup W B).1 at h
    exact h
  let lift : ∀ {W : FilteredObject C} (g : W ⟶ A),
      g ≫ f = 0 → (W ⟶ filteredKernel f) := by
    intro W g hg
    have hg' : g.hom ≫ f.hom = 0 := underlying_zero g hg
    let k := kernel.lift f.hom g.hom hg' ≫
      (Subobject.underlyingIso (kernel.ι f.hom)).inv
    refine ⟨k, ?_⟩
    intro i
    apply (Subobject.factors_iff _ _).mpr
    let u := (A.filtration.obj i).factorThru
      ((W.filtration.obj i).arrow ≫ g.hom) (g.map_filtration i)
    let hpb := Subobject.isPullback
      (Subobject.mk (kernel.ι f.hom)).arrow (A.filtration.obj i)
    refine ⟨hpb.lift u ((W.filtration.obj i).arrow ≫ k) ?_,
      hpb.lift_snd _ _ _⟩
    rw [Subobject.factorThru_arrow]
    simp [k, hpb, Category.assoc]
  refine ⟨KernelFork.IsLimit.ofι (filteredKernelι f) (filteredKernelι_comp f)
    lift ?_ ?_⟩
  · intro W g hg
    apply FilteredHom.ext _ _
    have hg' : g.hom ≫ f.hom = 0 := underlying_zero g hg
    change (kernel.lift f.hom g.hom hg' ≫
      (Subobject.underlyingIso (kernel.ι f.hom)).inv) ≫
        (Subobject.mk (kernel.ι f.hom)).arrow = g.hom
    simp [Category.assoc]
  · intro W g hg m hm
    apply FilteredHom.ext _ _
    letI : Mono (filteredKernelι f).hom := by
      change Mono (Subobject.mk (kernel.ι f.hom)).arrow
      infer_instance
    apply (cancel_mono (filteredKernelι f).hom).mp
    have hm' : m.hom ≫ (filteredKernelι f).hom = g.hom := by
      have h := congrArg FilteredHom.hom hm
      simpa only [filteredHom_comp_hom] using h
    rw [hm']
    have hg' : g.hom ≫ f.hom = 0 := underlying_zero g hg
    change g.hom = (kernel.lift f.hom g.hom hg' ≫
      (Subobject.underlyingIso (kernel.ι f.hom)).inv) ≫
        (Subobject.mk (kernel.ι f.hom)).arrow
    simp [Category.assoc]

noncomputable def filteredKernelFork_isLimit {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) :
    IsLimit (filteredKernelFork f) :=
  Classical.choice (filteredKernelFork_isLimit_exists f)

instance filteredHasKernels {C : Type u} [Category.{v} C] [Abelian C] :
    HasKernels (FilteredObject C) where
  has_limit f := ⟨⟨filteredKernelFork f, filteredKernelFork_isLimit f⟩⟩

/-- The filtered cokernel object uses the quotient filtration. -/
def filteredCokernel {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) : FilteredObject C :=
  quotientFilteredObject B (cokernel.π f.hom)

def filteredCokernelπ {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) : B ⟶ filteredCokernel f :=
  quotientFilteredHom B (cokernel.π f.hom)

theorem filteredCokernel_comp {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) :
    f ≫ filteredCokernelπ f = 0 := by
  apply FilteredHom.ext _ _
  change f.hom ≫ cokernel.π f.hom = 0
  exact cokernel.condition f.hom

def filteredCokernelCofork {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) : CokernelCofork f :=
  CokernelCofork.ofπ (filteredCokernelπ f) (filteredCokernel_comp f)

theorem filteredCokernelCofork_isColimit_exists {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) :
    Nonempty (IsColimit (filteredCokernelCofork f)) := by
  sorry

noncomputable def filteredCokernelCofork_isColimit {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) :
    IsColimit (filteredCokernelCofork f) :=
  Classical.choice (filteredCokernelCofork_isColimit_exists f)

instance filteredHasCokernels {C : Type u} [Category.{v} C] [Abelian C] :
    HasCokernels (FilteredObject C) where
  has_colimit f := ⟨⟨filteredCokernelCofork f, filteredCokernelCofork_isColimit f⟩⟩

theorem filtered_mono_iff_underlying_mono {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) :
    Mono f ↔ Mono f.hom := by
  sorry

theorem filtered_epi_iff_underlying_epi {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) :
    Epi f ↔ Epi f.hom := by
  sorry

def FilteredInjective {C : Type u} [Category.{v} C]
    {A B : FilteredObject C} (f : A ⟶ B) : Prop := Mono f.hom

def FilteredSurjective {C : Type u} [Category.{v} C]
    {A B : FilteredObject C} (f : A ⟶ B) : Prop := Epi f.hom

theorem filtered_injective_iff_mono {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) :
    FilteredInjective f ↔ Mono f := by
  exact (filtered_mono_iff_underlying_mono f).symm

theorem filtered_surjective_iff_epi {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) :
    FilteredSurjective f ↔ Epi f := by
  exact (filtered_epi_iff_underlying_epi f).symm

theorem filtered_injective_iff_zero_kernel {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) :
    FilteredInjective f ↔ IsZero (kernel f) := by
  rw [filtered_injective_iff_mono, mono_iff_isZero_kernel]

theorem filtered_surjective_iff_zero_cokernel {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) :
    FilteredSurjective f ↔ IsZero (cokernel f) := by
  rw [filtered_surjective_iff_epi, epi_iff_isZero_cokernel]

/-! ## Strict morphisms -/

/-- A filtered morphism is strict when the image of every step is the
    intersection of its total image with the target step. -/
def Strict {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) : Prop :=
  ∀ i : ℤ,
    (Subobject.«exists» f.hom).obj (A.filtration.obj i) =
      (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) ⊓ B.filtration.obj i

theorem strict_iff_induced_filtration {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (u : A ⟶ B)
    (hu : FilteredInjective u) :
    Strict u ↔
      ∀ i : ℤ,
        A.filtration.obj i = (Subobject.pullback u.hom).obj (B.filtration.obj i) := by
  sorry

theorem strict_iff_quotient_filtration {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (u : A ⟶ B)
    (hu : FilteredSurjective u) :
    Strict u ↔
      ∀ i : ℤ,
        B.filtration.obj i = (Subobject.«exists» u.hom).obj (A.filtration.obj i) := by
  sorry

theorem strict_iff_preimage_eq_sup_kernel {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) :
    Strict f ↔
      ∀ i : ℤ,
        (Subobject.pullback f.hom).obj (B.filtration.obj i) =
          A.filtration.obj i ⊔ Subobject.mk (kernel.ι f.hom) := by
  sorry

theorem strict_iff_coimage_image_isIso {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) :
    Strict f ↔ IsIso (Abelian.coimageImageComparison f) := by
  sorry

/-! ### Direct sums and the two basic strictness lemmas -/

def filteredBiproduct {C : Type u} [Category.{v} C] [Abelian C]
    (A B : FilteredObject C) : FilteredObject C where
  carrier := A.carrier ⊞ B.carrier
  filtration :=
    { obj := fun i =>
        Subobject.mk (biprod.map (A.filtration.obj i).arrow (B.filtration.obj i).arrow)
      antitone := by
        intro i j hij
        have hA : A.filtration.obj j ≤ A.filtration.obj i :=
          A.filtration.antitone hij
        have hB : B.filtration.obj j ≤ B.filtration.obj i :=
          B.filtration.antitone hij
        apply Subobject.mk_le_mk_of_comm
          (biprod.map (Subobject.ofLE _ _ hA) (Subobject.ofLE _ _ hB))
        apply biprod.hom_ext <;> simp }

def filteredBiproductLift {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : A ⟶ D) :
    A ⟶ filteredBiproduct B D := by
  refine ⟨biprod.lift f.hom g.hom, ?_⟩
  sorry

theorem strict_biproduct_lift_of_strict_mono {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : A ⟶ D)
    (hf : Strict f) (hfmono : FilteredInjective f) :
    Strict (filteredBiproductLift f g) ∧
      FilteredInjective (filteredBiproductLift f g) := by
  sorry

def filteredBiproductDesc {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A) :
    filteredBiproduct B D ⟶ A := by
  refine ⟨biprod.desc f.hom g.hom, ?_⟩
  sorry

theorem strict_biproduct_desc_of_strict_epi {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A)
    (hf : Strict f) (hfepi : FilteredSurjective f) :
    Strict (filteredBiproductDesc f g) ∧
      FilteredSurjective (filteredBiproductDesc f g) := by
  sorry

theorem strict_induced_iff {C : Type u} [Category.{v} C] [Abelian C]
    {A : FilteredObject C} (X : Subobject A.carrier) :
    Strict (inducedFilteredHom A X) := by
  sorry

theorem strict_quotient_iff {C : Type u} [Category.{v} C] [Abelian C]
    {A : FilteredObject C} {Y : C} (π : A.carrier ⟶ Y) [Epi π] :
    Strict (quotientFilteredHom A π) := by
  sorry

theorem strict_composition_of_strict_of_mono {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hf : Strict f) (hg : Strict g) (hgmono : FilteredInjective g) :
    Strict (f ≫ g) := by
  sorry

theorem strict_composition_of_strict_of_epi {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hf : Strict f) (hg : Strict g) (hfepi : FilteredSurjective f) :
    Strict (f ≫ g) := by
  sorry

structure StrictCompositionFailure {C : Type u} [Category.{v} C]
    [Abelian C] where
  A : FilteredObject C
  B : FilteredObject C
  D : FilteredObject C
  f : @FilteredHom C _ A B
  g : @FilteredHom C _ B D
  f_strict : Strict f
  g_strict : Strict g
  composite_nonzero : f.hom ≫ g.hom ≠ (0 : A.carrier ⟶ D.carrier)
  composite_not_strict : ¬ Strict (f ≫ g)

theorem exists_strict_composition_failure :
    ∃ (C : Type u) (_ : Category.{v} C) (_ : Abelian C),
      Nonempty (@StrictCompositionFailure C _ _) := by
  sorry

theorem exists_filtered_category_not_abelian :
    ∃ (C : Type u) (_ : Category.{v} C) (_ : Abelian C),
      ¬ Nonempty (CategoryTheory.Abelian (FilteredObject C)) := by
  sorry

/-! ### Subquotients -/

def inducedSubobjectMap {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    inducedFilteredObject A X ⟶ inducedFilteredObject A Y := by
  refine ⟨Subobject.ofLE X Y hXY, ?_⟩
  sorry

def filteredSubquotient {C : Type u} [Category.{v} C] [Abelian C]
    {A : FilteredObject C} {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    FilteredObject C :=
  filteredCokernel (inducedSubobjectMap A hXY)

def subquotientQuotientMap {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    quotientFilteredObject A (cokernel.π X.arrow) ⟶
      quotientFilteredObject A (cokernel.π Y.arrow) := by
  refine ⟨cokernel.desc X.arrow (cokernel.π Y.arrow) ?_, ?_⟩
  · change X.arrow ≫ cokernel.π Y.arrow = 0
    rw [← Subobject.ofLE_arrow hXY, Category.assoc, cokernel.condition, comp_zero]
  · sorry

def ambientSubquotientKernel {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    FilteredObject C :=
  filteredKernel (subquotientQuotientMap A hXY)

theorem filteredSubquotientComparison_exists {C : Type u} [Category.{v} C]
    [Abelian C] (A : FilteredObject C) (X Y : Subobject A.carrier) (hXY : X ≤ Y) :
    Nonempty (filteredSubquotient hXY ≅ ambientSubquotientKernel A hXY) := by
  sorry

noncomputable def filteredSubquotientComparison {C : Type u} [Category.{v} C]
    [Abelian C] (A : FilteredObject C) {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    filteredSubquotient hXY ≅ ambientSubquotientKernel A hXY :=
  Classical.choice (filteredSubquotientComparison_exists A X Y hXY)

def subquotientXToY {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    inducedFilteredObject A X ⟶ inducedFilteredObject A Y :=
  inducedSubobjectMap A hXY

def subquotientXToA {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (X : Subobject A.carrier) :
    inducedFilteredObject A X ⟶ A :=
  inducedFilteredHom A X

def subquotientYToA {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (Y : Subobject A.carrier) :
    inducedFilteredObject A Y ⟶ A :=
  inducedFilteredHom A Y

def subquotientYToAX {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) {X Y : Subobject A.carrier} :
    inducedFilteredObject A Y ⟶ quotientFilteredObject A (cokernel.π X.arrow) :=
  inducedFilteredHom A Y ≫ quotientFilteredHom A (cokernel.π X.arrow)

def subquotientYToYX {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    inducedFilteredObject A Y ⟶ filteredSubquotient hXY :=
  filteredCokernelπ (inducedSubobjectMap A hXY)

def subquotientYXToAX {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) {X Y : Subobject A.carrier} (hXY : X ≤ Y) :
    filteredSubquotient hXY ⟶ quotientFilteredObject A (cokernel.π X.arrow) :=
  (filteredSubquotientComparison A hXY).hom ≫
    filteredKernelι (subquotientQuotientMap A hXY)

theorem filtered_subquotient_maps_strict {C : Type u} [Category.{v} C]
    [Abelian C] (A : FilteredObject C) (X Y : Subobject A.carrier) (hXY : X ≤ Y) :
    Strict (subquotientXToY A hXY) ∧
      Strict (subquotientXToA A X) ∧
      Strict (subquotientYToA A Y) ∧
      Strict (subquotientYToAX A (X := X) (Y := Y)) ∧
      Strict (subquotientYToYX A hXY) ∧
      Strict (subquotientYXToAX A hXY) := by
  sorry

/-! ### Pushouts and pullbacks -/

structure FilteredPushoutData {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : A ⟶ D) where
  pushout : FilteredObject C
  inl : B ⟶ pushout
  inr : D ⟶ pushout
  comm : f ≫ inl = g ≫ inr
  isColimit : IsColimit (PushoutCocone.mk inl inr comm)

theorem filtered_pushout_exists {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : A ⟶ D) :
    Nonempty (FilteredPushoutData f g) := by
  sorry

theorem filtered_pushout_preserves_strict {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : A ⟶ D)
    (hfg : Strict f) (P : FilteredPushoutData f g) :
    Strict P.inr := by
  sorry

structure FilteredPullbackData {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A) where
  pullback : FilteredObject C
  fst : pullback ⟶ B
  snd : pullback ⟶ D
  comm : fst ≫ f = snd ≫ g
  isLimit : IsLimit (PullbackCone.mk fst snd comm)

theorem filtered_pullback_exists {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A) :
    Nonempty (FilteredPullbackData f g) := by
  sorry

theorem filtered_pullback_preserves_strict {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A)
    (hf : Strict f) (P : FilteredPullbackData f g) :
    Strict P.snd := by
  sorry

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
  sorry

theorem gradedPiece_map_id {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) (p : ℤ) :
    gradedPieceMap (𝟙 A) p = 𝟙 (gradedPiece A p) := by
  sorry

theorem gradedPiece_map_comp {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D) (p : ℤ) :
    gradedPieceMap (f ≫ g) p = gradedPieceMap f p ≫ gradedPieceMap g p := by
  sorry

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
  sorry

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
  sorry

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
      (quotientFilteredHom A (cokernel.π X.arrow)) p) (by sorry)

theorem graded_piece_subobject_short_exact {C : Type u} [Category.{v} C]
    [Abelian C] (A : FilteredObject C) (X : Subobject A.carrier) (p : ℤ) :
    (filteredSubobjectShortExact A X p).ShortExact := by
  sorry

def filteredKernelCoimageGradedShortComplex {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk
    (gradedPieceMap (C := C) (filteredKernelι f) p)
    (gradedPieceMap (C := C) (filteredCoimageπ f) p) (by sorry)

theorem graded_piece_kernel_coimage_short_exact {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    (filteredKernelCoimageGradedShortComplex f p).ShortExact := by
  sorry

def filteredImageCokernelGradedShortComplex {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk
    (gradedPieceMap (C := C) (filteredImageι f) p)
    (gradedPieceMap (C := C) (filteredCokernelπ f) p) (by sorry)

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
