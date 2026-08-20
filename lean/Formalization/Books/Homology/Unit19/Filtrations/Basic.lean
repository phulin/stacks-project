import Formalization.Books.Homology.Unit09.JordanHolder
import Formalization.Books.Homology.Unit16.GradedObjects
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.CategoryTheory.RegularCategory.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Subobject.FactorThru
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits

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
  let : HasFiniteProducts (FilteredObject C) := by
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
                simp [h, π, p, q, Category.assoc]
              simpa [P] using (Subobject.factors_iff _ _).mp hP
            simpa [t] using l)
          (fun s j => by
            apply FilteredHom.ext _ _
            change (Limits.Pi.lift (fun k => (s.proj k).hom) ≫ π j) =
              (s.proj j).hom
            simp [π, q])
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
    simp [k, Category.assoc]
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
    let : Mono (filteredKernelι f).hom := by
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
  have underlying_zero : ∀ {Z : FilteredObject C} (g : B ⟶ Z),
      f ≫ g = 0 → f.hom ≫ g.hom = 0 := by
    intro Z g hg
    have h := congrArg FilteredHom.hom hg
    change f.hom ≫ g.hom = (0 : filteredHomAddSubgroup A Z).1 at h
    exact h
  let desc : ∀ {Z : FilteredObject C} (g : B ⟶ Z),
      f ≫ g = 0 → (filteredCokernel f ⟶ Z) := by
    intro Z g hg
    have hg' : f.hom ≫ g.hom = 0 := underlying_zero g hg
    let d := cokernel.desc f.hom g.hom hg'
    refine ⟨d, ?_⟩
    intro i
    let π := cokernel.π f.hom
    let X := B.filtration.obj i
    let I := (Subobject.«exists» π).obj X
    let T := Z.filtration.obj i
    have hX : T.Factors (X.arrow ≫ g.hom) := g.map_filtration i
    have hπd : X.arrow ≫ π ≫ d = X.arrow ≫ g.hom := by
      simp [d, π]
    have hIle : I ≤ (Subobject.pullback d).obj T := by
      have hXle : X ≤ (Subobject.pullback (π ≫ d)).obj T := by
        let hpb := Subobject.isPullback (π ≫ d) T
        refine Subobject.le_of_comm
          (hpb.lift (T.factorThru (X.arrow ≫ g.hom) hX) X.arrow ?_) ?_
        · calc
            T.factorThru (X.arrow ≫ g.hom) hX ≫ T.arrow =
                X.arrow ≫ g.hom := T.factorThru_arrow (X.arrow ≫ g.hom) hX
            _ = X.arrow ≫ π ≫ d := hπd.symm
        · exact hpb.lift_snd _ _ _
      have hXle' : X ≤ (Subobject.pullback π).obj ((Subobject.pullback d).obj T) := by
        simpa only [Subobject.pullback_comp] using hXle
      have h := ((Subobject.existsPullbackAdj π).homEquiv X
        ((Subobject.pullback d).obj T)).symm
        (CategoryTheory.homOfLE hXle')
      exact h.le
    change T.Factors (I.arrow ≫ d)
    apply (Subobject.factors_iff _ _).mpr
    let hpb := Subobject.isPullback d T
    let q : (I : C) ⟶ (T : C) := Subobject.ofLE I ((Subobject.pullback d).obj T) hIle ≫
      Subobject.pullbackπ d T
    have hq : q ≫ T.arrow = I.arrow ≫ d := by
      dsimp [q]
      rw [Category.assoc, hpb.w, ← Category.assoc, Subobject.ofLE_arrow]
    let w : (I : C) ⟶ (Subobject.representative.obj T : C) := by
      simpa only [Subobject.representative_coe] using q
    refine ⟨w, ?_⟩
    dsimp [w]
    simpa only [Subobject.representative_coe] using hq
  refine ⟨CokernelCofork.IsColimit.ofπ (filteredCokernelπ f)
    (filteredCokernel_comp f) (fun g hg => desc g hg) ?_ ?_⟩
  · intro Z g hg
    apply FilteredHom.ext _ _
    change (filteredCokernelπ f).hom ≫ (desc g hg).hom = g.hom
    change cokernel.π f.hom ≫ cokernel.desc f.hom g.hom
      (underlying_zero g hg) = g.hom
    simp
  · intro Z g hg m hm
    apply FilteredHom.ext _ _
    let : Epi (filteredCokernelπ f).hom := by
      change Epi (cokernel.π f.hom)
      infer_instance
    apply (cancel_epi (filteredCokernelπ f).hom).mp
    have hm' : (filteredCokernelπ f).hom ≫ m.hom = g.hom := by
      have h := congrArg FilteredHom.hom hm
      simpa only [filteredHom_comp_hom] using h
    change (filteredCokernelπ f).hom ≫ m.hom =
      (filteredCokernelπ f).hom ≫ (desc g hg).hom
    calc
      (filteredCokernelπ f).hom ≫ m.hom = g.hom := hm'
      _ = (filteredCokernelπ f).hom ≫ (desc g hg).hom := by
        symm
        change cokernel.π f.hom ≫ cokernel.desc f.hom g.hom
          (underlying_zero g hg) = g.hom
        simp

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
  constructor
  · intro hf
    let : Mono f := hf
    apply (mono_iff_isZero_kernel f.hom).2
    have hk : IsZero (filteredKernel f) :=
      KernelFork.IsLimit.isZero_of_mono (filteredKernelFork_isLimit f)
    let e := hk.iso (zeroFilteredObject_isZero (C := C))
    let eC : (filteredKernel f).carrier ≅
        (zeroFilteredObject (C := C)).carrier :=
      { hom := e.hom.hom
        inv := e.inv.hom
        hom_inv_id := by
          have h := congrArg FilteredHom.hom e.hom_inv_id
          simpa only [filteredHom_comp_hom, filteredHom_id_hom] using h
        inv_hom_id := by
          have h := congrArg FilteredHom.hom e.inv_hom_id
          simpa only [filteredHom_comp_hom, filteredHom_id_hom] using h }
    have hkC : IsZero (filteredKernel f).carrier :=
      IsZero.of_iso (isZero_zero C) eC
    exact IsZero.of_iso hkC
      (Subobject.underlyingIso (kernel.ι f.hom)).symm
  · intro hf
    let : Mono f.hom := hf
    constructor
    intro X g h w
    apply FilteredHom.ext _ _
    apply (cancel_mono f.hom).mp
    have hw := congrArg FilteredHom.hom w
    simpa only [filteredHom_comp_hom] using hw

theorem filtered_epi_iff_underlying_epi {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) :
    Epi f ↔ Epi f.hom := by
  constructor
  · intro hf
    let : Epi f := hf
    apply (epi_iff_isZero_cokernel f.hom).2
    have hc : IsZero (filteredCokernel f) :=
      CokernelCofork.IsColimit.isZero_of_epi
        (filteredCokernelCofork_isColimit f)
    let e := hc.iso (zeroFilteredObject_isZero (C := C))
    let eC : (filteredCokernel f).carrier ≅
        (zeroFilteredObject (C := C)).carrier :=
      { hom := e.hom.hom
        inv := e.inv.hom
        hom_inv_id := by
          have h := congrArg FilteredHom.hom e.hom_inv_id
          simpa only [filteredHom_comp_hom, filteredHom_id_hom] using h
        inv_hom_id := by
          have h := congrArg FilteredHom.hom e.inv_hom_id
          simpa only [filteredHom_comp_hom, filteredHom_id_hom] using h }
    have hcC : IsZero (filteredCokernel f).carrier :=
      IsZero.of_iso (isZero_zero C) eC
    change IsZero (cokernel f.hom) at hcC
    exact hcC
  · intro hf
    let : Epi f.hom := hf
    constructor
    intro X g h w
    apply FilteredHom.ext _ _
    apply (cancel_epi f.hom).mp
    have hw := congrArg FilteredHom.hom w
    simpa only [filteredHom_comp_hom] using hw

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

end Formalization.Books.Homology.Unit19
