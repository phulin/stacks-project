import Formalization.Books.Homology.Unit16.GradedObjects
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
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
  let _ : Mono u.hom := hu
  have hmap (G : Subobject B.carrier) :
      (Subobject.map u.hom).obj ((Subobject.pullback u.hom).obj G) =
        (Subobject.map u.hom).obj (⊤ : Subobject A.carrier) ⊓ G := by
    rw [Subobject.map_top]
    change (Subobject.map u.hom).obj ((Subobject.pullback u.hom).obj G) =
      (Subobject.inf.obj (Quotient.mk'' (MonoOver.mk u.hom))).obj G
    exact (Subobject.inf_eq_map_pullback' (MonoOver.mk u.hom) G).symm
  have hinj : Function.Injective
      (fun P : Subobject A.carrier => (Subobject.map u.hom).obj P) := by
    intro P Q h
    calc
      P = (Subobject.pullback u.hom).obj ((Subobject.map u.hom).obj P) :=
        (Subobject.pullback_map_self u.hom P).symm
      _ = (Subobject.pullback u.hom).obj ((Subobject.map u.hom).obj Q) :=
        congrArg _ h
      _ = Q := Subobject.pullback_map_self u.hom Q
  constructor
  · intro h i
    apply hinj
    change (Subobject.map u.hom).obj (A.filtration.obj i) =
      (Subobject.map u.hom).obj
        ((Subobject.pullback u.hom).obj (B.filtration.obj i))
    rw [hmap]
    simpa only [Subobject.exists_iso_map u.hom] using h i
  · intro h i
    rw [Subobject.exists_iso_map u.hom, h i, hmap]

theorem strict_iff_quotient_filtration {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (u : A ⟶ B)
    (hu : FilteredSurjective u) :
    Strict u ↔
      ∀ i : ℤ,
        B.filtration.obj i = (Subobject.«exists» u.hom).obj (A.filtration.obj i) := by
  let _ : Epi u.hom := hu
  have htop : (Subobject.«exists» u.hom).obj (⊤ : Subobject A.carrier) = ⊤ := by
    apply (Subobject.isIso_arrow_iff_eq_top _).mp
    let F := Subobject.imageFactorisation u.hom (⊤ : Subobject A.carrier)
    let _ : Epi F.F.e := by
      exact (strongEpi_of_strongEpiMonoFactorisation
        (Abelian.imageStrongEpiMonoFactorisation
          ((⊤ : Subobject A.carrier).arrow ≫ u.hom)) F.isImage).epi
    let _ : Epi F.F.m := epi_of_epi_fac F.F.fac
    change IsIso F.F.m
    exact isIso_of_mono_of_epi F.F.m
  constructor
  · intro h i
    rw [h i, htop]
    simp
  · intro h i
    rw [h i, htop]
    simp

private theorem abelian_regular {C : Type u} [Category.{v} C] [Abelian C] : Regular C :=
  { hasCoequalizer_of_isKernelPair := fun _ => inferInstance
    regularEpiIsStableUnderBaseChange :=
      MorphismProperty.IsStableUnderBaseChange.mk' fun X Y S f g _ hg => by
        rw [MorphismProperty.regularEpi_iff] at hg ⊢
        let _ : IsRegularEpi g := hg
        let _ : Epi g := inferInstance
        let _ : Epi (pullback.fst f g) := Abelian.epi_pullback_of_epi_g f g
        let _ : NormalEpi (pullback.fst f g) := normalEpiOfEpi _
        infer_instance }

private theorem image_pullback_eq {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B)
    (P : Subobject B.carrier) :
    (Subobject.«exists» f.hom).obj ((Subobject.pullback f.hom).obj P) =
      (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) ⊓ P := by
  let _ : Regular C := abelian_regular
  simpa using Regular.exists_inf_pullback_eq_exists_inf f.hom
    (⊤ : Subobject A.carrier) P

private theorem imagePullback_relation {C : Type u} [Category.{v} C]
    {Q A I B R T : C} (q : Q ⟶ A) (f : A ⟶ B) (e : Q ⟶ I)
    (m : I ⟶ B) (r : R ⟶ I) (a : R ⟶ A) (t : T ⟶ R)
    (p : T ⟶ Q) (hfac : q ≫ f = e ≫ m) (hpb : p ≫ e = t ≫ r)
    (hr : r ≫ m = a ≫ f) : (p ≫ q) ≫ f = (t ≫ a) ≫ f := by
  rw [Category.assoc, hfac, ← Category.assoc, hpb, Category.assoc, hr,
    ← Category.assoc]

private theorem sub_comp_eq_zero_of_comp_eq {C : Type u} [Category.{v} C]
    [Preadditive C] {X Y Z : C} (a b : X ⟶ Y) (f : Y ⟶ Z)
    (h : b ≫ f = a ≫ f) : (a - b) ≫ f = 0 := by
  rw [Preadditive.sub_comp, ← h, sub_self]

private theorem eq_add_of_eq_sub {G : Type*} [AddCommGroup G]
    (a b c : G) (h : c = a - b) : a = b + c := by
  rw [h]
  abel

private theorem kernel_ift_comp_eq_zero {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {X Y Z W : C} (t : X ⟶ Y) [HasKernel t]
    (w : X ⟶ Z) (m : Z ⟶ W) [Mono m] (r : Y ⟶ W)
    (h : w ≫ m = t ≫ r) : kernel.ι t ≫ w = 0 := by
  apply (cancel_mono m).mp
  rw [Category.assoc, h, ← Category.assoc, kernel.condition t, zero_comp,
    zero_comp]

private theorem eq_of_epi_comp_eq {C : Type u} [Category.{v} C]
    {X Y Z W : C} (t : X ⟶ Y) [Epi t] (d : Y ⟶ Z) (w : X ⟶ Z)
    (m : Z ⟶ W) (r : Y ⟶ W) (hd : t ≫ d = w)
    (hw : w ≫ m = t ≫ r) : d ≫ m = r := by
  apply (cancel_epi t).mp
  rw [← Category.assoc, hd, hw]

private theorem pullback_exists_eq_sup_kernel {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B)
    (Q : Subobject A.carrier) :
    (Subobject.pullback f.hom).obj ((Subobject.«exists» f.hom).obj Q) =
      Q ⊔ Subobject.mk (kernel.ι f.hom) := by
    let P := (Subobject.«exists» f.hom).obj Q
    let R := (Subobject.pullback f.hom).obj P
    let K := Subobject.mk (kernel.ι f.hom)
    have hQle : Q ≤ R := by
      exact ((Subobject.existsPullbackAdj f.hom).homEquiv Q P
        (CategoryTheory.homOfLE (show
          (Subobject.«exists» f.hom).obj Q ≤ P from le_rfl))).le
    let hpb := Subobject.isPullback f.hom P
    have hKfac : R.Factors K.arrow := by
      apply (Subobject.factors_iff R K.arrow).mpr
      refine ⟨(Subobject.underlyingIso (kernel.ι f.hom)).hom ≫
        hpb.lift 0 (kernel.ι f.hom) (by simp), ?_⟩
      dsimp [K]
      rw [Category.assoc, hpb.lift_snd]
      exact Subobject.underlyingIso_hom_comp_eq_mk _
    have hKle : K ≤ R := Subobject.le_of_factors hKfac
    have hle : Q ⊔ K ≤ R := sup_le hQle hKle
    apply le_antisymm
    · let G := Subobject.imageFactorisation f.hom Q
      let _ : Epi G.F.e :=
        (strongEpi_of_strongEpiMonoFactorisation
          (Abelian.imageStrongEpiMonoFactorisation
            (Q.arrow ≫ f.hom)) G.isImage).epi
      have hG : Subobject.mk G.F.m = P := by
        change Subobject.mk P.arrow = P
        simp
      let r := Subobject.pullbackπ f.hom P
      let r' := r ≫ Subobject.ofLE P (Subobject.mk G.F.m) hG.symm.le ≫
        (Subobject.underlyingIso G.F.m).hom
      have hr' : r' ≫ G.F.m = R.arrow ≫ f.hom := by
        dsimp [r', r, R]
        simp [Category.assoc, hpb.w,
          Subobject.underlyingIso_hom_comp_eq_mk]
      let t := pullback.snd G.F.e r'
      let _ : Epi t := Abelian.epi_pullback_of_epi_f G.F.e r'
      let sQ := pullback.fst G.F.e r' ≫ Q.arrow
      let sA := t ≫ R.arrow
      have hs : sQ ≫ f.hom = sA ≫ f.hom :=
        imagePullback_relation Q.arrow f.hom G.F.e G.F.m r' R.arrow t
          (pullback.fst G.F.e r') G.F.fac.symm (pullback.condition) hr'
      have hdiff : (sA - sQ) ≫ f.hom = 0 :=
        sub_comp_eq_zero_of_comp_eq sA sQ f.hom hs
      let k := kernel.lift f.hom (sA - sQ) hdiff
      have hk : k ≫ kernel.ι f.hom = sA - sQ := by
        dsimp [k]
        simp
      have hdecomp : sA = sQ + k ≫ kernel.ι f.hom :=
        eq_add_of_eq_sub sA sQ (k ≫ kernel.ι f.hom) hk
      let S := Q ⊔ K
      have hQf : Q.Factors sQ :=
        Subobject.factors_comp_arrow (pullback.fst G.F.e r')
      have hQs : S.Factors sQ :=
        Subobject.sup_factors_of_factors_left hQf
      have hiK : (Subobject.underlyingIso (kernel.ι f.hom)).inv ≫
          K.arrow = kernel.ι f.hom := by
        apply (cancel_epi (Subobject.underlyingIso (kernel.ι f.hom)).hom).mp
        simp [K, Subobject.underlyingIso_hom_comp_eq_mk]
      let k' := k ≫ (Subobject.underlyingIso (kernel.ι f.hom)).inv
      have hKf : K.Factors (k ≫ kernel.ι f.hom) := by
        apply (Subobject.factors_iff K _).mpr
        refine ⟨k', ?_⟩
        dsimp [k']
        rw [Category.assoc, hiK]
      have hKs : S.Factors (k ≫ kernel.ι f.hom) :=
        Subobject.sup_factors_of_factors_right hKf
      have hsum : S.Factors (sQ + k ≫ kernel.ι f.hom) :=
        Subobject.factors_add sQ (k ≫ kernel.ι f.hom) hQs hKs
      have hSfac : S.Factors sA := by
        rw [hdecomp]
        exact hsum
      let w := S.factorThru sA hSfac
      have hw : w ≫ S.arrow = sA := by
        dsimp [w]
        simp
      have hzero : kernel.ι t ≫ w = 0 :=
        kernel_ift_comp_eq_zero t w S.arrow R.arrow (by simpa [sA] using hw)
      let d := Abelian.epiDesc t w hzero
      apply Subobject.le_of_comm d
      exact eq_of_epi_comp_eq t d w S.arrow R.arrow
        (Abelian.comp_epiDesc t w hzero) (by simpa [sA] using hw)
    · exact hle

private theorem kernel_le_pullback {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B)
    (P : Subobject B.carrier) :
    Subobject.mk (kernel.ι f.hom) ≤
      (Subobject.pullback f.hom).obj P := by
    let R := (Subobject.pullback f.hom).obj P
    let K := Subobject.mk (kernel.ι f.hom)
    let hpb := Subobject.isPullback f.hom P
    have hKfac : R.Factors K.arrow := by
      apply (Subobject.factors_iff R K.arrow).mpr
      refine ⟨(Subobject.underlyingIso (kernel.ι f.hom)).hom ≫
        hpb.lift 0 (kernel.ι f.hom) (by simp), ?_⟩
      dsimp [K]
      rw [Category.assoc, hpb.lift_snd]
      exact Subobject.underlyingIso_hom_comp_eq_mk _
    exact Subobject.le_of_factors hKfac

theorem strict_iff_preimage_eq_sup_kernel {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) :
    Strict f ↔
      ∀ i : ℤ,
        (Subobject.pullback f.hom).obj (B.filtration.obj i) =
          A.filtration.obj i ⊔ Subobject.mk (kernel.ι f.hom) := by
  constructor
  · intro h i
    have him :
        (Subobject.«exists» f.hom).obj
            ((Subobject.pullback f.hom).obj (B.filtration.obj i)) =
          (Subobject.«exists» f.hom).obj (A.filtration.obj i) := by
      rw [image_pullback_eq f (B.filtration.obj i)]
      exact (h i).symm
    have hRle :
        (Subobject.pullback f.hom).obj (B.filtration.obj i) ≤
          (Subobject.pullback f.hom).obj
            ((Subobject.«exists» f.hom).obj (A.filtration.obj i)) :=
      ((Subobject.existsPullbackAdj f.hom).homEquiv _ _
        (CategoryTheory.homOfLE him.le)).le
    rw [pullback_exists_eq_sup_kernel f (A.filtration.obj i)] at hRle
    have hAle : A.filtration.obj i ≤
        (Subobject.pullback f.hom).obj (B.filtration.obj i) := by
      apply ((Subobject.existsPullbackAdj f.hom).homEquiv _ _
        (CategoryTheory.homOfLE (show
          (Subobject.«exists» f.hom).obj (A.filtration.obj i) ≤
            B.filtration.obj i by
              rw [h i]
              exact inf_le_right))).le
    exact le_antisymm hRle
      (sup_le hAle (kernel_le_pullback f (B.filtration.obj i)))
  · intro h i
    have hR :
        (Subobject.pullback f.hom).obj (B.filtration.obj i) =
          (Subobject.pullback f.hom).obj
            ((Subobject.«exists» f.hom).obj (A.filtration.obj i)) := by
      calc
        (Subobject.pullback f.hom).obj (B.filtration.obj i) =
            A.filtration.obj i ⊔ Subobject.mk (kernel.ι f.hom) := h i
        _ = (Subobject.pullback f.hom).obj
            ((Subobject.«exists» f.hom).obj (A.filtration.obj i)) :=
          (pullback_exists_eq_sup_kernel f (A.filtration.obj i)).symm
    have him :
        (Subobject.«exists» f.hom).obj
            ((Subobject.pullback f.hom).obj (B.filtration.obj i)) =
          (Subobject.«exists» f.hom).obj (A.filtration.obj i) := by
      rw [hR]
      calc
        (Subobject.«exists» f.hom).obj
              ((Subobject.pullback f.hom).obj
                ((Subobject.«exists» f.hom).obj (A.filtration.obj i))) =
            (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) ⊓
              (Subobject.«exists» f.hom).obj (A.filtration.obj i) :=
          image_pullback_eq f _
        _ = (Subobject.«exists» f.hom).obj (A.filtration.obj i) := by
          apply le_antisymm inf_le_right
          exact le_inf ((Subobject.«exists» f.hom).monotone le_top) le_rfl
    calc
      (Subobject.«exists» f.hom).obj (A.filtration.obj i) =
          (Subobject.«exists» f.hom).obj
            ((Subobject.pullback f.hom).obj (B.filtration.obj i)) := him.symm
      _ = (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) ⊓
          (B.filtration.obj i) := image_pullback_eq f _


private theorem exists_comp {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (P : Subobject X) :
    (Subobject.«exists» (a ≫ b)).obj P =
      (Subobject.«exists» b).obj ((Subobject.«exists» a).obj P) := by
    apply le_antisymm
    · have h : P ≤ (Subobject.pullback (a ≫ b)).obj
          ((Subobject.«exists» b).obj ((Subobject.«exists» a).obj P)) := by
        rw [Subobject.pullback_comp]
        exact ((Subobject.existsPullbackAdj a).homEquiv P
          ((Subobject.pullback b).obj
            ((Subobject.«exists» b).obj ((Subobject.«exists» a).obj P))))
          (CategoryTheory.homOfLE
            (((Subobject.existsPullbackAdj b).homEquiv
              ((Subobject.«exists» a).obj P)
              ((Subobject.«exists» b).obj ((Subobject.«exists» a).obj P)))
              (CategoryTheory.homOfLE le_rfl)).le) |>.le
      exact ((Subobject.existsPullbackAdj (a ≫ b)).homEquiv P
        ((Subobject.«exists» b).obj ((Subobject.«exists» a).obj P))).symm
        (CategoryTheory.homOfLE h) |>.le
    · have h : (Subobject.«exists» a).obj P ≤
          (Subobject.pullback b).obj ((Subobject.«exists» (a ≫ b)).obj P) := by
        have h' : P ≤ (Subobject.pullback (a ≫ b)).obj
            ((Subobject.«exists» (a ≫ b)).obj P) :=
          (((Subobject.existsPullbackAdj (a ≫ b)).homEquiv P
            ((Subobject.«exists» (a ≫ b)).obj P))
            (CategoryTheory.homOfLE le_rfl)).le
        rw [Subobject.pullback_comp] at h'
        exact ((Subobject.existsPullbackAdj a).homEquiv P
          ((Subobject.pullback b).obj ((Subobject.«exists» (a ≫ b)).obj P))).symm
          (CategoryTheory.homOfLE h') |>.le
      exact ((Subobject.existsPullbackAdj b).homEquiv
        ((Subobject.«exists» a).obj P)
        ((Subobject.«exists» (a ≫ b)).obj P)).symm
        (CategoryTheory.homOfLE h) |>.le

private theorem exists_top_of_epi {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (u : X ⟶ Y) [Epi u] :
    (Subobject.«exists» u).obj (⊤ : Subobject X) = ⊤ := by
    apply (Subobject.isIso_arrow_iff_eq_top _).mp
    let F := Subobject.imageFactorisation u (⊤ : Subobject X)
    let _ : Epi F.F.e := by
      exact (strongEpi_of_strongEpiMonoFactorisation
        (Abelian.imageStrongEpiMonoFactorisation
          ((⊤ : Subobject X).arrow ≫ u)) F.isImage).epi
    let _ : Epi F.F.m := epi_of_epi_fac F.F.fac
    change IsIso F.F.m
    exact isIso_of_mono_of_epi F.F.m

private theorem strict_iff_exists_eq_of_epi
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : FilteredObject C} (u : X ⟶ Y) [Epi u.hom] :
    Strict u ↔ ∀ i : ℤ,
      (Subobject.«exists» u.hom).obj (X.filtration.obj i) =
        Y.filtration.obj i := by
  simp only [Strict, exists_top_of_epi u.hom, top_inf_eq]

private theorem subobjectMap_injective_of_mono
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {X Y : C} (u : X ⟶ Y) [Mono u] :
    Function.Injective (fun P : Subobject X => (Subobject.map u).obj P) := by
  intro P Q h
  calc
    P = (Subobject.pullback u).obj ((Subobject.map u).obj P) :=
      (Subobject.pullback_map_self u P).symm
    _ = (Subobject.pullback u).obj ((Subobject.map u).obj Q) := congrArg _ h
    _ = Q := Subobject.pullback_map_self u Q

private theorem map_pullback_eq_map_top_inf
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {X Y : C} (u : X ⟶ Y) [Mono u] (G : Subobject Y) :
    (Subobject.map u).obj ((Subobject.pullback u).obj G) =
      (Subobject.map u).obj (⊤ : Subobject X) ⊓ G := by
  rw [Subobject.map_top]
  change (Subobject.map u).obj ((Subobject.pullback u).obj G) =
    (Subobject.inf.obj (Quotient.mk'' (MonoOver.mk u))).obj G
  exact (Subobject.inf_eq_map_pullback' (MonoOver.mk u) G).symm

private theorem strict_iff_isIso_of_hom_iso {C : Type u} [Category.{v} C]
    [Abelian C] {X Y : FilteredObject C} (u : X ⟶ Y) (hu : IsIso u.hom) :
    Strict u ↔ IsIso u := by
    constructor
    · intro hs
      let : IsIso u.hom := hu
      have hstrict' := (strict_iff_induced_filtration u (by
        change Mono u.hom
        infer_instance)).mp hs
      let ui : Y ⟶ X :=
        ⟨inv u.hom, by
          intro i
          rw [hstrict' i]
          apply (Subobject.factors_iff _ _).mpr
          let hpb := Subobject.isPullback u.hom (Y.filtration.obj i)
          refine ⟨hpb.lift (𝟙 _) ((Y.filtration.obj i).arrow ≫ inv u.hom)
            (by simp [Category.assoc]), ?_⟩
          exact hpb.lift_snd _ _ _⟩
      refine ⟨⟨ui, ?_, ?_⟩⟩
      · apply FilteredHom.ext _ _
        change u.hom ≫ inv u.hom = 𝟙 _
        simp
      · apply FilteredHom.ext _ _
        change inv u.hom ≫ u.hom = 𝟙 _
        simp
    · intro hu
      let : IsIso u := hu
      have hu_mono : Mono u.hom :=
        (filtered_mono_iff_underlying_mono u).1 (by infer_instance)
      let : Mono u.hom := hu_mono
      apply (strict_iff_induced_filtration u hu_mono).2
      intro i
      let Xᵢ := X.filtration.obj i
      let Yᵢ := Y.filtration.obj i
      let P := (Subobject.pullback u.hom).obj Yᵢ
      have hXP : Xᵢ ≤ P := by
        apply Subobject.le_of_factors
        exact (CategoryTheory.Limits.pullback_factors_iff u.hom Yᵢ
          Xᵢ.arrow).2 (u.map_filtration i)
      have hPX : P ≤ Xᵢ := by
        have hi : Xᵢ.Factors (Yᵢ.arrow ≫ (inv u).hom) :=
          (inv u).map_filtration i
        rcases (Subobject.factors_iff _ _).mp hi with ⟨s, hs⟩
        apply Subobject.le_of_factors
        apply (Subobject.factors_iff _ _).mpr
        refine ⟨Subobject.pullbackπ u.hom Yᵢ ≫ s, ?_⟩
        calc
          (Subobject.pullbackπ u.hom Yᵢ ≫ s) ≫
              (Subobject.representative.obj Xᵢ).arrow =
              Subobject.pullbackπ u.hom Yᵢ ≫
                (s ≫ (Subobject.representative.obj Xᵢ).arrow) :=
            Category.assoc _ _ _
          _ = Subobject.pullbackπ u.hom Yᵢ ≫
              (Yᵢ.arrow ≫ (inv u).hom) := by rw [hs]
          _ = (Subobject.pullbackπ u.hom Yᵢ ≫ Yᵢ.arrow) ≫
              (inv u).hom := by simp [Category.assoc]
          _ = (P.arrow ≫ u.hom) ≫ (inv u).hom := by
                rw [(Subobject.isPullback u.hom Yᵢ).w]
          _ = P.arrow := by
            have huinv : u.hom ≫ (inv u).hom = 𝟙 _ := by
              exact congrArg FilteredHom.hom (IsIso.hom_inv_id u)
            rw [Category.assoc, huinv, Category.comp_id]
      exact le_antisymm hXP hPX

private theorem coimageComparison_eq_of_factorisations
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasKernels C] [HasCokernels C]
    {A B Q I : C} (f : A ⟶ B) (q : A ⟶ Q) [Epi q]
    (c : Q ⟶ I) (l : A ⟶ I) (ι : I ⟶ B)
    (eQ : Q ⟶ Abelian.coimage f) (eI : I ⟶ Abelian.image f)
    (hqQ : q ≫ eQ = Abelian.coimage.π f) (hqc : q ≫ c = l)
    (hli : l ≫ ι = f) (heI : eI ≫ Abelian.image.ι f = ι) :
    eQ ≫ Abelian.coimageImageComparison f = c ≫ eI := by
  apply (cancel_epi q).mp
  apply (cancel_mono (Abelian.image.ι f)).mp
  calc
    (q ≫ eQ ≫ Abelian.coimageImageComparison f) ≫ Abelian.image.ι f =
        (q ≫ eQ) ≫ Abelian.coimageImageComparison f ≫
          Abelian.image.ι f := by simp [Category.assoc]
    _ = f := by rw [hqQ]; exact Abelian.coimage_image_factorisation f
    _ = l ≫ ι := hli.symm
    _ = (q ≫ c) ≫ ι := by rw [hqc]
    _ = (q ≫ c) ≫ (eI ≫ Abelian.image.ι f) := by rw [heI]
    _ = (q ≫ c ≫ eI) ≫ Abelian.image.ι f := by simp [Category.assoc]

private theorem filtration_step_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B Q I : C} (q : A ⟶ Q) (c : Q ⟶ I) (ι : I ⟶ B) [Mono ι]
    (f : A ⟶ B) (P : Subobject A) (R : Subobject Q)
    (S : Subobject I) (T : Subobject B)
    (hcomp : q ≫ c ≫ ι = f)
    (hq : R = (Subobject.«exists» q).obj P)
    (hS : S = (Subobject.pullback ι).obj T)
    (htotal : (Subobject.«exists» f).obj (⊤ : Subobject A) =
      (Subobject.map ι).obj (⊤ : Subobject I)) :
    (Subobject.«exists» c).obj R = S ↔
      (Subobject.«exists» f).obj P =
        (Subobject.«exists» f).obj (⊤ : Subobject A) ⊓ T := by
  constructor
  · intro h
    calc
      (Subobject.«exists» f).obj P =
          (Subobject.«exists» (q ≫ c ≫ ι)).obj P := by rw [hcomp]
      _ = (Subobject.«exists» ι).obj
          ((Subobject.«exists» c).obj ((Subobject.«exists» q).obj P)) := by
        rw [← exists_comp, ← exists_comp]
      _ = (Subobject.map ι).obj ((Subobject.«exists» c).obj R) := by
        rw [Subobject.exists_iso_map ι, hq]
      _ = (Subobject.map ι).obj S := by rw [h]
      _ = (Subobject.map ι).obj ((Subobject.pullback ι).obj T) := by rw [hS]
      _ = (Subobject.map ι).obj (⊤ : Subobject I) ⊓ T :=
        map_pullback_eq_map_top_inf ι T
      _ = (Subobject.«exists» f).obj (⊤ : Subobject A) ⊓ T := by rw [htotal]
  · intro h
    apply subobjectMap_injective_of_mono ι
    calc
      (Subobject.map ι).obj ((Subobject.«exists» c).obj R) =
          (Subobject.map ι).obj
            ((Subobject.«exists» c).obj ((Subobject.«exists» q).obj P)) := by
        rw [hq]
      _ = (Subobject.«exists» f).obj P := by
        rw [← Subobject.exists_iso_map ι, ← exists_comp, ← exists_comp, hcomp]
      _ = (Subobject.«exists» f).obj (⊤ : Subobject A) ⊓ T := h
      _ = (Subobject.map ι).obj (⊤ : Subobject I) ⊓ T := by rw [htotal]
      _ = (Subobject.map ι).obj ((Subobject.pullback ι).obj T) :=
        (map_pullback_eq_map_top_inf ι T).symm
      _ = (Subobject.map ι).obj S := by rw [hS]

private theorem isIso_iff_of_iso_comp_eq_comp_iso
    {C : Type u} [Category.{v} C] {W X Y Z : C}
    (a : W ⟶ X) (f : X ⟶ Y) (b : W ⟶ Z) (c : Z ⟶ Y)
    (ha : IsIso a) (hc : IsIso c) (h : a ≫ f = b ≫ c) :
    IsIso f ↔ IsIso b := by
  let _ : IsIso a := ha
  let _ : IsIso c := hc
  constructor
  · intro hf
    let _ : IsIso f := hf
    have hcomp : IsIso (b ≫ c) := by rw [← h]; infer_instance
    exact IsIso.of_isIso_comp_right b c
  · intro hb
    let _ : IsIso b := hb
    have hcomp : IsIso (a ≫ f) := by rw [h]; infer_instance
    exact IsIso.of_isIso_comp_left a f

private def filteredFactorThruImage {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) :
    A ⟶ filteredKernel (filteredCokernelπ f) := by
  let n := filteredCokernelπ f
  let ι := filteredKernelι n
  let l₀ := kernel.lift n.hom f.hom (by
    change f.hom ≫ cokernel.π f.hom = 0
    exact cokernel.condition f.hom) ≫
    (Subobject.underlyingIso (kernel.ι n.hom)).inv
  refine ⟨l₀, ?_⟩
  intro i
  apply (Subobject.factors_iff _ _).mpr
  let X := A.filtration.obj i
  let Y := B.filtration.obj i
  let P := (Subobject.pullback ι.hom).obj Y
  let hP := Subobject.isPullback ι.hom Y
  let u := Y.factorThru (X.arrow ≫ f.hom) (f.map_filtration i)
  refine ⟨hP.lift u (X.arrow ≫ l₀) ?_, hP.lift_snd _ _ _⟩
  rw [Subobject.factorThru_arrow]
  change X.arrow ≫ f.hom =
    (X.arrow ≫ l₀) ≫ (Subobject.mk (kernel.ι n.hom)).arrow
  dsimp [l₀]
  simp only [Category.assoc]
  rw [Subobject.underlyingIso_arrow, kernel.lift_ι]

private theorem filteredFactorThruImage_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) :
    (filteredFactorThruImage f).hom ≫
      (filteredKernelι (filteredCokernelπ f)).hom = f.hom := by
  change (kernel.lift (cokernel.π f.hom) f.hom (cokernel.condition f.hom) ≫
      (Subobject.underlyingIso (kernel.ι (cokernel.π f.hom))).inv) ≫
    (Subobject.mk (kernel.ι (cokernel.π f.hom))).arrow = f.hom
  rw [Category.assoc, Subobject.underlyingIso_arrow, kernel.lift_ι]

private theorem filteredKernelι_comp_filteredFactorThruImage
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (f : A ⟶ B) :
    filteredKernelι f ≫ filteredFactorThruImage f = 0 := by
  apply FilteredHom.ext _ _
  let ι := filteredKernelι (filteredCokernelπ f)
  let _ : Mono ι.hom := by
    change Mono (Subobject.mk (kernel.ι (cokernel.π f.hom))).arrow
    infer_instance
  apply (cancel_mono ι.hom).mp
  rw [filteredHom_comp_hom]
  change ((filteredKernelι f).hom ≫ (filteredFactorThruImage f).hom) ≫ ι.hom =
    (0 : filteredHomAddSubgroup _ _).1 ≫ ι.hom
  rw [Category.assoc, filteredFactorThruImage_comp]
  change (filteredKernelι f).hom ≫ f.hom =
    (0 : (filteredKernel f).carrier ⟶ _ ) ≫ ι.hom
  rw [zero_comp]
  change (Subobject.mk (kernel.ι f.hom)).arrow ≫ f.hom = 0
  rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
    kernel.condition]
  simp

theorem strict_iff_coimage_image_isIso {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) :
    Strict f ↔ IsIso (Abelian.coimageImageComparison f) := by
  let n := filteredCokernelπ f
  let I := filteredKernel n
  let ι := filteredKernelι n
  let l : A ⟶ I := filteredFactorThruImage f
  let k := (filteredKernelFork f).π.app WalkingParallelPair.zero
  have hli : l.hom ≫ ι.hom = f.hom := filteredFactorThruImage_comp f
  have hkl : k ≫ l = 0 := filteredKernelι_comp_filteredFactorThruImage f
  let cc : CokernelCofork (show filteredKernel f ⟶ A from k) :=
    CokernelCofork.ofπ (f := (show filteredKernel f ⟶ A from k)) l hkl
  let c₀ := (filteredCokernelCofork_isColimit k).desc cc
  let q₀ := (filteredCokernelCofork k).π
  have hq₀c : q₀ ≫ c₀ = l := by
    exact (filteredCokernelCofork_isColimit k).fac cc WalkingParallelPair.one
  let eK := (filteredKernelFork_isLimit f).conePointUniqueUpToIso (limit.isLimit _)
  have hK : eK.hom ≫ kernel.ι f = k := by
    simpa [eK, k, filteredKernelFork] using
      IsLimit.conePointUniqueUpToIso_hom_comp
        (filteredKernelFork_isLimit f) (limit.isLimit _) WalkingParallelPair.zero
  let φQ : Arrow.mk k ≅ Arrow.mk (kernel.ι f) :=
    Arrow.isoMk' k (kernel.ι f) eK (Iso.refl _)
      (by simpa using hK)
  let cq : CokernelCofork (kernel.ι f) :=
    CokernelCofork.ofπ (Abelian.coimage.π f) (cokernel.condition _)
  let eQ₀ := CokernelCofork.mapIsoOfIsColimit
    (filteredCokernelCofork_isColimit k) (cokernelIsCokernel (kernel.ι f)) φQ
  let eN := (filteredCokernelCofork_isColimit f).coconePointUniqueUpToIso
    (colimit.isColimit _)
  have hN : n ≫ eN.hom = cokernel.π f := by
    change (filteredCokernelCofork f).π ≫ eN.hom = cokernel.π f
    simpa [eN] using
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (filteredCokernelCofork_isColimit f) (colimit.isColimit _) WalkingParallelPair.one
  let φI : Arrow.mk n ≅ Arrow.mk (cokernel.π f) :=
    Arrow.isoMk' n (cokernel.π f) (Iso.refl _) eN (by simpa using hN.symm)
  let eI₀ := KernelFork.mapIsoOfIsLimit
    (filteredKernelFork_isLimit n) (limit.isLimit _) φI
  have hI : eI₀.hom ≫ kernel.ι (cokernel.π f) =
      (filteredKernelFork n).π.app WalkingParallelPair.zero := by
    have hleft : φI.hom.left = 𝟙 B := by rfl
    simpa [eI₀, KernelFork.mapIsoOfIsLimit, φI, hleft] using
      KernelFork.mapOfIsLimit_ι (filteredKernelFork n) (limit.isLimit _)
        φI.hom
  have hfork : (filteredKernelFork n).π.app WalkingParallelPair.zero = ι := by
    rfl
  let : Epi q₀ := epi_of_isColimit_cofork
    (filteredCokernelCofork_isColimit k)
  have hqQ : q₀ ≫ eQ₀.hom = Abelian.coimage.π f := by
    simp [q₀, eQ₀, φQ]
  have hli' : l ≫ ι = f := by
    apply FilteredHom.ext _ _
    exact hli
  have hrel : eQ₀.hom ≫ Abelian.coimageImageComparison f =
      c₀ ≫ eI₀.hom := by
    apply coimageComparison_eq_of_factorisations f q₀ c₀ l ι
      eQ₀.hom eI₀.hom hqQ hq₀c hli'
    exact hI.trans hfork
  have hl0epi : Epi l.hom := by
    change Epi (Abelian.factorThruImage f.hom ≫
      (Subobject.underlyingIso (kernel.ι (cokernel.π f.hom))).inv)
    infer_instance
  let eKc : kernel f.hom ≅ (filteredKernel f).carrier :=
    (Subobject.underlyingIso (kernel.ι f.hom)).symm
  have hk : eKc.hom ≫ k.hom = kernel.ι f.hom := by
    change (Subobject.underlyingIso (kernel.ι f.hom)).inv ≫
      (Subobject.mk (kernel.ι f.hom)).arrow = kernel.ι f.hom
    simp
  let hck := cokernel.ofIsoComp (f := kernel.ι f.hom) k.hom eKc hk
  let eQ : (filteredCokernelCofork k).pt.carrier ≅
      cokernel (kernel.ι f.hom) := by
    change cokernel k.hom ≅ cokernel (kernel.ι f.hom)
    exact (cokernelIsCokernel k.hom).coconePointUniqueUpToIso hck
  have hqstd : q₀.hom ≫ eQ.hom = cokernel.π (kernel.ι f.hom) := by
    change cokernel.π k.hom ≫ eQ.hom = cokernel.π (kernel.ι f.hom)
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel k.hom) hck WalkingParallelPair.one
  let : Epi l.hom := hl0epi
  have hc0epi : Epi c₀.hom := by
    apply epi_of_epi_fac (f := q₀.hom) (g := c₀.hom) (h := l.hom)
    exact congrArg FilteredHom.hom hq₀c
  have Epi_q₀_hom : Epi q₀.hom := by
    change Epi (cokernel.π k.hom)
    infer_instance
  let d := eQ.hom ≫ Abelian.factorThruCoimage f.hom
  have hd : c₀.hom ≫ ι.hom = d := by
    apply (cancel_epi q₀.hom).mp
    calc
      q₀.hom ≫ c₀.hom ≫ ι.hom =
          (q₀ ≫ c₀).hom ≫ ι.hom := by simp [Category.assoc]
      _ = l.hom ≫ ι.hom := by rw [hq₀c]
      _ = f.hom := hli
      _ = cokernel.π (kernel.ι f.hom) ≫ Abelian.factorThruCoimage f.hom :=
        (Abelian.coimage.fac f.hom).symm
      _ = (q₀.hom ≫ eQ.hom) ≫ Abelian.factorThruCoimage f.hom := by
        rw [hqstd]
      _ = q₀.hom ≫ d := by
        dsimp [d]
        exact Category.assoc _ _ _
  have hdmono : Mono d := by
    dsimp [d]
    infer_instance
  let : Mono d := hdmono
  have hc0mono : Mono c₀.hom := by
    exact mono_of_mono_fac hd
  let : Epi c₀.hom := hc0epi
  let : Mono c₀.hom := hc0mono
  have hc0iso : IsIso c₀.hom := isIso_of_mono_of_epi c₀.hom
  have hqstrict : Strict q₀ := by
    apply (strict_iff_quotient_filtration q₀
      ((filtered_surjective_iff_epi q₀).2 inferInstance)).2
    intro i
    rfl
  let : Mono ι.hom := by
    change Mono (Subobject.mk (kernel.ι n.hom)).arrow
    infer_instance
  have histrict : Strict ι := by
    apply (strict_iff_induced_filtration ι (by
      change Mono ι.hom
      infer_instance)).2
    intro i
    rfl
  have htotal : (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) =
      (Subobject.map ι.hom).obj (⊤ : Subobject (filteredKernel n).carrier) := by
    rw [← Subobject.exists_iso_map ι.hom]
    rw [← hli]
    rw [exists_comp, exists_top_of_epi l.hom]
  have hc0strict_iff : Strict c₀ ↔
      ∀ i : ℤ,
        (Subobject.«exists» c₀.hom).obj
            ((filteredCokernelCofork k).pt.filtration.obj i) =
          cc.pt.filtration.obj i := by
    exact strict_iff_exists_eq_of_epi c₀
  have hq₀c' : q₀.hom ≫ c₀.hom = l.hom := by
    exact congrArg FilteredHom.hom hq₀c
  have hcomp : q₀.hom ≫ c₀.hom ≫ ι.hom = f.hom := by
    calc
      q₀.hom ≫ c₀.hom ≫ ι.hom =
          (q₀.hom ≫ c₀.hom) ≫ ι.hom := by simp [Category.assoc]
      _ = l.hom ≫ ι.hom := by rw [hq₀c']
      _ = f.hom := hli
  have hqfil (i : ℤ) :
      (filteredCokernelCofork k).pt.filtration.obj i =
        (Subobject.«exists» q₀.hom).obj (A.filtration.obj i) := by
    have hq := (strict_iff_quotient_filtration q₀
      ((filtered_surjective_iff_epi q₀).2 inferInstance)).mp hqstrict i
    simpa only [parallelPair_obj_zero] using hq
  have hstep (i : ℤ) :
      (Subobject.«exists» c₀.hom).obj
          ((filteredCokernelCofork k).pt.filtration.obj i) =
        cc.pt.filtration.obj i ↔
      (Subobject.«exists» f.hom).obj (A.filtration.obj i) =
        (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) ⊓
          B.filtration.obj i := by
    exact filtration_step_iff q₀.hom c₀.hom ι.hom f.hom
      (A.filtration.obj i) ((filteredCokernelCofork k).pt.filtration.obj i)
      (cc.pt.filtration.obj i) (B.filtration.obj i) hcomp (hqfil i) rfl htotal
  have hstrictc : Strict c₀ ↔ IsIso c₀ := by
    exact (strict_iff_isIso_of_hom_iso c₀ hc0iso)
  have hstep_iff : Strict c₀ ↔ Strict f := by
    constructor
    · intro hc i
      exact (hstep i).1 ((hc0strict_iff.mp hc) i)
    · intro hf
      apply hc0strict_iff.mpr
      intro i
      exact (hstep i).2 (hf i)
  have heQiso : IsIso eQ₀.hom := eQ₀.isIso_hom
  have heIiso : IsIso eI₀.hom := eI₀.isIso_hom
  have hiso : IsIso (Abelian.coimageImageComparison f) ↔ IsIso c₀ :=
    isIso_iff_of_iso_comp_eq_comp_iso eQ₀.hom
      (Abelian.coimageImageComparison f) c₀ eI₀.hom heQiso heIiso hrel
  constructor
  · intro hs
    exact hiso.mpr (hstrictc.mp (hstep_iff.mpr hs))
  · intro hi
    exact hstep_iff.mp (hstrictc.mpr (hiso.mp hi))

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
  intro i
  change (Subobject.mk
    (biprod.map (B.filtration.obj i).arrow (D.filtration.obj i).arrow)).Factors
    ((A.filtration.obj i).arrow ≫ biprod.lift f.hom g.hom)
  apply (Subobject.factors_iff _ _).mpr
  let u := (B.filtration.obj i).factorThru
    ((A.filtration.obj i).arrow ≫ f.hom) (f.map_filtration i)
  let v := (D.filtration.obj i).factorThru
    ((A.filtration.obj i).arrow ≫ g.hom) (g.map_filtration i)
  refine ⟨biprod.lift u v ≫
    (Subobject.underlyingIso
      (biprod.map (B.filtration.obj i).arrow (D.filtration.obj i).arrow)).inv, ?_⟩
  dsimp [u, v]
  apply biprod.hom_ext <;> simp [Category.assoc]

theorem strict_biproduct_lift_of_strict_mono {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : A ⟶ D)
    (hf : Strict f) (hfmono : FilteredInjective f) :
    Strict (filteredBiproductLift f g) ∧
      FilteredInjective (filteredBiproductLift f g) := by
  let : Mono f.hom := hfmono
  let h := filteredBiproductLift f g
  have hmono : FilteredInjective h := by
    change Mono (biprod.lift f.hom g.hom)
    constructor
    intro Z a b hab
    apply (cancel_mono f.hom).mp
    simpa only [Category.assoc, biprod.lift_fst] using
      congrArg (fun k => k ≫ biprod.fst) hab
  refine ⟨?_, hmono⟩
  apply (strict_iff_induced_filtration h hmono).2
  intro i
  let T : Subobject (B.carrier ⊞ D.carrier) :=
    Subobject.mk (biprod.map (B.filtration.obj i).arrow
      (D.filtration.obj i).arrow)
  let H : A.carrier ⟶ (B.carrier ⊞ D.carrier) :=
    biprod.lift f.hom g.hom
  let P := (Subobject.pullback H).obj T
  change A.filtration.obj i = P
  apply le_antisymm
  · apply Subobject.le_of_factors
    apply (CategoryTheory.Limits.pullback_factors_iff H T
      (A.filtration.obj i).arrow).2
    change T.Factors
      ((A.filtration.obj i).arrow ≫ biprod.lift f.hom g.hom)
    simpa [h, H, filteredBiproductLift, filteredBiproduct, T] using
      h.map_filtration i
  · rw [(strict_iff_induced_filtration f hfmono).1 hf i]
    apply Subobject.le_of_factors
    apply (CategoryTheory.Limits.pullback_factors_iff f.hom
      (B.filtration.obj i) P.arrow).2
    have hPfac : T.Factors (P.arrow ≫ H) :=
      (CategoryTheory.Limits.pullback_factors_iff H T P.arrow).1
        (Subobject.factors_self P)
    have hTfst : (B.filtration.obj i).Factors
        (T.arrow ≫ biprod.fst) := by
      have hfac := Subobject.factors_comp_arrow
        ((Subobject.underlyingIso
          (biprod.map (B.filtration.obj i).arrow
            (D.filtration.obj i).arrow)).hom ≫ biprod.fst)
      rw [Category.assoc, ← biprod.map_fst
        (B.filtration.obj i).arrow (D.filtration.obj i).arrow,
        ← Category.assoc,
        Subobject.underlyingIso_hom_comp_eq_mk] at hfac
      exact hfac
    have hcomp := Subobject.factors_of_factors_right
      (T.factorThru (P.arrow ≫ H) hPfac)
      (g := T.arrow ≫ biprod.fst) hTfst
    have heq :
        T.factorThru (P.arrow ≫ H) hPfac ≫
            (T.arrow ≫ biprod.fst) =
          (P.arrow ≫ H) ≫ biprod.fst := by
      calc
        T.factorThru (P.arrow ≫ H) hPfac ≫
              (T.arrow ≫ biprod.fst) =
            (T.factorThru (P.arrow ≫ H) hPfac ≫ T.arrow) ≫
              biprod.fst := (Category.assoc _ _ _).symm
        _ = (P.arrow ≫ H) ≫ biprod.fst := by
          rw [Subobject.factorThru_arrow]
    rw [heq] at hcomp
    have hh : H ≫ biprod.fst = f.hom := by
      dsimp [H]
      simp
    rw [Category.assoc, hh] at hcomp
    exact hcomp

def filteredBiproductDesc {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A) :
    filteredBiproduct B D ⟶ A := by
  refine ⟨biprod.desc f.hom g.hom, ?_⟩
  intro i
  let T : Subobject (B.carrier ⊞ D.carrier) :=
    Subobject.mk (biprod.map (B.filtration.obj i).arrow
      (D.filtration.obj i).arrow)
  change (A.filtration.obj i).Factors
    (T.arrow ≫ biprod.desc f.hom g.hom)
  apply (Subobject.factors_iff _ _).mpr
  let u := (A.filtration.obj i).factorThru
    ((B.filtration.obj i).arrow ≫ f.hom) (f.map_filtration i)
  let v := (A.filtration.obj i).factorThru
    ((D.filtration.obj i).arrow ≫ g.hom) (g.map_filtration i)
  refine ⟨(Subobject.underlyingIso
      (biprod.map (B.filtration.obj i).arrow (D.filtration.obj i).arrow)).hom ≫
    biprod.desc u v, ?_⟩
  have hT : T.arrow =
      (Subobject.underlyingIso
        (biprod.map (B.filtration.obj i).arrow
          (D.filtration.obj i).arrow)).hom ≫
        biprod.map (B.filtration.obj i).arrow
          (D.filtration.obj i).arrow := by
    simp [T]
  dsimp [u, v]
  calc
    ((Subobject.underlyingIso
      (biprod.map (B.filtration.obj i).arrow
        (D.filtration.obj i).arrow)).hom ≫
      biprod.desc
        ((A.filtration.obj i).factorThru
          ((B.filtration.obj i).arrow ≫ f.hom) (f.map_filtration i))
        ((A.filtration.obj i).factorThru
          ((D.filtration.obj i).arrow ≫ g.hom) (g.map_filtration i))) ≫
        (A.filtration.obj i).arrow =
      (Subobject.underlyingIso
        (biprod.map (B.filtration.obj i).arrow
          (D.filtration.obj i).arrow)).hom ≫
        (biprod.map (B.filtration.obj i).arrow
          (D.filtration.obj i).arrow) ≫
        biprod.desc f.hom g.hom := by
            rw [Category.assoc]
            congr 1
            simp [biprod.desc_eq, Category.assoc]
    _ = T.arrow ≫ biprod.desc f.hom g.hom := by
      rw [hT]
      simp only [Category.assoc]

theorem strict_biproduct_desc_of_strict_epi {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A)
    (hf : Strict f) (hfepi : FilteredSurjective f) :
    Strict (filteredBiproductDesc f g) ∧
      FilteredSurjective (filteredBiproductDesc f g) := by
  let : Epi f.hom := hfepi
  have hdesc_epi : FilteredSurjective (filteredBiproductDesc f g) := by
    change Epi (biprod.desc f.hom g.hom)
    have hfac : biprod.inl ≫ biprod.desc f.hom g.hom = f.hom :=
      biprod.inl_desc _ _
    exact epi_of_epi_fac hfac
  refine ⟨?_, hdesc_epi⟩
  apply (strict_iff_quotient_filtration
    (filteredBiproductDesc f g) hdesc_epi).2
  intro i
  let T : Subobject (B.carrier ⊞ D.carrier) :=
    Subobject.mk (biprod.map (B.filtration.obj i).arrow
      (D.filtration.obj i).arrow)
  let d : (B.carrier ⊞ D.carrier) ⟶ A.carrier :=
    biprod.desc f.hom g.hom
  let J := (Subobject.«exists» d).obj T
  change A.filtration.obj i = J
  apply le_antisymm
  · rw [(strict_iff_quotient_filtration f hfepi).1 hf i]
    have hBinl : (B.filtration.obj i) ≤
        (Subobject.pullback biprod.inl).obj T := by
      apply Subobject.le_of_factors
      apply (CategoryTheory.Limits.pullback_factors_iff biprod.inl T
        (B.filtration.obj i).arrow).2
      apply (Subobject.factors_iff _ _).mpr
      refine ⟨biprod.inl ≫ (Subobject.underlyingIso
        (biprod.map (B.filtration.obj i).arrow
          (D.filtration.obj i).arrow)).inv, ?_⟩
      simp [T, Category.assoc]
    have hunit : T ≤ (Subobject.pullback d).obj J :=
      ((Subobject.existsPullbackAdj
        d).homEquiv T J
        (CategoryTheory.homOfLE (show
          (Subobject.«exists» d).obj T ≤ J
            from le_rfl))).le
    have hcomp : f.hom = biprod.inl ≫ d := by
      symm
      dsimp [d]
      exact biprod.inl_desc _ _
    have hBpull : (B.filtration.obj i) ≤
        (Subobject.pullback f.hom).obj J := by
      rw [hcomp, Subobject.pullback_comp]
      exact hBinl.trans ((Subobject.pullback biprod.inl).monotone hunit)
    exact ((Subobject.existsPullbackAdj f.hom).homEquiv
      (B.filtration.obj i) J).symm
      (CategoryTheory.homOfLE hBpull) |>.le
  · have hTle : T ≤ (Subobject.pullback
        d).obj (A.filtration.obj i) := by
      apply Subobject.le_of_factors
      apply (CategoryTheory.Limits.pullback_factors_iff
        d (A.filtration.obj i) T.arrow).2
      change (A.filtration.obj i).Factors
        (T.arrow ≫ biprod.desc f.hom g.hom)
      exact (filteredBiproductDesc f g).map_filtration i
    exact ((Subobject.existsPullbackAdj
      d).homEquiv T
        (A.filtration.obj i)).symm
      (CategoryTheory.homOfLE hTle) |>.le

theorem strict_induced_iff {C : Type u} [Category.{v} C] [Abelian C]
    {A : FilteredObject C} (X : Subobject A.carrier) :
    Strict (inducedFilteredHom A X) := by
  have hmono : FilteredInjective (inducedFilteredHom A X) := by
    change Mono X.arrow
    infer_instance
  apply (strict_iff_induced_filtration (inducedFilteredHom A X) hmono).2
  exact fun _ => rfl

theorem strict_quotient_iff {C : Type u} [Category.{v} C] [Abelian C]
    {A : FilteredObject C} {Y : C} (π : A.carrier ⟶ Y) [Epi π] :
    Strict (quotientFilteredHom A π) := by
  apply (strict_iff_quotient_filtration (quotientFilteredHom A π)
    (by change Epi π; infer_instance)).2
  intro i
  rfl

theorem strict_composition_of_strict_of_mono {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hf : Strict f) (hg : Strict g) (hgmono : FilteredInjective g) :
    Strict (f ≫ g) := by
  let : Mono g.hom := hgmono
  have image_comp (X Y Z : C) (f₀ : X ⟶ Y) (g₀ : Y ⟶ Z)
      (P : Subobject X) :
      (Subobject.«exists» (f₀ ≫ g₀)).obj P =
        (Subobject.«exists» g₀).obj
          ((Subobject.«exists» f₀).obj P) := by
    apply le_antisymm
    · exact (((Subobject.existsPullbackAdj (f₀ ≫ g₀)).homEquiv P
          ((Subobject.«exists» g₀).obj
            ((Subobject.«exists» f₀).obj P))).symm
        (by
          rw [Subobject.pullback_comp]
          exact (Subobject.existsPullbackAdj f₀).homEquiv _ _
            ((Subobject.existsPullbackAdj g₀).unit.app
              ((Subobject.«exists» f₀).obj P)))).le
    · exact (((Subobject.existsPullbackAdj g₀).homEquiv
          ((Subobject.«exists» f₀).obj P)
          ((Subobject.«exists» (f₀ ≫ g₀)).obj P)).symm
        (((Subobject.existsPullbackAdj f₀).homEquiv P
            ((Subobject.pullback g₀).obj
              ((Subobject.«exists» (f₀ ≫ g₀)).obj P))).symm
          (by
            rw [← Subobject.pullback_comp]
            exact (Subobject.existsPullbackAdj (f₀ ≫ g₀)).unit.app P))).le
  intro i
  change (Subobject.«exists» (f.hom ≫ g.hom)).obj
      (A.filtration.obj i) =
    (Subobject.«exists» (f.hom ≫ g.hom)).obj (⊤ : Subobject A.carrier) ⊓
      D.filtration.obj i
  have hgi := hg i
  rw [Subobject.exists_iso_map g.hom] at hgi
  rw [image_comp, hf i, image_comp, Subobject.exists_iso_map g.hom,
    Subobject.inf_map, hgi]
  have hle_top :
      (Subobject.map g.hom).obj
          ((Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier)) ≤
        (Subobject.map g.hom).obj (⊤ : Subobject B.carrier) := by
    exact (Subobject.map g.hom).monotone le_top
  apply le_antisymm
  · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
  · exact le_inf inf_le_left
      (le_inf (inf_le_left.trans hle_top) inf_le_right)

theorem strict_composition_of_strict_of_epi {C : Type u} [Category.{v} C]
    [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)
    (hf : Strict f) (hg : Strict g) (hfepi : FilteredSurjective f) :
    Strict (f ≫ g) := by
  let : Epi f.hom := hfepi
  have image_comp (X Y Z : C) (f₀ : X ⟶ Y) (g₀ : Y ⟶ Z)
      (P : Subobject X) :
      (Subobject.«exists» (f₀ ≫ g₀)).obj P =
        (Subobject.«exists» g₀).obj
          ((Subobject.«exists» f₀).obj P) := by
    apply le_antisymm
    · exact (((Subobject.existsPullbackAdj (f₀ ≫ g₀)).homEquiv P
          ((Subobject.«exists» g₀).obj
            ((Subobject.«exists» f₀).obj P))).symm
        (by
          rw [Subobject.pullback_comp]
          exact (Subobject.existsPullbackAdj f₀).homEquiv _ _
            ((Subobject.existsPullbackAdj g₀).unit.app
              ((Subobject.«exists» f₀).obj P)))).le
    · exact (((Subobject.existsPullbackAdj g₀).homEquiv
          ((Subobject.«exists» f₀).obj P)
          ((Subobject.«exists» (f₀ ≫ g₀)).obj P)).symm
        (((Subobject.existsPullbackAdj f₀).homEquiv P
            ((Subobject.pullback g₀).obj
              ((Subobject.«exists» (f₀ ≫ g₀)).obj P))).symm
          (by
            rw [← Subobject.pullback_comp]
            exact (Subobject.existsPullbackAdj (f₀ ≫ g₀)).unit.app P))).le
  have htop :
      (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) =
        (⊤ : Subobject B.carrier) := by
    apply (Subobject.isIso_arrow_iff_eq_top _).mp
    let F := Subobject.imageFactorisation f.hom (⊤ : Subobject A.carrier)
    let _ : Epi F.F.e := by
      exact (strongEpi_of_strongEpiMonoFactorisation
        (Abelian.imageStrongEpiMonoFactorisation
          ((⊤ : Subobject A.carrier).arrow ≫ f.hom)) F.isImage).epi
    let _ : Epi F.F.m := epi_of_epi_fac F.F.fac
    change IsIso F.F.m
    exact isIso_of_mono_of_epi F.F.m
  have hfi := (strict_iff_quotient_filtration f hfepi).1 hf
  intro i
  change (Subobject.«exists» (f.hom ≫ g.hom)).obj
      (A.filtration.obj i) =
    (Subobject.«exists» (f.hom ≫ g.hom)).obj (⊤ : Subobject A.carrier) ⊓
      D.filtration.obj i
  rw [image_comp, ← hfi i, image_comp, htop, hg i]

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

@[instance_reducible]
private noncomputable def fgModuleReprAbelian :
    Abelian (FGModuleRepr (ZMod 2)) := by
  let E : FGModuleRepr (ZMod 2) ≌ FGModuleCat.{0} (ZMod 2) :=
    (FGModuleRepr.embed (ZMod 2)).asEquivalence
  letI : Preadditive (FGModuleRepr (ZMod 2)) :=
    Preadditive.ofFullyFaithful E.fullyFaithfulFunctor
  letI : HasFiniteProducts (FGModuleRepr (ZMod 2)) :=
    { out := fun n =>
        Adjunction.hasLimitsOfShape_of_equivalence E.functor }
  exact abelianOfEquivalence E.functor

@[instance_reducible]
private noncomputable def uliftFgModuleReprAbelian :
    letI : Category.{0} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
      CategoryTheory.uliftCategory _
    Abelian (ULift.{u} (FGModuleRepr (ZMod 2))) := by
  letI : Category.{0} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    CategoryTheory.uliftCategory _
  letI : Abelian (FGModuleRepr (ZMod 2)) := fgModuleReprAbelian
  letI : Preadditive (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    Preadditive.ofFullyFaithful
      (ULift.equivalence (C := FGModuleRepr (ZMod 2))).symm.fullyFaithfulFunctor
  letI : HasFiniteProducts (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    { out := fun n =>
        Adjunction.hasLimitsOfShape_of_equivalence
          (ULift.equivalence (C := FGModuleRepr (ZMod 2))).inverse }
  exact abelianOfEquivalence
    (ULift.equivalence (C := FGModuleRepr (ZMod 2))).inverse

@[instance_reducible]
private noncomputable def uliftHomFgModuleReprAbelian :
    letI : Category.{0} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
      CategoryTheory.uliftCategory _
    letI : Category.{v} (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
      ULiftHom.category
    Abelian (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) := by
  letI : Category.{0} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    CategoryTheory.uliftCategory _
  letI : Category.{v} (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    ULiftHom.category
  letI : Abelian (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    uliftFgModuleReprAbelian
  letI : Preadditive (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    Preadditive.ofFullyFaithful
      (ULiftHom.equiv (C := ULift.{u} (FGModuleRepr (ZMod 2)))).symm.fullyFaithfulFunctor
  letI : HasFiniteProducts
      (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    { out := fun n =>
        Adjunction.hasLimitsOfShape_of_equivalence
          (ULiftHom.equiv (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse }
  exact abelianOfEquivalence
    (ULiftHom.equiv (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse

private theorem uliftHomFgModuleReprUnit_ne_zero
    : letI : Abelian (FGModuleRepr (ZMod 2)) := fgModuleReprAbelian
      letI : Preadditive (FGModuleRepr (ZMod 2)) :=
        fgModuleReprAbelian.toPreadditive
      letI : Category.{0} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
        CategoryTheory.uliftCategory _
      letI : Preadditive (ULift.{u} (FGModuleRepr (ZMod 2))) :=
        Preadditive.ofFullyFaithful
          (ULift.equivalence (C := FGModuleRepr (ZMod 2))).symm.fullyFaithfulFunctor
      letI : Category.{v} (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
        ULiftHom.category
      letI : Abelian (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
        uliftHomFgModuleReprAbelian
    (𝟙 (ULiftHom.objUp (ULift.up (FGModuleRepr.ofFinite (ZMod 2) (ZMod 2)))) :
      _ ⟶ _) ≠ 0 := by
  let : Abelian (FGModuleRepr (ZMod 2)) := fgModuleReprAbelian
  let : Preadditive (FGModuleRepr (ZMod 2)) :=
    fgModuleReprAbelian.toPreadditive
  let : Category.{0} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    CategoryTheory.uliftCategory _
  let : Preadditive (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    Preadditive.ofFullyFaithful
      (ULift.equivalence (C := FGModuleRepr (ZMod 2))).symm.fullyFaithfulFunctor
  let : Category.{v} (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    ULiftHom.category
  let : Preadditive (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    Preadditive.ofFullyFaithful
      (ULiftHom.equiv
        (C := ULift.{u} (FGModuleRepr (ZMod 2)))).symm.fullyFaithfulFunctor
  let : (FGModuleRepr.embed (ZMod 2)).Additive :=
    Functor.FullyFaithful.additive_ofFullyFaithful
      (FGModuleRepr.embed (ZMod 2)).asEquivalence.fullyFaithfulFunctor
  let : (ULift.equivalence
      (C := FGModuleRepr (ZMod 2))).inverse.Additive :=
    Functor.FullyFaithful.additive_ofFullyFaithful
      (ULift.equivalence
        (C := FGModuleRepr (ZMod 2))).symm.fullyFaithfulFunctor
  let : (ULiftHom.equiv
      (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse.Additive :=
    Functor.FullyFaithful.additive_ofFullyFaithful
      (ULiftHom.equiv
        (C := ULift.{u} (FGModuleRepr (ZMod 2)))).symm.fullyFaithfulFunctor
  let V : ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    ULiftHom.objUp (ULift.up (FGModuleRepr.ofFinite (ZMod 2) (ZMod 2)))
  let e := FGModuleRepr.ofFiniteEquiv (ZMod 2) (ZMod 2)
  let x : ((FGModuleRepr.embed (ZMod 2)).obj
      ((ULift.equivalence
        (C := FGModuleRepr (ZMod 2))).inverse.obj
        ((ULiftHom.equiv
          (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse.obj V)) : Type) :=
    ULift.up (e.symm 1)
  have hx : x ≠ 0 := by
    intro hx
    apply (by decide : (1 : ZMod 2) ≠ 0)
    have hx' := congrArg (fun y => e (ULift.down y)) hx
    change e x.down = e 0 at hx'
    simpa [x] using hx'
  intro h
  have h' := congrArg
    (fun k : V ⟶ V =>
      (FGModuleRepr.embed (ZMod 2)).map
        ((ULift.equivalence
          (C := FGModuleRepr (ZMod 2))).inverse.map
          ((ULiftHom.equiv
            (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse.map k))) h
  have hzero :
      (FGModuleRepr.embed (ZMod 2)).map
          ((ULift.equivalence
            (C := FGModuleRepr (ZMod 2))).inverse.map
            ((ULiftHom.equiv
              (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse.map
              (0 : V ⟶ V))) = 0 := by
    rw [Functor.map_zero, Functor.map_zero, Functor.map_zero]
  have h'zero := h'.trans hzero
  have hmap :
      (FGModuleRepr.embed (ZMod 2)).map
          ((ULift.equivalence
            (C := FGModuleRepr (ZMod 2))).inverse.map
            ((ULiftHom.equiv
              (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse.map
              (𝟙 (ULiftHom.objUp
                (ULift.up (FGModuleRepr.ofFinite (ZMod 2) (ZMod 2))))))) =
        𝟙 _ := by
    simp
  have h'' := congrArg
    (fun k => k.hom x) h'zero
  rw [hmap] at h''
  have hid_apply :
      (ConcreteCategory.hom
        ((𝟙 ((FGModuleRepr.embed (ZMod 2)).obj
          ((ULift.equivalence
            (C := FGModuleRepr (ZMod 2))).inverse.obj
            ((ULiftHom.equiv
              (C := ULift.{u} (FGModuleRepr (ZMod 2)))).inverse.obj V))) :
          _ ⟶ _).hom)) x = x := by
    simp [ModuleCat.hom_id, LinearMap.id_apply]
  rw [hid_apply] at h''
  exact hx h''

private theorem nonzero_of_subobject_factor
    {C : Type u} [Category.{v} C] [Abelian C]
    {V W Z : C} (d : V ⟶ W) [Mono d]
    (q : W ⟶ Z) (r : Z ⟶ V) (hId : (𝟙 V : V ⟶ V) ≠ 0)
    (hfactor : (Subobject.underlyingIso d).inv ≫
      (Subobject.mk d).arrow ≫ q ≫ r = 𝟙 V) :
    (Subobject.mk d).arrow ≫ q ≠ 0 := by
  intro hz
  apply hId
  rw [← hfactor]
  simpa only [Category.assoc, zero_comp, comp_zero] using
    congrArg (fun t => (Subobject.underlyingIso d).inv ≫ t ≫ r) hz

private theorem not_strict_of_bot_top
    {C : Type u} [Category.{v} C] [Abelian C]
    {A D : FilteredObject C} (k : A ⟶ D) (hk : k.hom ≠ 0)
    (hA0 : A.filtration.obj 0 = ⊥)
    (hD0 : D.filtration.obj 0 = ⊤) :
    ¬ Strict k := by
  intro hs
  have hi := hs 0
  change (Subobject.«exists» k.hom).obj
      (A.filtration.obj 0) =
    (Subobject.«exists» k.hom).obj (⊤ : Subobject A.carrier) ⊓
      D.filtration.obj 0 at hi
  have hexbot : (Subobject.«exists» k.hom).obj
      (⊥ : Subobject A.carrier) = ⊥ := by
    apply le_antisymm
    · exact ((Subobject.existsPullbackAdj k.hom).homEquiv
        (⊥ : Subobject A.carrier) (⊥ : Subobject D.carrier)).symm
        (CategoryTheory.homOfLE bot_le) |>.le
    · exact bot_le
  rw [hA0, hexbot, hD0] at hi
  rw [inf_top_eq] at hi
  have hi' : (⊥ : Subobject D.carrier) =
      (Subobject.«exists» k.hom).obj
        (⊤ : Subobject A.carrier) := hi
  let I := Subobject.imageFactorisation k.hom
    (⊤ : Subobject A.carrier)
  have hF : Subobject.mk I.F.m =
      (Subobject.«exists» k.hom).obj
        (⊤ : Subobject A.carrier) := by
    change Subobject.mk
        ((Subobject.«exists» k.hom).obj
          (⊤ : Subobject A.carrier)).arrow = _
    simp
  have hfac' : (Subobject.mk I.F.m).Factors k.hom := by
    change ∃ h : A.carrier ⟶ I.F.I,
      h ≫ I.F.m = k.hom
    refine ⟨(asIso (⊤ : Subobject A.carrier).arrow).inv ≫
      I.F.e, ?_⟩
    rw [Category.assoc, I.F.fac]
    simp
  have hfac :
      ((Subobject.«exists» k.hom).obj
          (⊤ : Subobject A.carrier)).Factors k.hom := by
    rw [← hF]
    exact hfac'
  have hbotfac : (⊥ : Subobject D.carrier).Factors k.hom := by
    rw [hi']
    exact hfac
  exact hk ((Subobject.bot_factors_iff_zero _).mp hbotfac)

private theorem diagonal_pullback_bot
    {C : Type u} [Category.{v} C] [Abelian C]
    {V : C} (u d : V ⟶ V ⊞ V) [Mono u] [Mono d]
    (hds : (Subobject.mk d).arrow ≫ biprod.snd =
      (Subobject.underlyingIso d).hom)
    (hus : (Subobject.mk u).arrow ≫ biprod.snd = 0) :
    (Subobject.pullback (Subobject.mk d).arrow).obj
        (Subobject.mk u) = ⊥ := by
  apply le_antisymm
  · apply Subobject.le_of_factors
    apply (Subobject.bot_factors_iff_zero _).2
    have hp := (Subobject.isPullback (Subobject.mk d).arrow
      (Subobject.mk u)).w
    have hp' := congrArg (fun t => t ≫ biprod.snd) hp
    simp only [Category.assoc] at hp'
    rw [hus, hds, comp_zero] at hp'
    apply (cancel_mono (Subobject.underlyingIso d).hom).mp
    calc
      ((Subobject.pullback (Subobject.mk d).arrow).obj
          (Subobject.mk u)).arrow ≫
          (Subobject.underlyingIso d).hom = 0 := hp'.symm
      _ = 0 ≫ (Subobject.underlyingIso d).hom := by simp
  · exact bot_le

private def singleStepFiltration {C : Type u} [Category.{v} C]
    [HasZeroObject C] {W : C} (U : Subobject W) : DecreasingFiltration C W where
  obj i := if i < 0 then ⊤ else if i = 0 then U else ⊥
  antitone := by
    intro i j hij
    by_cases hi : i < 0
    · simp [hi]
    · by_cases hi0 : i = 0
      · subst i
        by_cases hj : j < 0
        · omega
        · by_cases hj0 : j = 0
          · simp [hj0]
          · simp [hj, hj0]
      · have hipos : 0 < i := by omega
        have hjpos : 0 < j := lt_of_lt_of_le hipos hij
        have hj : ¬ j < 0 := by omega
        have hj0 : ¬ j = 0 := by omega
        simp [hi, hi0, hj, hj0]

private theorem diagonalBiproduct_singleStep_zero
    {C : Type u} [Category.{v} C] [Abelian C] (V : C) :
    (Subobject.pullback
      (Subobject.mk (biprod.lift (𝟙 V) (𝟙 V))).arrow).obj
        ((singleStepFiltration (Subobject.mk (biprod.inl : V ⟶ V ⊞ V))).obj 0) = ⊥ := by
  change (Subobject.pullback
    (Subobject.mk (biprod.lift (𝟙 V) (𝟙 V))).arrow).obj
      (Subobject.mk (biprod.inl : V ⟶ V ⊞ V)) = ⊥
  apply diagonal_pullback_bot
  · rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
    simp
  · rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
    simp

set_option maxHeartbeats 2000000 in
theorem exists_strict_composition_failure :
    ∃ (C : Type u) (_ : Category.{v} C) (_ : Abelian C),
      Nonempty (@StrictCompositionFailure C _ _) := by
  let : Abelian (FGModuleRepr (ZMod 2)) :=
    fgModuleReprAbelian
  let : Preadditive (FGModuleRepr (ZMod 2)) :=
    fgModuleReprAbelian.toPreadditive
  let : Category.{0} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    CategoryTheory.uliftCategory _
  let : Preadditive (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    Preadditive.ofFullyFaithful
      (ULift.equivalence (C := FGModuleRepr (ZMod 2))).symm.fullyFaithfulFunctor
  let : Category.{v} (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    ULiftHom.category
  let : Abelian (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    uliftHomFgModuleReprAbelian
  let V : ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2))) :=
    ULiftHom.objUp (ULift.up (FGModuleRepr.ofFinite (ZMod 2) (ZMod 2)))
  let W : ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2))) := V ⊞ V
  let u : V ⟶ W := biprod.inl
  let v : V ⟶ W := biprod.inr
  let d : V ⟶ W := biprod.lift (𝟙 V) (𝟙 V)
  let : Mono u := by
    dsimp [u]
    exact mono_of_mono_fac (biprod.inl_fst)
  let : Mono v := by
    dsimp [v]
    exact mono_of_mono_fac (biprod.inr_snd)
  let : Mono d := by
    dsimp [d]
    exact mono_of_mono_fac (biprod.lift_fst _ _)
  let U : Subobject W := Subobject.mk u
  let X : Subobject W := Subobject.mk d
  let Y : Subobject W := Subobject.mk v
  let F : DecreasingFiltration
      (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) W :=
    singleStepFiltration U
  let B₀ : FilteredObject
      (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    { carrier := W, filtration := F }
  let A₀ : FilteredObject
      (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    inducedFilteredObject B₀ X
  let q : W ⟶ cokernel Y.arrow := cokernel.π Y.arrow
  let D₀ : FilteredObject
      (ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    quotientFilteredObject B₀ q
  let f₀ : A₀ ⟶ B₀ := inducedFilteredHom B₀ X
  let g₀ : B₀ ⟶ D₀ := quotientFilteredHom B₀ q
  have hUfst : IsIso (U.arrow ≫ biprod.fst) := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
    rw [biprod.inl_fst]
    infer_instance
  have hvr : biprod.inr ≫ q = 0 := by
    apply (cancel_epi (Subobject.underlyingIso v).hom).mp
    rw [← Category.assoc,
      Subobject.underlyingIso_hom_comp_eq_mk,
      cokernel.condition, comp_zero]
  have hY : Y.arrow ≫ biprod.fst = 0 := by
    change (Subobject.mk v).arrow ≫ biprod.fst = 0
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
    simp [v]
  let r : cokernel Y.arrow ⟶ V := cokernel.desc Y.arrow biprod.fst hY
  have hqr : q ≫ r = biprod.fst := by
    dsimp [q, r]
    exact cokernel.π_desc _ _ _
  let p : W ⟶ (U : ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2)))) :=
    biprod.fst ≫ (Subobject.underlyingIso u).inv
  have hfactor : q = p ≫ (U.arrow ≫ q) := by
    calc
      q = 𝟙 W ≫ q := by simp
      _ = (biprod.fst ≫ biprod.inl +
          biprod.snd ≫ biprod.inr) ≫ q := by rw [biprod.total]
      _ = biprod.fst ≫ biprod.inl ≫ q +
          biprod.snd ≫ biprod.inr ≫ q := by
        rw [Preadditive.add_comp, Category.assoc, Category.assoc]
      _ = biprod.fst ≫ biprod.inl ≫ q := by rw [hvr, comp_zero, add_zero]
      _ = p ≫ (U.arrow ≫ q) := by
        simp [p, U, u, Category.assoc]
  let : Epi (U.arrow ≫ q) := epi_of_epi_fac hfactor.symm
  have hqu : (Subobject.«exists» q).obj U =
      (⊤ : Subobject (cokernel Y.arrow)) := by
    apply (Subobject.isIso_arrow_iff_eq_top _).mp
    let I := Subobject.imageFactorisation q U
    let _ : Epi I.F.m := epi_of_epi_fac I.F.fac
    change IsIso I.F.m
    exact isIso_of_mono_of_epi I.F.m
  have hnonzero : f₀.hom ≫ g₀.hom ≠
      (0 : A₀.carrier ⟶ D₀.carrier) := by
    change X.arrow ≫ q ≠ 0
    have hId : (𝟙 V : V ⟶ V) ≠ 0 := by
      simpa [V] using uliftHomFgModuleReprUnit_ne_zero
    have hid : (Subobject.underlyingIso d).inv ≫ X.arrow ≫ q ≫ r =
        𝟙 V := by
      rw [hqr]
      rw [← Subobject.underlyingIso_hom_comp_eq_mk]
      simp [d]
    simpa [X] using
      nonzero_of_subobject_factor d q r hId (by simpa [X] using hid)
  have hB0 : B₀.filtration.obj 0 = U := by
    simp [B₀, F, singleStepFiltration]
  have hA0 : A₀.filtration.obj 0 = ⊥ := by
    exact diagonalBiproduct_singleStep_zero V
  have hD0 : D₀.filtration.obj 0 =
      (⊤ : Subobject (cokernel Y.arrow)) := by
    change (Subobject.«exists» q).obj (B₀.filtration.obj 0) = _
    rw [hB0, hqu]
  have hnotstrict : ¬ Strict (f₀ ≫ g₀) :=
    not_strict_of_bot_top (f₀ ≫ g₀) hnonzero hA0 hD0
  have hfstrict : Strict f₀ := by
    simpa only [f₀] using (strict_induced_iff (A := B₀) X)
  have hgstrict : Strict g₀ := by
    exact strict_quotient_iff (A := B₀) (π := q)
  refine ⟨ULiftHom.{v} (ULift.{u} (FGModuleRepr (ZMod 2))),
    inferInstance, inferInstance, ?_⟩
  let S : StrictCompositionFailure :=
    { A := A₀, B := B₀, D := D₀, f := f₀, g := g₀,
      f_strict := hfstrict,
      g_strict := hgstrict,
      composite_nonzero := hnonzero,
      composite_not_strict := hnotstrict }
  exact ⟨S⟩

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
