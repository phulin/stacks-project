import Formalization.Books.Homology.Unit16.GradedObjects
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
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
  let : Mono u.hom := hu
  have map_eq : ∀ P : Subobject A.carrier,
      (Subobject.map u.hom).obj P = Subobject.mk (P.arrow ≫ u.hom) := by
    intro P
    rw [← Subobject.mk_arrow P, Subobject.map_mk]
    apply Subobject.mk_eq_mk_of_comm _ _ (Subobject.underlyingIso P.arrow).symm
    simp
  have map_pullback_eq : ∀ G : Subobject B.carrier,
      (Subobject.map u.hom).obj ((Subobject.pullback u.hom).obj G) =
        (Subobject.map u.hom).obj (⊤ : Subobject A.carrier) ⊓ G := by
    intro G
    let P := (Subobject.pullback u.hom).obj G
    have hPG : (Subobject.map u.hom).obj P ≤ G := by
      rw [map_eq P, ← Subobject.mk_arrow G]
      apply Subobject.le_mk_of_comm
        ((Subobject.underlyingIso (P.arrow ≫ u.hom)).hom ≫
          Subobject.pullbackπ u.hom G)
      dsimp [P]
      rw [Category.assoc, (Subobject.isPullback u.hom G).w,
        Subobject.underlyingIso_hom_comp_eq_mk]
    apply le_antisymm
    · exact le_inf ((Subobject.map u.hom).monotone le_top) hPG
    · let X := (Subobject.map u.hom).obj (⊤ : Subobject A.carrier) ⊓ G
      have hXtop : X ≤ Subobject.mk u.hom := by
        dsimp [X]
        rw [Subobject.map_top]
        exact Subobject.inf_le_left _ _
      let q := Subobject.ofLEMk X u.hom hXtop
      let r := Subobject.ofLE X G (by
        dsimp [X]
        exact Subobject.inf_le_right _ _)
      have hqr : r ≫ G.arrow = q ≫ u.hom := by
        dsimp [q, r]
        simp
      rw [map_eq P]
      apply Subobject.le_mk_of_comm
        ((Subobject.isPullback u.hom G).lift r q hqr)
      dsimp [q, r]
      simp [P]
  constructor
  · intro h i
    have hi := h i
    rw [Subobject.exists_iso_map u.hom] at hi
    have hle : A.filtration.obj i ≤
        (Subobject.pullback u.hom).obj (B.filtration.obj i) := by
      have hmap : (Subobject.map u.hom).obj (A.filtration.obj i) ≤
          B.filtration.obj i := by
        rw [hi]
        exact Subobject.inf_le_right _ _
      exact ((Subobject.mapPullbackAdj u.hom).homEquiv _ _
        (CategoryTheory.homOfLE hmap)).le
    have hge : (Subobject.pullback u.hom).obj (B.filtration.obj i) ≤
        A.filtration.obj i := by
      have hmap : (Subobject.map u.hom).obj
          ((Subobject.pullback u.hom).obj (B.filtration.obj i)) ≤
          (Subobject.map u.hom).obj (A.filtration.obj i) := by
        rw [map_pullback_eq, hi]
      have ht := ((Subobject.mapPullbackAdj u.hom).homEquiv
        ((Subobject.pullback u.hom).obj (B.filtration.obj i))
        ((Subobject.map u.hom).obj (A.filtration.obj i)))
        (CategoryTheory.homOfLE hmap)
      simpa using ht.le
    exact le_antisymm hle hge
  · intro h i
    rw [Subobject.exists_iso_map u.hom]
    rw [h i, map_pullback_eq]

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

theorem strict_iff_preimage_eq_sup_kernel {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) :
    Strict f ↔
      ∀ i : ℤ,
        (Subobject.pullback f.hom).obj (B.filtration.obj i) =
          A.filtration.obj i ⊔ Subobject.mk (kernel.ι f.hom) := by
  have image_pullback_eq (P : Subobject B.carrier) :
      (Subobject.«exists» f.hom).obj
          ((Subobject.pullback f.hom).obj P) =
        (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) ⊓ P := by
    let Q := (Subobject.pullback f.hom).obj P
    let I := (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier)
    let F := Subobject.imageFactorisation f.hom (⊤ : Subobject A.carrier)
    have hF : Subobject.mk F.F.m = I := by
      change Subobject.mk I.arrow = I
      simp
    have hRF : (I ⊓ P) ≤ Subobject.mk F.F.m := by
      rw [hF]
      exact inf_le_left
    let _ : Epi F.F.e :=
      (strongEpi_of_strongEpiMonoFactorisation
        (Abelian.imageStrongEpiMonoFactorisation
          ((⊤ : Subobject A.carrier).arrow ≫ f.hom)) F.isImage).epi
    apply le_antisymm
    · apply le_inf
      · exact (Subobject.«exists» f.hom).monotone le_top
      · exact (((Subobject.existsPullbackAdj f.hom).homEquiv Q P).symm
          (CategoryTheory.homOfLE
            (show Q ≤ (Subobject.pullback f.hom).obj P from le_rfl))).le
    · let R := I ⊓ P
      let r₀ := Subobject.ofLE R (Subobject.mk F.F.m) hRF
      let r := r₀ ≫ (Subobject.underlyingIso F.F.m).hom
      have hr : r ≫ F.F.m = R.arrow := by
        dsimp [r, r₀]
        simp [Subobject.underlyingIso_hom_comp_eq_mk]
      let t := pullback.snd F.F.e r
      let _ : Epi t := Abelian.epi_pullback_of_epi_f F.F.e r
      let qX := pullback.fst F.F.e r ≫ (⊤ : Subobject A.carrier).arrow
      let up := t ≫ Subobject.ofLE R P inf_le_right
      have hq : up ≫ P.arrow = qX ≫ f.hom := by
        calc
          up ≫ P.arrow = t ≫ R.arrow := by
            dsimp [up]
            rw [Category.assoc, Subobject.ofLE_arrow]
          _ = t ≫ r ≫ F.F.m := by rw [hr]
          _ = (t ≫ r) ≫ F.F.m := by simp [Category.assoc]
          _ = (pullback.fst F.F.e r ≫ F.F.e) ≫ F.F.m := by
            rw [← pullback.condition]
          _ = pullback.fst F.F.e r ≫
                ((⊤ : Subobject A.carrier).arrow ≫ f.hom) := by
            simp only [Category.assoc, F.F.fac]
          _ = qX ≫ f.hom := by simp [qX]
      let hpb := Subobject.isPullback f.hom P
      let z := hpb.lift up qX hq
      have hzq : z ≫ Q.arrow = qX := by
        dsimp [z, Q]
        exact hpb.lift_snd _ _ _
      let G := Subobject.imageFactorisation f.hom Q
      let ze := z ≫ G.F.e
      have hze : ze ≫ G.F.m = t ≫ R.arrow := by
        calc
          ze ≫ G.F.m = (z ≫ Q.arrow) ≫ f.hom := by
            dsimp [ze]
            rw [Category.assoc, G.F.fac]
            simp only [Category.assoc]
          _ = qX ≫ f.hom := by rw [hzq]
          _ = t ≫ R.arrow := by
            symm
            simpa [up, t, r, r₀, qX, Category.assoc] using hq
      have hzero : kernel.ι t ≫ ze = 0 := by
        apply (cancel_mono G.F.m).mp
        calc
          (kernel.ι t ≫ ze) ≫ G.F.m =
              kernel.ι t ≫ (ze ≫ G.F.m) := by simp [Category.assoc]
          _ = kernel.ι t ≫ (t ≫ R.arrow) := by rw [hze]
          _ = (kernel.ι t ≫ t) ≫ R.arrow := by simp
          _ = 0 ≫ R.arrow := by rw [kernel.condition]
          _ = 0 := by rw [CategoryTheory.Limits.zero_comp]
          _ = 0 ≫ G.F.m := by rw [CategoryTheory.Limits.zero_comp]
      let d := Abelian.epiDesc t ze hzero
      have hG : Subobject.mk G.F.m =
          (Subobject.«exists» f.hom).obj Q := by
        change Subobject.mk ((Subobject.«exists» f.hom).obj Q).arrow =
          (Subobject.«exists» f.hom).obj Q
        simp
      let d' := d ≫ (Subobject.underlyingIso G.F.m).inv
      have hi : (Subobject.underlyingIso G.F.m).inv ≫
          (Subobject.mk G.F.m).arrow = G.F.m := by
        apply (cancel_epi (Subobject.underlyingIso G.F.m).hom).mp
        simp [Subobject.underlyingIso_hom_comp_eq_mk]
      have hle : R ≤ Subobject.mk G.F.m := by
        apply Subobject.le_of_comm d'
        apply (cancel_epi t).mp
        calc
          t ≫ (d' ≫ (Subobject.mk G.F.m).arrow) =
              (t ≫ d') ≫ (Subobject.mk G.F.m).arrow := by simp
          _ = t ≫ d ≫ G.F.m := by
            dsimp [d']
            simp [Category.assoc, hi]
          _ = t ≫ R.arrow := by
            rw [← Category.assoc, Abelian.comp_epiDesc, hze]
      simpa [R, hG] using hle
  have pullback_exists_eq_sup_kernel (Q : Subobject A.carrier) :
      (Subobject.pullback f.hom).obj
          ((Subobject.«exists» f.hom).obj Q) =
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
      have hs : sQ ≫ f.hom = sA ≫ f.hom := by
        calc
          sQ ≫ f.hom = (pullback.fst G.F.e r' ≫ G.F.e) ≫ G.F.m := by
            dsimp [sQ]
            rw [Category.assoc]
            exact (congrArg (fun k => pullback.fst G.F.e r' ≫ k)
              G.F.fac.symm).trans (Category.assoc _ _ _).symm
          _ = (t ≫ r') ≫ G.F.m := by rw [pullback.condition]
          _ = t ≫ (r' ≫ G.F.m) := by simp [Category.assoc]
          _ = t ≫ (R.arrow ≫ f.hom) := by rw [hr']
          _ = sA ≫ f.hom := by simp [sA, Category.assoc]
      have hdiff : (sA - sQ) ≫ f.hom = 0 := by
        rw [sub_comp, ← hs]
        simp
      let k := kernel.lift f.hom (sA - sQ) hdiff
      have hk : k ≫ kernel.ι f.hom = sA - sQ := by
        dsimp [k]
        simp
      have hdecomp : sA = sQ + k ≫ kernel.ι f.hom := by
        rw [hk]
        abel
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
      have hzero : kernel.ι t ≫ w = 0 := by
        apply (cancel_mono S.arrow).mp
        calc
          (kernel.ι t ≫ w) ≫ S.arrow =
              kernel.ι t ≫ (w ≫ S.arrow) := by simp [Category.assoc]
          _ = kernel.ι t ≫ sA := by rw [hw]
          _ = (kernel.ι t ≫ t) ≫ R.arrow := by simp [sA]
          _ = 0 ≫ R.arrow := by rw [kernel.condition]
          _ = 0 := CategoryTheory.Limits.zero_comp
          _ = 0 ≫ S.arrow := CategoryTheory.Limits.zero_comp.symm
      let d := Abelian.epiDesc t w hzero
      apply Subobject.le_of_comm d
      apply (cancel_epi t).mp
      calc
        t ≫ (d ≫ S.arrow) = (t ≫ d) ≫ S.arrow := by
          rw [Category.assoc]
        _ = w ≫ S.arrow := by rw [Abelian.comp_epiDesc]
        _ = sA := hw
    · exact hle
  have kernel_le_pullback (P : Subobject B.carrier) :
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
  constructor
  · intro h i
    have him :
        (Subobject.«exists» f.hom).obj
            ((Subobject.pullback f.hom).obj (B.filtration.obj i)) =
          (Subobject.«exists» f.hom).obj (A.filtration.obj i) := by
      rw [image_pullback_eq (B.filtration.obj i)]
      exact (h i).symm
    have hRle :
        (Subobject.pullback f.hom).obj (B.filtration.obj i) ≤
          (Subobject.pullback f.hom).obj
            ((Subobject.«exists» f.hom).obj (A.filtration.obj i)) :=
      ((Subobject.existsPullbackAdj f.hom).homEquiv _ _
        (CategoryTheory.homOfLE him.le)).le
    rw [pullback_exists_eq_sup_kernel (A.filtration.obj i)] at hRle
    have hAle : A.filtration.obj i ≤
        (Subobject.pullback f.hom).obj (B.filtration.obj i) := by
      apply ((Subobject.existsPullbackAdj f.hom).homEquiv _ _
        (CategoryTheory.homOfLE (show
          (Subobject.«exists» f.hom).obj (A.filtration.obj i) ≤
            B.filtration.obj i by
              rw [h i]
              exact inf_le_right))).le
    exact le_antisymm hRle
      (sup_le hAle (kernel_le_pullback (B.filtration.obj i)))
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
          (pullback_exists_eq_sup_kernel (A.filtration.obj i)).symm
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
          image_pullback_eq _
        _ = (Subobject.«exists» f.hom).obj (A.filtration.obj i) := by
          apply le_antisymm inf_le_right
          exact le_inf ((Subobject.«exists» f.hom).monotone le_top) le_rfl
    calc
      (Subobject.«exists» f.hom).obj (A.filtration.obj i) =
          (Subobject.«exists» f.hom).obj
            ((Subobject.pullback f.hom).obj (B.filtration.obj i)) := him.symm
      _ = (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) ⊓
          (B.filtration.obj i) := image_pullback_eq _

theorem strict_iff_coimage_image_isIso {C : Type u} [Category.{v} C]
    [Abelian C] {A B : FilteredObject C} (f : A ⟶ B) :
    Strict f ↔ IsIso (Abelian.coimageImageComparison f) := by
  let n := filteredCokernelπ f
  let I := filteredKernel n
  let ι := filteredKernelι n
  let l₀ := kernel.lift n.hom f.hom (by
    have h := congrArg FilteredHom.hom (filteredCokernel_comp f)
    change f.hom ≫ n.hom =
      (0 : filteredHomAddSubgroup A (filteredCokernel f)).1
    change f.hom ≫ n.hom =
      (0 : filteredHomAddSubgroup A (filteredCokernel f)).1 at h
    exact h) ≫
      (Subobject.underlyingIso (kernel.ι n.hom)).inv
  let l : A ⟶ I := ⟨l₀, by
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
    ⟩
  let k := (filteredKernelFork f).π.app WalkingParallelPair.zero
  have hli : l.hom ≫ ι.hom = f.hom := by
    change (kernel.lift n.hom f.hom _ ≫
        (Subobject.underlyingIso (kernel.ι n.hom)).inv) ≫
      (Subobject.mk (kernel.ι n.hom)).arrow = f.hom
    simp only [Category.assoc, Subobject.underlyingIso_arrow, kernel.lift_ι]
  have hkl : k ≫ l = 0 := by
    apply FilteredHom.ext _ _
    letI : Mono ι.hom := by
      change Mono (Subobject.mk (kernel.ι n.hom)).arrow
      infer_instance
    apply (cancel_mono ι.hom).mp
    rw [filteredHom_comp_hom]
    change (k.hom ≫ l.hom) ≫ ι.hom =
      (0 : filteredHomAddSubgroup _ _).1 ≫ ι.hom
    rw [Category.assoc, hli]
    change k.hom ≫ f.hom =
      (0 : (filteredKernel f).carrier ⟶ I.carrier) ≫ ι.hom
    rw [CategoryTheory.Limits.zero_comp]
    change (Subobject.mk (kernel.ι f.hom)).arrow ≫ f.hom = 0
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
      kernel.condition]
    simp
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
  letI : Epi q₀ := epi_of_isColimit_cofork
    (filteredCokernelCofork_isColimit k)
  have hqQ : q₀ ≫ eQ₀.hom = Abelian.coimage.π f := by
    simpa [q₀, eQ₀, φQ] using
      CokernelCofork.π_mapOfIsColimit
        (filteredCokernelCofork_isColimit k)
        (Cofork.ofπ (Abelian.coimage.π f) (cokernel.condition _)) φQ.hom
  have hli' : l ≫ ι = f := by
    apply FilteredHom.ext _ _
    exact hli
  have hrel : eQ₀.hom ≫ Abelian.coimageImageComparison f =
      c₀ ≫ eI₀.hom := by
    apply (cancel_epi q₀).mp
    apply (cancel_mono (kernel.ι (cokernel.π f))).mp
    change (q₀ ≫ eQ₀.hom ≫ Abelian.coimageImageComparison f) ≫
          kernel.ι (cokernel.π f) =
      (q₀ ≫ c₀ ≫ eI₀.hom) ≫ kernel.ι (cokernel.π f)
    calc
      (q₀ ≫ eQ₀.hom ≫ Abelian.coimageImageComparison f) ≫
          kernel.ι (cokernel.π f) =
          (q₀ ≫ eQ₀.hom) ≫ Abelian.coimageImageComparison f ≫
            kernel.ι (cokernel.π f) := by simp [Category.assoc]
      _ = Abelian.coimage.π f ≫ Abelian.coimageImageComparison f ≫
          kernel.ι (cokernel.π f) := by rw [hqQ]
      _ = f := Abelian.coimage_image_factorisation f
      _ = l ≫ ι := hli'.symm
      _ = (q₀ ≫ c₀) ≫ ι := by rw [hq₀c]
      _ = (q₀ ≫ c₀) ≫ (eI₀.hom ≫ kernel.ι (cokernel.π f)) := by
        exact congrArg (fun t => (q₀ ≫ c₀) ≫ t) (hI.trans hfork).symm
      _ = (q₀ ≫ c₀ ≫ eI₀.hom) ≫ kernel.ι (cokernel.π f) := by
        calc
          (q₀ ≫ c₀) ≫ (eI₀.hom ≫ kernel.ι (cokernel.π f)) =
              ((q₀ ≫ c₀) ≫ eI₀.hom) ≫ kernel.ι (cokernel.π f) :=
            (Category.assoc (q₀ ≫ c₀) eI₀.hom
              (kernel.ι (cokernel.π f))).symm
          _ = q₀ ≫ (c₀ ≫
                (eI₀.hom ≫ kernel.ι (cokernel.π f))) := by
            calc
              ((q₀ ≫ c₀) ≫ eI₀.hom) ≫ kernel.ι (cokernel.π f) =
                  (q₀ ≫ c₀) ≫
                    (eI₀.hom ≫ kernel.ι (cokernel.π f)) :=
                Category.assoc (q₀ ≫ c₀) eI₀.hom
                  (kernel.ι (cokernel.π f))
              _ = q₀ ≫ (c₀ ≫
                    (eI₀.hom ≫ kernel.ι (cokernel.π f))) :=
                Category.assoc q₀ c₀
                  (eI₀.hom ≫ kernel.ι (cokernel.π f))
          _ = q₀ ≫ ((c₀ ≫ eI₀.hom) ≫
                kernel.ι (cokernel.π f)) :=
            congrArg (fun t => q₀ ≫ t)
              (Category.assoc c₀ eI₀.hom (kernel.ι (cokernel.π f))).symm
          _ = (q₀ ≫ c₀ ≫ eI₀.hom) ≫
                kernel.ι (cokernel.π f) :=
            (Category.assoc q₀ (c₀ ≫ eI₀.hom)
              (kernel.ι (cokernel.π f))).symm
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
  letI : Epi l.hom := hl0epi
  have hc0epi : Epi c₀.hom := by
    apply epi_of_epi_fac (f := q₀.hom) (g := c₀.hom) (h := l.hom)
    exact congrArg FilteredHom.hom hq₀c
  haveI : Epi q₀.hom := by
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
  letI : Mono d := hdmono
  have hc0mono : Mono c₀.hom := by
    exact mono_of_mono_fac hd
  letI : Epi c₀.hom := hc0epi
  letI : Mono c₀.hom := hc0mono
  have hc0iso : IsIso c₀.hom := isIso_of_mono_of_epi c₀.hom
  have exists_comp : ∀ {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z)
      (P : Subobject X),
      (Subobject.«exists» (a ≫ b)).obj P =
        (Subobject.«exists» b).obj ((Subobject.«exists» a).obj P) := by
    intro X Y Z a b P
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
  have hqstrict : Strict q₀ := by
    apply (strict_iff_quotient_filtration q₀
      ((filtered_surjective_iff_epi q₀).2 inferInstance)).2
    intro i
    rfl
  letI : Mono ι.hom := by
    change Mono (Subobject.mk (kernel.ι n.hom)).arrow
    infer_instance
  have histrict : Strict ι := by
    apply (strict_iff_induced_filtration ι (by
      change Mono ι.hom
      infer_instance)).2
    intro i
    rfl
  have exists_top_of_epi : ∀ {X Y : C} (u : X ⟶ Y) [Epi u],
      (Subobject.«exists» u).obj (⊤ : Subobject X) = ⊤ := by
    intro X Y u hu
    letI : Epi u := hu
    apply (Subobject.isIso_arrow_iff_eq_top _).mp
    let F := Subobject.imageFactorisation u (⊤ : Subobject X)
    let _ : Epi F.F.e := by
      exact (strongEpi_of_strongEpiMonoFactorisation
        (Abelian.imageStrongEpiMonoFactorisation
          ((⊤ : Subobject X).arrow ≫ u)) F.isImage).epi
    let _ : Epi F.F.m := epi_of_epi_fac F.F.fac
    change IsIso F.F.m
    exact isIso_of_mono_of_epi F.F.m
  have htotal : (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) =
      (Subobject.map ι.hom).obj (⊤ : Subobject (filteredKernel n).carrier) := by
    rw [← Subobject.exists_iso_map ι.hom]
    rw [← hli]
    rw [exists_comp, exists_top_of_epi l.hom]
  have hmap_induced (G : Subobject B.carrier) :
      (Subobject.map ι.hom).obj ((Subobject.pullback ι.hom).obj G) =
        (Subobject.map ι.hom).obj
            (⊤ : Subobject (filteredKernel n).carrier) ⊓ G := by
    have map_eq : ∀ P : Subobject (filteredKernel n).carrier,
        (Subobject.map ι.hom).obj P =
          Subobject.mk (P.arrow ≫ ι.hom) := by
      intro P
      rw [← Subobject.mk_arrow P, Subobject.map_mk]
      apply Subobject.mk_eq_mk_of_comm _ _ (Subobject.underlyingIso P.arrow).symm
      simp
    let P := (Subobject.pullback ι.hom).obj G
    have hPG : (Subobject.map ι.hom).obj P ≤ G := by
      rw [map_eq P, ← Subobject.mk_arrow G]
      apply Subobject.le_mk_of_comm
        ((Subobject.underlyingIso (P.arrow ≫ ι.hom)).hom ≫
          Subobject.pullbackπ ι.hom G)
      dsimp [P]
      rw [Category.assoc, (Subobject.isPullback ι.hom G).w,
        Subobject.underlyingIso_hom_comp_eq_mk]
    apply le_antisymm
    · exact le_inf ((Subobject.map ι.hom).monotone le_top) hPG
    · let X := (Subobject.map ι.hom).obj
          (⊤ : Subobject (filteredKernel n).carrier) ⊓ G
      have hXtop : X ≤ Subobject.mk ι.hom := by
        dsimp [X]
        rw [Subobject.map_top]
        exact Subobject.inf_le_left _ _
      let q := Subobject.ofLEMk X ι.hom hXtop
      let r := Subobject.ofLE X G (by
        dsimp [X]
        exact Subobject.inf_le_right _ _)
      have hqr : r ≫ G.arrow = q ≫ ι.hom := by
        dsimp [q, r]
        simp
      rw [map_eq P]
      apply Subobject.le_mk_of_comm
        ((Subobject.isPullback ι.hom G).lift r q hqr)
      dsimp [q, r]
      simp [P]
  have hc0strict_iff : Strict c₀ ↔
      ∀ i : ℤ,
        (Subobject.«exists» c₀.hom).obj
            ((filteredCokernelCofork k).pt.filtration.obj i) =
          cc.pt.filtration.obj i := by
    constructor
    · intro h i
      have hi := h i
      rw [exists_top_of_epi c₀.hom] at hi
      simpa using hi
    · intro h i
      rw [show (Subobject.«exists» c₀.hom).obj
          (⊤ : Subobject (filteredCokernelCofork k).pt.carrier) = ⊤ by
            exact exists_top_of_epi c₀.hom]
      simpa using h i
  have hmap_inj : Function.Injective
      (fun P : Subobject (filteredKernel n).carrier =>
        (Subobject.map ι.hom).obj P) := by
    intro P Q h
    calc
      P = (Subobject.pullback ι.hom).obj
          ((Subobject.map ι.hom).obj P) :=
        (Subobject.pullback_map_self ι.hom P).symm
      _ = (Subobject.pullback ι.hom).obj
          ((Subobject.map ι.hom).obj Q) := congrArg _ h
      _ = Q := Subobject.pullback_map_self ι.hom Q
  have hq₀c' : q₀.hom ≫ c₀.hom = l.hom := by
    exact congrArg FilteredHom.hom hq₀c
  have hcomp : q₀.hom ≫ c₀.hom ≫ ι.hom = f.hom := by
    calc
      q₀.hom ≫ c₀.hom ≫ ι.hom =
          (q₀.hom ≫ c₀.hom) ≫ ι.hom := by simp [Category.assoc]
      _ = l.hom ≫ ι.hom := by rw [hq₀c']
      _ = f.hom := hli
  have hstep (i : ℤ) :
      (Subobject.«exists» c₀.hom).obj
          ((filteredCokernelCofork k).pt.filtration.obj i) =
        cc.pt.filtration.obj i ↔
      (Subobject.«exists» f.hom).obj (A.filtration.obj i) =
        (Subobject.«exists» f.hom).obj (⊤ : Subobject A.carrier) ⊓
          B.filtration.obj i := by
    constructor
    · intro h
      have hq := (strict_iff_quotient_filtration q₀
        ((filtered_surjective_iff_epi q₀).2 inferInstance)).mp hqstrict i
      have hq' :
          (filteredCokernelCofork k).pt.filtration.obj i =
            (Subobject.«exists» q₀.hom).obj (A.filtration.obj i) := by
        simpa only [parallelPair_obj_zero] using hq
      calc
        (Subobject.«exists» f.hom).obj (A.filtration.obj i) =
            (Subobject.«exists» (q₀.hom ≫ c₀.hom ≫ ι.hom)).obj
              (A.filtration.obj i) := by
          rw [hcomp]
        _ = (Subobject.«exists» ι.hom).obj
              ((Subobject.«exists» c₀.hom).obj
                ((Subobject.«exists» q₀.hom).obj (A.filtration.obj i))) := by
          rw [← exists_comp, ← exists_comp]
        _ = (Subobject.map ι.hom).obj
              ((Subobject.«exists» c₀.hom).obj
                ((Subobject.«exists» q₀.hom).obj (A.filtration.obj i))) := by
          rw [Subobject.exists_iso_map ι.hom]
        _ = (Subobject.map ι.hom).obj
              ((Subobject.«exists» c₀.hom).obj
                ((filteredCokernelCofork k).pt.filtration.obj i)) := by
          rw [hq']
        _ = (Subobject.map ι.hom).obj (cc.pt.filtration.obj i) := by
          rw [h]
        _ = (Subobject.map ι.hom).obj
              ((Subobject.pullback ι.hom).obj (B.filtration.obj i)) := rfl
        _ = (Subobject.map ι.hom).obj
              (⊤ : Subobject (filteredKernel n).carrier) ⊓
            B.filtration.obj i := hmap_induced _
        _ = (Subobject.«exists» f.hom).obj
              (⊤ : Subobject A.carrier) ⊓ B.filtration.obj i := by
          rw [htotal]
    · intro h
      apply hmap_inj
      change (Subobject.map ι.hom).obj
          ((Subobject.«exists» c₀.hom).obj
            ((filteredCokernelCofork k).pt.filtration.obj i)) =
        (Subobject.map ι.hom).obj (cc.pt.filtration.obj i)
      have hq := (strict_iff_quotient_filtration q₀
        ((filtered_surjective_iff_epi q₀).2 inferInstance)).mp hqstrict i
      have hq' :
          (filteredCokernelCofork k).pt.filtration.obj i =
            (Subobject.«exists» q₀.hom).obj (A.filtration.obj i) := by
        simpa only [parallelPair_obj_zero] using hq
      calc
        (Subobject.map ι.hom).obj
              ((Subobject.«exists» c₀.hom).obj
                ((filteredCokernelCofork k).pt.filtration.obj i)) =
            (Subobject.map ι.hom).obj
              ((Subobject.«exists» c₀.hom).obj
                ((Subobject.«exists» q₀.hom).obj (A.filtration.obj i))) := by
          rw [hq']
        _ = (Subobject.«exists» f.hom).obj (A.filtration.obj i) := by
          rw [← Subobject.exists_iso_map ι.hom, ← exists_comp, ← exists_comp,
            hcomp]
        _ = (Subobject.«exists» f.hom).obj
              (⊤ : Subobject A.carrier) ⊓ B.filtration.obj i := h
        _ = (Subobject.map ι.hom).obj
              (⊤ : Subobject (filteredKernel n).carrier) ⊓
            B.filtration.obj i := by
          rw [htotal]
        _ = (Subobject.map ι.hom).obj
              ((Subobject.pullback ι.hom).obj (B.filtration.obj i)) :=
          (hmap_induced _).symm
        _ = (Subobject.map ι.hom).obj (cc.pt.filtration.obj i) := rfl
  have strict_iff_isIso_of_hom_iso :
      ∀ {X Y : FilteredObject C} (u : X ⟶ Y), IsIso u.hom →
        (Strict u ↔ IsIso u) := by
    intro X Y u hu
    constructor
    · intro hs
      letI : IsIso u.hom := hu
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
      letI : IsIso u := hu
      have hu_mono : Mono u.hom :=
        (filtered_mono_iff_underlying_mono u).1 (by infer_instance)
      letI : Mono u.hom := hu_mono
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
  constructor
  · intro hs
    have hc : Strict c₀ := hstep_iff.mpr hs
    letI : IsIso c₀ := hstrictc.mp hc
    letI : IsIso eQ₀.hom := heQiso
    letI : IsIso eI₀.hom := heIiso
    have hcomp' : IsIso (eQ₀.hom ≫ Abelian.coimageImageComparison f) := by
      rw [hrel]
      exact IsIso.comp_isIso' (hstrictc.mp hc) heIiso
    letI : IsIso (eQ₀.hom ≫ Abelian.coimageImageComparison f) := hcomp'
    exact IsIso.of_isIso_comp_left eQ₀.hom _
  · intro hi
    have hc : IsIso c₀ := by
      letI : IsIso eQ₀.hom := heQiso
      letI : IsIso eI₀.hom := heIiso
      have hcomp' : IsIso (c₀ ≫ eI₀.hom) := by
        rw [← hrel]
        exact IsIso.comp_isIso' heQiso hi
      letI : IsIso (c₀ ≫ eI₀.hom) := hcomp'
      exact @IsIso.of_isIso_comp_right (FilteredObject C) _ _ _ _ c₀ eI₀.hom
        heIiso hcomp'
    exact hstep_iff.mp (hstrictc.mpr hc)

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
