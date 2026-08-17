import Formalization.Books.Homology.Unit05.AbelianCategories
import Mathlib.Algebra.Category.Grp.Ulift

/-!
# Homological Algebra, Chapter 6: Extensions

The chapter's extensions are represented by Mathlib short exact short complexes
with fixed end terms.  The quotient of the resulting extension category by
isomorphism is the book's `Ext` set; pullback, pushout, the Baer sum, and the
two six-term sequences are then exposed as chapter-facing declarations.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Opposite
open scoped ZeroObject

universe v u w

namespace Formalization.Books.Homology.Unit06

/-! ## Extensions and their morphisms -/

/-- An extension of `B` by `A`, with its structure maps retained explicitly. -/
structure Extension (C : Type u) [Category.{v} C] [Abelian C] (A B : C) where
  middle : C
  inclusion : A ⟶ middle
  projection : middle ⟶ B
  zero : inclusion ≫ projection = 0
  shortExact : (ShortComplex.mk inclusion projection zero).ShortExact

/-- The short complex underlying an extension. -/
def Extension.toShortComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E : Extension C A B) : ShortComplex C :=
  ShortComplex.mk E.inclusion E.projection E.zero

@[simp]
theorem Extension.toShortComplex_f
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E : Extension C A B) : E.toShortComplex.f = E.inclusion :=
  rfl

@[simp]
theorem Extension.toShortComplex_g
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E : Extension C A B) : E.toShortComplex.g = E.projection :=
  rfl

theorem Extension.toShortComplex_shortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E : Extension C A B) : E.toShortComplex.ShortExact :=
  E.shortExact

/-- A morphism of extensions whose end terms are allowed to vary. -/
structure ExtensionMorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B A' B' : C} (E : Extension C A B) (F : Extension C A' B') where
  left : A ⟶ A'
  middle : E.middle ⟶ F.middle
  right : B ⟶ B'
  comm_left : E.inclusion ≫ middle = left ≫ F.inclusion
  comm_right : middle ≫ F.projection = E.projection ≫ right

/-- A morphism in the category of extensions of a fixed `B` by a fixed `A`. -/
structure ExtensionHom
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E F : Extension C A B) where
  middle : E.middle ⟶ F.middle
  comm_left : E.inclusion ≫ middle = F.inclusion
  comm_right : middle ≫ F.projection = E.projection

@[ext]
theorem ExtensionHom.ext
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} {E F : Extension C A B} (f g : ExtensionHom E F)
    (h : f.middle = g.middle) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- View a fixed-endpoint morphism as a varying-endpoint morphism. -/
def ExtensionHom.toExtensionMorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} {E F : Extension C A B} (f : ExtensionHom E F) :
    ExtensionMorphism E F where
  left := 𝟙 A
  middle := f.middle
  right := 𝟙 B
  comm_left := by simpa using f.comm_left
  comm_right := by simpa using f.comm_right

instance extensionCategory
    {C : Type u} [Category.{v} C] [Abelian C] (A B : C) :
    Category (Extension C A B) where
  Hom := ExtensionHom
  id E :=
    { middle := 𝟙 E.middle
      comm_left := by simp
      comm_right := by simp }
  comp := fun {E F G} f g =>
    { middle := f.middle ≫ g.middle
      comm_left := by
        calc
          E.inclusion ≫ (f.middle ≫ g.middle) =
              (E.inclusion ≫ f.middle) ≫ g.middle := by simp [Category.assoc]
          _ = F.inclusion ≫ g.middle := by rw [f.comm_left]
          _ = G.inclusion := g.comm_left
      comm_right := by
        calc
          (f.middle ≫ g.middle) ≫ G.projection =
              f.middle ≫ (g.middle ≫ G.projection) := by simp [Category.assoc]
          _ = f.middle ≫ F.projection := by rw [g.comm_right]
          _ = E.projection := f.comm_right }
  id_comp f := by
    apply ExtensionHom.ext
    simp
  comp_id f := by
    apply ExtensionHom.ext
    simp
  assoc f g h := by
    apply ExtensionHom.ext
    simp [Category.assoc]

def ExtensionHom.toShortComplexHom
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} {E F : Extension C A B} (f : ExtensionHom E F) :
    E.toShortComplex ⟶ F.toShortComplex where
  τ₁ := 𝟙 A
  τ₂ := f.middle
  τ₃ := 𝟙 B
  comm₁₂ := by
    dsimp [Extension.toShortComplex]
    rw [Category.id_comp]
    exact f.comm_left.symm
  comm₂₃ := by
    dsimp [Extension.toShortComplex]
    rw [Category.comp_id]
    exact f.comm_right

/-- Isomorphism of extensions is the relation used to form `Ext`. -/
def extensionObjectIsoSetoid
    {C : Type u} [Category.{v} C] [Abelian C] (A B : C) :
    Setoid (Extension C A B) where
  r E F := Nonempty (E ≅ F)
  iseqv :=
    { refl := fun E => ⟨Iso.refl E⟩
      symm := by
        intro E F h
        rcases h with ⟨e⟩
        exact ⟨e.symm⟩
      trans := by
        intro E F G h₁ h₂
        rcases h₁ with ⟨e₁⟩
        rcases h₂ with ⟨e₂⟩
        exact ⟨e₁.trans e₂⟩ }

/-- The set of isomorphism classes of extensions of `B` by `A`. -/
abbrev Ext
    {C : Type u} [Category.{v} C] [Abelian C] (B A : C) :
    Type (max u v) := Quotient (extensionObjectIsoSetoid A B)

/-- The class of a particular extension. -/
def extensionClass
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E : Extension C A B) : Ext B A :=
  Quotient.mk (extensionObjectIsoSetoid A B) E

/-! ## Pullback and pushout of extensions -/

theorem pullback_extension_shortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B B' : C} (E : Extension C A B) (p : B' ⟶ B) :
    (ShortComplex.mk
      (pullback.lift E.inclusion 0 (by simp [E.zero]))
      (pullback.snd E.projection p)
      (by rw [pullback.lift_snd])).ShortExact := by
  sorry

/-- The pullback extension of `E` along `p : B' ⟶ B`. -/
noncomputable def pullbackExtension
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B B' : C} (E : Extension C A B) (p : B' ⟶ B) : Extension C A B' :=
  { middle := pullback E.projection p
    inclusion := pullback.lift E.inclusion 0 (by simp [E.zero])
    projection := pullback.snd E.projection p
    zero := by rw [pullback.lift_snd]
    shortExact := pullback_extension_shortExact E p }

/-- The canonical morphism from a pullback extension to the original one. -/
noncomputable def pullbackExtensionMorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B B' : C} (E : Extension C A B) (p : B' ⟶ B) :
    ExtensionMorphism (pullbackExtension E p) E where
  left := 𝟙 A
  middle := pullback.fst E.projection p
  right := p
  comm_left := by
    change pullback.lift E.inclusion 0 _ ≫ pullback.fst E.projection p =
      𝟙 A ≫ E.inclusion
    rw [pullback.lift_fst, Category.id_comp]
  comm_right := by
    change pullback.fst E.projection p ≫ E.projection =
      pullback.snd E.projection p ≫ p
    exact pullback.condition

theorem pushout_extension_shortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' B : C} (E : Extension C A B) (a : A ⟶ A') :
    (ShortComplex.mk
      (pushout.inl a E.inclusion)
      (pushout.desc 0 E.projection (by simp [E.zero]))
      (by rw [pushout.inl_desc])).ShortExact := by
  sorry

/-- The pushout extension of `E` along `a : A ⟶ A'`. -/
noncomputable def pushoutExtension
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' B : C} (E : Extension C A B) (a : A ⟶ A') : Extension C A' B :=
  { middle := pushout a E.inclusion
    inclusion := pushout.inl a E.inclusion
    projection := pushout.desc 0 E.projection (by simp [E.zero])
    zero := by rw [pushout.inl_desc]
    shortExact := pushout_extension_shortExact E a }

/-- The canonical morphism from an extension to its pushout. -/
noncomputable def pushoutExtensionMorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' B : C} (E : Extension C A B) (a : A ⟶ A') :
    ExtensionMorphism E (pushoutExtension E a) where
  left := a
  middle := pushout.inr a E.inclusion
  right := 𝟙 B
  comm_left := by
    simpa [pushoutExtension] using
      (pushout.condition : a ≫ pushout.inl a E.inclusion =
        E.inclusion ≫ pushout.inr a E.inclusion).symm
  comm_right := by
    change pushout.inr a E.inclusion ≫
        pushout.desc 0 E.projection _ = E.projection ≫ 𝟙 B
    rw [pushout.inr_desc, Category.comp_id]

theorem pullback_extension_preserves_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B B' : C} {E F : Extension C A B} (p : B' ⟶ B)
    (h : Nonempty (E ≅ F)) :
    Nonempty (pullbackExtension E p ≅ pullbackExtension F p) := by
  sorry

theorem pushout_extension_preserves_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' B : C} {E F : Extension C A B} (a : A ⟶ A')
    (h : Nonempty (E ≅ F)) :
    Nonempty (pushoutExtension E a ≅ pushoutExtension F a) := by
  sorry

/-- Pullback on extension classes. -/
noncomputable def pullbackClass
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B B' : C} (p : B' ⟶ B) : Ext B A → Ext B' A :=
  Quotient.map (fun E => pullbackExtension E p) (by
    intro E F h
    exact pullback_extension_preserves_iso p h)

/-- Pushout on extension classes. -/
noncomputable def pushoutClass
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' B : C} (a : A ⟶ A') : Ext B A → Ext B A' :=
  Quotient.map (fun E => pushoutExtension E a) (by
    intro E F h
    exact pushout_extension_preserves_iso a h)

/-- Simultaneous pushout and pullback on extension classes. -/
noncomputable def extensionClassMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' B B' : C} (a : A ⟶ A') (p : B' ⟶ B) :
    Ext B A → Ext B' A' :=
  fun x => pullbackClass p (pushoutClass a x)

theorem pullbackClass_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B B' B'' : C} (p : B' ⟶ B) (q : B'' ⟶ B') (x : Ext B A) :
    pullbackClass q (pullbackClass p x) = pullbackClass (q ≫ p) x := by
  sorry

theorem pushoutClass_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' A'' B : C} (a : A ⟶ A') (b : A' ⟶ A'') (x : Ext B A) :
    pushoutClass b (pushoutClass a x) = pushoutClass (a ≫ b) x := by
  sorry

theorem pushout_pullback_extension_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' B B' : C} (E : Extension C A B) (a : A ⟶ A') (p : B' ⟶ B) :
    Nonempty
      (pushoutExtension (pullbackExtension E p) a ≅
        pullbackExtension (pushoutExtension E a) p) := by
  sorry

theorem pushout_pullbackClass_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' B B' : C} (a : A ⟶ A') (p : B' ⟶ B) (x : Ext B A) :
    pushoutClass a (pullbackClass p x) =
      pullbackClass p (pushoutClass a x) := by
  sorry

/-- The set-valued functor described in the chapter. -/
noncomputable def extensionClassFunctor
    {C : Type u} [Category.{v} C] [Abelian C] :
    (C × Cᵒᵖ) ⥤ Type (max u v) where
  obj X := Ext X.2.unop X.1
  map {X Y} f := ↾(extensionClassMap f.1 f.2.unop)
  map_id := by
    intro X
    ext x
    sorry
  map_comp := by
    intro X Y Z f g
    ext x
    sorry

/-! ## The Baer sum -/

/-- The diagonal morphism into a binary biproduct. -/
def biprodDiagonal
    {C : Type u} [Category.{v} C] [Abelian C] (X : C) :
    X ⟶ X ⊞ X :=
  biprod.lift (𝟙 X) (𝟙 X)

/-- The codiagonal morphism out of a binary biproduct. -/
def biprodCodiagonal
    {C : Type u} [Category.{v} C] [Abelian C] (X : C) :
    X ⊞ X ⟶ X :=
  biprod.desc (𝟙 X) (𝟙 X)

/-- The direct sum of two extensions, before the pushout and pullback steps. -/
noncomputable def directSumExtension
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E₁ E₂ : Extension C A B) :
    Extension C (A ⊞ A) (B ⊞ B) where
  middle := E₁.middle ⊞ E₂.middle
  inclusion := biprod.map E₁.inclusion E₂.inclusion
  projection := biprod.map E₁.projection E₂.projection
  zero := by sorry
  shortExact := by
    sorry

/-- The extension represented by the Baer sum construction. -/
noncomputable def baerSumExtension
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E₁ E₂ : Extension C A B) : Extension C A B :=
  pullbackExtension
    (pushoutExtension (directSumExtension E₁ E₂) (biprodCodiagonal A))
    (biprodDiagonal B)

theorem baerSumExtension_preserves_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} {E₁ E₁' E₂ E₂' : Extension C A B}
    (h₁ : Nonempty (E₁ ≅ E₁')) (h₂ : Nonempty (E₂ ≅ E₂')) :
    Nonempty (baerSumExtension E₁ E₂ ≅ baerSumExtension E₁' E₂') := by
  sorry

/-- The Baer sum on extension classes. -/
noncomputable def baerSumClass
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} : Ext B A → Ext B A → Ext B A :=
  fun x y =>
    Quotient.liftOn₂ x y
      (fun E₁ E₂ => extensionClass (baerSumExtension E₁ E₂))
      (by
        intro E₁ E₂ E₁' E₂' h₁ h₂
        apply Quotient.sound
        exact baerSumExtension_preserves_iso h₁ h₂)

/-- The split extension represents the zero class. -/
noncomputable def splitExtension
    {C : Type u} [Category.{v} C] [Abelian C] (A B : C) : Extension C A B where
  middle := A ⊞ B
  inclusion := biprod.inl
  projection := biprod.snd
  zero := by simp
  shortExact := by
    sorry

noncomputable def zeroExtClass
    {C : Type u} [Category.{v} C] [Abelian C] {A B : C} : Ext B A :=
  extensionClass (splitExtension A B)

/-- Pushout along `-𝟙 A` gives the inverse extension used by the group law. -/
noncomputable def inverseExtension
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E : Extension C A B) : Extension C A B :=
  pushoutExtension E (-𝟙 A)

theorem inverseExtension_preserves_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} {E F : Extension C A B} (h : Nonempty (E ≅ F)) :
    Nonempty (inverseExtension E ≅ inverseExtension F) := by
  sorry

noncomputable def negExtClass
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} : Ext B A → Ext B A :=
  Quotient.map inverseExtension (by
    intro E F h
    exact inverseExtension_preserves_iso h)

noncomputable instance extClassAdd
    {C : Type u} [Category.{v} C] [Abelian C] {A B : C} : Add (Ext B A) :=
  ⟨baerSumClass⟩

noncomputable instance extClassZero
    {C : Type u} [Category.{v} C] [Abelian C] {A B : C} : Zero (Ext B A) :=
  ⟨zeroExtClass⟩

noncomputable instance extClassNeg
    {C : Type u} [Category.{v} C] [Abelian C] {A B : C} : Neg (Ext B A) :=
  ⟨negExtClass⟩

noncomputable instance extClassAddCommGroup
    {C : Type u} [Category.{v} C] [Abelian C] {A B : C} : AddCommGroup (Ext B A) where
  add_assoc := by sorry
  add_zero := by sorry
  zero_add := by sorry
  neg_add_cancel := by sorry
  add_comm := by sorry
  sub_eq_add_neg := by sorry
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem baer_sum_commutative_group_law
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} : Nonempty (AddCommGroup (Ext B A)) :=
  ⟨inferInstance⟩

/-- The extension-class map is an additive homomorphism in both variables. -/
noncomputable def extensionClassMapAddMonoidHom
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' B B' : C} (a : A ⟶ A') (p : B' ⟶ B) :
    Ext B A →+ Ext B' A' where
  toFun := extensionClassMap a p
  map_zero' := by sorry
  map_add' := by sorry

/-- The extension classes form the group-valued functor implicit in the source. -/
noncomputable def extensionClassAdditiveFunctor
    {C : Type u} [Category.{v} C] [Abelian C] :
    (C × Cᵒᵖ) ⥤ AddCommGrpCat.{max u v} where
  obj X := AddCommGrpCat.of (Ext X.2.unop X.1)
  map {X Y} f := AddCommGrpCat.ofHom
    (extensionClassMapAddMonoidHom f.1 f.2.unop)
  map_id := by
    intro X
    ext x
    sorry
  map_comp := by
    intro X Y Z f g
    ext x
    sorry

theorem baer_sum_functorial
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' B B' : C} (a : A ⟶ A') (p : B' ⟶ B)
    (x y : Ext B A) :
    extensionClassMap a p (x + y) =
      extensionClassMap a p x + extensionClassMap a p y := by
  sorry

/-! ## The canonical six-term sequences -/

/-- A six-arrow sequence, used for each of the chapter's six-term sequences. -/
noncomputable def sixTermSequence
    (G0 G1 G2 G3 G4 G5 G6 : AddCommGrpCat.{w})
    (d0 : G0 ⟶ G1) (d1 : G1 ⟶ G2) (d2 : G2 ⟶ G3)
    (d3 : G3 ⟶ G4) (d4 : G4 ⟶ G5) (d5 : G5 ⟶ G6) :
    ComposableArrows AddCommGrpCat.{w} 6 :=
  (ComposableArrows.mk₅ d1 d2 d3 d4 d5).precomp d0

/-- The Hom group, universe-lifted so that it can occur with `Ext`. -/
abbrev HomGroup
    {C : Type u} [Category.{v} C] [Abelian C] (X Y : C) :
    AddCommGrpCat.{max u v} :=
  AddCommGrpCat.uliftFunctor.{u, v}.obj
    ((preadditiveYoneda.obj Y).obj (Opposite.op X))

noncomputable def homPrecomposition
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y N : C} (f : X ⟶ Y) : HomGroup Y N ⟶ HomGroup X N :=
  AddCommGrpCat.uliftFunctor.map ((preadditiveYoneda.obj N).map f.op)

noncomputable def homPostcomposition
    {C : Type u} [Category.{v} C] [Abelian C]
    {N X Y : C} (f : X ⟶ Y) : HomGroup N X ⟶ HomGroup N Y :=
  AddCommGrpCat.uliftFunctor.map ((preadditiveCoyoneda.obj (Opposite.op N)).map f)

abbrev ExtGroupObject
    {C : Type u} [Category.{v} C] [Abelian C] (B A : C) :
    AddCommGrpCat.{max u v} :=
  AddCommGrpCat.of (Ext B A)

noncomputable def extPullbackHom
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B B' : C} (p : B' ⟶ B) :
    ExtGroupObject B A ⟶ ExtGroupObject B' A :=
  AddCommGrpCat.ofHom
    { toFun := pullbackClass p
      map_zero' := by sorry
      map_add' := by sorry }

noncomputable def extPushoutHom
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' B : C} (a : A ⟶ A') :
    ExtGroupObject B A ⟶ ExtGroupObject B A' :=
  AddCommGrpCat.ofHom
    { toFun := pushoutClass a
      map_zero' := by sorry
      map_add' := by sorry }

/-- Turn the short exact sequence `S` into its extension class. -/
def extensionOfShortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact) : Extension C S.X₁ S.X₃ where
  middle := S.X₂
  inclusion := S.f
  projection := S.g
  zero := S.zero
  shortExact := hS

noncomputable def contravariantBoundary
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact) (N : C) :
    HomGroup S.X₁ N ⟶ ExtGroupObject S.X₃ N :=
  AddCommGrpCat.ofHom
    { toFun := fun h =>
        pushoutClass h.down (extensionClass (extensionOfShortExact hS))
      map_zero' := by sorry
      map_add' := by sorry }

noncomputable def covariantBoundary
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact) (N : C) :
    HomGroup N S.X₃ ⟶ ExtGroupObject N S.X₁ :=
  AddCommGrpCat.ofHom
    { toFun := fun h =>
        pullbackClass h.down (extensionClass (extensionOfShortExact hS))
      map_zero' := by sorry
      map_add' := by sorry }

noncomputable def contravariantExtSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact) (N : C) :
    ComposableArrows AddCommGrpCat.{max u v} 6 :=
  sixTermSequence
    (0 : AddCommGrpCat.{max u v})
    (HomGroup S.X₃ N)
    (HomGroup S.X₂ N)
    (HomGroup S.X₁ N)
    (ExtGroupObject S.X₃ N)
    (ExtGroupObject S.X₂ N)
    (ExtGroupObject S.X₁ N)
    0
    (homPrecomposition S.g)
    (homPrecomposition S.f)
    (contravariantBoundary hS N)
    (extPullbackHom S.g)
    (extPullbackHom S.f)

noncomputable def covariantExtSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact) (N : C) :
    ComposableArrows AddCommGrpCat.{max u v} 6 :=
  sixTermSequence
    (0 : AddCommGrpCat.{max u v})
    (HomGroup N S.X₁)
    (HomGroup N S.X₂)
    (HomGroup N S.X₃)
    (ExtGroupObject N S.X₁)
    (ExtGroupObject N S.X₂)
    (ExtGroupObject N S.X₃)
    0
    (homPostcomposition S.f)
    (homPostcomposition S.g)
    (covariantBoundary hS N)
    (extPushoutHom S.f)
    (extPushoutHom S.g)

theorem contravariant_ext_six_term_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact) :
    ∀ N : C, (contravariantExtSequence S hS N).Exact := by
  intro N
  sorry

theorem covariant_ext_six_term_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact) :
    ∀ N : C, (covariantExtSequence S hS N).Exact := by
  intro N
  sorry

end Formalization.Books.Homology.Unit06
