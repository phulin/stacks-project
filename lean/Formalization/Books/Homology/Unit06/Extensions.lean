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
  let f : A ⟶ pullback E.projection p :=
    pullback.lift E.inclusion 0 (by simp [E.zero])
  let g : pullback E.projection p ⟶ B' := pullback.snd E.projection p
  let z : f ≫ g = 0 := by
    dsimp [f, g]
    rw [pullback.lift_snd]
  let S := ShortComplex.mk f g z
  have hK : IsLimit (KernelFork.ofι f z) := by
    have hE : IsLimit (KernelFork.ofι E.inclusion E.zero) :=
      E.shortExact.fIsKernel
    let lift : ∀ {W' : C} (k : W' ⟶ pullback E.projection p)
        (_ : k ≫ g = 0), W' ⟶ A :=
      fun k hk => hE.lift (KernelFork.ofι (k ≫ pullback.fst E.projection p) (by
        change k ≫ pullback.snd E.projection p = 0 at hk
        rw [Category.assoc, pullback.condition, ← Category.assoc, hk, zero_comp]))
    refine KernelFork.IsLimit.ofι f z lift ?_ ?_
    · intro _ k hk
      change k ≫ pullback.snd E.projection p = 0 at hk
      let l := lift k hk
      apply pullback.hom_ext
      · dsimp [l, lift, f]
        rw [Category.assoc, pullback.lift_fst]
        simpa using
          (hE.fac (KernelFork.ofι (k ≫ pullback.fst E.projection p) _)
            WalkingParallelPair.zero)
      · dsimp [l, lift, f]
        simp only [Category.assoc, pullback.lift_snd, comp_zero]
        exact hk.symm
    · intro _ k hk l hl
      change k ≫ pullback.snd E.projection p = 0 at hk
      dsimp [lift]
      refine hE.uniq (KernelFork.ofι (k ≫ pullback.fst E.projection p) _) l ?_
      intro j
      rcases j with (_ | _)
      · change l ≫ E.inclusion = k ≫ pullback.fst E.projection p
        rw [← hl, Category.assoc, pullback.lift_fst]
      · simp only [KernelFork.app_one, comp_zero]
  change S.ShortExact
  let : Epi E.projection := E.shortExact.epi_g
  let : Epi g := Abelian.epi_pullback_of_epi_f E.projection p
  exact
    { exact := S.exact_of_f_is_kernel hK
      mono_f := mono_of_isLimit_fork hK
      epi_g := inferInstance }

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
  let f : A' ⟶ pushout a E.inclusion := pushout.inl a E.inclusion
  let g : pushout a E.inclusion ⟶ B :=
    pushout.desc 0 E.projection (by simp [E.zero])
  let z : f ≫ g = 0 := by
    dsimp [f, g]
    rw [pushout.inl_desc]
  let S := ShortComplex.mk f g z
  have hC : IsColimit (CokernelCofork.ofπ g z) := by
    have hE : IsColimit (CokernelCofork.ofπ E.projection E.zero) :=
      E.shortExact.gIsCokernel
    let desc : ∀ {Z' : C} (k : pushout a E.inclusion ⟶ Z')
        (_ : f ≫ k = 0), B ⟶ Z' :=
      fun k hk => hE.desc (CokernelCofork.ofπ
        (pushout.inr a E.inclusion ≫ k) (by
          change pushout.inl a E.inclusion ≫ k = 0 at hk
          rw [← Category.assoc, ← pushout.condition, Category.assoc, hk, comp_zero]))
    refine CokernelCofork.IsColimit.ofπ g z desc ?_ ?_
    · intro _ k hk
      change pushout.inl a E.inclusion ≫ k = 0 at hk
      let l := desc k hk
      apply pushout.hom_ext
      · dsimp [l, desc, g]
        rw [← Category.assoc, pushout.inl_desc, zero_comp, hk]
      · dsimp [l, desc, g]
        rw [← Category.assoc, pushout.inr_desc]
        simpa using
          (hE.fac (CokernelCofork.ofπ (pushout.inr a E.inclusion ≫ k) _)
            WalkingParallelPair.one)
    · intro _ k hk l hl
      dsimp [desc]
      refine hE.uniq (CokernelCofork.ofπ (pushout.inr a E.inclusion ≫ k) _) l ?_
      intro j
      rcases j with (_ | _)
      · simp only [CokernelCofork.π_eq_zero, zero_comp]
      · change E.projection ≫ l = pushout.inr a E.inclusion ≫ k
        calc
          E.projection ≫ l =
              (pushout.inr a E.inclusion ≫ g) ≫ l := by
                rw [pushout.inr_desc]
          _ = pushout.inr a E.inclusion ≫ (g ≫ l) := by rw [Category.assoc]
          _ = pushout.inr a E.inclusion ≫ k := by rw [hl]
  change S.ShortExact
  have : Mono E.inclusion := E.shortExact.mono_f
  have : Mono f := Abelian.mono_pushout_of_mono_g a E.inclusion
  exact
    { exact := S.exact_of_g_is_cokernel hC
      mono_f := inferInstance
      epi_g := epi_of_isColimit_cofork hC }

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
  rcases h with ⟨e⟩
  have hhm : e.hom.middle ≫ e.inv.middle = 𝟙 E.middle := by
    exact congrArg (fun q : E ⟶ E => q.middle) e.hom_inv_id
  have hmi : e.inv.middle ≫ e.hom.middle = 𝟙 F.middle := by
    exact congrArg (fun q : F ⟶ F => q.middle) e.inv_hom_id
  let mMiddle : pullback E.projection p ⟶ pullback F.projection p :=
    pullback.lift (pullback.fst E.projection p ≫ e.hom.middle)
      (pullback.snd E.projection p) (by
        rw [Category.assoc, e.hom.comm_right]
        exact pullback.condition)
  let nMiddle : pullback F.projection p ⟶ pullback E.projection p :=
    pullback.lift (pullback.fst F.projection p ≫ e.inv.middle)
      (pullback.snd F.projection p) (by
        rw [Category.assoc, e.inv.comm_right]
        exact pullback.condition)
  let m : pullbackExtension E p ⟶ pullbackExtension F p :=
    { middle := mMiddle
      comm_left := by
        change
          pullback.lift E.inclusion 0 _ ≫ mMiddle =
            pullback.lift F.inclusion 0 _
        apply pullback.hom_ext
        · dsimp [mMiddle]
          rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
            pullback.lift_fst, e.hom.comm_left, pullback.lift_fst]
        · dsimp [mMiddle]
          simp only [Category.assoc, pullback.lift_snd]
      comm_right := by
        change mMiddle ≫ pullback.snd F.projection p =
          pullback.snd E.projection p
        dsimp [mMiddle]
        rw [pullback.lift_snd] }
  let n : pullbackExtension F p ⟶ pullbackExtension E p :=
    { middle := nMiddle
      comm_left := by
        change
          pullback.lift F.inclusion 0 _ ≫ nMiddle =
            pullback.lift E.inclusion 0 _
        apply pullback.hom_ext
        · dsimp [nMiddle]
          rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
            pullback.lift_fst, e.inv.comm_left, pullback.lift_fst]
        · dsimp [nMiddle]
          simp only [Category.assoc, pullback.lift_snd]
      comm_right := by
        change nMiddle ≫ pullback.snd E.projection p =
          pullback.snd F.projection p
        dsimp [nMiddle]
        rw [pullback.lift_snd] }
  have hmn : mMiddle ≫ nMiddle = 𝟙 _ := by
    apply pullback.hom_ext
    · dsimp [mMiddle, nMiddle]
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
        Category.assoc, hhm, Category.comp_id, Category.id_comp]
    · dsimp [mMiddle, nMiddle]
      rw [Category.assoc, pullback.lift_snd, pullback.lift_snd,
        Category.id_comp]
  have hnm : nMiddle ≫ mMiddle = 𝟙 _ := by
    apply pullback.hom_ext
    · dsimp [mMiddle, nMiddle]
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
        Category.assoc, hmi, Category.comp_id, Category.id_comp]
    · dsimp [mMiddle, nMiddle]
      rw [Category.assoc, pullback.lift_snd, pullback.lift_snd,
        Category.id_comp]
  exact ⟨
    { hom := m
      inv := n
      hom_inv_id := ExtensionHom.ext _ _ hmn
      inv_hom_id := ExtensionHom.ext _ _ hnm }⟩

theorem pushout_extension_preserves_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' B : C} {E F : Extension C A B} (a : A ⟶ A')
    (h : Nonempty (E ≅ F)) :
    Nonempty (pushoutExtension E a ≅ pushoutExtension F a) := by
  rcases h with ⟨e⟩
  have hhm : e.hom.middle ≫ e.inv.middle = 𝟙 E.middle := by
    exact congrArg (fun q : E ⟶ E => q.middle) e.hom_inv_id
  have hmi : e.inv.middle ≫ e.hom.middle = 𝟙 F.middle := by
    exact congrArg (fun q : F ⟶ F => q.middle) e.inv_hom_id
  let mMiddle : pushout a E.inclusion ⟶ pushout a F.inclusion :=
    pushout.desc (pushout.inl a F.inclusion)
      (e.hom.middle ≫ pushout.inr a F.inclusion) (by
        rw [pushout.condition, ← Category.assoc, e.hom.comm_left])
  let nMiddle : pushout a F.inclusion ⟶ pushout a E.inclusion :=
    pushout.desc (pushout.inl a E.inclusion)
      (e.inv.middle ≫ pushout.inr a E.inclusion) (by
        rw [pushout.condition, ← Category.assoc, e.inv.comm_left])
  let m : pushoutExtension E a ⟶ pushoutExtension F a :=
    { middle := mMiddle
      comm_left := by
        change pushout.inl a E.inclusion ≫ mMiddle =
          pushout.inl a F.inclusion
        dsimp [mMiddle]
        rw [pushout.inl_desc]
      comm_right := by
        change mMiddle ≫ pushout.desc 0 F.projection _ =
          pushout.desc 0 E.projection _
        apply pushout.hom_ext
        · dsimp [mMiddle]
          rw [← Category.assoc, pushout.inl_desc, pushout.inl_desc,
            pushout.inl_desc]
        · dsimp [mMiddle]
          rw [← Category.assoc, pushout.inr_desc, Category.assoc,
            pushout.inr_desc, e.hom.comm_right, pushout.inr_desc] }
  let n : pushoutExtension F a ⟶ pushoutExtension E a :=
    { middle := nMiddle
      comm_left := by
        change pushout.inl a F.inclusion ≫ nMiddle =
          pushout.inl a E.inclusion
        dsimp [nMiddle]
        rw [pushout.inl_desc]
      comm_right := by
        change nMiddle ≫ pushout.desc 0 E.projection _ =
          pushout.desc 0 F.projection _
        apply pushout.hom_ext
        · dsimp [nMiddle]
          rw [← Category.assoc, pushout.inl_desc, pushout.inl_desc,
            pushout.inl_desc]
        · dsimp [nMiddle]
          rw [← Category.assoc, pushout.inr_desc, Category.assoc,
            pushout.inr_desc, e.inv.comm_right, pushout.inr_desc] }
  have hmn : mMiddle ≫ nMiddle = 𝟙 _ := by
    apply pushout.hom_ext
    · rw [← Category.assoc, pushout.inl_desc, pushout.inl_desc,
        Category.comp_id]
    · dsimp [mMiddle, nMiddle]
      rw [← Category.assoc, pushout.inr_desc, Category.assoc,
        pushout.inr_desc, ← Category.assoc, hhm, Category.id_comp,
        Category.comp_id]
  have hnm : nMiddle ≫ mMiddle = 𝟙 _ := by
    apply pushout.hom_ext
    · rw [← Category.assoc, pushout.inl_desc, pushout.inl_desc,
        Category.comp_id]
    · dsimp [mMiddle, nMiddle]
      rw [← Category.assoc, pushout.inr_desc, Category.assoc,
        pushout.inr_desc, ← Category.assoc, hmi, Category.id_comp,
        Category.comp_id]
  exact ⟨
    { hom := m
      inv := n
      hom_inv_id := ExtensionHom.ext _ _ hmn
      inv_hom_id := ExtensionHom.ext _ _ hnm }⟩

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

private theorem pullback_extension_comp_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B B' B'' : C} (E : Extension C A B) (p : B' ⟶ B) (q : B'' ⟶ B') :
    Nonempty
      (pullbackExtension (pullbackExtension E p) q ≅
        pullbackExtension E (q ≫ p)) := by
  let iP : A ⟶ pullback E.projection p :=
    pullback.lift E.inclusion 0 (by simp [E.zero])
  let iL : A ⟶ pullback (pullback.snd E.projection p) q :=
    pullback.lift iP 0 (by
      dsimp [iP]
      rw [pullback.lift_snd]
      simp)
  let iR : A ⟶ pullback E.projection (q ≫ p) :=
    pullback.lift E.inclusion 0 (by simp [E.zero])
  let rP : pullback E.projection p ⟶ E.middle :=
    pullback.fst E.projection p
  let fP : pullback E.projection p ⟶ B' :=
    pullback.snd E.projection p
  let rL : pullback (pullback.snd E.projection p) q ⟶
      pullback E.projection p :=
    pullback.fst (pullback.snd E.projection p) q
  let fL : pullback (pullback.snd E.projection p) q ⟶ B'' :=
    pullback.snd (pullback.snd E.projection p) q
  let rR : pullback E.projection (q ≫ p) ⟶ E.middle :=
    pullback.fst E.projection (q ≫ p)
  let fR : pullback E.projection (q ≫ p) ⟶ B'' :=
    pullback.snd E.projection (q ≫ p)
  let mMiddle : pullback (pullback.snd E.projection p) q ⟶
      pullback E.projection (q ≫ p) :=
    pullback.lift (rL ≫ rP) fL (by
      dsimp [rL, rP, fL, fP]
      calc
        (pullback.fst (pullback.snd E.projection p) q ≫
            pullback.fst E.projection p) ≫ E.projection =
            pullback.fst (pullback.snd E.projection p) q ≫
              (pullback.fst E.projection p ≫ E.projection) := by simp [Category.assoc]
        _ = pullback.fst (pullback.snd E.projection p) q ≫
              (pullback.snd E.projection p ≫ p) := by rw [pullback.condition]
        _ = (pullback.fst (pullback.snd E.projection p) q ≫
            pullback.snd E.projection p) ≫ p := by simp [Category.assoc]
        _ = (pullback.snd (pullback.snd E.projection p) q ≫ q) ≫ p := by
          rw [pullback.condition]
        _ = pullback.snd (pullback.snd E.projection p) q ≫ (q ≫ p) := by
          simp [Category.assoc])
  let nInner : pullback E.projection (q ≫ p) ⟶ pullback E.projection p :=
    pullback.lift rR (fR ≫ q) (by
      dsimp [rR, fR]
      simp only [Category.assoc]
      rw [pullback.condition])
  let nMiddle : pullback E.projection (q ≫ p) ⟶
      pullback (pullback.snd E.projection p) q :=
    pullback.lift nInner fR (by
      dsimp [nInner]
      rw [pullback.lift_snd])
  have hm_r : mMiddle ≫ rR = rL ≫ rP := by
    dsimp [mMiddle]
    rw [pullback.lift_fst]
  have hm_f : mMiddle ≫ fR = fL := by
    dsimp [mMiddle]
    rw [pullback.lift_snd]
  have hninner_r : nInner ≫ rP = rR := by
    dsimp [nInner]
    rw [pullback.lift_fst]
  have hninner_f : nInner ≫ fP = fR ≫ q := by
    dsimp [nInner]
    rw [pullback.lift_snd]
  have hn_r : nMiddle ≫ rL = nInner := by
    dsimp [nMiddle]
    rw [pullback.lift_fst]
  have hn_f : nMiddle ≫ fL = fR := by
    dsimp [nMiddle]
    rw [pullback.lift_snd]
  have hmn_inner : mMiddle ≫ nInner = rL := by
    apply pullback.hom_ext
    · calc
        (mMiddle ≫ nInner) ≫ rP = mMiddle ≫ (nInner ≫ rP) := by simp [Category.assoc]
        _ = mMiddle ≫ rR := by rw [hninner_r]
        _ = rL ≫ rP := hm_r
    · calc
        (mMiddle ≫ nInner) ≫ fP = mMiddle ≫ (nInner ≫ fP) := by simp [Category.assoc]
        _ = mMiddle ≫ (fR ≫ q) := by rw [hninner_f]
        _ = (mMiddle ≫ fR) ≫ q := by simp [Category.assoc]
        _ = fL ≫ q := by rw [hm_f]
        _ = rL ≫ fP := by
          dsimp [rL, fL, fP]
          rw [pullback.condition]
  have hmn : mMiddle ≫ nMiddle = 𝟙 _ := by
    apply pullback.hom_ext
    · calc
        (mMiddle ≫ nMiddle) ≫ rL = mMiddle ≫ (nMiddle ≫ rL) := by simp [Category.assoc]
        _ = mMiddle ≫ nInner := by rw [hn_r]
        _ = rL := hmn_inner
        _ = 𝟙 _ ≫ rL := by simp
    · calc
        (mMiddle ≫ nMiddle) ≫ fL = mMiddle ≫ (nMiddle ≫ fL) := by simp [Category.assoc]
        _ = mMiddle ≫ fR := by rw [hn_f]
        _ = fL := hm_f
        _ = 𝟙 _ ≫ fL := by simp
  have hnm : nMiddle ≫ mMiddle = 𝟙 _ := by
    apply pullback.hom_ext
    · calc
        (nMiddle ≫ mMiddle) ≫ rR = nMiddle ≫ (mMiddle ≫ rR) := by simp [Category.assoc]
        _ = nMiddle ≫ (rL ≫ rP) := by rw [hm_r]
        _ = (nMiddle ≫ rL) ≫ rP := by simp [Category.assoc]
        _ = nInner ≫ rP := by rw [hn_r]
        _ = rR := hninner_r
        _ = 𝟙 _ ≫ rR := by simp
    · calc
        (nMiddle ≫ mMiddle) ≫ fR = nMiddle ≫ (mMiddle ≫ fR) := by simp [Category.assoc]
        _ = nMiddle ≫ fL := by rw [hm_f]
        _ = fR := hn_f
        _ = 𝟙 _ ≫ fR := by simp
  let m : ExtensionHom (pullbackExtension (pullbackExtension E p) q)
      (pullbackExtension E (q ≫ p)) :=
    { middle := mMiddle
      comm_left := by
        change iL ≫ mMiddle = iR
        apply pullback.hom_ext
        · calc
            (iL ≫ mMiddle) ≫ rR = iL ≫ (mMiddle ≫ rR) := by simp [Category.assoc]
            _ = iL ≫ (rL ≫ rP) := by rw [hm_r]
            _ = (iL ≫ rL) ≫ rP := by simp [Category.assoc]
            _ = iP ≫ rP := by
              dsimp [iL]
              rw [pullback.lift_fst]
            _ = E.inclusion := by
              dsimp [iP, rP]
              rw [pullback.lift_fst]
            _ = iR ≫ rR := by
              dsimp [iR, rR]
              rw [pullback.lift_fst]
        · calc
            (iL ≫ mMiddle) ≫ fR = iL ≫ (mMiddle ≫ fR) := by simp [Category.assoc]
            _ = iL ≫ fL := by rw [hm_f]
            _ = 0 := by
              dsimp [iL]
              rw [pullback.lift_snd]
            _ = iR ≫ fR := by
              dsimp [iR, fR]
              rw [pullback.lift_snd]
      comm_right := by
        change mMiddle ≫ fR = fL
        exact hm_f }
  let n : ExtensionHom (pullbackExtension E (q ≫ p))
      (pullbackExtension (pullbackExtension E p) q) :=
    { middle := nMiddle
      comm_left := by
        change iR ≫ nMiddle = iL
        apply pullback.hom_ext
        · calc
            (iR ≫ nMiddle) ≫ rL = iR ≫ (nMiddle ≫ rL) := by simp [Category.assoc]
            _ = iR ≫ nInner := by rw [hn_r]
            _ = iP := by
              apply pullback.hom_ext
              · calc
                  (iR ≫ nInner) ≫ rP = iR ≫ (nInner ≫ rP) := by simp [Category.assoc]
                  _ = iR ≫ rR := by rw [hninner_r]
                  _ = E.inclusion := by
                    dsimp [iR, rR]
                    rw [pullback.lift_fst]
                  _ = iP ≫ rP := by
                    dsimp [iP, rP]
                    rw [pullback.lift_fst]
              · calc
                  (iR ≫ nInner) ≫ fP = iR ≫ (nInner ≫ fP) := by simp [Category.assoc]
                  _ = iR ≫ (fR ≫ q) := by rw [hninner_f]
                  _ = (iR ≫ fR) ≫ q := by simp [Category.assoc]
                  _ = 0 := by
                    dsimp [iR, fR]
                    rw [pullback.lift_snd, zero_comp]
                  _ = iP ≫ fP := by
                    dsimp [iP, fP]
                    rw [pullback.lift_snd]
            _ = iL ≫ rL := by
              dsimp [iL]
              rw [pullback.lift_fst]
        · calc
            (iR ≫ nMiddle) ≫ fL = iR ≫ (nMiddle ≫ fL) := by simp [Category.assoc]
            _ = iR ≫ fR := by rw [hn_f]
            _ = 0 := by
              dsimp [iR, fR]
              rw [pullback.lift_snd]
            _ = iL ≫ fL := by
              dsimp [iL, fL]
              rw [pullback.lift_snd]
      comm_right := by
        change nMiddle ≫ fL = fR
        exact hn_f }
  exact ⟨
    { hom := m
      inv := n
      hom_inv_id := ExtensionHom.ext _ _ hmn
      inv_hom_id := ExtensionHom.ext _ _ hnm }⟩

private theorem pushout_extension_comp_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' A'' B : C} (E : Extension C A B) (a : A ⟶ A') (b : A' ⟶ A'') :
    Nonempty
      (pushoutExtension (pushoutExtension E a) b ≅
        pushoutExtension E (a ≫ b)) := by
  let iP : A' ⟶ pushout a E.inclusion :=
    pushout.inl a E.inclusion
  let rP : E.middle ⟶ pushout a E.inclusion :=
    pushout.inr a E.inclusion
  let gP : pushout a E.inclusion ⟶ B :=
    pushout.desc 0 E.projection (by simp [E.zero])
  let iL : A'' ⟶ pushout b iP :=
    pushout.inl b iP
  let rL : pushout a E.inclusion ⟶ pushout b iP :=
    pushout.inr b iP
  let gL : pushout b iP ⟶ B :=
    pushout.desc 0 gP (by
      dsimp [gP]
      rw [pushout.inl_desc]
      simp)
  let iR : A'' ⟶ pushout (a ≫ b) E.inclusion :=
    pushout.inl (a ≫ b) E.inclusion
  let rR : E.middle ⟶ pushout (a ≫ b) E.inclusion :=
    pushout.inr (a ≫ b) E.inclusion
  let gR : pushout (a ≫ b) E.inclusion ⟶ B :=
    pushout.desc 0 E.projection (by simp [E.zero])
  let mapP : pushout a E.inclusion ⟶ pushout (a ≫ b) E.inclusion :=
    pushout.desc (b ≫ iR) rR (by
      dsimp [iP, iR, rR]
      calc
        a ≫ (b ≫ pushout.inl (a ≫ b) E.inclusion) =
            (a ≫ b) ≫ pushout.inl (a ≫ b) E.inclusion := by simp [Category.assoc]
        _ = E.inclusion ≫ pushout.inr (a ≫ b) E.inclusion := by
          rw [pushout.condition]
        _ = E.inclusion ≫ rR := by rfl)
  let mMiddle : pushout b iP ⟶ pushout (a ≫ b) E.inclusion :=
    pushout.desc iR mapP (by
      dsimp [iP, iR, mapP]
      rw [pushout.inl_desc])
  let nMiddle : pushout (a ≫ b) E.inclusion ⟶ pushout b iP :=
    pushout.desc iL (rP ≫ rL) (by
      dsimp [iL, rP, rL]
      calc
        (a ≫ b) ≫ pushout.inl b (pushout.inl a E.inclusion) =
            a ≫ (b ≫ pushout.inl b (pushout.inl a E.inclusion)) := by simp [Category.assoc]
        _ = a ≫ (pushout.inl a E.inclusion ≫ pushout.inr b (pushout.inl a E.inclusion)) := by
          rw [pushout.condition]
        _ = (a ≫ pushout.inl a E.inclusion) ≫ pushout.inr b (pushout.inl a E.inclusion) := by
          simp [Category.assoc]
        _ = (E.inclusion ≫ pushout.inr a E.inclusion) ≫
            pushout.inr b (pushout.inl a E.inclusion) := by
          rw [pushout.condition]
        _ = E.inclusion ≫ pushout.inr a E.inclusion ≫
            pushout.inr b (pushout.inl a E.inclusion) := by simp [Category.assoc]
        _ = E.inclusion ≫ pushout.inr a E.inclusion ≫ rL := by rfl)
  have hm_i : iL ≫ mMiddle = iR := by
    dsimp [mMiddle]
    rw [pushout.inl_desc]
  have hm_r : rL ≫ mMiddle = mapP := by
    dsimp [mMiddle]
    rw [pushout.inr_desc]
  have hn_i : iR ≫ nMiddle = iL := by
    dsimp [nMiddle]
    rw [pushout.inl_desc]
  have hn_r : rR ≫ nMiddle = rP ≫ rL := by
    dsimp [nMiddle]
    rw [pushout.inr_desc]
  have hmapP_g : mapP ≫ gR = gP := by
    apply pushout.hom_ext
    · calc
        iP ≫ mapP ≫ gR = (iP ≫ mapP) ≫ gR := by simp [Category.assoc]
        _ = (b ≫ iR) ≫ gR := by rw [show iP ≫ mapP = b ≫ iR by
          dsimp [mapP]
          rw [pushout.inl_desc]]
        _ = 0 := by
          dsimp [iR, gR]
          simp only [Category.assoc, pushout.inl_desc, comp_zero]
        _ = iP ≫ gP := by
          dsimp [iP, gP]
          simp only [pushout.inl_desc]
    · calc
        rP ≫ mapP ≫ gR = (rP ≫ mapP) ≫ gR := by simp [Category.assoc]
        _ = rR ≫ gR := by
          rw [show rP ≫ mapP = rR by
            dsimp [mapP]
            rw [pushout.inr_desc]]
        _ = E.projection := by
          dsimp [rR, gR]
          rw [pushout.inr_desc]
        _ = rP ≫ gP := by
          dsimp [rP, gP]
          rw [pushout.inr_desc]
  have hm_g : mMiddle ≫ gR = gL := by
    apply pushout.hom_ext
    · calc
        iL ≫ mMiddle ≫ gR = (iL ≫ mMiddle) ≫ gR := by simp [Category.assoc]
        _ = iR ≫ gR := by rw [hm_i]
        _ = 0 := by
          dsimp [iR, gR]
          simp only [pushout.inl_desc]
        _ = iL ≫ gL := by
          dsimp [iL, gL]
          simp only [pushout.inl_desc]
    · calc
        rL ≫ mMiddle ≫ gR = (rL ≫ mMiddle) ≫ gR := by simp [Category.assoc]
        _ = mapP ≫ gR := by rw [hm_r]
        _ = gP := hmapP_g
        _ = rL ≫ gL := by
          dsimp [rL, gL]
          rw [pushout.inr_desc]
  have hn_g : nMiddle ≫ gL = gR := by
    apply pushout.hom_ext
    · calc
        iR ≫ nMiddle ≫ gL = (iR ≫ nMiddle) ≫ gL := by simp [Category.assoc]
        _ = iL ≫ gL := by rw [hn_i]
        _ = 0 := by
          dsimp [iL, gL]
          simp only [pushout.inl_desc]
        _ = iR ≫ gR := by
          dsimp [iR, gR]
          simp only [pushout.inl_desc]
    · calc
        rR ≫ nMiddle ≫ gL = (rR ≫ nMiddle) ≫ gL := by simp [Category.assoc]
        _ = (rP ≫ rL) ≫ gL := by rw [hn_r]
        _ = rP ≫ (rL ≫ gL) := by simp [Category.assoc]
        _ = rP ≫ gP := by
          dsimp [rL, gL]
          rw [pushout.inr_desc]
        _ = E.projection := by
          dsimp [rP, gP]
          rw [pushout.inr_desc]
        _ = rR ≫ gR := by
          dsimp [rR, gR]
          rw [pushout.inr_desc]
  have hmn_map : mapP ≫ nMiddle = rL := by
    apply pushout.hom_ext
    · calc
        iP ≫ mapP ≫ nMiddle = (iP ≫ mapP) ≫ nMiddle := by simp [Category.assoc]
        _ = (b ≫ iR) ≫ nMiddle := by rw [show iP ≫ mapP = b ≫ iR by
          dsimp [mapP]
          rw [pushout.inl_desc]]
        _ = b ≫ (iR ≫ nMiddle) := by simp [Category.assoc]
        _ = b ≫ iL := by rw [hn_i]
        _ = iP ≫ rL := by
          dsimp [iP, rL]
          rw [pushout.condition]
    · calc
        rP ≫ mapP ≫ nMiddle = (rP ≫ mapP) ≫ nMiddle := by simp [Category.assoc]
        _ = rR ≫ nMiddle := by
          rw [show rP ≫ mapP = rR by
            dsimp [mapP]
            rw [pushout.inr_desc]]
        _ = rP ≫ rL := hn_r
  have hmn : mMiddle ≫ nMiddle = 𝟙 _ := by
    apply pushout.hom_ext
    · calc
        iL ≫ mMiddle ≫ nMiddle = (iL ≫ mMiddle) ≫ nMiddle := by simp [Category.assoc]
        _ = iR ≫ nMiddle := by rw [hm_i]
        _ = iL := hn_i
        _ = iL ≫ 𝟙 _ := by simp
    · calc
        rL ≫ mMiddle ≫ nMiddle = (rL ≫ mMiddle) ≫ nMiddle := by simp [Category.assoc]
        _ = mapP ≫ nMiddle := by rw [hm_r]
        _ = rL := hmn_map
        _ = rL ≫ 𝟙 _ := by simp
  have hnm : nMiddle ≫ mMiddle = 𝟙 _ := by
    apply pushout.hom_ext
    · calc
        iR ≫ nMiddle ≫ mMiddle = (iR ≫ nMiddle) ≫ mMiddle := by simp [Category.assoc]
        _ = iL ≫ mMiddle := by rw [hn_i]
        _ = iR := hm_i
        _ = iR ≫ 𝟙 _ := by simp
    · calc
        rR ≫ nMiddle ≫ mMiddle = (rR ≫ nMiddle) ≫ mMiddle := by simp [Category.assoc]
        _ = (rP ≫ rL) ≫ mMiddle := by rw [hn_r]
        _ = rP ≫ (rL ≫ mMiddle) := by simp [Category.assoc]
        _ = rP ≫ mapP := by rw [hm_r]
        _ = rR := by
          dsimp [mapP]
          rw [pushout.inr_desc]
        _ = rR ≫ 𝟙 _ := by simp
  let m : ExtensionHom (pushoutExtension (pushoutExtension E a) b)
      (pushoutExtension E (a ≫ b)) :=
    { middle := mMiddle
      comm_left := by
        change iL ≫ mMiddle = iR
        exact hm_i
      comm_right := by
        change mMiddle ≫ gR = gL
        exact hm_g }
  let n : ExtensionHom (pushoutExtension E (a ≫ b))
      (pushoutExtension (pushoutExtension E a) b) :=
    { middle := nMiddle
      comm_left := by
        change iR ≫ nMiddle = iL
        exact hn_i
      comm_right := by
        change nMiddle ≫ gL = gR
        exact hn_g }
  exact ⟨
    { hom := m
      inv := n
      hom_inv_id := ExtensionHom.ext _ _ hmn
      inv_hom_id := ExtensionHom.ext _ _ hnm }⟩

theorem pullbackClass_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B B' B'' : C} (p : B' ⟶ B) (q : B'' ⟶ B') (x : Ext B A) :
    pullbackClass q (pullbackClass p x) = pullbackClass (q ≫ p) x := by
  refine Quotient.inductionOn x ?_
  intro E
  change extensionClass (pullbackExtension (pullbackExtension E p) q) =
    extensionClass (pullbackExtension E (q ≫ p))
  apply Quotient.sound
  exact pullback_extension_comp_iso E p q

theorem pushoutClass_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' A'' B : C} (a : A ⟶ A') (b : A' ⟶ A'') (x : Ext B A) :
    pushoutClass b (pushoutClass a x) = pushoutClass (a ≫ b) x := by
  refine Quotient.inductionOn x ?_
  intro E
  change extensionClass (pushoutExtension (pushoutExtension E a) b) =
    extensionClass (pushoutExtension E (a ≫ b))
  apply Quotient.sound
  exact pushout_extension_comp_iso E a b

theorem pushout_pullback_extension_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' B B' : C} (E : Extension C A B) (a : A ⟶ A') (p : B' ⟶ B) :
    Nonempty
      (pushoutExtension (pullbackExtension E p) a ≅
        pullbackExtension (pushoutExtension E a) p) := by
  let iP : A ⟶ pullback E.projection p :=
    pullback.lift E.inclusion 0 (by simp [E.zero])
  let rP : pullback E.projection p ⟶ E.middle :=
    pullback.fst E.projection p
  let fP : pullback E.projection p ⟶ B' :=
    pullback.snd E.projection p
  have hiP : iP ≫ fP = 0 := by
    dsimp [iP, fP]
    rw [pullback.lift_snd]
  let iL : A' ⟶ pushout a iP :=
    pushout.inl a iP
  let rL : pullback E.projection p ⟶ pushout a iP :=
    pushout.inr a iP
  let gL : pushout a iP ⟶ B' :=
    pushout.desc 0 fP (by
      dsimp [iP, fP]
      rw [pullback.lift_snd]
      simp)
  let iQ : A' ⟶ pushout a E.inclusion :=
    pushout.inl a E.inclusion
  let rQ : E.middle ⟶ pushout a E.inclusion :=
    pushout.inr a E.inclusion
  have hQ : a ≫ (0 : A' ⟶ B) = E.inclusion ≫ E.projection := by
    rw [comp_zero, E.zero]
  let gQ : pushout a E.inclusion ⟶ B :=
    pushout.desc 0 E.projection hQ
  have hiQ : iQ ≫ gQ = 0 := by
    dsimp [iQ, gQ]
    rw [pushout.inl_desc]
  have hgQ : rQ ≫ gQ = E.projection := by
    dsimp [rQ, gQ]
    rw [pushout.inr_desc]
  let iR : A' ⟶ pullback gQ p :=
    pullback.lift iQ 0 (by rw [hiQ, zero_comp])
  let rR : pullback gQ p ⟶ pushout a E.inclusion :=
    pullback.fst gQ p
  let fR : pullback gQ p ⟶ B' :=
    pullback.snd gQ p
  have hmapP : (rP ≫ rQ) ≫ gQ = fP ≫ p := by
    calc
      (rP ≫ rQ) ≫ gQ = rP ≫ (rQ ≫ gQ) := by simp [Category.assoc]
      _ = rP ≫ E.projection := by rw [hgQ]
      _ = fP ≫ p := by
        dsimp [rP, fP]
        exact pullback.condition
  let mapP : pullback E.projection p ⟶ pullback gQ p :=
    pullback.lift (rP ≫ rQ) fP hmapP
  have hmapP_f : mapP ≫ fR = fP := by
    dsimp [mapP]
    rw [pullback.lift_snd]
  let mMiddle : pushout a iP ⟶ pullback gQ p :=
    pushout.desc iR mapP (by
      apply pullback.hom_ext
      · calc
          (a ≫ iR) ≫ rR = a ≫ (iR ≫ rR) := by simp [Category.assoc]
          _ = a ≫ iQ := by
            dsimp [iR, rR]
            rw [pullback.lift_fst]
          _ = E.inclusion ≫ rQ := by
            dsimp [iQ, rQ]
            rw [pushout.condition]
          _ = (iP ≫ rP) ≫ rQ := by
            dsimp [iP, rP]
            rw [pullback.lift_fst]
          _ = iP ≫ (rP ≫ rQ) := by simp [Category.assoc]
          _ = iP ≫ (mapP ≫ rR) := by
            dsimp [mapP]
            rw [pullback.lift_fst]
          _ = (iP ≫ mapP) ≫ rR := by simp [Category.assoc]
      · calc
          (a ≫ iR) ≫ fR = a ≫ (iR ≫ fR) := by simp [Category.assoc]
          _ = 0 := by
            dsimp [iR, fR]
            rw [pullback.lift_snd, comp_zero]
          _ = (iP ≫ mapP) ≫ fR := by
            rw [Category.assoc, hmapP_f]
            exact hiP.symm)
  have hm_i : iL ≫ mMiddle = iR := by
    dsimp [mMiddle]
    rw [pushout.inl_desc]
  have hm_r : rL ≫ mMiddle = mapP := by
    dsimp [mMiddle]
    rw [pushout.inr_desc]
  have hm_f : mapP ≫ fR = fP := by
    exact hmapP_f
  have hm_g : mMiddle ≫ fR = gL := by
    apply pushout.hom_ext
    · calc
        iL ≫ mMiddle ≫ fR = (iL ≫ mMiddle) ≫ fR := by simp [Category.assoc]
        _ = iR ≫ fR := by rw [hm_i]
        _ = 0 := by
          dsimp [iR, fR]
          rw [pullback.lift_snd]
        _ = iL ≫ gL := by
          dsimp [iL, gL]
          rw [pushout.inl_desc]
    · calc
        rL ≫ mMiddle ≫ fR = (rL ≫ mMiddle) ≫ fR := by simp [Category.assoc]
        _ = mapP ≫ fR := by rw [hm_r]
        _ = fP := hm_f
        _ = rL ≫ gL := by
          dsimp [rL, gL]
          rw [pushout.inr_desc]
  let φ : (pushoutExtension (pullbackExtension E p) a).toShortComplex ⟶
      (pullbackExtension (pushoutExtension E a) p).toShortComplex :=
    { τ₁ := 𝟙 A'
      τ₂ := mMiddle
      τ₃ := 𝟙 B'
      comm₁₂ := by
        change 𝟙 A' ≫ iR = iL ≫ mMiddle
        rw [Category.id_comp, hm_i]
      comm₂₃ := by
        change mMiddle ≫ fR = gL ≫ 𝟙 B'
        rw [hm_g, Category.comp_id] }
  have hmono : Mono mMiddle := by
    letI : Mono (pushoutExtension (pullbackExtension E p) a).toShortComplex.f :=
      (pushoutExtension (pullbackExtension E p) a).shortExact.mono_f
    letI : Mono (pullbackExtension (pushoutExtension E a) p).toShortComplex.f :=
      (pullbackExtension (pushoutExtension E a) p).shortExact.mono_f
    letI : Mono φ.τ₁ := by
      dsimp [φ]
      constructor
      intro Z g h w
      rw [← Category.comp_id g, ← Category.comp_id h]
      exact w
    letI : Mono φ.τ₃ := by
      dsimp [φ]
      constructor
      intro Z g h w
      rw [← Category.comp_id g, ← Category.comp_id h]
      exact w
    apply ShortComplex.mono_τ₂_of_exact_of_mono φ
    exact (pushoutExtension (pullbackExtension E p) a).shortExact.exact
  have hepi : Epi mMiddle := by
    letI : Epi (pushoutExtension (pullbackExtension E p) a).toShortComplex.g :=
      (pushoutExtension (pullbackExtension E p) a).shortExact.epi_g
    letI : Epi (pullbackExtension (pushoutExtension E a) p).toShortComplex.g :=
      (pullbackExtension (pushoutExtension E a) p).shortExact.epi_g
    letI : Epi φ.τ₁ := by
      dsimp [φ]
      constructor
      intro Z g h w
      rw [← Category.id_comp g, ← Category.id_comp h]
      exact w
    letI : Epi φ.τ₃ := by
      dsimp [φ]
      constructor
      intro Z g h w
      rw [← Category.id_comp g, ← Category.id_comp h]
      exact w
    apply ShortComplex.epi_τ₂_of_exact_of_epi φ
    exact (pullbackExtension (pushoutExtension E a) p).shortExact.exact
  letI : Mono mMiddle := hmono
  letI : Epi mMiddle := hepi
  letI : IsIso mMiddle := isIso_of_mono_of_epi mMiddle
  let invMiddle : pullback gQ p ⟶ pushout a iP := inv mMiddle
  let m : ExtensionHom (pushoutExtension (pullbackExtension E p) a)
      (pullbackExtension (pushoutExtension E a) p) :=
    { middle := mMiddle
      comm_left := by
        change iL ≫ mMiddle = iR
        exact hm_i
      comm_right := by
        change mMiddle ≫ fR = gL
        exact hm_g }
  let n : ExtensionHom (pullbackExtension (pushoutExtension E a) p)
      (pushoutExtension (pullbackExtension E p) a) :=
    { middle := invMiddle
      comm_left := by
        change iR ≫ invMiddle = iL
        rw [← cancel_mono mMiddle, Category.assoc, IsIso.inv_hom_id,
          Category.comp_id, hm_i]
      comm_right := by
        change invMiddle ≫ gL = fR
        rw [← cancel_epi mMiddle, IsIso.hom_inv_id_assoc, hm_g] }
  exact ⟨
    { hom := m
      inv := n
      hom_inv_id := ExtensionHom.ext _ _ (by
        dsimp [m, n]
        exact IsIso.hom_inv_id mMiddle)
      inv_hom_id := ExtensionHom.ext _ _ (by
        dsimp [m, n]
        exact IsIso.inv_hom_id mMiddle) }⟩

theorem pushout_pullbackClass_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    {A A' B B' : C} (a : A ⟶ A') (p : B' ⟶ B) (x : Ext B A) :
    pushoutClass a (pullbackClass p x) =
      pullbackClass p (pushoutClass a x) := by
  refine Quotient.inductionOn x ?_
  intro E
  change extensionClass (pushoutExtension (pullbackExtension E p) a) =
    extensionClass (pullbackExtension (pushoutExtension E a) p)
  apply Quotient.sound
  exact pushout_pullback_extension_iso E a p

private theorem pullback_extension_id_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E : Extension C A B) :
    Nonempty (pullbackExtension E (𝟙 B) ≅ E) := by
  let m : ExtensionHom (pullbackExtension E (𝟙 B)) E :=
    { middle := pullback.fst E.projection (𝟙 B)
      comm_left := by
        change pullback.lift E.inclusion 0 _ ≫ pullback.fst E.projection (𝟙 B) =
          E.inclusion
        rw [pullback.lift_fst]
      comm_right := by
        change pullback.fst E.projection (𝟙 B) ≫ E.projection =
          pullback.snd E.projection (𝟙 B)
        rw [pullback.condition, Category.comp_id] }
  let n : ExtensionHom E (pullbackExtension E (𝟙 B)) :=
    { middle := pullback.lift (𝟙 E.middle) E.projection (by simp)
      comm_left := by
        change E.inclusion ≫ pullback.lift (𝟙 E.middle) E.projection _ =
          pullback.lift E.inclusion 0 _
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
        · simp only [Category.assoc, pullback.lift_snd]
          rw [E.zero]
      comm_right := by
        change pullback.lift (𝟙 E.middle) E.projection _ ≫
          pullback.snd E.projection (𝟙 B) = E.projection
        rw [pullback.lift_snd] }
  exact ⟨
    { hom := m
      inv := n
      hom_inv_id := ExtensionHom.ext _ _ (by
        change pullback.fst E.projection (𝟙 B) ≫
          pullback.lift (𝟙 E.middle) E.projection _ = 𝟙 _
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, Category.comp_id,
            Category.id_comp]
        · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
          rw [pullback.condition, Category.comp_id])
      inv_hom_id := ExtensionHom.ext _ _ (by
        change pullback.lift (𝟙 E.middle) E.projection _ ≫
          pullback.fst E.projection (𝟙 B) = 𝟙 _
        rw [pullback.lift_fst]) }⟩

private theorem pushout_extension_id_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E : Extension C A B) :
    Nonempty (pushoutExtension E (𝟙 A) ≅ E) := by
  let m : ExtensionHom (pushoutExtension E (𝟙 A)) E :=
    { middle := pushout.desc E.inclusion (𝟙 E.middle) (by simp)
      comm_left := by
        change pushout.inl (𝟙 A) E.inclusion ≫
            pushout.desc E.inclusion (𝟙 E.middle) _ = E.inclusion
        rw [pushout.inl_desc]
      comm_right := by
        change pushout.desc E.inclusion (𝟙 E.middle) _ ≫ E.projection =
          pushout.desc 0 E.projection _
        apply pushout.hom_ext
        · rw [← Category.assoc, pushout.inl_desc, E.zero, pushout.inl_desc]
        · rw [← Category.assoc, pushout.inr_desc, Category.id_comp,
            pushout.inr_desc] }
  let n : ExtensionHom E (pushoutExtension E (𝟙 A)) :=
    { middle := pushout.inr (𝟙 A) E.inclusion
      comm_left := by
        dsimp [pushoutExtension]
        change E.inclusion ≫ pushout.inr (𝟙 A) E.inclusion =
          pushout.inl (𝟙 A) E.inclusion
        simpa using (pushout.condition :
          𝟙 A ≫ pushout.inl (𝟙 A) E.inclusion =
            E.inclusion ≫ pushout.inr (𝟙 A) E.inclusion).symm
      comm_right := by
        change pushout.inr (𝟙 A) E.inclusion ≫
            pushout.desc 0 E.projection _ = E.projection
        rw [pushout.inr_desc] }
  exact ⟨
    { hom := m
      inv := n
      hom_inv_id := ExtensionHom.ext _ _ (by
        change pushout.desc E.inclusion (𝟙 E.middle) _ ≫
          pushout.inr (𝟙 A) E.inclusion = 𝟙 _
        apply pushout.hom_ext
        · rw [← Category.assoc, pushout.inl_desc]
          simpa using (pushout.condition :
            𝟙 A ≫ pushout.inl (𝟙 A) E.inclusion =
              E.inclusion ≫ pushout.inr (𝟙 A) E.inclusion).symm
        · rw [← Category.assoc, pushout.inr_desc]
          simp)
      inv_hom_id := ExtensionHom.ext _ _ (by
        change pushout.inr (𝟙 A) E.inclusion ≫
          pushout.desc E.inclusion (𝟙 E.middle) _ = 𝟙 _
        rw [pushout.inr_desc]) }⟩

/-- The set-valued functor described in the chapter. -/
noncomputable def extensionClassFunctor
    {C : Type u} [Category.{v} C] [Abelian C] :
    (C × Cᵒᵖ) ⥤ Type (max u v) where
  obj X := Ext X.2.unop X.1
  map {X Y} f := ↾(extensionClassMap f.1 f.2.unop)
  map_id := by
    intro X
    ext x
    change extensionClassMap (𝟙 X.1) (𝟙 X.2.unop) x = x
    change pullbackClass (𝟙 X.2.unop) (pushoutClass (𝟙 X.1) x) = x
    refine Quotient.inductionOn x ?_
    intro E
    change extensionClass (pullbackExtension (pushoutExtension E (𝟙 X.1))
      (𝟙 X.2.unop)) = extensionClass E
    apply Quotient.sound
    exact ⟨(pullback_extension_id_iso (pushoutExtension E (𝟙 X.1))).some.trans
      (pushout_extension_id_iso E).some⟩
  map_comp := by
    intro X Y Z f g
    ext x
    change extensionClassMap ((f ≫ g).1) ((f ≫ g).2.unop) x =
      extensionClassMap g.1 g.2.unop (extensionClassMap f.1 f.2.unop x)
    change pullbackClass ((f ≫ g).2.unop) (pushoutClass (f ≫ g).1 x) =
      pullbackClass g.2.unop (pushoutClass g.1
        (pullbackClass f.2.unop (pushoutClass f.1 x)))
    rw [show (f ≫ g).1 = f.1 ≫ g.1 by rfl,
      show (f ≫ g).2.unop = g.2.unop ≫ f.2.unop by rfl]
    rw [pushout_pullbackClass_comm g.1 f.2.unop (pushoutClass f.1 x)]
    rw [pullbackClass_comp, pushoutClass_comp]

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
  zero := by
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_map E₁.inclusion E₂.inclusion,
        Category.assoc, biprod.inl_map E₁.projection E₂.projection,
        ← Category.assoc, E₁.zero, zero_comp]
      simp
    · rw [← Category.assoc, biprod.inr_map E₁.inclusion E₂.inclusion,
        Category.assoc, biprod.inr_map E₁.projection E₂.projection,
        ← Category.assoc, E₂.zero, zero_comp]
      simp
  shortExact := by
    let z : biprod.map E₁.inclusion E₂.inclusion ≫
        biprod.map E₁.projection E₂.projection = 0 := by
      apply biprod.hom_ext'
      · rw [← Category.assoc, biprod.inl_map E₁.inclusion E₂.inclusion,
          Category.assoc, biprod.inl_map E₁.projection E₂.projection,
          ← Category.assoc, E₁.zero, zero_comp]
        simp
      · rw [← Category.assoc, biprod.inr_map E₁.inclusion E₂.inclusion,
          Category.assoc, biprod.inr_map E₁.projection E₂.projection,
          ← Category.assoc, E₂.zero, zero_comp]
        simp
    let S : ShortComplex C :=
      ShortComplex.mk (biprod.map E₁.inclusion E₂.inclusion)
        (biprod.map E₁.projection E₂.projection) z
    have hK₁ := E₁.shortExact.fIsKernel
    have hK₂ := E₂.shortExact.fIsKernel
    letI : Mono E₁.inclusion := E₁.shortExact.mono_f
    letI : Mono E₂.inclusion := E₂.shortExact.mono_f
    letI : Epi E₁.projection := E₁.shortExact.epi_g
    letI : Epi E₂.projection := E₂.shortExact.epi_g
    have hExact : S.Exact := by
      apply S.exact_of_f_is_kernel
      let lift : ∀ s : KernelFork (biprod.map E₁.projection E₂.projection),
          s.pt ⟶ A ⊞ A := fun s =>
        biprod.lift
          (hK₁.lift (KernelFork.ofι (s.ι ≫ biprod.fst) (by
            calc
              (s.ι ≫ biprod.fst) ≫ E₁.projection =
                  s.ι ≫ (biprod.fst ≫ E₁.projection) := by rw [Category.assoc]
              _ = s.ι ≫
                  (biprod.map E₁.projection E₂.projection ≫ biprod.fst) := by
                rw [biprod.map_fst]
              _ = (s.ι ≫ biprod.map E₁.projection E₂.projection) ≫
                  biprod.fst := by rw [Category.assoc]
              _ = 0 := by rw [KernelFork.condition s, zero_comp])))
          (hK₂.lift (KernelFork.ofι (s.ι ≫ biprod.snd) (by
            calc
              (s.ι ≫ biprod.snd) ≫ E₂.projection =
                  s.ι ≫ (biprod.snd ≫ E₂.projection) := by rw [Category.assoc]
              _ = s.ι ≫
                  (biprod.map E₁.projection E₂.projection ≫ biprod.snd) := by
                rw [biprod.map_snd]
              _ = (s.ι ≫ biprod.map E₁.projection E₂.projection) ≫
                  biprod.snd := by rw [Category.assoc]
              _ = 0 := by rw [KernelFork.condition s, zero_comp])))
      refine Fork.IsLimit.mk _ lift ?_ ?_
      · intro s
        apply biprod.hom_ext
        · dsimp [lift]
          dsimp [S]
          simp only [Category.assoc, biprod.map_fst]
          rw [← Category.assoc, biprod.lift_fst]
          simpa only [KernelFork.ι_ofι, Fork.ι_ofι] using
            (Fork.IsLimit.lift_ι (s := KernelFork.ofι E₁.inclusion E₁.zero)
              (t := KernelFork.ofι (s.ι ≫ biprod.fst) _) hK₁)
        · dsimp [lift]
          dsimp [S]
          simp only [Category.assoc, biprod.map_snd]
          rw [← Category.assoc, biprod.lift_snd]
          simpa only [KernelFork.ι_ofι, Fork.ι_ofι] using
            (Fork.IsLimit.lift_ι (s := KernelFork.ofι E₂.inclusion E₂.zero)
              (t := KernelFork.ofι (s.ι ≫ biprod.snd) _) hK₂)
      · intro s m hm
        change m ≫ biprod.map E₁.inclusion E₂.inclusion = s.ι at hm
        apply biprod.hom_ext
        · apply (cancel_mono E₁.inclusion).1
          calc
            (m ≫ biprod.fst) ≫ E₁.inclusion =
                (m ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.fst := by
              calc
                (m ≫ biprod.fst) ≫ E₁.inclusion =
                    m ≫ (biprod.fst ≫ E₁.inclusion) := by rw [Category.assoc]
                _ = m ≫
                    (biprod.map E₁.inclusion E₂.inclusion ≫ biprod.fst) := by
                  rw [biprod.map_fst]
                _ = (m ≫ biprod.map E₁.inclusion E₂.inclusion) ≫
                    biprod.fst := by rw [Category.assoc]
            _ = s.ι ≫ biprod.fst := by rw [hm]
            _ = (lift s ≫ biprod.fst) ≫ E₁.inclusion := by
              dsimp [lift]
              rw [biprod.lift_fst]
              simpa only [KernelFork.ι_ofι, Fork.ι_ofι] using
                (Fork.IsLimit.lift_ι (s := KernelFork.ofι E₁.inclusion E₁.zero)
                  (t := KernelFork.ofι (s.ι ≫ biprod.fst) _) hK₁).symm
        · apply (cancel_mono E₂.inclusion).1
          calc
            (m ≫ biprod.snd) ≫ E₂.inclusion =
                (m ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.snd := by
              calc
                (m ≫ biprod.snd) ≫ E₂.inclusion =
                    m ≫ (biprod.snd ≫ E₂.inclusion) := by rw [Category.assoc]
                _ = m ≫
                    (biprod.map E₁.inclusion E₂.inclusion ≫ biprod.snd) := by
                  rw [biprod.map_snd]
                _ = (m ≫ biprod.map E₁.inclusion E₂.inclusion) ≫
                    biprod.snd := by rw [Category.assoc]
            _ = s.ι ≫ biprod.snd := by rw [hm]
            _ = (lift s ≫ biprod.snd) ≫ E₂.inclusion := by
              dsimp [lift]
              rw [biprod.lift_snd]
              simpa only [KernelFork.ι_ofι, Fork.ι_ofι] using
                (Fork.IsLimit.lift_ι (s := KernelFork.ofι E₂.inclusion E₂.zero)
                  (t := KernelFork.ofι (s.ι ≫ biprod.snd) _) hK₂).symm
    have hmono : Mono (biprod.map E₁.inclusion E₂.inclusion) := by
      constructor
      intro Z g h w
      apply biprod.hom_ext
      · apply (cancel_mono E₁.inclusion).1
        calc
          (g ≫ biprod.fst) ≫ E₁.inclusion =
              (g ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.fst := by
            calc
              (g ≫ biprod.fst) ≫ E₁.inclusion =
                  g ≫ (biprod.fst ≫ E₁.inclusion) := by rw [Category.assoc]
              _ = g ≫
                  (biprod.map E₁.inclusion E₂.inclusion ≫ biprod.fst) := by
                rw [biprod.map_fst]
              _ = (g ≫ biprod.map E₁.inclusion E₂.inclusion) ≫
                  biprod.fst := by rw [Category.assoc]
          _ = (h ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.fst := by
            rw [w]
          _ = (h ≫ biprod.fst) ≫ E₁.inclusion := by
            calc
              (h ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.fst =
                  h ≫ (biprod.map E₁.inclusion E₂.inclusion ≫ biprod.fst) := by
                rw [Category.assoc]
              _ = h ≫ (biprod.fst ≫ E₁.inclusion) := by
                rw [biprod.map_fst]
              _ = (h ≫ biprod.fst) ≫ E₁.inclusion := by rw [Category.assoc]
      · apply (cancel_mono E₂.inclusion).1
        calc
          (g ≫ biprod.snd) ≫ E₂.inclusion =
              (g ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.snd := by
            calc
              (g ≫ biprod.snd) ≫ E₂.inclusion =
                  g ≫ (biprod.snd ≫ E₂.inclusion) := by rw [Category.assoc]
              _ = g ≫
                  (biprod.map E₁.inclusion E₂.inclusion ≫ biprod.snd) := by
                rw [biprod.map_snd]
              _ = (g ≫ biprod.map E₁.inclusion E₂.inclusion) ≫
                  biprod.snd := by rw [Category.assoc]
          _ = (h ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.snd := by
            rw [w]
          _ = (h ≫ biprod.snd) ≫ E₂.inclusion := by
            calc
              (h ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.snd =
                  h ≫ (biprod.map E₁.inclusion E₂.inclusion ≫ biprod.snd) := by
                rw [Category.assoc]
              _ = h ≫ (biprod.snd ≫ E₂.inclusion) := by
                rw [biprod.map_snd]
              _ = (h ≫ biprod.snd) ≫ E₂.inclusion := by rw [Category.assoc]
    have hepi : Epi (biprod.map E₁.projection E₂.projection) := by
      constructor
      intro Z g h w
      apply biprod.hom_ext'
      · apply (cancel_epi E₁.projection).1
        calc
          E₁.projection ≫ biprod.inl ≫ g =
              (biprod.inl ≫ biprod.map E₁.projection E₂.projection) ≫ g := by
            rw [biprod.inl_map, Category.assoc]
          _ = biprod.inl ≫
              (biprod.map E₁.projection E₂.projection ≫ g) := by
            rw [Category.assoc]
          _ = biprod.inl ≫
              (biprod.map E₁.projection E₂.projection ≫ h) := by
            rw [w]
          _ = E₁.projection ≫ biprod.inl ≫ h := by
            rw [← Category.assoc, biprod.inl_map, Category.assoc]
      · apply (cancel_epi E₂.projection).1
        calc
          E₂.projection ≫ biprod.inr ≫ g =
              (biprod.inr ≫ biprod.map E₁.projection E₂.projection) ≫ g := by
            rw [biprod.inr_map, Category.assoc]
          _ = biprod.inr ≫
              (biprod.map E₁.projection E₂.projection ≫ g) := by
            rw [Category.assoc]
          _ = biprod.inr ≫
              (biprod.map E₁.projection E₂.projection ≫ h) := by
            rw [w]
          _ = E₂.projection ≫ biprod.inr ≫ h := by
            rw [← Category.assoc, biprod.inr_map, Category.assoc]
    simpa [S] using (show S.ShortExact from
      { exact := hExact
        mono_f := hmono
        epi_g := hepi })

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
  rcases h₁ with ⟨e₁⟩
  rcases h₂ with ⟨e₂⟩
  let dHom : ExtensionHom (directSumExtension E₁ E₂) (directSumExtension E₁' E₂') :=
    { middle := biprod.map e₁.hom.middle e₂.hom.middle
      comm_left := by
        dsimp [directSumExtension]
        apply biprod.hom_ext
        · rw [Category.assoc, biprod.map_fst, biprod.map_fst,
            ← Category.assoc, biprod.map_fst, Category.assoc, e₁.hom.comm_left]
        · rw [Category.assoc, biprod.map_snd, biprod.map_snd,
            ← Category.assoc, biprod.map_snd, Category.assoc, e₂.hom.comm_left]
      comm_right := by
        dsimp [directSumExtension]
        apply biprod.hom_ext'
        · rw [← Category.assoc, biprod.inl_map, Category.assoc,
            biprod.inl_map, ← Category.assoc, e₁.hom.comm_right,
            biprod.inl_map]
        · rw [← Category.assoc, biprod.inr_map, Category.assoc,
            biprod.inr_map, ← Category.assoc, e₂.hom.comm_right,
            biprod.inr_map] }
  let dInv : ExtensionHom (directSumExtension E₁' E₂') (directSumExtension E₁ E₂) :=
    { middle := biprod.map e₁.inv.middle e₂.inv.middle
      comm_left := by
        dsimp [directSumExtension]
        apply biprod.hom_ext
        · rw [Category.assoc, biprod.map_fst, biprod.map_fst,
            ← Category.assoc, biprod.map_fst, Category.assoc, e₁.inv.comm_left]
        · rw [Category.assoc, biprod.map_snd, biprod.map_snd,
            ← Category.assoc, biprod.map_snd, Category.assoc, e₂.inv.comm_left]
      comm_right := by
        dsimp [directSumExtension]
        apply biprod.hom_ext'
        · rw [← Category.assoc, biprod.inl_map, Category.assoc,
            biprod.inl_map, ← Category.assoc, e₁.inv.comm_right,
            biprod.inl_map]
        · rw [← Category.assoc, biprod.inr_map, Category.assoc,
            biprod.inr_map, ← Category.assoc, e₂.inv.comm_right,
            biprod.inr_map] }
  have h₁' : e₁.hom.middle ≫ e₁.inv.middle = 𝟙 E₁.middle := by
    exact congrArg (fun q : E₁ ⟶ E₁ => q.middle) e₁.hom_inv_id
  have h₂' : e₂.hom.middle ≫ e₂.inv.middle = 𝟙 E₂.middle := by
    exact congrArg (fun q : E₂ ⟶ E₂ => q.middle) e₂.hom_inv_id
  have h₁'' : e₁.inv.middle ≫ e₁.hom.middle = 𝟙 E₁'.middle := by
    exact congrArg (fun q : E₁' ⟶ E₁' => q.middle) e₁.inv_hom_id
  have h₂'' : e₂.inv.middle ≫ e₂.hom.middle = 𝟙 E₂'.middle := by
    exact congrArg (fun q : E₂' ⟶ E₂' => q.middle) e₂.inv_hom_id
  have hdHomInv : dHom.middle ≫ dInv.middle = 𝟙 _ := by
    dsimp [dHom, dInv, directSumExtension]
    apply biprod.hom_ext'
    · simp
      rw [← Category.assoc, h₁', Category.id_comp]
    · simp
      rw [← Category.assoc, h₂', Category.id_comp]
  have hdInvHom : dInv.middle ≫ dHom.middle = 𝟙 _ := by
    dsimp [dHom, dInv, directSumExtension]
    apply biprod.hom_ext'
    · simp
      rw [← Category.assoc, h₁'', Category.id_comp]
    · simp
      rw [← Category.assoc, h₂'', Category.id_comp]
  have hd : Nonempty (directSumExtension E₁ E₂ ≅ directSumExtension E₁' E₂') :=
    ⟨{ hom := dHom
       inv := dInv
       hom_inv_id := ExtensionHom.ext _ _ hdHomInv
       inv_hom_id := ExtensionHom.ext _ _ hdInvHom }⟩
  have hp :
      Nonempty
        (pushoutExtension (directSumExtension E₁ E₂) (biprodCodiagonal A) ≅
          pushoutExtension (directSumExtension E₁' E₂') (biprodCodiagonal A)) :=
    pushout_extension_preserves_iso (biprodCodiagonal A) hd
  simpa [baerSumExtension] using
    (pullback_extension_preserves_iso
      (E := pushoutExtension (directSumExtension E₁ E₂) (biprodCodiagonal A))
      (F := pushoutExtension (directSumExtension E₁' E₂') (biprodCodiagonal A))
      (biprodDiagonal B) hp)

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
    exact
      { exact := (ShortComplex.mk biprod.inl biprod.snd (by simp)).exact_of_f_is_kernel
          (biprod.isKernelSndKernelFork A B)
        mono_f := inferInstance
        epi_g := inferInstance }

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
  exact pushout_extension_preserves_iso (-𝟙 A) h

private theorem pushout_pullback_extension_morphism_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B A' B' : C} {E : Extension C A B} {F : Extension C A' B'}
    (e : ExtensionMorphism E F) :
    Nonempty
      (pushoutExtension E e.left ≅ pullbackExtension F e.right) := by
  let iP : A' ⟶ pushout e.left E.inclusion :=
    pushout.inl e.left E.inclusion
  let gP : pushout e.left E.inclusion ⟶ B :=
    pushout.desc 0 E.projection (by simp [E.zero])
  let k : pushout e.left E.inclusion ⟶ F.middle :=
    pushout.desc F.inclusion e.middle e.comm_left.symm
  have hk_g : k ≫ F.projection = gP ≫ e.right := by
    apply pushout.hom_ext
    · dsimp [k, gP]
      calc
        pushout.inl e.left E.inclusion ≫
            pushout.desc F.inclusion e.middle _ ≫ F.projection =
            (pushout.inl e.left E.inclusion ≫
              pushout.desc F.inclusion e.middle _) ≫ F.projection := by
                rw [Category.assoc]
        _ = F.inclusion ≫ F.projection := by rw [pushout.inl_desc]
        _ = 0 := F.zero
        _ = (pushout.inl e.left E.inclusion ≫
            pushout.desc 0 E.projection (by simp [E.zero])) ≫ e.right := by
              rw [pushout.inl_desc, zero_comp]
        _ = pushout.inl e.left E.inclusion ≫
            pushout.desc 0 E.projection (by simp [E.zero]) ≫ e.right := by
              rw [Category.assoc]
    · dsimp [k, gP]
      calc
        pushout.inr e.left E.inclusion ≫
            pushout.desc F.inclusion e.middle _ ≫ F.projection =
            (pushout.inr e.left E.inclusion ≫
              pushout.desc F.inclusion e.middle _) ≫ F.projection := by
                rw [Category.assoc]
        _ = e.middle ≫ F.projection := by rw [pushout.inr_desc]
        _ = E.projection ≫ e.right := e.comm_right
        _ = (pushout.inr e.left E.inclusion ≫
            pushout.desc 0 E.projection (by simp [E.zero])) ≫ e.right := by
              rw [pushout.inr_desc]
        _ = pushout.inr e.left E.inclusion ≫
            pushout.desc 0 E.projection (by simp [E.zero]) ≫ e.right := by
              rw [Category.assoc]
  let mMiddle : pushout e.left E.inclusion ⟶
      pullback F.projection e.right :=
    pullback.lift k gP hk_g
  let iQ : A' ⟶ pullback F.projection e.right :=
    pullback.lift F.inclusion 0 (by simp [F.zero])
  have hm_f : mMiddle ≫ pullback.snd F.projection e.right = gP := by
    dsimp [mMiddle]
    rw [pullback.lift_snd]
  have hm_i : iP ≫ mMiddle = iQ := by
    apply pullback.hom_ext
    · dsimp [iP, iQ, mMiddle, k]
      rw [Category.assoc, pullback.lift_fst, pushout.inl_desc,
        pullback.lift_fst]
    · dsimp [iP, iQ, mMiddle, gP]
      rw [Category.assoc, pullback.lift_snd, pushout.inl_desc,
        pullback.lift_snd]
  let φ : (pushoutExtension E e.left).toShortComplex ⟶
      (pullbackExtension F e.right).toShortComplex :=
    { τ₁ := 𝟙 A'
      τ₂ := mMiddle
      τ₃ := 𝟙 B
      comm₁₂ := by
        change 𝟙 A' ≫ iQ = iP ≫ mMiddle
        rw [Category.id_comp, hm_i]
      comm₂₃ := by
        change mMiddle ≫ pullback.snd F.projection e.right =
          gP ≫ 𝟙 B
        rw [hm_f, Category.comp_id] }
  have hmono : Mono mMiddle := by
    letI : Mono (pushoutExtension E e.left).toShortComplex.f :=
      (pushoutExtension E e.left).shortExact.mono_f
    letI : Mono (pullbackExtension F e.right).toShortComplex.f :=
      (pullbackExtension F e.right).shortExact.mono_f
    letI : Mono φ.τ₁ := by
      dsimp [φ]
      constructor
      intro Z g h w
      rw [← Category.comp_id g, ← Category.comp_id h]
      exact w
    letI : Mono φ.τ₃ := by
      dsimp [φ]
      constructor
      intro Z g h w
      rw [← Category.comp_id g, ← Category.comp_id h]
      exact w
    apply ShortComplex.mono_τ₂_of_exact_of_mono φ
    exact (pushoutExtension E e.left).shortExact.exact
  have hepi : Epi mMiddle := by
    letI : Epi (pushoutExtension E e.left).toShortComplex.g :=
      (pushoutExtension E e.left).shortExact.epi_g
    letI : Epi (pullbackExtension F e.right).toShortComplex.g :=
      (pullbackExtension F e.right).shortExact.epi_g
    letI : Epi φ.τ₁ := by
      dsimp [φ]
      constructor
      intro Z g h w
      rw [← Category.id_comp g, ← Category.id_comp h]
      exact w
    letI : Epi φ.τ₃ := by
      dsimp [φ]
      constructor
      intro Z g h w
      rw [← Category.id_comp g, ← Category.id_comp h]
      exact w
    apply ShortComplex.epi_τ₂_of_exact_of_epi φ
    exact (pullbackExtension F e.right).shortExact.exact
  letI : Mono mMiddle := hmono
  letI : Epi mMiddle := hepi
  letI : IsIso mMiddle := isIso_of_mono_of_epi mMiddle
  let invMiddle : pullback F.projection e.right ⟶
      pushout e.left E.inclusion := inv mMiddle
  let m : ExtensionHom (pushoutExtension E e.left)
      (pullbackExtension F e.right) :=
    { middle := mMiddle
      comm_left := by
        change iP ≫ mMiddle = iQ
        exact hm_i
      comm_right := by
        change mMiddle ≫ pullback.snd F.projection e.right = gP
        exact hm_f }
  let n : ExtensionHom (pullbackExtension F e.right)
      (pushoutExtension E e.left) :=
    { middle := invMiddle
      comm_left := by
        change iQ ≫ invMiddle = iP
        rw [← cancel_mono mMiddle, Category.assoc, IsIso.inv_hom_id,
          Category.comp_id, hm_i]
      comm_right := by
        change invMiddle ≫ gP = pullback.snd F.projection e.right
        rw [← cancel_epi mMiddle, IsIso.hom_inv_id_assoc, hm_f] }
  exact ⟨
    { hom := m
      inv := n
      hom_inv_id := ExtensionHom.ext _ _ (by
        dsimp [m, n]
        exact IsIso.hom_inv_id mMiddle)
      inv_hom_id := ExtensionHom.ext _ _ (by
        dsimp [m, n]
        exact IsIso.inv_hom_id mMiddle) }⟩

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

private theorem baerSumExtension_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E₁ E₂ : Extension C A B) :
    Nonempty (baerSumExtension E₁ E₂ ≅ baerSumExtension E₂ E₁) := by
  let sA : A ⊞ A ⟶ A ⊞ A := biprod.desc biprod.inr biprod.inl
  let sB : B ⊞ B ⟶ B ⊞ B := biprod.desc biprod.inr biprod.inl
  let sM : E₁.middle ⊞ E₂.middle ⟶ E₂.middle ⊞ E₁.middle :=
    biprod.desc biprod.inr biprod.inl
  let e : ExtensionMorphism (directSumExtension E₁ E₂)
      (directSumExtension E₂ E₁) :=
    { left := sA
      middle := sM
      right := sB
      comm_left := by
        dsimp [sA, sM, directSumExtension]
        apply biprod.hom_ext
        · simp [biprodCodiagonal, biprod.desc_eq, Category.assoc, add_comp, comp_add]
        · simp [biprodCodiagonal, biprod.desc_eq, Category.assoc, add_comp, comp_add]
      comm_right := by
        dsimp [sB, sM, directSumExtension]
        apply biprod.hom_ext'
        · simp [biprod.desc_eq, Category.assoc, add_comp, comp_add]
        · simp [biprod.desc_eq, Category.assoc, add_comp, comp_add] }
  have h₀ := pushout_pullback_extension_morphism_iso e
  have h₁ := pushout_extension_preserves_iso (biprodCodiagonal A) h₀
  have h₂ := pullback_extension_preserves_iso (biprodDiagonal B) h₁
  have h₃ := pushout_extension_comp_iso (directSumExtension E₁ E₂)
    sA (biprodCodiagonal A)
  have h₄ := pullback_extension_preserves_iso (biprodDiagonal B) h₃
  have h₅ := pushout_pullback_extension_iso (directSumExtension E₂ E₁)
    (biprodCodiagonal A) sB
  have h₇ := pullback_extension_comp_iso
    (pushoutExtension (directSumExtension E₂ E₁) (biprodCodiagonal A))
    sB (biprodDiagonal B)
  have hsA : sA ≫ biprodCodiagonal A = biprodCodiagonal A := by
    dsimp [sA, biprodCodiagonal]
    simp [biprod.desc_eq, Category.assoc, add_comp, comp_add, add_comm]
  have hsB : biprodDiagonal B ≫ sB = biprodDiagonal B := by
    dsimp [sB, biprodDiagonal]
    simp [biprod.lift_desc, biprod.lift_eq, biprod.desc_eq,
      Category.assoc, add_comp, comp_add, add_comm]
  have h₄' : Nonempty
      (pullbackExtension
          (pushoutExtension (directSumExtension E₁ E₂)
            (biprodCodiagonal A)) (biprodDiagonal B) ≅
        pullbackExtension
          (pushoutExtension (pushoutExtension
            (directSumExtension E₁ E₂) sA) (biprodCodiagonal A))
          (biprodDiagonal B)) := by
    exact ⟨by simpa [baerSumExtension, hsA] using h₄.some.symm⟩
  have h₇' : Nonempty
      (pullbackExtension
          (pullbackExtension (pushoutExtension
            (directSumExtension E₂ E₁) (biprodCodiagonal A)) sB)
          (biprodDiagonal B) ≅
        baerSumExtension E₂ E₁) := by
    simpa [baerSumExtension, hsB] using h₇
  exact ⟨h₄'.some.trans (h₂.some.trans
    ((pullback_extension_preserves_iso
      (biprodDiagonal B) h₅).some.trans h₇'.some))⟩

private theorem baerSumExtension_add_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E : Extension C A B) :
    Nonempty (baerSumExtension E (splitExtension A B) ≅ E) := by
  let S := splitExtension A B
  let l : A ⊞ A ⟶ A := biprodCodiagonal A
  let r : B ⊞ B ⟶ B := biprod.fst
  let j : S.middle ⟶ E.middle := biprod.fst ≫ E.inclusion
  let m : E.middle ⊞ S.middle ⟶ E.middle := biprod.desc (𝟙 _) j
  let e : ExtensionMorphism (directSumExtension E S) E :=
    { left := l
      middle := m
      right := r
      comm_left := by
        dsimp [l, m, j, S, directSumExtension, splitExtension]
        apply biprod.hom_ext'
        · simp [biprodCodiagonal, biprod.desc_eq, Category.assoc, add_comp, comp_add]
        · simp [biprodCodiagonal, biprod.desc_eq, Category.assoc, add_comp, comp_add]
      comm_right := by
        dsimp [m, j, r, S, directSumExtension, splitExtension]
        apply biprod.hom_ext'
        · simp [biprod.desc_eq, Category.assoc, add_comp, comp_add, E.zero]
        · simp [biprod.desc_eq, Category.assoc, add_comp, comp_add, E.zero] }
  have h₀ := pushout_pullback_extension_morphism_iso e
  have h₁ := pullback_extension_preserves_iso (biprodDiagonal B) h₀
  have h₂ := pullback_extension_comp_iso E r (biprodDiagonal B)
  have hr : biprodDiagonal B ≫ r = 𝟙 B := by
    dsimp [biprodDiagonal, r]
    simp
  have h₃ : Nonempty
      (pullbackExtension E (biprodDiagonal B ≫ r) ≅ E) := by
    simpa [hr] using pullback_extension_id_iso E
  exact ⟨h₁.some.trans (h₂.some.trans h₃.some)⟩

private theorem baerSumClass_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (x y : Ext B A) : baerSumClass x y = baerSumClass y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro E₁ E₂
  change extensionClass (baerSumExtension E₁ E₂) =
    extensionClass (baerSumExtension E₂ E₁)
  exact Quotient.sound (baerSumExtension_comm E₁ E₂)

private theorem baerSumClass_add_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (x : Ext B A) : baerSumClass x zeroExtClass = x := by
  refine Quotient.inductionOn x ?_
  intro E
  change extensionClass (baerSumExtension E (splitExtension A B)) =
    extensionClass E
  exact Quotient.sound (baerSumExtension_add_zero E)

private noncomputable def directSumExtensionVarying
    {C : Type u} [Category.{v} C] [Abelian C]
    {A₁ B₁ A₂ B₂ : C}
    (E₁ : Extension C A₁ B₁) (E₂ : Extension C A₂ B₂) :
    Extension C (A₁ ⊞ A₂) (B₁ ⊞ B₂) where
  middle := E₁.middle ⊞ E₂.middle
  inclusion := biprod.map E₁.inclusion E₂.inclusion
  projection := biprod.map E₁.projection E₂.projection
  zero := by
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_map E₁.inclusion E₂.inclusion,
        Category.assoc, biprod.inl_map E₁.projection E₂.projection,
        ← Category.assoc, E₁.zero, zero_comp]
      simp
    · rw [← Category.assoc, biprod.inr_map E₁.inclusion E₂.inclusion,
        Category.assoc, biprod.inr_map E₁.projection E₂.projection,
        ← Category.assoc, E₂.zero, zero_comp]
      simp
  shortExact := by
    let z : biprod.map E₁.inclusion E₂.inclusion ≫
        biprod.map E₁.projection E₂.projection = 0 := by
      apply biprod.hom_ext'
      · rw [← Category.assoc, biprod.inl_map E₁.inclusion E₂.inclusion,
          Category.assoc, biprod.inl_map E₁.projection E₂.projection,
          ← Category.assoc, E₁.zero, zero_comp]
        simp
      · rw [← Category.assoc, biprod.inr_map E₁.inclusion E₂.inclusion,
          Category.assoc, biprod.inr_map E₁.projection E₂.projection,
          ← Category.assoc, E₂.zero, zero_comp]
        simp
    let S : ShortComplex C :=
      ShortComplex.mk (biprod.map E₁.inclusion E₂.inclusion)
        (biprod.map E₁.projection E₂.projection) z
    have hK₁ := E₁.shortExact.fIsKernel
    have hK₂ := E₂.shortExact.fIsKernel
    letI : Mono E₁.inclusion := E₁.shortExact.mono_f
    letI : Mono E₂.inclusion := E₂.shortExact.mono_f
    letI : Epi E₁.projection := E₁.shortExact.epi_g
    letI : Epi E₂.projection := E₂.shortExact.epi_g
    have hExact : S.Exact := by
      apply S.exact_of_f_is_kernel
      let lift : ∀ s : KernelFork (biprod.map E₁.projection E₂.projection),
          s.pt ⟶ A₁ ⊞ A₂ := fun s =>
        biprod.lift
          (hK₁.lift (KernelFork.ofι (s.ι ≫ biprod.fst) (by
            calc
              (s.ι ≫ biprod.fst) ≫ E₁.projection =
                  s.ι ≫ (biprod.fst ≫ E₁.projection) := by rw [Category.assoc]
              _ = s.ι ≫
                  (biprod.map E₁.projection E₂.projection ≫ biprod.fst) := by
                rw [biprod.map_fst]
              _ = (s.ι ≫ biprod.map E₁.projection E₂.projection) ≫
                  biprod.fst := by rw [Category.assoc]
              _ = 0 := by rw [KernelFork.condition s, zero_comp])))
          (hK₂.lift (KernelFork.ofι (s.ι ≫ biprod.snd) (by
            calc
              (s.ι ≫ biprod.snd) ≫ E₂.projection =
                  s.ι ≫ (biprod.snd ≫ E₂.projection) := by rw [Category.assoc]
              _ = s.ι ≫
                  (biprod.map E₁.projection E₂.projection ≫ biprod.snd) := by
                rw [biprod.map_snd]
              _ = (s.ι ≫ biprod.map E₁.projection E₂.projection) ≫
                  biprod.snd := by rw [Category.assoc]
              _ = 0 := by rw [KernelFork.condition s, zero_comp])))
      refine Fork.IsLimit.mk _ lift ?_ ?_
      · intro s
        apply biprod.hom_ext
        · dsimp [lift]
          dsimp [S]
          simp only [Category.assoc, biprod.map_fst]
          rw [← Category.assoc, biprod.lift_fst]
          simpa only [KernelFork.ι_ofι, Fork.ι_ofι] using
            (Fork.IsLimit.lift_ι (s := KernelFork.ofι E₁.inclusion E₁.zero)
              (t := KernelFork.ofι (s.ι ≫ biprod.fst) _) hK₁)
        · dsimp [lift]
          dsimp [S]
          simp only [Category.assoc, biprod.map_snd]
          rw [← Category.assoc, biprod.lift_snd]
          simpa only [KernelFork.ι_ofι, Fork.ι_ofι] using
            (Fork.IsLimit.lift_ι (s := KernelFork.ofι E₂.inclusion E₂.zero)
              (t := KernelFork.ofι (s.ι ≫ biprod.snd) _) hK₂)
      · intro s m hm
        change m ≫ biprod.map E₁.inclusion E₂.inclusion = s.ι at hm
        apply biprod.hom_ext
        · apply (cancel_mono E₁.inclusion).1
          calc
            (m ≫ biprod.fst) ≫ E₁.inclusion =
                (m ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.fst := by
              calc
                (m ≫ biprod.fst) ≫ E₁.inclusion =
                    m ≫ (biprod.fst ≫ E₁.inclusion) := by rw [Category.assoc]
                _ = m ≫
                    (biprod.map E₁.inclusion E₂.inclusion ≫ biprod.fst) := by
                  rw [biprod.map_fst]
                _ = (m ≫ biprod.map E₁.inclusion E₂.inclusion) ≫
                    biprod.fst := by rw [Category.assoc]
            _ = s.ι ≫ biprod.fst := by rw [hm]
            _ = (lift s ≫ biprod.fst) ≫ E₁.inclusion := by
              dsimp [lift]
              rw [biprod.lift_fst]
              simpa only [KernelFork.ι_ofι, Fork.ι_ofι] using
                (Fork.IsLimit.lift_ι (s := KernelFork.ofι E₁.inclusion E₁.zero)
                  (t := KernelFork.ofι (s.ι ≫ biprod.fst) _) hK₁).symm
        · apply (cancel_mono E₂.inclusion).1
          calc
            (m ≫ biprod.snd) ≫ E₂.inclusion =
                (m ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.snd := by
              calc
                (m ≫ biprod.snd) ≫ E₂.inclusion =
                    m ≫ (biprod.snd ≫ E₂.inclusion) := by rw [Category.assoc]
                _ = m ≫
                    (biprod.map E₁.inclusion E₂.inclusion ≫ biprod.snd) := by
                  rw [biprod.map_snd]
                _ = (m ≫ biprod.map E₁.inclusion E₂.inclusion) ≫
                    biprod.snd := by rw [Category.assoc]
            _ = s.ι ≫ biprod.snd := by rw [hm]
            _ = (lift s ≫ biprod.snd) ≫ E₂.inclusion := by
              dsimp [lift]
              rw [biprod.lift_snd]
              simpa only [KernelFork.ι_ofι, Fork.ι_ofι] using
                (Fork.IsLimit.lift_ι (s := KernelFork.ofι E₂.inclusion E₂.zero)
                  (t := KernelFork.ofι (s.ι ≫ biprod.snd) _) hK₂).symm
    have hmono : Mono (biprod.map E₁.inclusion E₂.inclusion) := by
      constructor
      intro Z g h w
      apply biprod.hom_ext
      · apply (cancel_mono E₁.inclusion).1
        calc
          (g ≫ biprod.fst) ≫ E₁.inclusion =
              (g ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.fst := by
            calc
              (g ≫ biprod.fst) ≫ E₁.inclusion =
                  g ≫ (biprod.fst ≫ E₁.inclusion) := by rw [Category.assoc]
              _ = g ≫
                  (biprod.map E₁.inclusion E₂.inclusion ≫ biprod.fst) := by
                rw [biprod.map_fst]
              _ = (g ≫ biprod.map E₁.inclusion E₂.inclusion) ≫
                  biprod.fst := by rw [Category.assoc]
          _ = (h ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.fst := by
            rw [w]
          _ = (h ≫ biprod.fst) ≫ E₁.inclusion := by
            calc
              (h ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.fst =
                  h ≫ (biprod.map E₁.inclusion E₂.inclusion ≫ biprod.fst) := by
                rw [Category.assoc]
              _ = h ≫ (biprod.fst ≫ E₁.inclusion) := by
                rw [biprod.map_fst]
              _ = (h ≫ biprod.fst) ≫ E₁.inclusion := by rw [Category.assoc]
      · apply (cancel_mono E₂.inclusion).1
        calc
          (g ≫ biprod.snd) ≫ E₂.inclusion =
              (g ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.snd := by
            calc
              (g ≫ biprod.snd) ≫ E₂.inclusion =
                  g ≫ (biprod.snd ≫ E₂.inclusion) := by rw [Category.assoc]
              _ = g ≫
                  (biprod.map E₁.inclusion E₂.inclusion ≫ biprod.snd) := by
                rw [biprod.map_snd]
              _ = (g ≫ biprod.map E₁.inclusion E₂.inclusion) ≫
                  biprod.snd := by rw [Category.assoc]
          _ = (h ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.snd := by
            rw [w]
          _ = (h ≫ biprod.snd) ≫ E₂.inclusion := by
            calc
              (h ≫ biprod.map E₁.inclusion E₂.inclusion) ≫ biprod.snd =
                  h ≫ (biprod.map E₁.inclusion E₂.inclusion ≫ biprod.snd) := by
                rw [Category.assoc]
              _ = h ≫ (biprod.snd ≫ E₂.inclusion) := by
                rw [biprod.map_snd]
              _ = (h ≫ biprod.snd) ≫ E₂.inclusion := by rw [Category.assoc]
    have hepi : Epi (biprod.map E₁.projection E₂.projection) := by
      constructor
      intro Z g h w
      apply biprod.hom_ext'
      · apply (cancel_epi E₁.projection).1
        calc
          E₁.projection ≫ biprod.inl ≫ g =
              (biprod.inl ≫ biprod.map E₁.projection E₂.projection) ≫ g := by
            rw [biprod.inl_map, Category.assoc]
          _ = biprod.inl ≫
              (biprod.map E₁.projection E₂.projection ≫ g) := by
            rw [Category.assoc]
          _ = biprod.inl ≫
              (biprod.map E₁.projection E₂.projection ≫ h) := by
            rw [w]
          _ = E₁.projection ≫ biprod.inl ≫ h := by
            rw [← Category.assoc, biprod.inl_map, Category.assoc]
      · apply (cancel_epi E₂.projection).1
        calc
          E₂.projection ≫ biprod.inr ≫ g =
              (biprod.inr ≫ biprod.map E₁.projection E₂.projection) ≫ g := by
            rw [biprod.inr_map, Category.assoc]
          _ = biprod.inr ≫
              (biprod.map E₁.projection E₂.projection ≫ g) := by
            rw [Category.assoc]
          _ = biprod.inr ≫
              (biprod.map E₁.projection E₂.projection ≫ h) := by
            rw [w]
          _ = E₂.projection ≫ biprod.inr ≫ h := by
            rw [← Category.assoc, biprod.inr_map, Category.assoc]
    simpa [S] using (show S.ShortExact from
      { exact := hExact
        mono_f := hmono
        epi_g := hepi })

private def biprodAssoc
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z : C} : (X ⊞ Y) ⊞ Z ⟶ X ⊞ (Y ⊞ Z) :=
  biprod.lift
    (biprod.fst ≫ biprod.fst)
    (biprod.lift (biprod.fst ≫ biprod.snd) biprod.snd)

private def biprodAssocInv
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z : C} : X ⊞ (Y ⊞ Z) ⟶ (X ⊞ Y) ⊞ Z :=
  biprod.lift
    (biprod.lift biprod.fst (biprod.snd ≫ biprod.fst))
    (biprod.snd ≫ biprod.snd)

private theorem biprodAssoc_hom_inv
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z : C} :
    biprodAssoc (X := X) (Y := Y) (Z := Z) ≫
        biprodAssocInv (X := X) (Y := Y) (Z := Z) = 𝟙 _ := by
  apply biprod.hom_ext
  · apply biprod.hom_ext
    · simp [biprodAssoc, biprodAssocInv, Category.assoc]
    · simp [biprodAssoc, biprodAssocInv, Category.assoc]
  · simp [biprodAssoc, biprodAssocInv, Category.assoc]

private theorem biprodAssoc_inv_hom
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z : C} :
    biprodAssocInv (X := X) (Y := Y) (Z := Z) ≫
        biprodAssoc (X := X) (Y := Y) (Z := Z) = 𝟙 _ := by
  apply biprod.hom_ext
  · simp [biprodAssoc, biprodAssocInv, Category.assoc]
  · apply biprod.hom_ext
    · simp [biprodAssoc, biprodAssocInv, Category.assoc]
    · simp [biprodAssoc, biprodAssocInv, Category.assoc]

private def directSumExtensionAssocMorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E₁ E₂ E₃ : Extension C A B) :
    ExtensionMorphism
      (directSumExtensionVarying (directSumExtension E₁ E₂) E₃)
      (directSumExtensionVarying E₁ (directSumExtension E₂ E₃)) :=
  { left := biprodAssoc (X := A) (Y := A) (Z := A)
    middle := biprodAssoc (X := E₁.middle) (Y := E₂.middle) (Z := E₃.middle)
    right := biprodAssoc (X := B) (Y := B) (Z := B)
    comm_left := by
      dsimp [directSumExtensionVarying, directSumExtension, biprodAssoc]
      apply biprod.hom_ext'
      · apply biprod.hom_ext
        · simp [Category.assoc]
        · apply biprod.hom_ext'
          · apply biprod.hom_ext
            · simp [Category.assoc, biprod.inl_map, biprod.inr_map,
                biprod.lift_eq, biprod.lift_fst, biprod.lift_snd,
                biprod.map_fst, biprod.map_snd]
            · simp [Category.assoc, biprod.inl_map, biprod.inr_map,
                biprod.lift_eq, biprod.lift_fst, biprod.lift_snd,
                biprod.map_fst, biprod.map_snd]
          · apply biprod.hom_ext
            · simp [Category.assoc]
            · simp [Category.assoc]
      · apply biprod.hom_ext
        · simp [Category.assoc]
        · apply biprod.hom_ext
          · simp [Category.assoc]
          · simp [Category.assoc]
    comm_right := by
      dsimp [directSumExtensionVarying, directSumExtension, biprodAssoc]
      apply biprod.hom_ext
      · simp [Category.assoc]
      · apply biprod.hom_ext
        · apply biprod.hom_ext'
          · simp [Category.assoc]
          · simp [Category.assoc]
        · apply biprod.hom_ext'
          · simp [Category.assoc]
          · simp [Category.assoc] }

private theorem biprod_map_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    {W X Y Z U V : C}
    (f : W ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ U) (k : Z ⟶ V) :
    biprod.map f g ≫ biprod.map h k = biprod.map (f ≫ h) (g ≫ k) := by
  apply biprod.hom_ext'
  · simp [Category.assoc]
  · simp [Category.assoc]

private def directSumPushoutMorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {A₁ A₁' B₁ A₂ B₂ : C}
    (E₁ : Extension C A₁ B₁) (E₂ : Extension C A₂ B₂)
    (a : A₁ ⟶ A₁') :
    ExtensionMorphism (directSumExtensionVarying E₁ E₂)
      (directSumExtensionVarying (pushoutExtension E₁ a) E₂) :=
  { left := biprod.map a (𝟙 A₂)
    middle := biprod.map (pushout.inr a E₁.inclusion) (𝟙 E₂.middle)
    right := 𝟙 (B₁ ⊞ B₂)
    comm_left := by
      dsimp [directSumExtensionVarying, pushoutExtension]
      rw [biprod_map_comp, biprod_map_comp]
      simp [pushout.condition]
    comm_right := by
      dsimp [directSumExtensionVarying, pushoutExtension]
      rw [biprod_map_comp]
      simp [pushout.inr_desc] }

private def directSumPullbackMorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {A₁ B₁ B₁' A₂ B₂ : C}
    (E₁ : Extension C A₁ B₁) (E₂ : Extension C A₂ B₂)
    (p : B₁' ⟶ B₁) :
    ExtensionMorphism
      (directSumExtensionVarying (pullbackExtension E₁ p) E₂)
      (pullbackExtension (directSumExtensionVarying E₁ E₂)
        (biprod.map p (𝟙 B₂))) :=
  let mMiddle : (pullback E₁.projection p) ⊞ E₂.middle ⟶
      pullback (biprod.map E₁.projection E₂.projection)
        (biprod.map p (𝟙 B₂)) :=
    pullback.lift
      (biprod.map (pullback.fst E₁.projection p) (𝟙 E₂.middle))
      (biprod.map (pullback.snd E₁.projection p) E₂.projection) (by
        rw [biprod_map_comp, biprod_map_comp]
        apply congrArg₂ biprod.map
        · simp [pullback.condition]
        · simp)
  have hm_fst :
      mMiddle ≫ pullback.fst (biprod.map E₁.projection E₂.projection)
          (biprod.map p (𝟙 B₂)) =
        biprod.map (pullback.fst E₁.projection p) (𝟙 E₂.middle) := by
    dsimp [mMiddle]
    rw [pullback.lift_fst]
  have hm_snd :
      mMiddle ≫ pullback.snd (biprod.map E₁.projection E₂.projection)
          (biprod.map p (𝟙 B₂)) =
        biprod.map (pullback.snd E₁.projection p) E₂.projection := by
    dsimp [mMiddle]
    rw [pullback.lift_snd]
  { left := 𝟙 _
    middle := mMiddle
    right := 𝟙 _
    comm_left := by
      dsimp [directSumExtensionVarying, pullbackExtension]
      apply biprod.hom_ext'
      · apply pullback.hom_ext
        · simp only [Category.assoc]
          rw [hm_fst]
          simp only [← Category.assoc]
          rw [biprod.inl_map]
          simp only [Category.assoc]
          rw [biprod.inl_map]
          simp only [← Category.assoc]
          rw [pullback.lift_fst]
          simp only [Category.assoc, pullback.lift_fst, biprod.inl_map,
            Category.comp_id]
        · simp only [Category.assoc]
          rw [hm_snd]
          simp only [← Category.assoc]
          rw [biprod.inl_map]
          simp only [Category.assoc]
          rw [biprod.inl_map]
          simp only [← Category.assoc]
          rw [pullback.lift_snd]
          simp only [Category.assoc]
          rw [pullback.lift_snd]
          simp only [comp_zero, zero_comp, Category.comp_id]
      · apply pullback.hom_ext
        · simp only [Category.assoc]
          rw [hm_fst]
          simp only [← Category.assoc]
          rw [biprod.inr_map]
          simp only [Category.assoc]
          rw [biprod.inr_map]
          rw [pullback.lift_fst]
          simp only [Category.id_comp]
          rw [biprod.inr_map]
        · simp only [Category.assoc]
          rw [hm_snd]
          simp only [← Category.assoc]
          rw [biprod.inr_map]
          simp only [Category.assoc]
          rw [biprod.inr_map]
          rw [pullback.lift_snd]
          simp only [← Category.assoc]
          rw [E₂.zero]
          simp only [zero_comp, comp_zero, Category.comp_id]
    comm_right := by
      dsimp [directSumExtensionVarying, pullbackExtension]
      apply biprod.hom_ext'
      · rw [hm_snd]
        simp only [Category.comp_id]
      · rw [hm_snd]
        simp only [Category.comp_id]
        }

private theorem directSumExtension_varying_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E₁ E₂ : Extension C A B) :
    Nonempty (directSumExtension E₁ E₂ ≅
      directSumExtensionVarying E₁ E₂) := by
  have h : directSumExtension E₁ E₂ = directSumExtensionVarying E₁ E₂ := by
    rfl
  rw [h]
  exact ⟨Iso.refl _⟩

private theorem baerSumLeftAssoc_normal_form
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E₁ E₂ E₃ : Extension C A B) :
    Nonempty
      (baerSumExtension (baerSumExtension E₁ E₂) E₃ ≅
        pullbackExtension
          (pushoutExtension
            (directSumExtensionVarying (directSumExtension E₁ E₂) E₃)
            ((biprod.map (biprodCodiagonal A) (𝟙 A)) ≫ biprodCodiagonal A))
          ((biprodDiagonal B) ≫ (biprod.map (biprodDiagonal B) (𝟙 B)))) := by
  let σ : A ⊞ A ⟶ A := biprodCodiagonal A
  let δ : B ⟶ B ⊞ B := biprodDiagonal B
  let u : (A ⊞ A) ⊞ A ⟶ A ⊞ A := biprod.map σ (𝟙 A)
  let s : (A ⊞ A) ⊞ A ⟶ A := u ≫ σ
  let t : B ⊞ B ⟶ (B ⊞ B) ⊞ B := biprod.map δ (𝟙 B)
  let r : B ⟶ (B ⊞ B) ⊞ B := δ ≫ t
  let D₁₂ : Extension C (A ⊞ A) (B ⊞ B) := directSumExtension E₁ E₂
  let P₁₂ : Extension C A (B ⊞ B) := pushoutExtension D₁₂ σ
  let D₀ : Extension C ((A ⊞ A) ⊞ A) ((B ⊞ B) ⊞ B) :=
    directSumExtensionVarying D₁₂ E₃
  let Q : Extension C (A ⊞ A) ((B ⊞ B) ⊞ B) :=
    directSumExtensionVarying P₁₂ E₃
  let D : Extension C A B := baerSumExtension E₁ E₂
  let L : Extension C (A ⊞ A) (B ⊞ B) :=
    directSumExtension D E₃
  let Lvar : Extension C (A ⊞ A) (B ⊞ B) :=
    directSumExtensionVarying D E₃
  have hL0 : Nonempty (Lvar ≅ pullbackExtension Q t) := by
    have h := pushout_pullback_extension_morphism_iso
      (directSumPullbackMorphism P₁₂ E₃ δ)
    have h' : Nonempty
        (pushoutExtension Lvar (𝟙 (A ⊞ A)) ≅
          pullbackExtension (pullbackExtension Q t) (𝟙 (B ⊞ B))) := by
      simpa [Lvar, Q, P₁₂, D₁₂, D, baerSumExtension, δ, t,
        directSumPullbackMorphism] using h
    exact ⟨(pushout_extension_id_iso Lvar).some.symm.trans
      (h'.some.trans (pullback_extension_id_iso (pullbackExtension Q t)).some)⟩
  have hP0 : Nonempty
      (pushoutExtension D₀ u ≅
        pullbackExtension Q (𝟙 ((B ⊞ B) ⊞ B))) := by
    have h := pushout_pullback_extension_morphism_iso
      (directSumPushoutMorphism D₁₂ E₃ σ)
    simpa [D₀, Q, D₁₂, P₁₂, σ, u, directSumPushoutMorphism] using h
  have hP : Nonempty (pushoutExtension D₀ u ≅ Q) := by
    exact ⟨hP0.some.trans (pullback_extension_id_iso Q).some⟩
  have hC : Nonempty
      (pushoutExtension Q σ ≅ pushoutExtension D₀ s) := by
    have h₁ := pushout_extension_preserves_iso σ hP
    have h₂ := pushout_extension_comp_iso D₀ u σ
    exact ⟨h₁.some.symm.trans (by simpa [s] using h₂.some)⟩
  have hInnerVar : Nonempty
      (pushoutExtension Lvar σ ≅
        pullbackExtension (pushoutExtension D₀ s) t) := by
    have h₁ := pushout_extension_preserves_iso σ hL0
    have h₂ := pushout_pullback_extension_iso Q σ t
    have h₃ := pullback_extension_preserves_iso t hC
    exact ⟨h₁.some.trans (h₂.some.trans h₃.some)⟩
  have hInner : Nonempty
      (pushoutExtension L σ ≅
        pullbackExtension (pushoutExtension D₀ s) t) := by
    have h := directSumExtension_varying_iso D E₃
    have h' := pushout_extension_preserves_iso σ h
    exact ⟨h'.some.trans hInnerVar.some⟩
  have hOuter : Nonempty
      (pullbackExtension (pushoutExtension L σ) δ ≅
        pullbackExtension (pullbackExtension (pushoutExtension D₀ s) t) δ) :=
    pullback_extension_preserves_iso δ hInner
  have hComp := pullback_extension_comp_iso (pushoutExtension D₀ s) t δ
  have hFinal : Nonempty
      (pullbackExtension (pullbackExtension (pushoutExtension D₀ s) t) δ ≅
        pullbackExtension (pushoutExtension D₀ s) r) := by
    simpa [r] using hComp
  exact ⟨by
    simpa [baerSumExtension, L, D, σ, δ, s, r, D₀, D₁₂] using
      (hOuter.some.trans hFinal.some)⟩

private def biprodCyclic
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z : C} : (X ⊞ Y) ⊞ Z ⟶ (Y ⊞ Z) ⊞ X :=
  biprod.lift
    (biprod.lift
      ((biprod.fst : (X ⊞ Y) ⊞ Z ⟶ X ⊞ Y) ≫
        (biprod.snd : X ⊞ Y ⟶ Y))
      (biprod.snd : (X ⊞ Y) ⊞ Z ⟶ Z))
    ((biprod.fst : (X ⊞ Y) ⊞ Z ⟶ X ⊞ Y) ≫
      (biprod.fst : X ⊞ Y ⟶ X))

private theorem biprodCyclic_natural
    {C : Type u} [Category.{v} C] [Abelian C]
    {X X' Y Y' Z Z' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    biprod.map (biprod.map f g) h ≫
        biprodCyclic (X := X') (Y := Y') (Z := Z') =
      biprodCyclic (X := X) (Y := Y) (Z := Z) ≫
        biprod.map (biprod.map g h) f := by
  apply biprod.hom_ext
  · apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp [biprodCyclic, Category.assoc]
      · simp [biprodCyclic, Category.assoc]
    · apply biprod.hom_ext
      · simp [biprodCyclic, Category.assoc]
      · simp [biprodCyclic, Category.assoc]
  · apply biprod.hom_ext'
    · simp [biprodCyclic, Category.assoc]
    · simp [biprodCyclic, Category.assoc]

private def directSumExtensionCyclicMorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E₁ E₂ E₃ : Extension C A B) :
    ExtensionMorphism
      (directSumExtensionVarying (directSumExtension E₁ E₂) E₃)
      (directSumExtensionVarying (directSumExtension E₂ E₃) E₁) :=
  { left := biprodCyclic (X := A) (Y := A) (Z := A)
    middle := biprodCyclic (X := E₁.middle) (Y := E₂.middle) (Z := E₃.middle)
    right := biprodCyclic (X := B) (Y := B) (Z := B)
    comm_left := by
      simpa [directSumExtensionVarying, directSumExtension] using
        (biprodCyclic_natural E₁.inclusion E₂.inclusion E₃.inclusion)
    comm_right := by
      simpa [directSumExtensionVarying, directSumExtension] using
        (biprodCyclic_natural E₁.projection E₂.projection E₃.projection).symm }

private theorem baerSumExtension_assoc
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E₁ E₂ E₃ : Extension C A B) :
    Nonempty
      (baerSumExtension (baerSumExtension E₁ E₂) E₃ ≅
        baerSumExtension E₁ (baerSumExtension E₂ E₃)) := by
  let σ : A ⊞ A ⟶ A := biprodCodiagonal A
  let δ : B ⟶ B ⊞ B := biprodDiagonal B
  let u : (A ⊞ A) ⊞ A ⟶ A ⊞ A := biprod.map σ (𝟙 A)
  let s : (A ⊞ A) ⊞ A ⟶ A := u ≫ σ
  let t : B ⊞ B ⟶ (B ⊞ B) ⊞ B := biprod.map δ (𝟙 B)
  let r : B ⟶ (B ⊞ B) ⊞ B := δ ≫ t
  let cA : (A ⊞ A) ⊞ A ⟶ (A ⊞ A) ⊞ A :=
    biprodCyclic (X := A) (Y := A) (Z := A)
  let cB : (B ⊞ B) ⊞ B ⟶ (B ⊞ B) ⊞ B :=
    biprodCyclic (X := B) (Y := B) (Z := B)
  let D₁₂₃ : Extension C ((A ⊞ A) ⊞ A) ((B ⊞ B) ⊞ B) :=
    directSumExtensionVarying (directSumExtension E₁ E₂) E₃
  let D₂₃₁ : Extension C ((A ⊞ A) ⊞ A) ((B ⊞ B) ⊞ B) :=
    directSumExtensionVarying (directSumExtension E₂ E₃) E₁
  have hs : cA ≫ s = s := by
    dsimp [cA, s, u, σ, biprodCyclic, biprodCodiagonal]
    simp [biprod.lift_eq, biprod.desc_eq, Category.assoc, add_comp,
      comp_add, add_comm, add_left_comm, add_assoc]
  have hr : r ≫ cB = r := by
    dsimp [r, t, δ, cB, biprodCyclic, biprodDiagonal]
    simp [biprod.lift_eq, biprod.desc_eq, Category.assoc, add_comp,
      comp_add, add_comm]
  have hC : Nonempty
      (pushoutExtension D₁₂₃ s ≅
        pullbackExtension (pushoutExtension D₂₃₁ s) cB) := by
    have h₀ := pushout_pullback_extension_morphism_iso
      (directSumExtensionCyclicMorphism E₁ E₂ E₃)
    have h₁ := pushout_extension_preserves_iso s h₀
    have h₁' : Nonempty
        (pushoutExtension (pushoutExtension D₁₂₃ cA) s ≅
          pushoutExtension (pullbackExtension D₂₃₁ cB) s) := by
      simpa [D₁₂₃, D₂₃₁, cA, cB, directSumExtensionCyclicMorphism] using h₁
    have h₂ := pushout_pullback_extension_iso D₂₃₁ s cB
    have h₃ := pushout_extension_comp_iso D₁₂₃ cA s
    have h₃' : Nonempty
        (pushoutExtension D₁₂₃ s ≅
          pushoutExtension (pushoutExtension D₁₂₃ cA) s) := by
      exact ⟨by simpa [hs] using h₃.some.symm⟩
    exact ⟨h₃'.some.trans (h₁'.some.trans h₂.some)⟩
  have hP := pullback_extension_preserves_iso r hC
  have hComp := pullback_extension_comp_iso (pushoutExtension D₂₃₁ s) cB r
  have hComp' : Nonempty
      (pullbackExtension (pullbackExtension (pushoutExtension D₂₃₁ s) cB) r ≅
        pullbackExtension (pushoutExtension D₂₃₁ s) r) := by
    simpa [hr] using hComp
  have hN : Nonempty
      (pullbackExtension (pushoutExtension D₁₂₃ s) r ≅
        pullbackExtension (pushoutExtension D₂₃₁ s) r) :=
    ⟨hP.some.trans hComp'.some⟩
  have h₁ := baerSumLeftAssoc_normal_form E₁ E₂ E₃
  have h₂ := baerSumLeftAssoc_normal_form E₂ E₃ E₁
  have hLeft : Nonempty
      (baerSumExtension (baerSumExtension E₁ E₂) E₃ ≅
        baerSumExtension (baerSumExtension E₂ E₃) E₁) := by
    have hN' : Nonempty
        (pullbackExtension (pushoutExtension D₁₂₃ s) r ≅
          pullbackExtension (pushoutExtension D₂₃₁ s) r) := by
      simpa [D₁₂₃, D₂₃₁, σ, δ, s, r] using hN
    exact ⟨h₁.some.trans (hN'.some.trans h₂.some.symm)⟩
  exact ⟨hLeft.some.trans
    (baerSumExtension_comm (baerSumExtension E₂ E₃) E₁).some⟩

private theorem inverse_baerSumExtension_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (E : Extension C A B) :
    Nonempty
      (baerSumExtension (inverseExtension E) E ≅ splitExtension A B) := by
  let D : Extension C (A ⊞ A) (B ⊞ B) :=
    directSumExtensionVarying E E
  let v : A ⊞ A ⟶ A ⊞ A := biprod.map (-𝟙 A) (𝟙 A)
  let σ : A ⊞ A ⟶ A := biprodCodiagonal A
  let δ : B ⟶ B ⊞ B := biprodDiagonal B
  let w : A ⊞ A ⟶ A := v ≫ σ
  let rMiddle := pullback D.projection δ
  let rInclusion : A ⊞ A ⟶ rMiddle :=
    pullback.lift D.inclusion 0 (by simp [D.zero])
  let rProjection : rMiddle ⟶ B := pullback.snd D.projection δ
  let dS : D.middle ⟶ E.middle := biprod.snd
  let dF : D.middle ⟶ E.middle := biprod.fst
  let d : rMiddle ⟶ E.middle :=
    pullback.fst D.projection δ ≫ (dS - dF)
  have hrel :
      pullback.fst D.projection δ ≫ D.projection =
        pullback.snd D.projection δ ≫ δ :=
    pullback.condition
  have hfirst :
      pullback.fst D.projection δ ≫
          dS ≫ E.projection =
        pullback.snd D.projection δ := by
    have hδsnd : δ ≫ (biprod.snd : (B ⊞ B) ⟶ B) = 𝟙 B := by
      dsimp [δ, biprodDiagonal]
      simp
    have h := congrArg
      (fun k => k ≫ (biprod.snd : (B ⊞ B) ⟶ B)) hrel
    simpa [D, directSumExtensionVarying, Category.assoc, hδsnd] using h
  have hsecond :
      pullback.fst D.projection δ ≫
          dF ≫ E.projection =
        pullback.snd D.projection δ := by
    have hδfst : δ ≫ (biprod.fst : (B ⊞ B) ⟶ B) = 𝟙 B := by
      dsimp [δ, biprodDiagonal]
      simp
    have h := congrArg
      (fun k => k ≫ (biprod.fst : (B ⊞ B) ⟶ B)) hrel
    simpa [D, directSumExtensionVarying, Category.assoc, hδfst] using h
  have hd : d ≫ E.projection = 0 := by
    dsimp [d]
    rw [Category.assoc, sub_comp, comp_sub]
    rw [hfirst, hsecond, sub_self]
  letI : Mono E.inclusion := E.shortExact.mono_f
  let kA : rMiddle ⟶ A :=
    E.shortExact.fIsKernel.lift (KernelFork.ofι d hd)
  have hkA : kA ≫ E.inclusion = d := by
    dsimp [kA]
    simpa using
      (E.shortExact.fIsKernel.fac (KernelFork.ofι d hd)
        WalkingParallelPair.zero)
  have hd_inl : biprod.inl ≫ rInclusion ≫ d = -E.inclusion := by
    dsimp [d, rInclusion]
    rw [← Category.assoc (pullback.lift D.inclusion 0 _) (pullback.fst D.projection δ)
      (dS - dF), pullback.lift_fst]
    rw [comp_sub]
    simp [dS, dF, D, directSumExtensionVarying, Category.assoc, biprod.inl_map,
      biprod.lift_eq, add_comp, comp_add]
  have hd_inr : biprod.inr ≫ rInclusion ≫ d = E.inclusion := by
    dsimp [d, rInclusion]
    rw [← Category.assoc (pullback.lift D.inclusion 0 _) (pullback.fst D.projection δ)
      (dS - dF), pullback.lift_fst]
    rw [comp_sub]
    simp [dS, dF, D, directSumExtensionVarying, Category.assoc, biprod.inr_map,
      biprod.lift_eq, add_comp, comp_add]
  let hleft : rInclusion ≫ kA = w := by
    apply biprod.hom_ext'
    · apply (cancel_mono E.inclusion).1
      simp only [Category.assoc]
      rw [hkA]
      rw [hd_inl]
      simp [w, v, σ, biprodCodiagonal, biprod.desc_eq, Category.assoc,
        add_comp, comp_add]
    · apply (cancel_mono E.inclusion).1
      simp only [Category.assoc]
      rw [hkA]
      rw [hd_inr]
      simp [w, v, σ, biprodCodiagonal, biprod.desc_eq, Category.assoc,
        add_comp, comp_add]
  let kR : rMiddle ⟶ A ⊞ B := biprod.lift kA rProjection
  have hrzero : rInclusion ≫ rProjection = 0 := by
    dsimp [rInclusion]
    rw [pullback.lift_snd]
  have hkR : rInclusion ≫ kR = w ≫ biprod.inl := by
    dsimp [kR]
    rw [biprod.lift_eq]
    rw [comp_add, ← Category.assoc, ← Category.assoc, hleft, hrzero,
      zero_comp, add_zero]
  let P : Extension C A B :=
    pushoutExtension (pullbackExtension D δ) w
  let pInl : A ⟶ pushout w rInclusion := pushout.inl w rInclusion
  let pInr : rMiddle ⟶ pushout w rInclusion := pushout.inr w rInclusion
  let pG : pushout w rInclusion ⟶ B :=
    pushout.desc 0 rProjection (by simp [hrzero])
  have hpG_inl : pInl ≫ pG = 0 := by
    dsimp [pInl, pG]
    rw [pushout.inl_desc]
  have hpG_inr : pInr ≫ pG = rProjection := by
    dsimp [pInr, pG]
    rw [pushout.inr_desc]
  have hkG : kR ≫ biprod.snd = rProjection := by
    dsimp [kR]
    rw [biprod.lift_snd]
  let mMiddle : pushout w rInclusion ⟶ A ⊞ B :=
    pushout.desc biprod.inl kR hkR.symm
  have hm_left : pInl ≫ mMiddle = biprod.inl := by
    dsimp [pInl, mMiddle]
    rw [pushout.inl_desc]
  have hm_right : mMiddle ≫ biprod.snd = pG := by
    apply pushout.hom_ext
    · rw [← Category.assoc, hm_left]
      simpa [pInl] using hpG_inl.symm
    · rw [← Category.assoc, pushout.inr_desc, hkG, hpG_inr]
  let m : ExtensionHom
      (pushoutExtension (pullbackExtension D δ) w) (splitExtension A B) :=
    { middle := mMiddle
      comm_left := by
        change pInl ≫ mMiddle = biprod.inl
        exact hm_left
      comm_right := by
        change mMiddle ≫ biprod.snd = pG
        exact hm_right }
  let φ := m.toShortComplexHom
  have hmono : Mono mMiddle := by
    letI : Mono P.toShortComplex.f := P.shortExact.mono_f
    letI : Mono (splitExtension A B).toShortComplex.f :=
      (splitExtension A B).shortExact.mono_f
    letI : Mono φ.τ₁ := by
      dsimp [φ]
      constructor
      intro Z g h w
      rw [← Category.comp_id g, ← Category.comp_id h]
      exact w
    letI : Mono φ.τ₃ := by
      dsimp [φ]
      constructor
      intro Z g h w
      rw [← Category.comp_id g, ← Category.comp_id h]
      exact w
    apply ShortComplex.mono_τ₂_of_exact_of_mono φ
    exact P.shortExact.exact
  have hepi : Epi mMiddle := by
    letI : Epi P.toShortComplex.g := P.shortExact.epi_g
    letI : Epi (splitExtension A B).toShortComplex.g :=
      (splitExtension A B).shortExact.epi_g
    letI : Epi φ.τ₁ := by
      dsimp [φ]
      constructor
      intro Z g h w
      rw [← Category.id_comp g, ← Category.id_comp h]
      exact w
    letI : Epi φ.τ₃ := by
      dsimp [φ]
      constructor
      intro Z g h w
      rw [← Category.id_comp g, ← Category.id_comp h]
      exact w
    apply ShortComplex.epi_τ₂_of_exact_of_epi φ
    exact (splitExtension A B).shortExact.exact
  letI : Mono mMiddle := hmono
  letI : Epi mMiddle := hepi
  letI : IsIso mMiddle := isIso_of_mono_of_epi mMiddle
  let invMiddle : A ⊞ B ⟶ pushout w rInclusion := inv mMiddle
  let n : ExtensionHom (splitExtension A B)
      (pushoutExtension (pullbackExtension D δ) w) :=
    { middle := invMiddle
      comm_left := by
        change (biprod.inl : A ⟶ A ⊞ B) ≫ invMiddle = pInl
        rw [← cancel_mono mMiddle, Category.assoc biprod.inl invMiddle mMiddle,
          IsIso.inv_hom_id,
          Category.comp_id, hm_left]
      comm_right := by
        change invMiddle ≫ pG = (biprod.snd : A ⊞ B ⟶ B)
        rw [← cancel_epi mMiddle, IsIso.hom_inv_id_assoc, hm_right] }
  have hIsoP : Nonempty
      (pushoutExtension (pullbackExtension D δ) w ≅ splitExtension A B) := ⟨
    { hom := m
      inv := n
      hom_inv_id := ExtensionHom.ext _ _ (IsIso.hom_inv_id mMiddle)
      inv_hom_id := ExtensionHom.ext _ _ (IsIso.inv_hom_id mMiddle) }⟩
  have hP0 : Nonempty
      (pushoutExtension D v ≅
        pullbackExtension (directSumExtensionVarying (inverseExtension E) E)
          (𝟙 (B ⊞ B))) := by
    have h := pushout_pullback_extension_morphism_iso
      (directSumPushoutMorphism E E (-𝟙 A))
    simpa [D, v, directSumPushoutMorphism, inverseExtension] using h
  have hP1 : Nonempty
      (pushoutExtension D v ≅
        directSumExtensionVarying (inverseExtension E) E) := by
    exact ⟨hP0.some.trans
      (pullback_extension_id_iso
        (directSumExtensionVarying (inverseExtension E) E)).some⟩
  have hC : Nonempty
      (pushoutExtension
          (directSumExtensionVarying (inverseExtension E) E) σ ≅
        pushoutExtension D w) := by
    have h₁ := pushout_extension_preserves_iso σ hP1
    have h₂ := pushout_extension_comp_iso D v σ
    exact ⟨h₁.some.symm.trans (by simpa [w] using h₂.some)⟩
  have hVar : Nonempty
      (directSumExtension (inverseExtension E) E ≅
        directSumExtensionVarying (inverseExtension E) E) :=
    directSumExtension_varying_iso (inverseExtension E) E
  have hBaer : Nonempty
      (baerSumExtension (inverseExtension E) E ≅
        pullbackExtension (pushoutExtension D w) δ) := by
    have h₁ := pushout_extension_preserves_iso σ hVar
    have h₂ := pullback_extension_preserves_iso δ h₁
    have h₃ := pullback_extension_preserves_iso δ hC
    exact ⟨h₂.some.trans h₃.some⟩
  have h₄ := pushout_pullback_extension_iso D w δ
  exact ⟨hBaer.some.trans (h₄.some.symm.trans hIsoP.some)⟩

noncomputable instance extClassAddCommGroup
    {C : Type u} [Category.{v} C] [Abelian C] {A B : C} : AddCommGroup (Ext B A) where
  add_assoc := by
    intro x y z
    refine Quotient.inductionOn x ?_
    intro E₁
    refine Quotient.inductionOn y ?_
    intro E₂
    refine Quotient.inductionOn z ?_
    intro E₃
    change extensionClass
        (baerSumExtension (baerSumExtension E₁ E₂) E₃) =
      extensionClass (baerSumExtension E₁ (baerSumExtension E₂ E₃))
    exact Quotient.sound (baerSumExtension_assoc E₁ E₂ E₃)
  add_zero := by
    intro x
    exact baerSumClass_add_zero x
  zero_add := by
    intro x
    change baerSumClass zeroExtClass x = x
    rw [show baerSumClass zeroExtClass x = baerSumClass x zeroExtClass by
      exact baerSumClass_comm _ _]
    exact baerSumClass_add_zero x
  neg_add_cancel := by
    intro x
    refine Quotient.inductionOn x ?_
    intro E
    change extensionClass (baerSumExtension (inverseExtension E) E) =
      extensionClass (splitExtension A B)
    exact Quotient.sound (inverse_baerSumExtension_iso E)
  add_comm := by
    intro x y
    exact baerSumClass_comm x y
  sub_eq_add_neg := by
    intros
    rfl
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
