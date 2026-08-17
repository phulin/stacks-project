import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits

namespace Scratch

#check LinearMap.comp_apply
#check LinearMap.coe_comp
#check LinearMap.inl
#check LinearMap.inr
#check LinearMap.inl_apply
#check LinearMap.inr_apply
#check LinearMap.prod
#check LinearMap.coprod
#check LinearMap.coprod_apply
#check Submodule.mem_map
#check Submodule.mem_sup
#check Submodule.sum_mem
#check Submodule.add_mem
#check LinearMap.mem_ker
#check Submodule.Quotient.mk_eq_zero
#check Submodule.mkQ_surjective
#check Submodule.ker_mkQ

open CategoryTheory
open CategoryTheory.Limits

universe u w

noncomputable section

def relationLinearMap {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    (A : Type w) →ₗ[R] (B × C) where
  toFun x := (uab.hom x, -uac.hom x)
  map_add' x y := by
    ext <;> simp [add_comm]
  map_smul' r x := by simp

def relationMap {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    A ⟶ ModuleCat.of R (B × C) :=
  ModuleCat.ofHom (relationLinearMap uab uac)

def forkCokernel {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) : ModuleCat.{w} R :=
  cokernel (relationMap uab uac)

theorem test_fork {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    Nonempty
      (colimit (span uab uac) ≅ forkCokernel uab uac) := by
  let q : A ⟶ B ⊞ C := biprod.lift uab (-uac)
  have hrel :
      relationMap uab uac = q ≫ (ModuleCat.biprodIsoProd B C).hom := by
    have hrel' :
        relationMap uab uac ≫ (ModuleCat.biprodIsoProd B C).inv = q := by
      apply biprod.hom_ext
      · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst, biprod.lift_fst]
        ext x
        rfl
      · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd, biprod.lift_snd]
        ext x
        simp [relationMap, relationLinearMap, ModuleCat.comp_apply]
    apply (cancel_mono (ModuleCat.biprodIsoProd B C).inv).1
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact hrel'
  let hpush : IsColimit
      (CokernelCofork.ofπ (f := relationMap uab uac)
        ((ModuleCat.biprodIsoProd B C).inv ≫
          Abelian.BiproductToPushoutIsCokernel.biproductToPushout uab uac) (by
            rw [hrel, Category.assoc, Iso.hom_inv_id_assoc]
            exact
              (Abelian.BiproductToPushoutIsCokernel.biproductToPushoutCofork uab uac).condition)) :=
    CokernelCofork.isColimitOfIsColimitOfIff
      (Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout uab uac)
      (relationMap uab uac) (ModuleCat.biprodIsoProd B C).symm (by
        intro W φ
        simp [q, hrel, Category.assoc])
  let e : pushout uab uac ≅ forkCokernel uab uac :=
    IsColimit.coconePointUniqueUpToIso hpush
      (colimit.isColimit (parallelPair (relationMap uab uac) 0))
  let t : Cocone (span uab uac) :=
    Cocone.extend (colimit.cocone (span uab uac)) e.hom
  have ht : IsColimit t := by
    apply IsColimit.ofIsoColimit (colimit.isColimit (span uab uac))
    exact Cocone.ext e (by intro j; rfl)
  exact ⟨(colimit.isColimit (span uab uac)).coconePointUniqueUpToIso ht⟩

def quotientLeft {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    B →ₗ[R] ((B × C) ⧸ LinearMap.range (relationLinearMap uab uac)) :=
  (LinearMap.range (relationLinearMap uab uac)).mkQ.comp (LinearMap.inl R B C)

def quotientRight {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    C →ₗ[R] ((B × C) ⧸ LinearMap.range (relationLinearMap uab uac)) :=
  (LinearMap.range (relationLinearMap uab uac)).mkQ.comp (LinearMap.inr R B C)

abbrev quotientCocone {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    PushoutCocone uab uac :=
  PushoutCocone.mk (ModuleCat.ofHom (quotientLeft uab uac))
    (ModuleCat.ofHom (quotientRight uab uac)) (by
      apply ModuleCat.hom_ext
      ext x
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
      change (LinearMap.range (relationLinearMap uab uac)).mkQ
          (uab.hom x, 0) =
        (LinearMap.range (relationLinearMap uab uac)).mkQ
          (0, uac.hom x)
      rw [← sub_eq_zero]
      rw [← map_sub]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact LinearMap.mem_range.mpr ⟨x, by
        simp [relationLinearMap]⟩)

def quotientIsColimit {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    IsColimit (quotientCocone uab uac) := by
  apply PushoutCocone.isColimitAux'
  intro s
  let f : (B × C) →ₗ[R] (s.pt : Type w) :=
    LinearMap.coprod s.inl.hom s.inr.hom
  have hf : LinearMap.range (relationLinearMap uab uac) ≤ LinearMap.ker f := by
    rintro z ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have hs := congrArg (fun q => q.hom x) s.condition
    change s.inl.hom (uab.hom x) = s.inr.hom (uac.hom x) at hs
    change s.inl.hom (uab.hom x) + s.inr.hom (-uac.hom x) = 0
    rw [map_neg, ← hs, add_neg_cancel]
  let l := (LinearMap.range (relationLinearMap uab uac)).liftQ f hf
  refine ⟨ModuleCat.ofHom l, ?_, ?_, ?_⟩
  · apply ModuleCat.hom_ext
    ext b
    change l ((LinearMap.range (relationLinearMap uab uac)).mkQ (b, 0)) = _
    simp [l, f]
  · apply ModuleCat.hom_ext
    ext c
    change l ((LinearMap.range (relationLinearMap uab uac)).mkQ (0, c)) = _
    simp [l, f]
  · intro m hm₁ hm₂
    let m' : ModuleCat.of R
        ((B × C) ⧸ LinearMap.range (relationLinearMap uab uac)) ⟶ s.pt := m
    have hm₁' : m'.hom.comp (quotientLeft uab uac) = s.inl.hom := by
      have h := congrArg (fun q => q.hom) hm₁
      change m'.hom.comp (quotientLeft uab uac) = s.inl.hom at h
      exact h
    have hm₂' : m'.hom.comp (quotientRight uab uac) = s.inr.hom := by
      have h := congrArg (fun q => q.hom) hm₂
      change m'.hom.comp (quotientRight uab uac) = s.inr.hom at h
      exact h
    have hml : m' = ModuleCat.ofHom l := by
      apply ModuleCat.hom_ext
      change m'.hom = l
      apply LinearMap.ext
      intro q
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
        (LinearMap.range (relationLinearMap uab uac)) q
      rcases z with ⟨b, c⟩
      change m'.hom ((LinearMap.range (relationLinearMap uab uac)).mkQ (b, c)) =
        l ((LinearMap.range (relationLinearMap uab uac)).mkQ (b, c))
      have hsplit : (b, c) = (b, 0) + (0, c) := by ext <;> simp
      have hsplitQ :
          (LinearMap.range (relationLinearMap uab uac)).mkQ (b, c) =
            (LinearMap.range (relationLinearMap uab uac)).mkQ (b, 0) +
              (LinearMap.range (relationLinearMap uab uac)).mkQ (0, c) := by
        rw [hsplit, map_add]
      rw [hsplitQ, (m'.hom).map_add, l.map_add]
      change (m'.hom.comp (quotientLeft uab uac)) b +
          (m'.hom.comp (quotientRight uab uac)) c =
        l ((LinearMap.range (relationLinearMap uab uac)).mkQ (b, 0)) +
          l ((LinearMap.range (relationLinearMap uab uac)).mkQ (0, c))
      rw [hm₁', hm₂']
      have hlb :
          l ((LinearMap.range (relationLinearMap uab uac)).mkQ (b, 0)) =
            s.inl.hom b := by
        simp [l, Submodule.liftQ_apply, f]
      have hlc :
          l ((LinearMap.range (relationLinearMap uab uac)).mkQ (0, c)) =
            s.inr.hom c := by
        simp [l, Submodule.liftQ_apply, f]
      rw [hlb, hlc]
    change m' = ModuleCat.ofHom l
    exact hml

def quotientIso {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    colimit (span uab uac) ≅ ModuleCat.of R
      ((B × C) ⧸ LinearMap.range (relationLinearMap uab uac)) :=
  (colimit.isColimit (span uab uac)).coconePointUniqueUpToIso
    (quotientIsColimit uab uac)

lemma quotientIso_left {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    colimit.ι (span uab uac) WalkingSpan.left ≫ (quotientIso uab uac).hom =
      ModuleCat.ofHom (quotientLeft uab uac) := by
  change colimit.ι (span uab uac) WalkingSpan.left ≫
      ((colimit.isColimit (span uab uac)).coconePointUniqueUpToIso
        (quotientIsColimit uab uac)).hom =
    (quotientCocone uab uac).ι.app WalkingSpan.left
  exact (colimit.isColimit (span uab uac)).comp_coconePointUniqueUpToIso_hom
    (quotientIsColimit uab uac) WalkingSpan.left

lemma quotientIso_right {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    colimit.ι (span uab uac) WalkingSpan.right ≫ (quotientIso uab uac).hom =
      ModuleCat.ofHom (quotientRight uab uac) := by
  change colimit.ι (span uab uac) WalkingSpan.right ≫
      ((colimit.isColimit (span uab uac)).coconePointUniqueUpToIso
        (quotientIsColimit uab uac)).hom =
    (quotientCocone uab uac).ι.app WalkingSpan.right
  exact (colimit.isColimit (span uab uac)).comp_coconePointUniqueUpToIso_hom
    (quotientIsColimit uab uac) WalkingSpan.right

lemma quotientIso_zero {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    colimit.ι (span uab uac) WalkingSpan.zero ≫ (quotientIso uab uac).hom =
      uab ≫ ModuleCat.ofHom (quotientLeft uab uac) := by
  have h := colimit.w (span uab uac) WalkingSpan.Hom.fst
  rw [← h, Category.assoc, span_map_fst, quotientIso_left]
  rfl

theorem test_kernel_a {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    LinearMap.ker (colimit.ι (span uab uac) WalkingSpan.zero).hom =
      LinearMap.ker uab.hom ⊔ LinearMap.ker uac.hom := by
  let i : A ⟶ colimit (span uab uac) :=
    colimit.ι (span uab uac) WalkingSpan.zero
  change LinearMap.ker i.hom = LinearMap.ker uab.hom ⊔ LinearMap.ker uac.hom
  ext (x : (A : Type w))
  constructor
  · intro hx
    have hz := congrArg (fun q => q.hom x) (quotientIso_zero uab uac)
    change (quotientIso uab uac).hom (i.hom x) =
        quotientLeft uab uac (uab.hom x) at hz
    have hx' : i.hom x = 0 :=
      (LinearMap.mem_ker.mp hx)
    rw [hx', map_zero] at hz
    have hq : quotientLeft uab uac (uab.hom x) = 0 := by
      exact hz.symm
    have hmem : (uab.hom x, 0) ∈ LinearMap.range (relationLinearMap uab uac) := by
      change (LinearMap.range (relationLinearMap uab uac)).mkQ
          (uab.hom x, 0) = 0 at hq
      have hk : (uab.hom x, 0) ∈
          (LinearMap.range (relationLinearMap uab uac)).mkQ.ker :=
        (LinearMap.mem_ker).2 hq
      simpa only [Submodule.ker_mkQ] using hk
    rcases LinearMap.mem_range.mp hmem with ⟨y, hy⟩
    have hxy : uab.hom y = uab.hom x := by
      have := congrArg Prod.fst hy
      simpa [relationLinearMap] using this
    have hyker : uac.hom y = 0 := by
      have := congrArg Prod.snd hy
      simpa [relationLinearMap] using this
    apply (Submodule.mem_sup).2
    refine ⟨x - y, ?_, y, ?_, sub_add_cancel x y⟩
    · rw [LinearMap.mem_ker, map_sub, hxy.symm, sub_self]
    · exact (LinearMap.mem_ker).2 hyker
  · intro hx
    rcases (Submodule.mem_sup).1 hx with ⟨y, hy, z, hz, rfl⟩
    have hy' : uab.hom y = 0 := (LinearMap.mem_ker).1 hy
    have hz' : uac.hom z = 0 := (LinearMap.mem_ker).1 hz
    have hrel : quotientLeft uab uac (uab.hom z) =
        quotientRight uab uac (uac.hom z) := by
      change (LinearMap.range (relationLinearMap uab uac)).mkQ
          (uab.hom z, 0) =
        (LinearMap.range (relationLinearMap uab uac)).mkQ
          (0, uac.hom z)
      rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact LinearMap.mem_range.mpr ⟨z, by simp [relationLinearMap]⟩
    have hq : quotientLeft uab uac (uab.hom (y + z)) = 0 := by
      rw [map_add, hy', zero_add, hrel, hz', map_zero]
    apply (LinearMap.mem_ker).2
    apply (ConcreteCategory.bijective_of_isIso (quotientIso uab uac).hom).1
    have he := congrArg (fun q => q.hom (y + z)) (quotientIso_zero uab uac)
    change (quotientIso uab uac).hom (i.hom (y + z)) =
      quotientLeft uab uac (uab.hom (y + z)) at he
    rw [hq] at he
    simpa using he

theorem test_kernel_b {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    LinearMap.ker (colimit.ι (span uab uac) WalkingSpan.left).hom =
      Submodule.map uab.hom (LinearMap.ker uac.hom) := by
  let i : B ⟶ colimit (span uab uac) :=
    colimit.ι (span uab uac) WalkingSpan.left
  change LinearMap.ker i.hom = Submodule.map uab.hom (LinearMap.ker uac.hom)
  ext (x : (B : Type w))
  constructor
  · intro hx
    have hz := congrArg (fun q => q.hom x) (quotientIso_left uab uac)
    change (quotientIso uab uac).hom (i.hom x) =
        quotientLeft uab uac x at hz
    have hx' : i.hom x = 0 := (LinearMap.mem_ker.mp hx)
    rw [hx', map_zero] at hz
    have hq : quotientLeft uab uac x = 0 := hz.symm
    have hmem : (x, 0) ∈ LinearMap.range (relationLinearMap uab uac) := by
      change (LinearMap.range (relationLinearMap uab uac)).mkQ (x, 0) = 0 at hq
      have hk : (x, 0) ∈
          (LinearMap.range (relationLinearMap uab uac)).mkQ.ker :=
        (LinearMap.mem_ker).2 hq
      simpa only [Submodule.ker_mkQ] using hk
    rcases LinearMap.mem_range.mp hmem with ⟨y, hy⟩
    have hxy : uab.hom y = x := by
      have := congrArg Prod.fst hy
      simpa [relationLinearMap] using this
    have hyker : uac.hom y = 0 := by
      have := congrArg Prod.snd hy
      simpa [relationLinearMap] using this
    exact (Submodule.mem_map).2 ⟨y, (LinearMap.mem_ker).2 hyker, hxy⟩
  · intro hx
    rcases (Submodule.mem_map).1 hx with ⟨y, hy, hxy⟩
    have hy' : uac.hom y = 0 := (LinearMap.mem_ker).1 hy
    have hrel : quotientLeft uab uac (uab.hom y) =
        quotientRight uab uac (uac.hom y) := by
      change (LinearMap.range (relationLinearMap uab uac)).mkQ
          (uab.hom y, 0) =
        (LinearMap.range (relationLinearMap uab uac)).mkQ
          (0, uac.hom y)
      rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact LinearMap.mem_range.mpr ⟨y, by simp [relationLinearMap]⟩
    have hq : quotientLeft uab uac (uab.hom y) = 0 := by
      rw [hrel, hy', map_zero]
    rw [← hxy]
    apply (LinearMap.mem_ker).2
    apply (ConcreteCategory.bijective_of_isIso (quotientIso uab uac).hom).1
    have he := congrArg (fun q => q.hom (uab.hom y)) (quotientIso_left uab uac)
    change (quotientIso uab uac).hom (i.hom (uab.hom y)) =
      quotientLeft uab uac (uab.hom y) at he
    rw [hq] at he
    simpa using he

abbrev integerZeroModule : ModuleCat ℤ := ModuleCat.of ℤ (Fin 0 → ℤ)

def nonDirectedSourceSystem : WalkingSpan ⥤ ModuleCat ℤ :=
  span
    (0 : integerZeroModule ⟶ ModuleCat.of ℤ ℤ)
    (0 : integerZeroModule ⟶ ModuleCat.of ℤ ℤ)

def nonDirectedTargetSystem : WalkingSpan ⥤ ModuleCat ℤ :=
  span (𝟙 (ModuleCat.of ℤ ℤ)) (𝟙 (ModuleCat.of ℤ ℤ))

def nonDirectedSystemMap :
    nonDirectedSourceSystem ⟶ nonDirectedTargetSystem :=
  spanHomMk (0 : integerZeroModule ⟶ ModuleCat.of ℤ ℤ)
    (𝟙 (ModuleCat.of ℤ ℤ)) (𝟙 (ModuleCat.of ℤ ℤ))

theorem test_stagewise_injective :
    ∀ i : WalkingSpan,
      Function.Injective ((nonDirectedSystemMap.app i).hom) := by
  intro i
  cases i with
  | none =>
      intro x y _
      funext z
      exact Fin.elim0 z
  | some j =>
      cases j with
      | left =>
          intro x y h
          change x = y at h
          exact h
      | right =>
          intro x y h
          change x = y at h
          exact h

theorem test_not_injective :
    ¬ Function.Injective ((colim.map nonDirectedSystemMap).hom) := by
  intro hinj
  let c : Cocone nonDirectedSourceSystem :=
    PushoutCocone.mk (𝟙 (ModuleCat.of ℤ ℤ)) 0 (by
      simp [nonDirectedSourceSystem])
  let d := colimit.desc nonDirectedSourceSystem c
  let x : ℤ := 1
  have hxy :
      (colimit.ι nonDirectedSourceSystem WalkingSpan.left).hom x ≠
        (colimit.ι nonDirectedSourceSystem WalkingSpan.right).hom x := by
    intro h
    have hd := congrArg (fun q => d.hom q) h
    have hleft := colimit.ι_desc c WalkingSpan.left
    have hright := colimit.ι_desc c WalkingSpan.right
    have hleft_lin :
        d.hom.comp (colimit.ι nonDirectedSourceSystem WalkingSpan.left).hom =
          (c.ι.app WalkingSpan.left).hom := by
      simpa only [d, ModuleCat.hom_comp] using congrArg (fun q => q.hom) hleft
    have hright_lin :
        d.hom.comp (colimit.ι nonDirectedSourceSystem WalkingSpan.right).hom =
          (c.ι.app WalkingSpan.right).hom := by
      simpa only [d, ModuleCat.hom_comp] using congrArg (fun q => q.hom) hright
    have hleft' := congrArg (fun q => q x) hleft_lin
    have hright' := congrArg (fun q => q x) hright_lin
    have hleft_eval :
        d.hom ((colimit.ι nonDirectedSourceSystem WalkingSpan.left).hom x) =
          (c.ι.app WalkingSpan.left).hom x := by
      calc
        d.hom ((colimit.ι nonDirectedSourceSystem WalkingSpan.left).hom x) =
            (d.hom.comp (colimit.ι nonDirectedSourceSystem WalkingSpan.left).hom) x :=
          (LinearMap.comp_apply _ _ _).symm
        _ = (c.ι.app WalkingSpan.left).hom x := hleft'
    have hright_eval :
        d.hom ((colimit.ι nonDirectedSourceSystem WalkingSpan.right).hom x) =
          (c.ι.app WalkingSpan.right).hom x := by
      calc
        d.hom ((colimit.ι nonDirectedSourceSystem WalkingSpan.right).hom x) =
            (d.hom.comp (colimit.ι nonDirectedSourceSystem WalkingSpan.right).hom) x :=
          (LinearMap.comp_apply _ _ _).symm
        _ = (c.ι.app WalkingSpan.right).hom x := hright'
    rw [hleft_eval, hright_eval] at hd
    dsimp [c, x] at hd
    change (1 : ℤ) = 0 at hd
    exact one_ne_zero hd
  apply hxy
  apply hinj
  have hlegs :
      colimit.ι nonDirectedTargetSystem WalkingSpan.left =
        colimit.ι nonDirectedTargetSystem WalkingSpan.right := by
    have hleft := colimit.w nonDirectedTargetSystem WalkingSpan.Hom.fst
    have hright := colimit.w nonDirectedTargetSystem WalkingSpan.Hom.snd
    change colimit.ι nonDirectedTargetSystem WalkingSpan.left =
      colimit.ι nonDirectedTargetSystem WalkingSpan.zero at hleft
    change colimit.ι nonDirectedTargetSystem WalkingSpan.right =
      colimit.ι nonDirectedTargetSystem WalkingSpan.zero at hright
    exact hleft.trans hright.symm
  have hleg := congrArg (fun q => q.hom x) hlegs
  have hl := congrArg (fun q => q.hom x)
    (colimit.ι_map nonDirectedSystemMap WalkingSpan.left)
  have hr := congrArg (fun q => q.hom x)
    (colimit.ι_map nonDirectedSystemMap WalkingSpan.right)
  have hl' :
      (colim.map nonDirectedSystemMap).hom
          ((colimit.ι nonDirectedSourceSystem WalkingSpan.left).hom x) =
        (colimit.ι nonDirectedTargetSystem WalkingSpan.left).hom x := by
    change (colim.map nonDirectedSystemMap).hom
        ((colimit.ι nonDirectedSourceSystem WalkingSpan.left).hom x) =
      (colimit.ι nonDirectedTargetSystem WalkingSpan.left).hom x at hl
    exact hl
  have hr' :
      (colim.map nonDirectedSystemMap).hom
          ((colimit.ι nonDirectedSourceSystem WalkingSpan.right).hom x) =
        (colimit.ι nonDirectedTargetSystem WalkingSpan.right).hom x := by
    change (colim.map nonDirectedSystemMap).hom
        ((colimit.ι nonDirectedSourceSystem WalkingSpan.right).hom x) =
      (colimit.ι nonDirectedTargetSystem WalkingSpan.right).hom x at hr
    exact hr
  exact hl'.trans (hleg.trans hr'.symm)

def firstMap {R : Type u} [CommRing R]
    {I : Type w} [Category I]
    (S : I ⥤ ShortComplex (ModuleCat R)) :
    (S ⋙ ShortComplex.π₁) ⟶ (S ⋙ ShortComplex.π₂) where
  app i := (S.obj i).f
  naturality _i _j f := (S.map f).comm₁₂

def secondMap {R : Type u} [CommRing R]
    {I : Type w} [Category I]
    (S : I ⥤ ShortComplex (ModuleCat R)) :
    (S ⋙ ShortComplex.π₂) ⟶ (S ⋙ ShortComplex.π₃) where
  app i := (S.obj i).g
  naturality _i _j f := (S.map f).comm₂₃

theorem test_complex {R : Type u} [CommRing R]
    {I : Type w} [Category I]
    (S : I ⥤ ShortComplex (ModuleCat R)) :
    colim.map (firstMap S) ≫ colim.map (secondMap S) = 0 := by
  apply colimit.hom_ext
  intro i
  rw [← Category.assoc, colimit.ι_map, Category.assoc, colimit.ι_map]
  have hi :
      (firstMap S).app i ≫ (secondMap S).app i = 0 := by
    change (S.obj i).f ≫ (S.obj i).g = 0
    exact (S.obj i).zero
  rw [← Category.assoc, hi, zero_comp, comp_zero]

end

end Scratch
