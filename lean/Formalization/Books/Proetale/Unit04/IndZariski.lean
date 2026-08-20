import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit154.FilteredColimitsEtale
import Formalization.Books.Proetale.Unit03.LocalIsomorphisms

/-!
# Pro-étale Cohomology, Chapter 4: Ind-Zariski algebra

The source defines ind-Zariski maps as filtered colimits of local
isomorphisms.  The local-isomorphism stages below use Mathlib's canonical
`Algebra.IsLocalIso` class, and the filtered colimit is recorded in the
category of `A`-algebras so that the structure maps and the target
identification are part of the presentation.
-/

namespace Formalization.Books.Proetale.Unit04

open CategoryTheory CategoryTheory.Limits

universe u

/-! ## Filtered colimit presentations -/

/-- A filtered colimit presentation of an `A`-algebra whose stages are local
isomorphisms over `A`.

The diagram lives in `Under (CommRingCat.of A)`, so every stage already
contains its structure map from `A`.  The final isomorphism is likewise in
that category and therefore identifies the induced map on the colimit with
the specified ring map `f`.
-/
structure IndZariskiPresentation
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    extends Formalization.Books.Algebra.Unit154.FilteredColimitData f where
  stagesLocalIsomorphism : ∀ i,
    Formalization.Books.Proetale.Unit03.IsLocalIsomorphism
      (diagram.obj i).hom.hom

/-- A ring map is ind-Zariski when its target is a filtered colimit of
`A`-algebras whose structure maps are local isomorphisms.
-/
def IsIndZariski {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  Nonempty (IndZariskiPresentation f)

private theorem isLocalIsomorphism_localizationAway
    {A : Type u} [CommRing A] (r : A) :
    Formalization.Books.Proetale.Unit03.IsLocalIsomorphism
      (algebraMap A (Localization.Away r)) := by
  have hcanon : Algebra.IsLocalIso A (Localization.Away r) := by
    let : Algebra (Localization.Away r)
        (Localization.Away (1 : Localization.Away r)) := inferInstance
    let hs : Algebra.IsStandardOpenImmersion A (Localization.Away r) :=
      ⟨r, inferInstance⟩
    let e : Localization.Away r ≃ₐ[A]
        Localization.Away (1 : Localization.Away r) :=
      (IsLocalization.atOne (Localization.Away r)
        (S := Localization.Away (1 : Localization.Away r))).restrictScalars A
    exact ⟨fun q hq => ⟨1, hq.one_notMem, hs.of_algEquiv e⟩⟩
  unfold Formalization.Books.Proetale.Unit03.IsLocalIsomorphism
  let alg0 : Algebra A (Localization.Away r) := inferInstance
  have heq : (algebraMap A (Localization.Away r)).toAlgebra = alg0 := by
    apply IsScalarTower.Algebra.ext
    intro a x
    change (algebraMap A (Localization.Away r)) a * x = a • x
    rw [Algebra.smul_def]
  rw [heq]
  exact hcanon

private theorem localizationAway_prod_dvd
    {A : Type u} [CommRing A] (S : Submonoid A)
    (t u : Finset S) (h : t ⊆ u) :
    t.prod (fun s : S => (s : A)) ∣ u.prod (fun s : S => (s : A)) := by
  classical
  refine ⟨(u \ t).prod (fun s : S => (s : A)), ?_⟩
  calc
    u.prod (fun s : S => (s : A)) =
        (u \ t).prod (fun s : S => (s : A)) * t.prod (fun s : S => (s : A)) :=
      (Finset.prod_sdiff h).symm
    _ = t.prod (fun s : S => (s : A)) * (u \ t).prod (fun s : S => (s : A)) := by
      rw [mul_comm]

private structure LocalizationIndex (S : Type u) where
  carrier : Finset S

private instance localizationIndexPartialOrder (S : Type u) :
    PartialOrder (LocalizationIndex S) where
  le t u := t.carrier ⊆ u.carrier
  lt t u := t.carrier ⊂ u.carrier
  le_refl t := by intro x hx; exact hx
  le_trans _ _ _ htu huv := by
    intro x hx
    exact huv (htu hx)
  le_antisymm t u htu hut := by
    cases t with
    | mk t =>
      cases u with
      | mk u =>
        have h : t = u := Finset.Subset.antisymm htu hut
        cases h
        rfl

private instance localizationIndexFiltered (S : Type u) :
    IsFiltered (LocalizationIndex S) := by
  classical
  refine { nonempty := ⟨⟨∅⟩⟩, cocone_objs := ?_, cocone_maps := ?_ }
  · intro t u
    let v : LocalizationIndex S := ⟨t.carrier ∪ u.carrier⟩
    exact ⟨v, CategoryTheory.homOfLE (Finset.subset_union_left),
      CategoryTheory.homOfLE (Finset.subset_union_right), trivial⟩
  · intro t u f g
    exact ⟨u, 𝟙 _, Subsingleton.elim _ _⟩

private noncomputable def localizationAwayDiagram
    {A : Type u} [CommRing A] (S : Submonoid A) :
    LocalizationIndex S ⥤ Under (CommRingCat.of A) := by
  classical
  refine {
    obj := fun t => CommRingCat.mkUnder (CommRingCat.of A)
      (Localization.Away (t.carrier.prod (fun s : S => (s : A))))
    map := fun {t u} h => ?_
    map_id := ?_
    map_comp := ?_ }
  · let rt := t.carrier.prod (fun s : S => (s : A))
    let ru := u.carrier.prod (fun s : S => (s : A))
    let hr : IsUnit (algebraMap A (Localization.Away ru) rt) :=
      IsLocalization.Away.isUnit_of_dvd (S := Localization.Away ru) (x := ru)
        (localizationAway_prod_dvd S t.carrier u.carrier (CategoryTheory.leOfHom h))
    exact Under.homMk (CommRingCat.ofHom (Localization.awayLift
      (algebraMap A (Localization.Away ru)) rt hr)) (by
        apply CommRingCat.hom_ext
        change (IsLocalization.Away.lift rt hr).comp
            (algebraMap A (Localization.Away rt)) =
          algebraMap A (Localization.Away ru)
        exact IsLocalization.Away.lift_comp rt hr)
  · intro t
    dsimp [CommRingCat.mkUnder]
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    simp only [Under.homMk_right, Under.id_right]
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id]
    change Localization.awayLift
        (algebraMap A (Localization.Away
          (t.carrier.prod (fun s : S => (s : A)))))
        (t.carrier.prod (fun s : S => (s : A))) _ =
      RingHom.id (Localization.Away
        (t.carrier.prod (fun s : S => (s : A))))
    apply IsLocalization.ringHom_ext (M := Submonoid.powers
      (t.carrier.prod (fun s : S => (s : A))))
    simp [Localization.awayLift]
  · intro t u v htu huv
    let htu' : IsUnit (algebraMap A (Localization.Away
        (u.carrier.prod (fun s : S => (s : A))))
        (t.carrier.prod (fun s : S => (s : A)))) :=
      IsLocalization.Away.isUnit_of_dvd
        (S := Localization.Away (u.carrier.prod (fun s : S => (s : A))))
        (x := u.carrier.prod (fun s : S => (s : A)))
        (localizationAway_prod_dvd S t.carrier u.carrier (CategoryTheory.leOfHom htu))
    let huv' : IsUnit (algebraMap A (Localization.Away
        (v.carrier.prod (fun s : S => (s : A))))
        (u.carrier.prod (fun s : S => (s : A)))) :=
      IsLocalization.Away.isUnit_of_dvd
        (S := Localization.Away (v.carrier.prod (fun s : S => (s : A))))
        (x := v.carrier.prod (fun s : S => (s : A)))
        (localizationAway_prod_dvd S u.carrier v.carrier (CategoryTheory.leOfHom huv))
    let htv' : IsUnit (algebraMap A (Localization.Away
        (v.carrier.prod (fun s : S => (s : A))))
        (t.carrier.prod (fun s : S => (s : A)))) :=
      IsLocalization.Away.isUnit_of_dvd
        (S := Localization.Away (v.carrier.prod (fun s : S => (s : A))))
        (x := v.carrier.prod (fun s : S => (s : A)))
        (localizationAway_prod_dvd S t.carrier v.carrier
          (show t.carrier ⊆ v.carrier from
            fun x hx => (CategoryTheory.leOfHom huv)
              ((CategoryTheory.leOfHom htu) hx)))
    dsimp [CommRingCat.mkUnder]
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    simp only [Under.homMk_right, Under.comp_right]
    simp only [CommRingCat.hom_ofHom]
    simp only [CommRingCat.hom_comp]
    change Localization.awayLift
        (algebraMap A (Localization.Away
          (v.carrier.prod (fun s : S => (s : A)))))
        (t.carrier.prod (fun s : S => (s : A))) htv' =
      (Localization.awayLift
        (algebraMap A (Localization.Away
          (v.carrier.prod (fun s : S => (s : A)))))
        (u.carrier.prod (fun s : S => (s : A))) huv').comp
        (Localization.awayLift
          (algebraMap A (Localization.Away
            (u.carrier.prod (fun s : S => (s : A)))))
          (t.carrier.prod (fun s : S => (s : A))) htu')
    apply IsLocalization.ringHom_ext (M := Submonoid.powers
      (t.carrier.prod (fun s : S => (s : A))))
    simp [Localization.awayLift]
    rw [RingHom.comp_assoc]
    rw [IsLocalization.Away.lift_comp
      (t.carrier.prod (fun s : S => (s : A))) htu']
    rw [IsLocalization.Away.lift_comp
      (u.carrier.prod (fun s : S => (s : A))) huv']

private noncomputable def localizationAwayCocone
    {A : Type u} [CommRing A] (S : Submonoid A) :
    Cocone (localizationAwayDiagram S) := by
  classical
  refine { pt := CommRingCat.mkUnder (CommRingCat.of A) (Localization S), ι := ?_ }
  refine { app := fun t => ?_, naturality := ?_ }
  · let rt := t.carrier.prod (fun s : S => (s : A))
    have hrt : rt ∈ S := by
      exact S.prod_mem (fun s hs => s.property)
    let hr : IsUnit (algebraMap A (Localization S) rt) :=
      IsLocalization.map_units (Localization S) ⟨rt, hrt⟩
    exact Under.homMk (CommRingCat.ofHom (Localization.awayLift
      (algebraMap A (Localization S)) rt hr)) (by
        apply CommRingCat.hom_ext
        change (IsLocalization.Away.lift rt hr).comp
            (algebraMap A (Localization.Away rt)) =
          algebraMap A (Localization S)
        exact IsLocalization.Away.lift_comp rt hr)
  · intro t v htv
    let rt := t.carrier.prod (fun s : S => (s : A))
    let rv := v.carrier.prod (fun s : S => (s : A))
    have htv' : IsUnit (algebraMap A (Localization.Away rv) rt) :=
      IsLocalization.Away.isUnit_of_dvd (S := Localization.Away rv) (x := rv)
        (localizationAway_prod_dvd S t.carrier v.carrier
          (CategoryTheory.leOfHom htv))
    have hrv_mem : rv ∈ S := by
      exact S.prod_mem (fun s hs => s.property)
    have hrv : IsUnit (algebraMap A (Localization S) rv) :=
      IsLocalization.map_units (Localization S) ⟨rv, hrv_mem⟩
    have hrt_mem : rt ∈ S := by
      exact S.prod_mem (fun s hs => s.property)
    have hrt : IsUnit (algebraMap A (Localization S) rt) :=
      IsLocalization.map_units (Localization S) ⟨rt, hrt_mem⟩
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    simp only [Under.comp_right, CommRingCat.hom_comp]
    change (Localization.awayLift
        (algebraMap A (Localization S))
        rv hrv).comp
        (Localization.awayLift
          (algebraMap A (Localization.Away
            (v.carrier.prod (fun s : S => (s : A)))))
          rt htv') =
      Localization.awayLift
        (algebraMap A (Localization S))
        rt hrt
    apply IsLocalization.ringHom_ext (M := Submonoid.powers
      (t.carrier.prod (fun s : S => (s : A))))
    simp [Localization.awayLift]
    rw [RingHom.comp_assoc]
    rw [IsLocalization.Away.lift_comp rt htv']
    rw [IsLocalization.Away.lift_comp rv hrv]

private noncomputable def localizationAwayIsColimit
    {A : Type u} [CommRing A] (S : Submonoid A) :
    IsColimit (localizationAwayCocone S) := by
  classical
  refine { desc := fun s => ?_, fac := ?_, uniq := ?_ }
  · let g : A →+* s.pt.right := s.pt.hom.hom
    have hg : ∀ y : S, IsUnit (g y) := by
      intro y
      let t : LocalizationIndex S := ⟨{y}⟩
      let rt := t.carrier.prod (fun s : S => (s : A))
      have hrt : IsUnit (algebraMap A (Localization.Away rt) rt) :=
        IsLocalization.Away.algebraMap_isUnit rt
      have hrel :
          (s.ι.app t).right.hom.comp
              ((localizationAwayDiagram S).obj t).hom.hom = g := by
        change (s.ι.app t).right.hom.comp
            (algebraMap A (Localization.Away rt)) = s.pt.hom.hom
        exact congrArg CommRingCat.Hom.hom (Under.w (s.ι.app t))
      have hval := congrArg (fun k : A →+* s.pt.right => k rt) hrel
      have hrt' : IsUnit (g rt) := by
        rw [← hval]
        exact IsUnit.map (s.ι.app t).right.hom hrt
      simpa [rt, t] using hrt'
    let l : Localization S →+* s.pt.right := IsLocalization.lift hg
    exact Under.homMk (CommRingCat.ofHom l) (by
      apply CommRingCat.hom_ext
      change l.comp (algebraMap A (Localization S)) = g
      exact IsLocalization.lift_comp hg)
  · intro s j
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    simp only [localizationAwayCocone, Under.comp_right, CommRingCat.hom_comp]
    let rj := j.carrier.prod (fun s : S => (s : A))
    have hrj_mem : rj ∈ S := by
      exact S.prod_mem (fun s hs => s.property)
    have hrj : IsUnit (algebraMap A (Localization S) rj) :=
      IsLocalization.map_units (Localization S) ⟨rj, hrj_mem⟩
    change (IsLocalization.lift (M := S) _).comp
        (Localization.awayLift
          (algebraMap A (Localization S))
          rj hrj) =
      (s.ι.app j).right.hom
    apply IsLocalization.ringHom_ext (M := Submonoid.powers rj)
    simp [Localization.awayLift]
    rw [RingHom.comp_assoc]
    rw [IsLocalization.Away.lift_comp rj hrj]
    rw [IsLocalization.lift_comp]
    have hrel :
        (s.ι.app j).right.hom.comp (algebraMap A (Localization.Away rj)) =
          s.pt.hom.hom := by
      exact congrArg CommRingCat.Hom.hom (Under.w (s.ι.app j))
    exact hrel.symm
  · intro s m hm
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    change (Under.Hom.right m).hom =
      IsLocalization.lift (M := S) (S := Localization S) _
    apply IsLocalization.ringHom_ext (R := A) (S := Localization S) (M := S)
    rw [IsLocalization.lift_comp]
    exact congrArg CommRingCat.Hom.hom (Under.w m)

/-! ## Ind-Zariski maps -/

/-- Localization is the basic example of an ind-Zariski map.

The source points to the standard filtered-colimit presentation of a
localization; its proof is deferred to the proof stage.
-/
theorem localization_isIndZariski
    {A : Type u} [CommRing A] (S : Submonoid A) :
    IsIndZariski (algebraMap A (Localization S)) := by
  refine ⟨{
    index := LocalizationIndex S
    diagram := localizationAwayDiagram S
    cocone := localizationAwayCocone S
    isColimit := localizationAwayIsColimit S
    targetIso := ?_
    stagesLocalIsomorphism := ?_ }⟩
  · exact Iso.refl _
  · intro t
    exact isLocalIsomorphism_localizationAway _

/-- Ind-Zariski maps are stable under base change. -/
theorem isIndZariski_baseChange
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (f : A →+* B) (g : A →+* A')
    (hf : IsIndZariski f) :
    IsIndZariski (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  sorry

/-- Ind-Zariski maps are stable under composition. -/
theorem isIndZariski_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hf : IsIndZariski f) (hg : IsIndZariski g) :
    IsIndZariski (g.comp f) := by
  sorry

/-- The permanence property: among `A`-algebras, an ind-Zariski map between
two ind-Zariski algebras is again ind-Zariski. -/
theorem isIndZariski_of_algebraHom
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (h : B →ₐ[A] C)
    (hB : IsIndZariski (algebraMap A B))
    (hC : IsIndZariski (algebraMap A C)) :
    IsIndZariski h.toRingHom := by
  sorry

/-- A filtered colimit of ind-Zariski `A`-algebras is ind-Zariski over `A`.

The cocone and its colimit witness are explicit, as is the isomorphism of
the cocone point with the target ring map.
-/
theorem isIndZariski_filteredColimit
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of A))
    (hF : ∀ j, IsIndZariski (F.obj j).hom.hom)
    (c : Cocone F) (hc : IsColimit c)
    (e : c.pt ≅ Formalization.Books.Algebra.Unit127.underRingHom f) :
    IsIndZariski f := by
  sorry

/-- An ind-Zariski map identifies the local rings at corresponding primes. -/
theorem isIndZariski_identifiesLocalRings
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : IsIndZariski f) :
    Formalization.Books.Proetale.Unit03.IdentifiesLocalRings f := by
  sorry

end Formalization.Books.Proetale.Unit04
