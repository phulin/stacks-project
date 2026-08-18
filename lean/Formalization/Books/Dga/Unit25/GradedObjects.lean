import Formalization.Books.Dga.Unit25.Totalization
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.CategoryTheory.GradedObject
import Mathlib.Logic.Function.Basic

/-!
# The graded category of graded objects

The homogeneous Hom type is written with the two indices used in the book.
The equality proof in the dependent product is the Lean representation of the
condition `p + q = n`; in particular this is a product of component Hom types,
not a direct sum. -/

noncomputable section

open CategoryTheory
open DirectSum
open scoped DirectSum

universe u v w

namespace Formalization.Books.Dga.Unit25

variable {B : Type u} [Category.{v} B]
  [Formalization.Books.Homology.Unit03.AdditiveCategory B]

abbrev GradedDegreePair (n : ℤ) :=
  {pq : ℤ × ℤ // pq.1 + pq.2 = n}

/-- A degree-`n` map of graded objects, displayed as the family
`f_{p,q} : A^{-q} ⟶ B^p` for `p + q = n`. -/
abbrev GradedObjectHomogeneous
    (A C : CategoryTheory.GradedObject ℤ B) (n : ℤ) :=
  ∀ s : GradedDegreePair n, (A (-s.1.2) ⟶ C s.1.1)

instance gradedObjectHomogeneousAddCommGroup
    (A C : CategoryTheory.GradedObject ℤ B) (n : ℤ) :
    AddCommGroup (GradedObjectHomogeneous A C n) := inferInstance

instance gradedObjectHomogeneousIntModule
    (A C : CategoryTheory.GradedObject ℤ B) (n : ℤ) :
    Module ℤ (GradedObjectHomogeneous A C n) := inferInstance

/-- The component formula for composition of homogeneous graded-object maps. -/
def gradedObjectHomogeneousComponent
    {A C : CategoryTheory.GradedObject ℤ B} {n : ℤ}
    (f : GradedObjectHomogeneous A C n) (p q : ℤ) (h : p + q = n) :
    A (-q) ⟶ C p :=
  f ⟨(p, q), h⟩

def gradedObjectHomogeneousComp
    {A C E : CategoryTheory.GradedObject ℤ B} (i j : ℤ)
    (f : GradedObjectHomogeneous A C i)
    (g : GradedObjectHomogeneous C E j) :
    GradedObjectHomogeneous A E (i + j) :=
  fun s =>
    gradedObjectHomogeneousComponent f (-(j - s.1.1)) s.1.2 (by omega) ≫
      gradedObjectHomogeneousComponent g s.1.1 (j - s.1.1) (by omega)

/-- The degree-zero identity family. -/
def gradedObjectHomogeneousId
    (A : CategoryTheory.GradedObject ℤ B) :
  GradedObjectHomogeneous A A 0 :=
  fun s => eqToHom (congrArg A (by omega))

omit [Formalization.Books.Homology.Unit03.AdditiveCategory B] in
theorem gradedObjectHomogeneousComp_component
    {A C E : CategoryTheory.GradedObject ℤ B} {i j : ℤ}
    (f : GradedObjectHomogeneous A C i)
    (g : GradedObjectHomogeneous C E j)
    (p r : ℤ) (h : p + r = i + j) :
    gradedObjectHomogeneousComponent (gradedObjectHomogeneousComp i j f g) p r h =
      gradedObjectHomogeneousComponent f (-(j - p)) r (by omega) ≫
        gradedObjectHomogeneousComponent g p (j - p) (by omega) :=
  by simp [gradedObjectHomogeneousComp, gradedObjectHomogeneousComponent]

/-- The totalization specification for graded objects.  The subtype pins the
homogeneous composition and identity in the generic totalization data to the
component formulas above. -/
def GradedObjectTotalizationSpec : Type _ :=
  {D : TotalGradedCategoryData ℤ (CategoryTheory.GradedObject ℤ B)
      (fun A C n => GradedObjectHomogeneous A C n) //
    (∀ A, D.homogeneous_id A = gradedObjectHomogeneousId A) ∧
    (∀ {A C E : CategoryTheory.GradedObject ℤ B} {i j : ℤ}
      (f : GradedObjectHomogeneous A C i)
      (g : GradedObjectHomogeneous C E j),
      D.homogeneous_comp f g = gradedObjectHomogeneousComp i j f g)}

/-- The direct-sum extension of the componentwise composition exists. -/
theorem gradedObjectTotalizationSpec_nonempty :
    Nonempty (GradedObjectTotalizationSpec (B := B)) := by
  have hid_comp :
      ∀ {A C : CategoryTheory.GradedObject ℤ B} {j : ℤ}
        (f : GradedObjectHomogeneous A C j)
        (s : GradedDegreePair (0 + j)),
        gradedObjectHomogeneousComp (0 : ℤ) j
            (gradedObjectHomogeneousId A) f s =
          f ⟨s.1, by omega⟩ := by
    intro A C j f s
    obtain ⟨⟨p, q⟩, h⟩ := s
    have hq : q = j - p := by omega
    subst q
    simp [gradedObjectHomogeneousComp, gradedObjectHomogeneousComponent,
      gradedObjectHomogeneousId]
  have hcomp_id :
      ∀ {A C : CategoryTheory.GradedObject ℤ B} {i : ℤ}
        (f : GradedObjectHomogeneous A C i)
        (s : GradedDegreePair (i + 0)),
        gradedObjectHomogeneousComp i (0 : ℤ) f
            (gradedObjectHomogeneousId C) s =
          f ⟨s.1, by omega⟩ := by
    intro A C i f s
    obtain ⟨⟨p, q⟩, h⟩ := s
    have hq : q = -p + i := by omega
    subst q
    dsimp [gradedObjectHomogeneousComp, gradedObjectHomogeneousComponent,
      gradedObjectHomogeneousId]
    have hp : -(0 - p) = p := by omega
    have hC : C (-(0 - p)) = C p := congrArg C hp
    apply eq_of_heq
    symm
    apply (heq_comp_eqToHom_iff
      (f := f ⟨(-(0 - p), -p + i), by omega⟩)
      (g := f ⟨(p, -p + i), by omega⟩) hC).2
    have hs :
        (⟨(p, -p + i), by omega⟩ : GradedDegreePair i) =
          ⟨(-(0 - p), -p + i), by omega⟩ := by
      apply Subtype.ext
      change (p, -p + i) = (-(0 - p), -p + i)
      exact Prod.ext (by omega) rfl
    congr 1
  let total_comp :
      ∀ {A C E : CategoryTheory.GradedObject ℤ B},
        DirectSum ℤ (fun n => GradedObjectHomogeneous A C n) →
          DirectSum ℤ (fun n => GradedObjectHomogeneous C E n) →
            DirectSum ℤ (fun n => GradedObjectHomogeneous A E n) :=
    fun {A C E} f g =>
      DirectSum.toModule ℤ ℤ
        ((DirectSum ℤ (fun n => GradedObjectHomogeneous C E n)) →ₗ[ℤ]
          DirectSum ℤ (fun n => GradedObjectHomogeneous A E n))
        (fun i =>
          { toFun := fun fi =>
              DirectSum.toModule ℤ ℤ
                (DirectSum ℤ (fun n => GradedObjectHomogeneous A E n))
                (fun j =>
                  { toFun := fun gj =>
                      DirectSum.lof ℤ ℤ
                        (fun n => GradedObjectHomogeneous A E n) (i + j)
                        (gradedObjectHomogeneousComp i j fi gj)
                    map_add' := by
                      intro gj gj'
                      have hcomp := congrArg
                        (DirectSum.lof ℤ ℤ
                          (fun n => GradedObjectHomogeneous A E n) (i + j))
                        (show gradedObjectHomogeneousComp i j fi (gj + gj') =
                            gradedObjectHomogeneousComp i j fi gj +
                              gradedObjectHomogeneousComp i j fi gj' by
                          funext s
                          simp [gradedObjectHomogeneousComp,
                            gradedObjectHomogeneousComponent])
                      rw [hcomp]
                      exact (DirectSum.lof ℤ ℤ
                        (fun n => GradedObjectHomogeneous A E n) (i + j)).map_add _ _
                    map_smul' := by
                      intro r gj
                      have hcomp := congrArg
                        (DirectSum.lof ℤ ℤ
                          (fun n => GradedObjectHomogeneous A E n) (i + j))
                        (show gradedObjectHomogeneousComp i j fi (r • gj) =
                            r • gradedObjectHomogeneousComp i j fi gj by
                          funext s
                          simp [gradedObjectHomogeneousComp,
                            gradedObjectHomogeneousComponent])
                      rw [hcomp]
                      exact (DirectSum.lof ℤ ℤ
                        (fun n => GradedObjectHomogeneous A E n) (i + j)).map_smul _ _ })
            map_add' := by
              intro fi fi'
              apply DirectSum.linearMap_ext
              intro j
              apply LinearMap.ext
              intro gj'
              simp only [LinearMap.comp_apply, LinearMap.add_apply]
              simp only [DirectSum.toModule_lof]
              dsimp
              have hcomp := congrArg
                (DirectSum.lof ℤ ℤ
                  (fun n => GradedObjectHomogeneous A E n) (i + j))
                (show gradedObjectHomogeneousComp i j (fi + fi') gj' =
                    gradedObjectHomogeneousComp i j fi gj' +
                      gradedObjectHomogeneousComp i j fi' gj' by
                  funext s
                  simp [gradedObjectHomogeneousComp,
                    gradedObjectHomogeneousComponent])
              rw [hcomp]
              exact (DirectSum.lof ℤ ℤ
                (fun n => GradedObjectHomogeneous A E n) (i + j)).map_add _ _
            map_smul' := by
              intro r fi
              apply DirectSum.linearMap_ext
              intro j
              apply LinearMap.ext
              intro gj'
              simp only [LinearMap.comp_apply, LinearMap.smul_apply]
              simp only [DirectSum.toModule_lof]
              dsimp
              have hcomp := congrArg
                (DirectSum.lof ℤ ℤ
                  (fun n => GradedObjectHomogeneous A E n) (i + j))
                (show gradedObjectHomogeneousComp i j (r • fi) gj' =
                    r • gradedObjectHomogeneousComp i j fi gj' by
                  funext s
                  simp [gradedObjectHomogeneousComp,
                    gradedObjectHomogeneousComponent])
              rw [hcomp]
              exact (DirectSum.lof ℤ ℤ
                (fun n => GradedObjectHomogeneous A E n) (i + j)).map_smul _ _ }) f g
  have hcomp_add_left :
      ∀ {A C E : CategoryTheory.GradedObject ℤ B}
        (f f' : DirectSum ℤ (fun n => GradedObjectHomogeneous A C n))
        (g : DirectSum ℤ (fun n => GradedObjectHomogeneous C E n)),
        total_comp (f + f') g = total_comp f g + total_comp f' g := by
    intro A C E f f' g
    simp [total_comp]
  have hcomp_add_right :
      ∀ {A C E : CategoryTheory.GradedObject ℤ B}
        (f : DirectSum ℤ (fun n => GradedObjectHomogeneous A C n))
        (g g' : DirectSum ℤ (fun n => GradedObjectHomogeneous C E n)),
        total_comp f (g + g') = total_comp f g + total_comp f g' := by
    intro A C E f g g'
    simp [total_comp]
  have hcomp_smul_left :
      ∀ {A C E : CategoryTheory.GradedObject ℤ B} (r : ℤ)
        (f : DirectSum ℤ (fun n => GradedObjectHomogeneous A C n))
        (g : DirectSum ℤ (fun n => GradedObjectHomogeneous C E n)),
        total_comp (r • f) g = r • total_comp f g := by
    intro A C E r f g
    simp [total_comp]
  have hcomp_smul_right :
      ∀ {A C E : CategoryTheory.GradedObject ℤ B} (r : ℤ)
        (f : DirectSum ℤ (fun n => GradedObjectHomogeneous A C n))
        (g : DirectSum ℤ (fun n => GradedObjectHomogeneous C E n)),
        total_comp f (r • g) = r • total_comp f g := by
    intro A C E r f g
    simp [total_comp]
  have hcomp_lof :
      ∀ {A C E : CategoryTheory.GradedObject ℤ B} {i j : ℤ}
        (f : GradedObjectHomogeneous A C i)
        (g : GradedObjectHomogeneous C E j),
        total_comp
            (DirectSum.lof ℤ ℤ
              (fun n => GradedObjectHomogeneous A C n) i f)
            (DirectSum.lof ℤ ℤ
              (fun n => GradedObjectHomogeneous C E n) j g) =
          DirectSum.lof ℤ ℤ
            (fun n => GradedObjectHomogeneous A E n) (i + j)
            (gradedObjectHomogeneousComp i j f g) := by
    intro A C E i j f g
    simp [total_comp]
  refine ⟨
    { homogeneous_id := fun A => gradedObjectHomogeneousId A
      homogeneous_comp := fun f g => gradedObjectHomogeneousComp _ _ f g
      total_comp := total_comp
      total_comp_add_left := by
        intro A C E f f' g
        exact hcomp_add_left f f' g
      total_comp_add_right := by
        intro A C E f g g'
        exact hcomp_add_right f g g'
      total_comp_smul_left := by
        intro A C E r f g
        exact hcomp_smul_left r f g
      total_comp_smul_right := by
        intro A C E r f g
        exact hcomp_smul_right r f g
      total_comp_lof := by
        intro A C E i j f g
        simp [total_comp]
      total_comp_degree := by
        intro A C E i j f g
        rcases f.property with ⟨f', hf⟩
        rcases g.property with ⟨g', hg⟩
        refine ⟨gradedObjectHomogeneousComp i j f' g', ?_⟩
        rw [← hf, ← hg]
        simp [total_comp]
      total_id := fun A => DirectSum.lof ℤ ℤ
        (fun n => GradedObjectHomogeneous A A n) 0
        (gradedObjectHomogeneousId A)
      total_id_eq_lof := by intro A; rfl
      total_id_comp := by
        intro A C f
        refine DirectSum.induction_on f ?_ ?_ ?_
        · simp [total_comp]
        · intro j g
          change total_comp
              (DirectSum.lof ℤ ℤ
                (fun n => GradedObjectHomogeneous A A n) 0
                (gradedObjectHomogeneousId A))
              (DirectSum.lof ℤ ℤ
                (fun n => GradedObjectHomogeneous A C n) j g) =
            DirectSum.lof ℤ ℤ
              (fun n => GradedObjectHomogeneous A C n) j g
          simp [total_comp]
          rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
          apply (DFinsupp.single_eq_single_iff _ _ _ _).2
          left
          constructor
          · omega
          · apply Function.hfunext
              (congrArg (fun n => GradedDegreePair n)
                (show (0 : ℤ) + j = j by omega))
            intro s s' hs
            have hpred :
                (fun pq : ℤ × ℤ => pq.1 + pq.2 = 0 + j) ≍
                  (fun pq : ℤ × ℤ => pq.1 + pq.2 = j) := by
              apply heq_of_eq
              funext pq
              simp only [zero_add]
            have hpair : s.1 = s'.1 := eq_of_heq
              ((Subtype.heq_iff_coe_heq rfl hpred).mp hs)
            have hs0 :
                (⟨s.1, by omega⟩ : GradedDegreePair j) = s' := by
              apply Subtype.ext
              exact hpair
            exact HEq.trans (heq_of_eq (hid_comp g s))
              (congr_arg_heq g hs0)
        · intro f g hf hg
          rw [hcomp_add_right, hf, hg]
      total_comp_id := by
        intro A C f
        refine DirectSum.induction_on f ?_ ?_ ?_
        · simp [total_comp]
        · intro i f
          change total_comp
              (DirectSum.lof ℤ ℤ
                (fun n => GradedObjectHomogeneous A C n) i f)
              (DirectSum.lof ℤ ℤ
                (fun n => GradedObjectHomogeneous C C n) 0
                (gradedObjectHomogeneousId C)) =
            DirectSum.lof ℤ ℤ
              (fun n => GradedObjectHomogeneous A C n) i f
          simp [total_comp]
          rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
          apply (DFinsupp.single_eq_single_iff _ _ _ _).2
          left
          constructor
          · omega
          · apply Function.hfunext
              (congrArg (fun n => GradedDegreePair n)
                (show i + (0 : ℤ) = i by omega))
            intro s s' hs
            have hpred :
                (fun pq : ℤ × ℤ => pq.1 + pq.2 = i + 0) ≍
                  (fun pq : ℤ × ℤ => pq.1 + pq.2 = i) := by
              apply heq_of_eq
              funext pq
              simp only [add_zero]
            have hpair : s.1 = s'.1 := eq_of_heq
              ((Subtype.heq_iff_coe_heq rfl hpred).mp hs)
            have hs0 :
                (⟨s.1, by omega⟩ : GradedDegreePair i) = s' := by
              apply Subtype.ext
              exact hpair
            exact HEq.trans (heq_of_eq (hcomp_id f s))
              (congr_arg_heq f hs0)
        · intro f g hf hg
          rw [hcomp_add_left, hf, hg]
      total_assoc := by
        intro A C E F f g h
        refine DirectSum.induction_on f ?_ ?_ ?_
        · simp [total_comp]
        · intro i f
          refine DirectSum.induction_on g ?_ ?_ ?_
          · simp [total_comp]
          · intro j g
            refine DirectSum.induction_on h ?_ ?_ ?_
            · simp [total_comp]
            · intro k h
              change total_comp
                  (total_comp
                    (DirectSum.lof ℤ ℤ
                      (fun n => GradedObjectHomogeneous A C n) i f)
                    (DirectSum.lof ℤ ℤ
                      (fun n => GradedObjectHomogeneous C E n) j g))
                  (DirectSum.lof ℤ ℤ
                    (fun n => GradedObjectHomogeneous E F n) k h) =
                total_comp
                  (DirectSum.lof ℤ ℤ
                    (fun n => GradedObjectHomogeneous A C n) i f)
                  (total_comp
                    (DirectSum.lof ℤ ℤ
                      (fun n => GradedObjectHomogeneous C E n) j g)
                    (DirectSum.lof ℤ ℤ
                      (fun n => GradedObjectHomogeneous E F n) k h))
              rw [hcomp_lof (f := f) (g := g)]
              rw [hcomp_lof (f := g) (g := h)]
              rw [hcomp_lof
                (f := gradedObjectHomogeneousComp i j f g) (g := h)]
              rw [hcomp_lof
                (f := f)
                (g := gradedObjectHomogeneousComp j k g h)]
              rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
              apply (DFinsupp.single_eq_single_iff _ _ _ _).2
              left
              constructor
              · omega
              · apply Function.hfunext
                  (congrArg (fun n => GradedDegreePair n)
                    (show (i + j) + k = i + (j + k) by omega))
                intro s s' hs
                have hpred :
                    (fun pq : ℤ × ℤ => pq.1 + pq.2 = (i + j) + k) ≍
                      (fun pq : ℤ × ℤ => pq.1 + pq.2 = i + (j + k)) := by
                  apply heq_of_eq
                  funext pq
                  simp only [add_assoc]
                have hpair : s.1 = s'.1 := eq_of_heq
                  ((Subtype.heq_iff_coe_heq rfl hpred).mp hs)
                have hs0 :
                    (⟨s.1, by omega⟩ : GradedDegreePair (i + (j + k))) = s' := by
                  apply Subtype.ext
                  exact hpair
                have hcomp :
                    gradedObjectHomogeneousComp (i + j) k
                        (gradedObjectHomogeneousComp i j f g) h s =
                      gradedObjectHomogeneousComp i (j + k) f
                        (gradedObjectHomogeneousComp j k g h)
                        ⟨s.1, by omega⟩ := by
                  obtain ⟨⟨p, q⟩, hq⟩ := s
                  dsimp [gradedObjectHomogeneousComp,
                    gradedObjectHomogeneousComponent]
                  have hf :
                      (⟨(-(j - -(k - p)), q), by omega⟩ : GradedDegreePair i) =
                        ⟨(-(j + k - p), q), by omega⟩ := by
                    apply Subtype.ext
                    change (-(j - -(k - p)), q) = (-(j + k - p), q)
                    exact Prod.ext (by omega) rfl
                  have hg :
                      (⟨(-(k - p), j - -(k - p)), by omega⟩ :
                        GradedDegreePair j) =
                        ⟨(-(k - p), j + k - p), by omega⟩ := by
                    apply Subtype.ext
                    change (-(k - p), j - -(k - p)) =
                      (-(k - p), j + k - p)
                    exact Prod.ext (by omega) (by omega)
                  simp only [Category.assoc]
                  congr 1
                  · apply congrArg C
                    omega
                  · exact congr_arg_heq f hf
                  · apply heq_comp
                    · apply congrArg C
                      omega
                    · rfl
                    · rfl
                    · exact congr_arg_heq g hg
                    · exact heq_of_eq rfl
                exact HEq.trans (heq_of_eq hcomp)
                  (congr_arg_heq
                    (gradedObjectHomogeneousComp i (j + k) f
                      (gradedObjectHomogeneousComp j k g h)) hs0)
            · intro h h' hh hh'
              change total_comp
                  (total_comp
                    (DirectSum.lof ℤ ℤ
                      (fun n => GradedObjectHomogeneous A C n) i f)
                    (DirectSum.lof ℤ ℤ
                      (fun n => GradedObjectHomogeneous C E n) j g))
                  (h + h') =
                total_comp
                  (DirectSum.lof ℤ ℤ
                    (fun n => GradedObjectHomogeneous A C n) i f)
                  (total_comp
                    (DirectSum.lof ℤ ℤ
                      (fun n => GradedObjectHomogeneous C E n) j g)
                    (h + h'))
              have hh0 :
                  total_comp
                      (total_comp
                        (DirectSum.lof ℤ ℤ
                          (fun n => GradedObjectHomogeneous A C n) i f)
                        (DirectSum.lof ℤ ℤ
                          (fun n => GradedObjectHomogeneous C E n) j g)) h =
                    total_comp
                      (DirectSum.lof ℤ ℤ
                        (fun n => GradedObjectHomogeneous A C n) i f)
                      (total_comp
                        (DirectSum.lof ℤ ℤ
                          (fun n => GradedObjectHomogeneous C E n) j g) h) := by
                simpa only [DirectSum.lof_eq_of] using hh
              have hh0' :
                  total_comp
                      (total_comp
                        (DirectSum.lof ℤ ℤ
                          (fun n => GradedObjectHomogeneous A C n) i f)
                        (DirectSum.lof ℤ ℤ
                          (fun n => GradedObjectHomogeneous C E n) j g)) h' =
                    total_comp
                      (DirectSum.lof ℤ ℤ
                        (fun n => GradedObjectHomogeneous A C n) i f)
                      (total_comp
                        (DirectSum.lof ℤ ℤ
                          (fun n => GradedObjectHomogeneous C E n) j g) h') := by
                simpa only [DirectSum.lof_eq_of] using hh'
              calc
                total_comp
                    (total_comp
                      (DirectSum.lof ℤ ℤ
                        (fun n => GradedObjectHomogeneous A C n) i f)
                      (DirectSum.lof ℤ ℤ
                        (fun n => GradedObjectHomogeneous C E n) j g))
                    (h + h') =
                    total_comp
                        (total_comp
                          (DirectSum.lof ℤ ℤ
                            (fun n => GradedObjectHomogeneous A C n) i f)
                          (DirectSum.lof ℤ ℤ
                            (fun n => GradedObjectHomogeneous C E n) j g)) h +
                      total_comp
                        (total_comp
                          (DirectSum.lof ℤ ℤ
                            (fun n => GradedObjectHomogeneous A C n) i f)
                          (DirectSum.lof ℤ ℤ
                            (fun n => GradedObjectHomogeneous C E n) j g)) h' :=
                  hcomp_add_right _ _ _
                _ =
                    total_comp
                        (DirectSum.lof ℤ ℤ
                          (fun n => GradedObjectHomogeneous A C n) i f)
                        (total_comp
                          (DirectSum.lof ℤ ℤ
                            (fun n => GradedObjectHomogeneous C E n) j g) h) +
                      total_comp
                        (DirectSum.lof ℤ ℤ
                          (fun n => GradedObjectHomogeneous A C n) i f)
                        (total_comp
                          (DirectSum.lof ℤ ℤ
                            (fun n => GradedObjectHomogeneous C E n) j g) h') := by
                  rw [hh0, hh0']
                _ = total_comp
                    (DirectSum.lof ℤ ℤ
                      (fun n => GradedObjectHomogeneous A C n) i f)
                    (total_comp
                      (DirectSum.lof ℤ ℤ
                        (fun n => GradedObjectHomogeneous C E n) j g) h +
                      total_comp
                        (DirectSum.lof ℤ ℤ
                          (fun n => GradedObjectHomogeneous C E n) j g) h') := by
                  symm
                  apply hcomp_add_right
                _ = total_comp
                    (DirectSum.lof ℤ ℤ
                      (fun n => GradedObjectHomogeneous A C n) i f)
                    (total_comp
                      (DirectSum.lof ℤ ℤ
                        (fun n => GradedObjectHomogeneous C E n) j g)
                      (h + h')) := by
                  exact congrArg
                    (fun x => total_comp
                      (DirectSum.lof ℤ ℤ
                        (fun n => GradedObjectHomogeneous A C n) i f) x)
                    (hcomp_add_right
                      (DirectSum.lof ℤ ℤ
                        (fun n => GradedObjectHomogeneous C E n) j g) h h').symm
          · intro g g' hg hg'
            change total_comp
                (total_comp
                  (DirectSum.lof ℤ ℤ
                    (fun n => GradedObjectHomogeneous A C n) i f) (g + g')) h =
              total_comp
                (DirectSum.lof ℤ ℤ
                  (fun n => GradedObjectHomogeneous A C n) i f)
                (total_comp (g + g') h)
            have hg0 :
                total_comp
                    (total_comp
                      (DirectSum.lof ℤ ℤ
                        (fun n => GradedObjectHomogeneous A C n) i f) g) h =
                  total_comp
                    (DirectSum.lof ℤ ℤ
                      (fun n => GradedObjectHomogeneous A C n) i f)
                    (total_comp g h) := by
              simpa only [DirectSum.lof_eq_of] using hg
            have hg0' :
                total_comp
                    (total_comp
                      (DirectSum.lof ℤ ℤ
                        (fun n => GradedObjectHomogeneous A C n) i f) g') h =
                  total_comp
                    (DirectSum.lof ℤ ℤ
                      (fun n => GradedObjectHomogeneous A C n) i f)
                    (total_comp g' h) := by
              simpa only [DirectSum.lof_eq_of] using hg'
            calc
              total_comp
                  (total_comp
                    (DirectSum.lof ℤ ℤ
                      (fun n => GradedObjectHomogeneous A C n) i f) (g + g')) h =
                  total_comp
                      (total_comp
                        (DirectSum.lof ℤ ℤ
                          (fun n => GradedObjectHomogeneous A C n) i f) g +
                        total_comp
                          (DirectSum.lof ℤ ℤ
                            (fun n => GradedObjectHomogeneous A C n) i f) g') h := by
                    rw [hcomp_add_right, hcomp_add_left]
              _ = total_comp
                    (total_comp
                      (DirectSum.lof ℤ ℤ
                        (fun n => GradedObjectHomogeneous A C n) i f) g) h +
                    total_comp
                      (total_comp
                        (DirectSum.lof ℤ ℤ
                          (fun n => GradedObjectHomogeneous A C n) i f) g') h := by
                    apply hcomp_add_left
              _ = total_comp
                    (DirectSum.lof ℤ ℤ
                      (fun n => GradedObjectHomogeneous A C n) i f)
                    (total_comp g h) +
                    total_comp
                      (DirectSum.lof ℤ ℤ
                        (fun n => GradedObjectHomogeneous A C n) i f)
                      (total_comp g' h) := by
                    rw [hg0, hg0']
              _ = total_comp
                    (DirectSum.lof ℤ ℤ
                      (fun n => GradedObjectHomogeneous A C n) i f)
                    (total_comp g h + total_comp g' h) := by
                    symm
                    apply hcomp_add_right
              _ = total_comp
                    (DirectSum.lof ℤ ℤ
                      (fun n => GradedObjectHomogeneous A C n) i f)
                    (total_comp (g + g') h) := by
                    rw [hcomp_add_left]
        · intro f f' hf hf'
          calc
            total_comp (total_comp (f + f') g) h =
                total_comp (total_comp f g + total_comp f' g) h := by
              rw [hcomp_add_left]
            _ = total_comp (total_comp f g) h +
                total_comp (total_comp f' g) h := by
              apply hcomp_add_left
            _ = total_comp f (total_comp g h) +
                total_comp f' (total_comp g h) := by
              rw [hf, hf']
            _ = total_comp (f + f') (total_comp g h) := by
              symm
              apply hcomp_add_left }
    , by
      constructor
      · intro A
        rfl
      · intro A C E i j f g
        rfl⟩

noncomputable def gradedObjectTotalizationSpec :
    GradedObjectTotalizationSpec (B := B) :=
  Classical.choice (gradedObjectTotalizationSpec_nonempty (B := B))

noncomputable def gradedObjectCategoryData :
    TotalGradedCategoryData ℤ (CategoryTheory.GradedObject ℤ B)
      (fun A C n => GradedObjectHomogeneous A C n) :=
  (gradedObjectTotalizationSpec (B := B)).1

abbrev GradedObjectCategory :=
  TotalGradedObject (gradedObjectCategoryData (B := B))

def gradedObjectCategoryObject
    (A : CategoryTheory.GradedObject ℤ B) : GradedObjectCategory (B := B) :=
  ⟨A⟩

@[simp] theorem gradedObjectCategoryObject_underlying
    (A : CategoryTheory.GradedObject ℤ B) :
    (gradedObjectCategoryObject (B := B) A).underlying = A :=
  rfl

@[instance_reducible] noncomputable def gradedObjectGradedCategory :
    GradedCategory ℤ (GradedObjectCategory (B := B)) := inferInstance

theorem gradedObjectTotalization_homogeneous_id (A : CategoryTheory.GradedObject ℤ B) :
    (gradedObjectCategoryData (B := B)).homogeneous_id A =
      gradedObjectHomogeneousId A :=
  (gradedObjectTotalizationSpec (B := B)).2.1 A

theorem gradedObjectTotalization_homogeneous_comp
    {A C E : CategoryTheory.GradedObject ℤ B} {i j : ℤ}
    (f : GradedObjectHomogeneous A C i)
    (g : GradedObjectHomogeneous C E j) :
    (gradedObjectCategoryData (B := B)).homogeneous_comp f g =
      gradedObjectHomogeneousComp i j f g :=
  (gradedObjectTotalizationSpec (B := B)).2.2 f g

/-! The degree-zero category is the usual pointwise category of graded
objects, up to the harmless type synonyms used to keep the two category
structures distinct. -/

theorem gradedObject_degree_zero_recovers_graded_objects :
    Nonempty
      (DegreeZero (gradedObjectGradedCategory (B := B)) ≌
        CategoryTheory.GradedObject ℤ B) := by
  let homTo {A C : CategoryTheory.GradedObject ℤ B}
      (f : directSumComponent ℤ
        (fun n => GradedObjectHomogeneous A C n) 0) :
      GradedObjectHomogeneous A C 0 :=
    Classical.choose f.2
  let homFrom {A C : CategoryTheory.GradedObject ℤ B}
      (f : GradedObjectHomogeneous A C 0) :
      directSumComponent ℤ
        (fun n => GradedObjectHomogeneous A C n) 0 :=
      ⟨DirectSum.lof ℤ ℤ
        (fun n => GradedObjectHomogeneous A C n) 0 f,
      ⟨f, rfl⟩⟩
  let totalComp0 {A C E : CategoryTheory.GradedObject ℤ B}
      (f : directSumComponent ℤ
        (fun n => GradedObjectHomogeneous A C n) 0)
      (g : directSumComponent ℤ
        (fun n => GradedObjectHomogeneous C E n) 0) :
      directSumComponent ℤ
        (fun n => GradedObjectHomogeneous A E n) 0 :=
    ⟨(gradedObjectCategoryData (B := B)).total_comp
        (f : DirectSum ℤ (fun n => GradedObjectHomogeneous A C n))
        (g : DirectSum ℤ (fun n => GradedObjectHomogeneous C E n)),
      (gradedObjectCategoryData (B := B)).total_comp_degree f g⟩
  have homFrom_homTo {A C : CategoryTheory.GradedObject ℤ B}
      (f : directSumComponent ℤ
        (fun n => GradedObjectHomogeneous A C n) 0) :
      homFrom (homTo f) = f := by
    apply Subtype.ext
    exact Classical.choose_spec f.2
  have homTo_homFrom {A C : CategoryTheory.GradedObject ℤ B}
      (f : GradedObjectHomogeneous A C 0) :
      homTo (homFrom f) = f := by
    apply DirectSum.of_injective 0
    simpa [DirectSum.lof_eq_of, homTo, homFrom] using
      (Classical.choose_spec (homFrom f).2)
  have homFrom_injective {A C : CategoryTheory.GradedObject ℤ B} :
      Function.Injective (homFrom (A := A) (C := C)) := by
    intro f g h
    exact (homTo_homFrom f).symm.trans
      ((congrArg (homTo (A := A) (C := C)) h).trans
        (homTo_homFrom g))
  let familyToMap {A C : CategoryTheory.GradedObject ℤ B}
      (f : GradedObjectHomogeneous A C 0) : A ⟶ C :=
    fun p => eqToHom (congrArg A (show p = -(-p) by omega)) ≫
      f ⟨(p, -p), by omega⟩
  let mapToFamily {A C : CategoryTheory.GradedObject ℤ B}
      (f : A ⟶ C) : GradedObjectHomogeneous A C 0 :=
    fun s => eqToHom
        (congrArg A (show -s.1.2 = s.1.1 by omega)) ≫ f s.1.1
  have mapToFamily_familyToMap
      {A C : CategoryTheory.GradedObject ℤ B}
      (f : GradedObjectHomogeneous A C 0) :
      mapToFamily (familyToMap f) = f := by
    funext s
    obtain ⟨⟨p, q⟩, h⟩ := s
    have hq : q = -p := by omega
    subst q
    simp [mapToFamily, familyToMap]
  have familyToMap_mapToFamily
      {A C : CategoryTheory.GradedObject ℤ B}
      (f : A ⟶ C) :
      familyToMap (mapToFamily f) = f := by
    funext p
    simp [mapToFamily, familyToMap]
  have hzero_id (A : CategoryTheory.GradedObject ℤ B) :
      mapToFamily (𝟙 A) = gradedObjectHomogeneousId A := by
    funext s
    obtain ⟨⟨p, q⟩, h⟩ := s
    have hq : q = -p := by omega
    subst q
    simp [mapToFamily, gradedObjectHomogeneousId]
  have hzero_comp {A C E : CategoryTheory.GradedObject ℤ B}
      (f : GradedObjectHomogeneous A C 0)
      (g : GradedObjectHomogeneous C E 0) :
      gradedObjectHomogeneousComp 0 0 f g =
        mapToFamily (familyToMap f ≫ familyToMap g) := by
    funext s
    obtain ⟨⟨p, q⟩, h⟩ := s
    have hq : q = -p := by omega
    subst q
    dsimp [gradedObjectHomogeneousComp,
      gradedObjectHomogeneousComponent, mapToFamily, familyToMap]
    have hp : -(0 - p) = p := by omega
    have hq : 0 - p = -p := by omega
    simp
    have hf :
        (⟨(-(0 - p), -p), by omega⟩ : GradedDegreePair 0) =
          ⟨(p, -p), by omega⟩ := by
      apply Subtype.ext
      change (-(0 - p), -p) = (p, -p)
      exact Prod.ext hp rfl
    have hg :
        (⟨(p, 0 - p), by omega⟩ : GradedDegreePair 0) =
          ⟨(p, -p), by omega⟩ := by
      apply Subtype.ext
      change (p, 0 - p) = (p, -p)
      exact Prod.ext rfl hq
    have hff :
        f ⟨(-(0 - p), -p), by omega⟩ ≍
          f ⟨(p, -p), by omega⟩ ≫
            eqToHom (congrArg C (show p = -(-p) by omega)) := by
      exact ((comp_eqToHom_heq_iff _ _
        (congrArg C (show p = -(-p) by omega))).2
        (congr_arg_heq f hf).symm).symm
    have hgg :
        g ⟨(p, 0 - p), by omega⟩ ≍
          g ⟨(p, -p), by omega⟩ :=
      congr_arg_heq g hg
    apply eq_of_heq
    simpa only [Category.assoc] using
      (heq_comp
        (f := f ⟨(-(0 - p), -p), by omega⟩)
        (g := g ⟨(p, 0 - p), by omega⟩)
        (f' := f ⟨(p, -p), by omega⟩ ≫
          eqToHom (congrArg C (show p = -(-p) by omega)))
        (g' := g ⟨(p, -p), by omega⟩)
        rfl (congrArg C (show -(0 - p) = -(-p) by omega)) rfl hff hgg)
  have hsource_id (A : CategoryTheory.GradedObject ℤ B) :
      homFrom (mapToFamily (𝟙 A)) =
        𝟙 (DegreeZero.of (gradedObjectGradedCategory (B := B))
          (gradedObjectCategoryObject (B := B) A)) := by
    apply Subtype.ext
    change DirectSum.lof ℤ ℤ
        (fun n => GradedObjectHomogeneous A A n) 0
        (mapToFamily (𝟙 A)) =
      (gradedObjectCategoryData (B := B)).total_id A
    rw [hzero_id, (gradedObjectCategoryData (B := B)).total_id_eq_lof,
      gradedObjectTotalization_homogeneous_id]
  have hhom_comp {A C E : CategoryTheory.GradedObject ℤ B}
      (f : directSumComponent ℤ
        (fun n => GradedObjectHomogeneous A C n) 0)
    (g : directSumComponent ℤ
        (fun n => GradedObjectHomogeneous C E n) 0) :
      homTo (totalComp0 f g) =
        gradedObjectHomogeneousComp 0 0 (homTo f) (homTo g) := by
    apply homFrom_injective
    rw [homFrom_homTo]
    rw [← homFrom_homTo f, ← homFrom_homTo g]
    simp only [homTo_homFrom]
    dsimp [totalComp0, homFrom]
    apply Subtype.ext
    change (gradedObjectCategoryData (B := B)).total_comp
        (DirectSum.lof ℤ ℤ
          (fun n => GradedObjectHomogeneous A C n) 0 (homTo f))
        (DirectSum.lof ℤ ℤ
          (fun n => GradedObjectHomogeneous C E n) 0 (homTo g)) =
      DirectSum.lof ℤ ℤ
        (fun n => GradedObjectHomogeneous A E n) 0
        (gradedObjectHomogeneousComp 0 0 (homTo f) (homTo g))
    rw [(gradedObjectCategoryData (B := B)).total_comp_lof]
    congr 1
    exact gradedObjectTotalization_homogeneous_comp (B := B) _ _
  have hsource_comp {A C E : CategoryTheory.GradedObject ℤ B}
      (f : A ⟶ C) (g : C ⟶ E) :
      homFrom (mapToFamily (f ≫ g)) =
        totalComp0 (homFrom (mapToFamily f))
          (homFrom (mapToFamily g)) := by
    apply Subtype.ext
    change DirectSum.lof ℤ ℤ
        (fun n => GradedObjectHomogeneous A E n) 0
        (mapToFamily (f ≫ g)) =
      (gradedObjectCategoryData (B := B)).total_comp _ _
    rw [(gradedObjectCategoryData (B := B)).total_comp_lof]
    congr 1
    rw [gradedObjectTotalization_homogeneous_comp (B := B)]
    rw [hzero_comp, familyToMap_mapToFamily, familyToMap_mapToFamily]
  let F :
      DegreeZero (gradedObjectGradedCategory (B := B)) ⥤
        CategoryTheory.GradedObject ℤ B :=
    { obj := fun X => (DegreeZero.obj
          (gradedObjectGradedCategory (B := B)) X).underlying
      map := fun f => familyToMap (homTo f)
      map_id := by
        intro X
        cases X with
        | up X =>
          cases X with
          | mk A =>
            change familyToMap (homTo
                (𝟙 (DegreeZero.of
                  (gradedObjectGradedCategory (B := B))
                  (gradedObjectCategoryObject (B := B) A)))) = 𝟙 A
            rw [← hsource_id A]
            change familyToMap
              (homTo (homFrom (mapToFamily (𝟙 A)))) = 𝟙 A
            calc
              familyToMap
                  (homTo (homFrom (mapToFamily (𝟙 A)))) =
                familyToMap (mapToFamily (𝟙 A)) := by
                  congr 1
                  exact homTo_homFrom (mapToFamily (𝟙 A))
              _ = 𝟙 A := familyToMap_mapToFamily (𝟙 A)
      map_comp := by
        intro X Y Z f g
        cases X with
        | up X =>
          cases X with
          | mk A =>
            cases Y with
            | up Y =>
              cases Y with
              | mk C =>
                cases Z with
                | up Z =>
                  cases Z with
                  | mk E =>
                    change directSumComponent ℤ
                      (fun n => GradedObjectHomogeneous A C n) 0 at f
                    change directSumComponent ℤ
                      (fun n => GradedObjectHomogeneous C E n) 0 at g
                    change familyToMap (homTo (totalComp0 f g)) =
                      familyToMap (homTo f) ≫ familyToMap (homTo g)
                    rw [hhom_comp, hzero_comp, familyToMap_mapToFamily] }
  let G :
      CategoryTheory.GradedObject ℤ B ⥤
        DegreeZero (gradedObjectGradedCategory (B := B)) :=
    { obj := fun A => DegreeZero.of
          (gradedObjectGradedCategory (B := B))
          (gradedObjectCategoryObject (B := B) A)
      map := fun f => homFrom (mapToFamily f)
      map_id := by
        intro A
        exact hsource_id A
      map_comp := by
        intro A C E f g
        change homFrom (mapToFamily (f ≫ g)) =
            totalComp0 (homFrom (mapToFamily f))
              (homFrom (mapToFamily g))
        exact hsource_comp f g }
  let unitIso (X : DegreeZero (gradedObjectGradedCategory (B := B))) :
      X ≅ (F ⋙ G).obj X := by
    cases X with
    | up X =>
      cases X with
      | mk A =>
        exact Iso.refl _
  let counitIso (A : CategoryTheory.GradedObject ℤ B) :
      (G ⋙ F).obj A ≅ A := by
    exact Iso.refl _
  let unitNatIso :
      𝟭 (DegreeZero (gradedObjectGradedCategory (B := B))) ≅ F ⋙ G := by
    refine NatIso.ofComponents
        (fun X => unitIso X)
        (fun {X Y} f => ?_)
    cases X with
    | up X =>
      cases X with
      | mk A =>
        cases Y with
        | up Y =>
          cases Y with
          | mk C =>
            change directSumComponent ℤ
              (fun n => GradedObjectHomogeneous A C n) 0 at f
            dsimp [unitIso, F, G]
            apply Subtype.ext
            change (gradedObjectCategoryData (B := B)).total_comp f.1
                ((gradedObjectCategoryData (B := B)).total_id C) =
              (gradedObjectCategoryData (B := B)).total_comp
                ((gradedObjectCategoryData (B := B)).total_id A)
                ((homFrom (mapToFamily (familyToMap (homTo f))) :
                  directSumComponent ℤ
                    (fun n => GradedObjectHomogeneous A C n) 0) :
                  DirectSum ℤ (fun n => GradedObjectHomogeneous A C n))
            rw [(gradedObjectCategoryData (B := B)).total_comp_id,
              (gradedObjectCategoryData (B := B)).total_id_comp]
            calc
              (f : DirectSum ℤ (fun n => GradedObjectHomogeneous A C n)) =
                  (homFrom (homTo f) : DirectSum ℤ
                    (fun n => GradedObjectHomogeneous A C n)) :=
                congrArg Subtype.val (homFrom_homTo f).symm
              _ = (homFrom (mapToFamily (familyToMap (homTo f))) :
                  DirectSum ℤ (fun n => GradedObjectHomogeneous A C n)) := by
                rw [mapToFamily_familyToMap]
  let counitNatIso :
      G ⋙ F ≅ 𝟭 (CategoryTheory.GradedObject ℤ B) := by
    refine NatIso.ofComponents (fun A => counitIso A) (fun {X Y} f => ?_)
    simp [counitIso]
    dsimp [F, G]
    change familyToMap (homTo (homFrom (mapToFamily f))) ≫ 𝟙 Y =
      𝟙 X ≫ f
    rw [Category.comp_id, Category.id_comp, homTo_homFrom,
      familyToMap_mapToFamily]
  refine ⟨⟨F, G, unitNatIso, counitNatIso, ?_⟩⟩
  · intro X
    cases X with
    | up X =>
      cases X with
      | mk A =>
        change F.map (unitIso (DegreeZero.of
          (gradedObjectGradedCategory (B := B))
          (gradedObjectCategoryObject A))).hom ≫ (counitIso A).hom = 𝟙 A
        have hunit :
            (unitIso (DegreeZero.of (gradedObjectGradedCategory (B := B))
              (gradedObjectCategoryObject A))).hom =
              𝟙 (DegreeZero.of (gradedObjectGradedCategory (B := B))
                (gradedObjectCategoryObject A)) := by
          dsimp [unitIso]
          rfl
        have hmap :
            F.map (unitIso (DegreeZero.of (gradedObjectGradedCategory (B := B))
              (gradedObjectCategoryObject A))).hom = 𝟙 A := by
          rw [hunit]
          exact F.map_id _
        have hcount : (counitIso A).hom = 𝟙 A := by
          rfl
        rw [hmap, hcount]
        dsimp [F]
        exact Category.id_comp (𝟙 A)

noncomputable def gradedObject_degree_zero_equivalence :
    DegreeZero (gradedObjectGradedCategory (B := B)) ≌
      CategoryTheory.GradedObject ℤ B :=
  Classical.choice (gradedObject_degree_zero_recovers_graded_objects (B := B))

end Formalization.Books.Dga.Unit25
