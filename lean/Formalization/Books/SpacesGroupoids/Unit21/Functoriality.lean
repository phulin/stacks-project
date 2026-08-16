import Formalization.Books.SpacesGroupoids.Unit21.Core

/-!
# Groupoids in Algebraic Spaces, Chapter 21: functoriality of quotient stacks
-/

namespace Formalization.Books.SpacesGroupoids.Unit21

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

/-! ## Functoriality -/

/-- A morphism of groupoids induces a canonical map between their quotient
stack models. -/
noncomputable def quotient_stack_functorial
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {S B : C} (B_to_S : B ⟶ S)
    (J : GrothendieckTopology (Over S))
    {G H : GroupoidInAlgebraicSpaces C B}
    (f : GroupoidHom G H)
    (X : QuotientStack S J B_to_S G)
    (Y : QuotientStack S J B_to_S H) :
    QuotientStackMorphism X Y := by
  sorry

/-- The chosen representative of the canonical quotient-stack map. -/
noncomputable def quotientStackMap
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {S B : C} (B_to_S : B ⟶ S)
    (J : GrothendieckTopology (Over S))
    {G H : GroupoidInAlgebraicSpaces C B}
    (f : GroupoidHom G H)
    (X : QuotientStack S J B_to_S G)
    (Y : QuotientStack S J B_to_S H) :
    QuotientStackMorphism X Y :=
  quotient_stack_functorial B_to_S J f X Y

/-! ## The pullback groupoid attached to a groupoid morphism -/

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {S B : C} (B_to_S : B ⟶ S)
variable {G H : GroupoidInAlgebraicSpaces C B} (f : GroupoidHom G H)

/-- The object `U'' = U ×_{U',t'} R'`. -/
noncomputable def pullbackGroupoidObject : C :=
  pullback f.map_obj H.data.t

/-- The arrow object `R'' = R ×_{U',t'} R'`. -/
noncomputable def pullbackGroupoidArrow : C :=
  pullback (G.data.s ≫ f.map_obj) H.data.t

/-- The source map `(r,r') ↦ (s(r),r')`. -/
noncomputable def pullbackGroupoidSource :
    pullbackGroupoidArrow f ⟶ pullbackGroupoidObject f :=
  pullback.lift
    (pullback.fst (G.data.s ≫ f.map_obj) H.data.t ≫ G.data.s)
    (pullback.snd (G.data.s ≫ f.map_obj) H.data.t)
    (by sorry)

/-- The second component of the target and inverse formulas,
`(r,r') ↦ c'(f(r),r')`. -/
noncomputable def pullbackGroupoidComposedArrow :
    pullbackGroupoidArrow f ⟶ H.data.R :=
  pullback.lift
    (pullback.fst (G.data.s ≫ f.map_obj) H.data.t ≫ f.map_arr)
    (pullback.snd (G.data.s ≫ f.map_obj) H.data.t)
    (by sorry) ≫ H.data.c

/-- The target map `(r,r') ↦ (t(r),c'(f(r),r'))`. -/
noncomputable def pullbackGroupoidTarget :
    pullbackGroupoidArrow f ⟶ pullbackGroupoidObject f :=
  pullback.lift
    (pullback.fst (G.data.s ≫ f.map_obj) H.data.t ≫ G.data.t)
    (pullbackGroupoidComposedArrow f)
    (by sorry)

/-- The identity map `(u,r') ↦ (e(u),r')`. -/
noncomputable def pullbackGroupoidIdentity :
    pullbackGroupoidObject f ⟶ pullbackGroupoidArrow f :=
  pullback.lift
    (pullback.fst f.map_obj H.data.t ≫ G.data.e)
    (pullback.snd f.map_obj H.data.t)
    (by sorry)

/-- The inverse map `(r,r') ↦ (i(r),c'(f(r),r'))`. -/
noncomputable def pullbackGroupoidInverse :
    pullbackGroupoidArrow f ⟶ pullbackGroupoidArrow f :=
  pullback.lift
    (pullback.fst (G.data.s ≫ f.map_obj) H.data.t ≫ G.data.i)
    (pullbackGroupoidComposedArrow f)
    (by sorry)

/-- The auxiliary pair of arrows used to define the composition formula. -/
noncomputable def pullbackGroupoidCompositionPair :
    pullback (pullbackGroupoidSource f) (pullbackGroupoidTarget f) ⟶
      pullback G.data.s G.data.t :=
  pullback.lift
    (pullback.fst (pullbackGroupoidSource f) (pullbackGroupoidTarget f) ≫
      pullback.fst (G.data.s ≫ f.map_obj) H.data.t)
    (pullback.snd (pullbackGroupoidSource f) (pullbackGroupoidTarget f) ≫
      pullback.fst (G.data.s ≫ f.map_obj) H.data.t)
    (by sorry)

/-- The composition map `((r₁,r'₁),(r₂,r'₂)) ↦ (c(r₁,r₂),r'₂)`. -/
noncomputable def pullbackGroupoidComposition :
    pullback (pullbackGroupoidSource f) (pullbackGroupoidTarget f) ⟶
      pullbackGroupoidArrow f :=
  pullback.lift
    (pullbackGroupoidCompositionPair f ≫ G.data.c)
    (pullback.snd (pullbackGroupoidSource f) (pullbackGroupoidTarget f) ≫
      pullback.snd (G.data.s ≫ f.map_obj) H.data.t)
    (by sorry)

/-- The groupoid data defined by the five formulas in the source. -/
noncomputable def pullbackGroupoidData : GroupoidData C B where
  U := pullbackGroupoidObject f
  R := pullbackGroupoidArrow f
  U_to_B := pullback.fst f.map_obj H.data.t ≫ G.data.U_to_B
  R_to_B := pullback.fst (G.data.s ≫ f.map_obj) H.data.t ≫ G.data.R_to_B
  s := pullbackGroupoidSource f
  t := pullbackGroupoidTarget f
  s_over_B := by sorry
  t_over_B := by sorry
  c := pullbackGroupoidComposition f
  c_over_B := by sorry
  e := pullbackGroupoidIdentity f
  e_over_B := by sorry
  i := pullbackGroupoidInverse f
  i_over_B := by sorry

/-- The groupoid in algebraic spaces produced by the pullback construction. -/
noncomputable def pullbackGroupoid : GroupoidInAlgebraicSpaces C B where
  data := pullbackGroupoidData f
  axioms := by sorry

/-- The projection `g : (U'',R'') → (U,R)`. -/
noncomputable def pullbackGroupoidProjection :
    GroupoidHom (pullbackGroupoid f) G where
  map_obj := pullback.fst f.map_obj H.data.t
  map_arr := pullback.fst (G.data.s ≫ f.map_obj) H.data.t
  map_obj_over_B := by sorry
  map_arr_over_B := by sorry
  map_source := by sorry
  map_target := by sorry
  map_identity := by sorry
  map_inverse := by sorry
  map_composition := by sorry

/-- The structure map of the constructed groupoid to `U'`, given on both
objects and arrows by `(u,r') ↦ s'(r')`. -/
noncomputable def pullbackGroupoidTargetBaseMap :
    GroupoidBaseMap (pullbackGroupoid f) H.data.U H.data.U_to_B where
  object := pullback.snd f.map_obj H.data.t ≫ H.data.s
  arrow := pullback.snd (G.data.s ≫ f.map_obj) H.data.t ≫ H.data.s
  source := by sorry
  target := by sorry
  object_over_B := by sorry
  arrow_over_B := by sorry

/-! ## The 2-cartesian square -/

/-- The canonical square whose four sides are the maps described in the source:
the functorial maps on the top and left, the map to `U'` on the right, and the
atlas map on the bottom. -/
noncomputable def canonicalQuotientStackSquare
    {J : GrothendieckTopology (Over S)}
    (Q : QuotientStack S J B_to_S G)
    (Q' : QuotientStack S J B_to_S H)
    (Q'' : QuotientStack S J B_to_S (pullbackGroupoid f)) :
    QuotientStackCartesianSquare
      Q''.value Q.value
      (RepresentableStack (overS B_to_S H.data.U H.data.U_to_B))
      Q'.value where
  left := quotientStackMap B_to_S J (pullbackGroupoidProjection f) Q'' Q
  right := Q''.mapTo H.data.U_to_B (pullbackGroupoidTargetBaseMap f)
  top := quotientStackMap B_to_S J f Q Q'
  bottom := Q'.fromObject
  commutes := by sorry
  isTwoPullback := by sorry

/-- The quotient-stack square attached to `f` is 2-commutative and identifies
the quotient of the constructed pullback groupoid with the 2-fibre product. -/
theorem cartesian_square_of_quotient_stack
    {J : GrothendieckTopology (Over S)}
    (Q : QuotientStack S J B_to_S G)
    (Q' : QuotientStack S J B_to_S H)
    (Q'' : QuotientStack S J B_to_S (pullbackGroupoid f)) :
    Nonempty
      (QuotientStackCartesianSquare
        Q''.value Q.value
        (RepresentableStack (overS B_to_S H.data.U H.data.U_to_B))
        Q'.value) :=
  ⟨canonicalQuotientStackSquare B_to_S f Q Q' Q''⟩

end

end Formalization.Books.SpacesGroupoids.Unit21
