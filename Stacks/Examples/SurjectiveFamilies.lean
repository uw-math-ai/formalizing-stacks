import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Stacks.Site

open CategoryTheory
open CategoryTheory.Limits

abbrev JointlySurjective.{u} {Y : Type u} (U : Precover Y)
  := ∀ y : Y, ∃ f ∈ U, ∃ x : f.left, y = f.hom x

namespace JointlySurjective

def has_limit.{u} : ∀ (x : WalkingCospan ⥤ Type u), HasLimit x := fun F =>
  let hom_left : (F.obj .left) ⟶ (F.obj .one)   := F.map WalkingCospan.Hom.inl
  let hom_right : (F.obj .right) ⟶ (F.obj .one) := F.map WalkingCospan.Hom.inr

  let p_val_type := (F.obj .left) × (F.obj .right)
  let pt : Type u := { p : p_val_type // hom_left p.fst = hom_right p.snd }

  let pt_left : pt ⟶ F.obj .left := fun X => X.val.fst
  let pt_right : pt ⟶ F.obj .right := fun X => X.val.snd

  ⟨⟨{
    cone := {
      pt := pt
      π := {
        app span := match span with
          | .left => fun X => by
            simp at X
            exact X.val.fst
          | .right => fun X => by
            simp at X
            exact X.val.snd
          | .one => by
            simp
            exact pt_left ≫ hom_left
        naturality {X Y} f := by
          change WalkingCospan.Hom _ _ at f
          cases f
          rw [CategoryTheory.Limits.WidePullbackShape.hom_id]
          repeat simp only [Functor.const_obj_obj,
            Functor.const_obj_map, id_eq, Category.id_comp,
            CategoryTheory.Functor.map_id, Category.comp_id]
          case term j =>
            cases j
            rfl
            ext a
            simp only [types_comp_apply]
            rw [a.property]
      }
    }
  }⟩⟩

instance instHasPullbacks.{u} : HasPullbacks (Type u) where
  has_limit := fun F@{ obj, map, map_id, map_comp } => ⟨⟨
    let hom_left : (obj .left) ⟶ (obj .one)   := map WalkingCospan.Hom.inl
    let hom_right : (obj .right) ⟶ (obj .one) := map WalkingCospan.Hom.inr

    let pt : Type u :=
      { p : (obj .left) × (obj .right) // hom_left p.fst = hom_right p.snd }

    {
      cone := {
        pt := pt
        π := {
          app span X :=
            match span with
            | .left => by
              simp at X
              exact X.val.fst
            | .right => by
              sorry
            | .one => by
              simp only [Functor.const_obj_obj]
              sorry
        }
      }
    }
    sorry⟩⟩

def SurjectiveFamiliesSite.{u} : Site (Type u) := {
  coverings X := setOf JointlySurjective
  iso f hf y := by
    exists Over.mk f
    constructor
    · rfl
    · exists inv f y
      simp
      have p := (comp_apply (inv f) f y)
      simp at p
      exact p
  trans U U_jointly_surjective V y := by
    obtain ⟨ f, f_in_U, x, y_is_f_x ⟩ := U_jointly_surjective y
    obtain ⟨ g, g_in_V_f, z, x_is_g_z ⟩ := (V f f_in_U).property x
    exists (Over.mk (g.hom ≫ f.hom))
    apply And.intro
    · exists f
      exists f_in_U
      exists g
    · exists z
      simp
      rw [y_is_f_x, x_is_g_z]
  pullback f U U_jointly_surjective y := by
    obtain ⟨ g, g_in_U, x, f_y_is_g_x ⟩ := U_jointly_surjective (f.hom y)
    exists Over.mk pullback.snd g.hom f.hom
    apply And.intro
    · exists g
    · exists by
        exists (x, y)
        rw [f_y_is_g_x]
}

end JointlySurjective
