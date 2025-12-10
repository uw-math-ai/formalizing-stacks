import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Stacks.Site
import Stacks.Examples.SurjectiveFamilies.Surj
import Stacks.Examples.SurjectiveFamilies.HasPullbacks

open CategoryTheory
open CategoryTheory.Limits

namespace JointlySurjective

def SurjectiveFamiliesSite.{u} : Site (Type u) := {
  coverings X := setOf JointlySurjective
  iso {X Y : Type u} (f : Y ⟶ X) (hf : IsIso f) x :=
    ⟨Over.mk f, ⟨by simp, inv f x, by
      change x = (inv f ≫ f) x
      rw [(CategoryTheory.inv_comp_eq_id f).mpr]
      repeat rfl
    ⟩⟩
  trans {X} U U_jointly_surjective V x := by
    simp only [Functor.const_obj_obj,
      Functor.id_obj, exists_prop, Set.mem_setOf_eq, ↓existsAndEq, and_true,
      Over.mk_left, Over.mk_hom, types_comp_apply]
    let ⟨f, f_in_U, x, y_is_f_x⟩ := U_jointly_surjective x
    let ⟨cov, is_joint_surj⟩ := V f f_in_U
    let ⟨g, in_cov, g_left, heq⟩ := is_joint_surj x
    exact ⟨f, cov, g, ⟨f_in_U, is_joint_surj, in_cov⟩, ⟨g_left, by simp_all⟩⟩
  pullback {X} f U U_jointly_surjective y := by
    obtain ⟨g, g_in_U, x, f_y_is_g_x⟩ := U_jointly_surjective (f.hom y)
    simp at U_jointly_surjective
    change U_jointly_surjective g at g_in_U

    have h := g_in_U
    simp only [Functor.id_obj, Functor.const_obj_obj, Set.mem_setOf_eq,
      exists_exists_and_eq_and, Over.mk_left, Over.mk_hom]
    refine ⟨g, g_in_U, ?_⟩

    let left : pullback g.hom f.hom ⟶ g.left := pullback.fst g.hom f.hom
    let right : pullback g.hom f.hom ⟶ f.left := pullback.snd g.hom f.hom

    let hom_y_to_hom_x : f.left ⟶ g.left := fun e => x
    let hom_x_to_hom_y : g.left ⟶ f.left := fun e => y

    let lifted : pullback g.hom f.hom := @pullback.lift _ _ _ _ _ _ g.hom f.hom _ (hom_y_to_hom_x) (CategoryStruct.id _) (by unfold hom_y_to_hom_x; simp; sorry)
    sorry
}

end JointlySurjective
