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

def coverings.{u} (X : Type u) : Set (Precover X) := setOf JointlySurjective

def iso.{u} {X Y : Type u} (f : Y ⟶ X) (hF : IsIso f) (x : X) :
  ∃ (f_1 : Over X), f_1 ∈ ({Over.mk f} : Set (Over X)) ∧ ∃ x_1, x = f_1.hom x_1 :=
  ⟨Over.mk f, ⟨by simp, inv f x, by
      change x = (inv f ≫ f) x
      rw [(CategoryTheory.inv_comp_eq_id f).mpr]
      repeat rfl
    ⟩⟩

def trans.{u} {X : Type u} (U : Precover X)
  (U_jointly_surjective : U ∈ coverings X)
  (V : ∀ f ∈ U, ∃ cover, cover ∈ coverings f.left) (x : X) :
  ∃ f cov g, (f ∈ U ∧ cov ∈ coverings f.left ∧ g ∈ cov) ∧ ∃ x_1, x = f.hom (g.hom x_1) := by
    simp only [Functor.id_obj]
    let ⟨f, f_in_U, x, y_is_f_x⟩ := U_jointly_surjective x
    let ⟨cov, is_joint_surj⟩ := V f f_in_U
    let ⟨g, in_cov, g_left, heq⟩ := is_joint_surj x
    exact ⟨f, cov, g, ⟨f_in_U, is_joint_surj, in_cov⟩, ⟨g_left, by rw[← heq]; exact y_is_f_x⟩⟩

def SurjectiveFamiliesSite.{u} : Site (Type u) := {
  coverings := coverings
  iso := iso
  trans := trans
  pullback {X} f U U_jointly_surjective y := by
    obtain ⟨g, g_in_U, x, f_y_is_g_x⟩ := U_jointly_surjective (f.hom y)
    simp only [Functor.id_obj, Functor.const_obj_obj, Set.mem_setOf_eq,
      exists_exists_and_eq_and, Over.mk_left, Over.mk_hom]
    refine ⟨g, g_in_U, ?_⟩

    let left : pullback g.hom f.hom ⟶ g.left := pullback.fst g.hom f.hom
    let right : pullback g.hom f.hom ⟶ f.left := pullback.snd g.hom f.hom

    let pt := (pullback.cone g.hom f.hom).pt

    let my_F : WalkingCospan ⥤ Type u := {
      obj span := match span with
        | .left => g.left
        | .right => f.left
        | .none => g.left × f.left
      map hom := by
        split
        split
        exact CategoryStruct.id _
        contradiction
        exact fun e => ⟨e, (by assumption)⟩
        split
        contradiction
        exact CategoryStruct.id _
        exact fun e => ⟨(by assumption), e⟩
        split
        repeat contradiction
        exact CategoryStruct.id _
    }

    let h := has_limit my_F

    let lifted := pullback.lift 
    sorry
}

end JointlySurjective
