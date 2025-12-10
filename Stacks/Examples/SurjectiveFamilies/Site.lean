import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Stacks.Site
import Stacks.Examples.SurjectiveFamilies.Surj
import Stacks.Examples.SurjectiveFamilies.HasPullbacks

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.limit

namespace JointlySurjective

def coverings.{u} (X : Type u) : Set (Precover X) := setOf JointlySurjective

def iso.{u} {X Y : Type u} (f : Y ⟶ X) (hF : IsIso f) (x : X) :
  ∃ (f_1 : Over X), f_1 ∈ ({Over.mk f} : Set (Over X)) ∧ ∃ x_1, x = f_1.hom x_1 :=
  ⟨Over.mk f, ⟨Set.mem_singleton _, inv f x, by
      change x = (inv f ≫ f) x
      rw [(CategoryTheory.inv_comp_eq_id f).mpr]
      repeat rfl
    ⟩⟩

def trans.{u} ⦃X : Type u⦄ (U : Precover X)
  (U_jointly_surjective : U ∈ coverings X)
  (V : ∀ f ∈ U, ∃ cover, cover ∈ coverings f.left) (x : X) :
  ∃ f cov g, (f ∈ U ∧ cov ∈ coverings f.left ∧ g ∈ cov) ∧ ∃ x_1, x = f.hom (g.hom x_1) := by
    let ⟨f, f_in_U, x, y_is_f_x⟩ := U_jointly_surjective x
    let ⟨cov, is_joint_surj⟩ := V f f_in_U
    let ⟨g, in_cov, g_left, heq⟩ := is_joint_surj x
    exact ⟨f, cov, g, ⟨f_in_U, is_joint_surj, in_cov⟩, ⟨g_left, by rw [← heq]; exact y_is_f_x⟩⟩

def SurjectiveFamiliesSite.{u} : Site (Type u) := {
  coverings := coverings
  iso := iso
  trans {X} U U_jointly V x := by
    simp only [Functor.const_obj_obj, Functor.id_obj, exists_prop,
      Set.mem_setOf_eq, ↓existsAndEq, and_true, Over.mk_left, Over.mk_hom, types_comp_apply]
    exact trans U U_jointly V x
  pullback {X} f U U_jointly_surjective y := by
    obtain ⟨g, g_in_U, x, f_y_is_g_x⟩ := U_jointly_surjective (f.hom y)
    simp only [Functor.id_obj, Functor.const_obj_obj, Set.mem_setOf_eq,
      exists_exists_and_eq_and, Over.mk_left, Over.mk_hom]
    refine ⟨g, g_in_U, ?_⟩

    let left : pullback g.hom f.hom ⟶ g.left := pullback.fst g.hom f.hom
    let right : pullback g.hom f.hom ⟶ f.left := pullback.snd g.hom f.hom

    let pt := (pullback.cone g.hom f.hom).pt

    let my_F_obj : WalkingCospan → Type u
      | .left => g.left
      | .right => f.left
      | .none => g.left × f.left

    let my_F_map {X Y : WalkingCospan} (hom : X ⟶ Y) : (my_F_obj X ⟶ my_F_obj Y) :=
      match X, Y with
        | .left, .left
        | .right, .right =>
          CategoryStruct.id _
        | .right, none => fun e => ⟨x, e⟩
        | .left, none => fun e => ⟨e, y⟩
        | none, none => CategoryStruct.id _

    have my_F_map_comp {X Y Z : WalkingCospan} (f : X ⟶ Y) (g : Y ⟶ Z) :
      my_F_map (f ≫ g) = my_F_map f ≫ my_F_map g := by
      unfold my_F_map at *
      change WalkingCospan.Hom _ _ at f
      change WalkingCospan.Hom _ _ at g
      cases f
      cases g
      · simp only [WidePullbackShape.hom_id, Category.comp_id]
        cases X
        · simp only [Category.comp_id]
        case id.id.some val =>
          cases val
          repeat simp
      · simp only [WidePullbackShape.hom_id, Category.id_comp]
        case id.term j =>
          cases j
          repeat simp
      case term j =>
        cases g
        simp only [WidePullbackShape.hom_id, Category.comp_id]

    let my_F : WalkingCospan ⥤ Type u := {
      obj := my_F_obj
      map := my_F_map
      map_comp := my_F_map_comp
    }

    let cone := limit.cone my_F

    let h := @pullback.lift _ _ _ _ _ _ g.hom f.hom _ (cone.π.app .left) (cone.π.app .right) (by
      have nat_left := cone.π.naturality (CategoryStruct.id .left)
      have nat_right := cone.π.naturality (CategoryStruct.id .right)

      change _ = cone.π.app WalkingCospan.left ≫ my_F_map (𝟙 WalkingCospan.left) at nat_left
      change _ = cone.π.app WalkingCospan.right ≫ my_F_map (𝟙 WalkingCospan.right) at nat_right

      unfold my_F_map at nat_left
      unfold my_F_map at nat_right

      simp at nat_left
      simp at nat_right

      rw [nat_left, nat_right]

      unfold my_F_map
      simp only [Functor.const_obj_obj, Functor.id_obj, Category.assoc]
      unfold my_F_obj
      simp only
      conv =>
        left
        right
        rw [Category.id_comp]
        rfl
      conv =>
        right
        right
        rw [Category.id_comp]
        rfl
      ext a
      change (cone.π.app WalkingCospan.left ≫ g.hom) a = (cone.π.app WalkingCospan.right ≫ f.hom) a
      simp?
      let o := cone.π.app WalkingCospan.left a
      unfold my_F at o
      unfold my_F_obj at o
      simp at o
      
      sorry
    )

    sorry
}

end JointlySurjective
