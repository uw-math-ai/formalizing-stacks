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

def pullback.{u} {X : Type u} (f : Over X) (U : Precover X)
  (U_jointly_surjective : U ∈ coverings X) (y : f.left) :
  ∃ f_1 ∈ {x | ∃ g ∈ U, Over.mk (pullback.snd g.hom f.hom) = x}, ∃ x, y = f_1.hom x := by
  obtain ⟨g, g_in_U, x, f_y_is_g_x⟩ := U_jointly_surjective (f.hom y)
  use Over.mk <| pullback.snd g.hom f.hom
  simp only [Functor.id_obj, Functor.const_obj_obj, Set.mem_setOf_eq, Over.mk_left, Over.mk_hom]
  let mk_pb : X ⟶ Limits.pullback g.hom f.hom := pullback.lift (Function.const _ x)
    (Function.const _ y) (by
      ext
      exact f_y_is_g_x.symm
    )
  constructor
  · use g
  use mk_pb (f.hom y)
  simp [mk_pb]

instance instSite.{u} : Site (Type u) where
  coverings := coverings
  iso := iso
  trans {X} U U_jointly V x := by
    simp only [Functor.const_obj_obj, Functor.id_obj, exists_prop,
      Set.mem_setOf_eq, ↓existsAndEq, and_true, Over.mk_left, Over.mk_hom, types_comp_apply]
    exact trans U U_jointly V x
  pullback := pullback

end JointlySurjective
