import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Types.Basic
import Stacks.Site

open CategoryTheory

abbrev JointlySurjective.{u} {Y : Type u} (U : Precover Y)
  := ∀ y : Y, ∃ f ∈ U, ∃ x : f.left, y = f.hom x

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
  pullback := sorry
}
