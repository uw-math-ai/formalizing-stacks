import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.Tactic.ApplyFun
import Stacks.Site

open CategoryTheory
open CategoryTheory.Limits

/-
Cat forms a site, where adjunctions between functors satisfy the "iso" property.
Since Cat also has limits of every shape, it should also have pullbacks?
  Thereby satisfying the "pullback" property.
Furthermore, functors compose, so the trans property should also be fulfilled.
-/

instance instCategoryCat.{v, u} : Category.{max v u, (max v u) + 1} Cat.{v, u} := by
  have h := Cat.category.{v, u}
  unfold LargeCategory at h
  exact h

instance instPullbacksCat : @HasPullbacks.{0, 1} Cat.{0, 0} instCategoryCat.{0, 0} := by
  have h : HasLimitsOfShape WalkingCospan Cat :=
    @HasLimits.has_limits_of_shape.{0, 1} Cat.{0, 0} _ Cat.instHasLimits.{0} WalkingCospan _
  unfold HasPullbacks
  exact h

@[simp]
def coverings (X : Cat) : Set (Precover X) := { cov | ∀ ov ∈ cov, IsIso ov.hom }

@[simp]
def iso {X Y : Cat} (hom : Y ⟶ X) (h_is_iso : IsIso hom) : {Over.mk hom} ∈ coverings X := by
  unfold coverings
  simp
  exact h_is_iso

instance instSiteCat : @Site Cat _ (by sorry) where
  -- In the coverings if the functor is bijective
  coverings := coverings
  iso := iso
  trans {X} cov₀ is_covering h_mk_cov := fun ov h_ov => by
    simp at h_ov
    have ⟨f, ⟨f_in_cov₀, ⟨g, ⟨g_in_precov', h_ov_eq⟩⟩⟩⟩ := h_ov
    simp_all

    let precov'  := (h_mk_cov f f_in_cov₀).val
    let property : ∀ ov ∈ precov', IsIso ov.hom := (h_mk_cov f f_in_cov₀).property

    have f_iso : IsIso f.hom := is_covering f f_in_cov₀
    have g_iso : IsIso g.hom := property g g_in_precov'

    have h_g_in_precov' : g ∈ precov' := by
      change (h_mk_cov f f_in_cov₀).val g
      exact g_in_precov'

    have over_comp_in_coverings : {Over.mk (g.hom ≫ f.hom)} ∈ coverings X := by
      simp
      apply CategoryTheory.IsIso.comp_isIso

    rw [← h_ov_eq]
    rw [Over.mk_hom]

    unfold coverings at over_comp_in_coverings
    simp at over_comp_in_coverings

    exact over_comp_in_coverings


