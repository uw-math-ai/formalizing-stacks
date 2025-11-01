import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Category.Cat.Limit

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor

/-
Cat forms a site, where bijections between morphisms. Specifically the
  functors given by the morphisms are fully faithful.
  satisfy the "iso" property.
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
