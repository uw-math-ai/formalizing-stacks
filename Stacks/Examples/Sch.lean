import Mathlib
import Stacks.Site2Mathlib
import Stacks.Sheaves

open AlgebraicGeometry
open TopologicalSpace
open CategoryTheory

namespace Sch

instance instSite : Site' Scheme :=
  Site'.of_pretopology (Scheme.pretopology (fun {_X _Y} f => IsImmersion f))

theorem sheaf.{u} (S : Scheme.{u}) : IsSheaf.{u, u + 1} Scheme (uliftYoneda.obj.{u + 1} S) := by
  
  sorry

end Sch
