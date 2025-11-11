import Mathlib
import Stacks.Site2Mathlib

open TopologicalSpace
open CategoryTheory

namespace Zar

instance instSite.{u} {C : Type u} [TopologicalSpace C] :
  Site' (Opens C) := Site'.of_pretopology (Opens.pretopology C)

end Zar
