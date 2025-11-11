import Mathlib
import Stacks.Site2Mathlib
import Stacks.Sheaves

open AlgebraicGeometry
open TopologicalSpace
open CategoryTheory

namespace Sch

instance instSite.{u} : Site' Scheme.{u} :=
  Site'.of_pretopology Scheme.zariskiPretopology

instance instSubcanonical.{u} : GrothendieckTopology.Subcanonical instSite.{u}.toGrothendieck := by
  simp [instSite, Site'.toGrothendieck, ← Scheme.zariskiTopology_eq]
  exact Scheme.subcanonical_zariskiTopology

def sheaf.{u} (S : Scheme.{u}) : Sheaf (Site'.toGrothendieck instSite.{u}) (Type u) :=
  instSite.{u}.toGrothendieck.yoneda.obj S

end Sch
