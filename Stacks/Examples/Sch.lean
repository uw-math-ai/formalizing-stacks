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

def presheaf.{u} (S : Scheme.{u}) : Presheaf Scheme.{u} (Type u)  :=
  (sheafToPresheaf.{u, u, u + 1, u + 1} instSite.{u}.toGrothendieck _).obj
    <| (instSite.{u}.toGrothendieck.yoneda.obj S)

theorem sheaf.{u} (S : Scheme.{u}) : IsSheaf instSite (presheaf S) := by
  intro U pre pre_is_cov fam fam_compatible
  -- The zariski topology is subcanonical
  have h := Sheaf.isSheaf_yoneda_obj S
  
  sorry

end Sch
