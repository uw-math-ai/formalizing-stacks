import Mathlib
import Stacks.Site2Mathlib
import Stacks.Sheaves

open AlgebraicGeometry
open TopologicalSpace
open CategoryTheory

namespace Sch

instance instSite : Site' Scheme :=
  Site'.of_pretopology Scheme.zariskiPretopology

instance instSubcanonical : GrothendieckTopology.Subcanonical instSite.toGrothendieck := by
  unfold instSite
  unfold Site'.toGrothendieck
  simp
  rw [← Scheme.zariskiTopology_eq]
  exact Scheme.subcanonical_zariskiTopology

theorem sheaf.{u} : IsSheaf.{u, u + 1} Scheme (instSite.toGrothendieck.yoneda) := by
  intro U pre pre_is_cov fam fam_compatible
  -- The zariski topology is subcanonical
  have h := Sheaf.isSheaf_yoneda_obj S
  
  sorry

end Sch
