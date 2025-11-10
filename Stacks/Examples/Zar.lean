import Mathlib
import Stacks.Site2Mathlib
import Stacks.Site

open TopologicalSpace
open CategoryTheory

namespace Zar

def coverings.{u} {C : Type u} [TopologicalSpace C] (X : Opens C) : Set (Presieve X) :=
  (Opens.pretopology C).coverings X

def iso.{u} {C : Type u} [TopologicalSpace C] {X Y : Opens C}
  (f : Y ⟶ X) (h_iso : IsIso f) : Presieve.singleton f ∈ coverings X :=
    Pretopology.has_isos (Opens.pretopology C) f

instance instSite.{u} {C : Type u} [TopologicalSpace C] :
  Site' (Opens C) where
    coverings := coverings
    iso := iso
    trans {X} precov h_is_precov mk_left_cov := by
      apply Pretopology.transitive (Opens.pretopology C) precov
      · exact h_is_precov
      simp
    pullback f U h_precov_is_cov :=  Pretopology.pullbacks (Opens.pretopology C) f U h_precov_is_cov

end Zar
