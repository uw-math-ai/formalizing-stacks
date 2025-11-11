import Mathlib

open CategoryTheory
open CategoryTheory.Limits

class Site'.{u, v} (C : Type v) [Category.{u, v} C] [HasPullbacks.{u, v} C] where
  coverings (X : C) : Set (Presieve X)
  iso {X Y : C} (f : Y ⟶ X) : IsIso f → Presieve.singleton f ∈ coverings X
  trans {X : C} (U : Presieve X)
    (hU : U ∈ coverings X)
    (R : ⦃Y : C⦄ → ⦃f : Y ⟶ X⦄ → U f → { y : Presieve Y // y ∈ coverings Y}) :
      Presieve.bind U (fun {Y : C} {_f : Y ⟶ X} h => (R h).val) ∈ coverings X
  pullback {X Y : C} (f : Y ⟶ X) (U : Presieve X) (hU : U ∈ coverings X) :
    Presieve.pullbackArrows f U ∈ coverings Y

namespace Site'

def of_pretopology.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C]
  (pre : Pretopology C) : Site' C where
  coverings := pre.coverings
  iso {X Y} f h_iso := pre.has_isos f
  trans {X} precov h_is_precov mk_left_cov := by
    apply Pretopology.transitive pre precov
    · exact h_is_precov
    simp
  pullback f U h_precov_is_cov := pre.pullbacks f U h_precov_is_cov

def to_pretopology.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C]
  (s : Site' C) : Pretopology C where
  coverings := s.coverings
  has_isos X Y f h_iso := @s.iso X Y f h_iso
  pullbacks X Y f cov is_cov := @s.pullback X Y f cov is_cov
  transitive X U R is_cov h := @s.trans X U is_cov
    (fun Y f in_cov => { val := @R Y f in_cov, property := @h Y f in_cov })

def toGrothendieck.{u, v} {C : Type v} [h_cat : Category.{u, v} C] [HasPullbacks.{u, v} C]
  (s : Site' C) : GrothendieckTopology.{u, v} C :=
  s.to_pretopology.toGrothendieck

theorem of_to_pretopology_eq.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C]
  (pre : Pretopology C) : to_pretopology (of_pretopology pre) = pre := rfl

end Site'
