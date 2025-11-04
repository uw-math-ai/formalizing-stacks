import Mathlib

open CategoryTheory
open CategoryTheory.Limits

structure Site.{u, v} (C : Type v) [Category.{u, v} C] [HasPullbacks.{u, v} C] where
  coverings (X : C) : Set (Presieve X)
  iso {X Y : C} (f : Y ⟶ X) : IsIso f → Presieve.singleton f ∈ coverings X
  trans {X : C} (U : Presieve X)
    (hU : U ∈ coverings X)
    (R : ⦃Y : C⦄ → ⦃f : Y ⟶ X⦄ → U f → Presieve Y) : Presieve.bind U R ∈ coverings X
  pullback {X Y : C} (f : Y ⟶ X) (U : Presieve X) (hU : coverings X U) :
    Presieve.pullbackArrows f U ∈ coverings Y
