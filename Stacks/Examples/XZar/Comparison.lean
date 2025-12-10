import Stacks.Site
import Stacks.SiteLeo

open CategoryTheory
open CategoryTheory.Limits

universe u v

variable {C : Type v} [Category.{u, v} C] (X : C)

--constructs a precover (via sets) from a precover (via indexing types)
def Precover_of_Precover₂ (U : Precover₂ X) : Precover X := fun f =>
  ∃ i : U.I, f = Over.mk (U.hom i)

--constructs a site (via sets) from a site (via indexing types)
def Site_of_Site₂ [HasPullbacks.{u, v} C] (S : Site₂ C) : Site C where
  coverings X := (Precover_of_Precover₂ X)'' (S.coverings X)
  iso f hf := by
    use SingletonPrecover f
    constructor
    · apply S.iso hf
    · ext
      constructor
      · intro hx
        simp
        unfold Precover_of_Precover₂ at hx
        cases hx
        assumption
      · intro hx
        use ⟨PUnit.unit⟩
        congr
  trans := sorry
  pullback := sorry
