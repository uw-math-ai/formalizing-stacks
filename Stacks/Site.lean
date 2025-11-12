import Mathlib

open CategoryTheory
open CategoryTheory.Limits

-- A family or morphisms with destination dst.
abbrev Precover.{u, v} {C : Type v} [Category.{u, v} C] (X : C) := Set (Over X)

structure Site.{u, v} (C : Type v) [Category.{u, v} C] [HasPullbacks.{u, v} C] where
  coverings (X : C) : Set (Precover X)
  iso {X Y : C} (f : Y ⟶ X) : IsIso f → { Over.mk f } ∈ coverings X
  trans {X : C} (U : Precover X) (hU : U ∈ coverings X)
        (V : ∀ f ∈ U, { cover // cover ∈ coverings f.left }) :
    { Over.mk (g.hom ≫ f.hom) | (f : Over X) (hf : f ∈ U) (g ∈ (V f hf).val) } ∈ coverings X
  pullback {X : C} (f : Over X) (U : Precover X) (hU : U ∈ coverings X) :
    { Over.mk (pullback.snd g.hom f.hom) | g ∈ U } ∈ coverings f.left

namespace Site

def toPretopology.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C]
  (S : Site C) : Pretopology C where
  coverings X := ⋃ cov ∈ S.coverings X, (fun ov => Presieve.singleton ov.hom) '' cov
  has_isos {X Y} f is_iso := by
    simp
    exact ⟨{Over.mk f}, S.iso f is_iso, by simp⟩
  pullbacks X {Y} f precov precov_is_cov := by
    simp_all
    obtain ⟨i, ⟨is_cov, ⟨ov, in_cov, h_ov_eq⟩⟩⟩ := precov_is_cov
    have h_pullbacks := S.pullback (Over.mk f) i is_cov
    use {x | ∃ g ∈ i, Over.mk (pullback.snd g.hom f) = x}
    constructor
    case h.left =>
      exact h_pullbacks
    simp
    use ov
    constructor
    case h.left =>
      exact in_cov
    rw [← CategoryTheory.Presieve.pullback_singleton, ← h_ov_eq]
  transitive {X} presieve presieve_Y is_cov mk_cov := by
    simp_all
    obtain ⟨i, is_cov, ov, ⟨ov_i, ov_eq⟩⟩ := is_cov
    have ⟨precov, is_cov, ov', ov_in_precov', ov_eq'⟩ := mk_cov ov.hom (by rw [← ov_eq]; simp)
    use i
    constructor
    assumption
    use ov
    constructor
    exact ov_i
    unfold Presieve.bind
    funext
    simp
    constructor
    intro h
    constructor
    constructor
    use ov.hom
    constructor
    
    
    sorry

end Site

instance equivOfPretopology.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C] : Site C ≃ Pretopology C where
  toFun S := by
    sorry
