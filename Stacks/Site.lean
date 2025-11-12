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
  coverings X := { presieve |
    ∃ precov ∈ S.coverings X,
      ∀ (Y : C) (hom : Y ⟶ X) (in_presieve : hom ∈ @presieve Y),
        Over.mk hom ∈ precov }
  has_isos {X Y} f is_iso := by
    use {Over.mk f}
    constructor
    exact S.iso f is_iso
    intro Y' g in_presieve
    change Presieve.singleton f g at in_presieve
    cases in_presieve
    rfl
  pullbacks X {Y} f precov precov_is_cov := by
    simp
    simp at precov_is_cov
    have ⟨precov₁, ⟨precov₁_is_cov, all_ov_in_precov⟩⟩ := precov_is_cov
    have h_pullback := S.pullback (Over.mk f) precov₁ precov₁_is_cov
    simp at h_pullback
    use {x | ∃ g ∈ precov₁, Over.mk (pullback.snd g.hom f) = x}
    constructor
    exact h_pullback
    intro Y₁ hom in_pb_arrows
    cases in_pb_arrows
    case h.right.mk Z j precov_Z =>
      simp
      have h := all_ov_in_precov Z j precov_Z
      use Over.mk j
      constructor
      exact h
      rfl
  transitive {X} presieve presieve_Y is_cov mk_cov := by
    simp_all
    obtain ⟨i, is_cov, ov, ⟨ov_i, ov_eq⟩⟩ := is_cov
    have h := S.trans i (by assumption) (fun ov' in_cov => by
      have h := mk_cov ov'.hom in_cov
      
      sorry
    )
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
