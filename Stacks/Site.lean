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
  -- Map every precover to a presieve
  coverings X := (fun precov => fun ⦃Y⦄ => fun hom => Over.mk hom ∈ precov) '' (S.coverings X)
  has_isos {X Y} f is_iso := by
    simp
    use {Over.mk f}
    constructor
    exact S.iso f is_iso
    simp
    funext
    case h.right.h.h x g =>
      simp
      constructor
      intro h
      cases h
      simp
      intro h
      cases h
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
    obtain ⟨precov, in_cov, h⟩ := is_cov
    use precov
    constructor
    exact in_cov
    intro Y hom in_bind
    obtain ⟨Y₁, g, f, ⟨f_mem_pre, ⟨x_mem, h_eq⟩⟩⟩ := in_bind
    have comp_mk := S.trans precov in_cov
      (fun ov in_precov => { val := { Over.mk (CategoryStruct.id ov.left) }, property := (by
        apply S.iso
        apply IsIso.id)
      })
    have ⟨precov', in_cov_Y, in_precov'⟩ := mk_cov f f_mem_pre
    have hg_in_sieve := h Y₁ f f_mem_pre
    rw [← h_eq]
    simp at comp_mk
    have h : presieve (g ≫ f) := by
      cases h_eq
      
      sorry
    sorry

end Site

instance equivOfPretopology.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C] : Site C ≃ Pretopology C where
  toFun S := by
    sorry
