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
  -- There should be an easier way to do this, but we can't extract a hom easily from over
  -- with the right type
  coverings X := (fun precov => fun ⦃Y⦄ => fun hom => Over.mk hom ∈ precov) '' (S.coverings X)
  has_isos {X Y} f is_iso := by
    use {Over.mk f}
    constructor
    exact S.iso f is_iso
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
    simp_all
    obtain ⟨x, in_cov, precov_eq⟩ := precov_is_cov
    have h_in_cov_y := S.pullback (Over.mk f) x in_cov
    simp at h_in_cov_y
    use {x_1 | ∃ g ∈ x, Over.mk (pullback.snd g.hom f) = x_1}
    simp [h_in_cov_y]
    funext
    case h.h.h Z g =>
      simp
      constructor
      intro h
      obtain ⟨g', in_precov, ov_eq⟩ := h
      cases ov_eq
      apply Presieve.pullbackArrows.mk
      rw [← precov_eq]
      simp
      change g' ∈ x
      exact in_precov
      intro h
      cases h
      cases precov_eq
      case mpr.mk.refl Z h hRh =>
        exists Over.mk h
  transitive {X} presieve presieve_Y is_cov mk_cov := by
    simp_all
    obtain ⟨cov, is_cov, h_pre_eq⟩ := is_cov
    let h_trans := S.trans cov is_cov (fun ov in_cov => by
      let h : ∃ cover : Precover ov.left, cover ∈ S.coverings ov.left := by
        have h := mk_cov ov.hom (by
          rw[← h_pre_eq]
          simp
          change ov ∈ cov
          exact in_cov
        )
        obtain ⟨x, ⟨mem_coverings, h⟩⟩ := h
        simp at mem_coverings
        use x
      let h' := Classical.choose h
      exists h'
      exact Classical.choose_spec h
    )
    simp at h_trans
    unfold Presieve.bind
    simp
    exists cov
    constructor
    exact is_cov
    simp_all
    funext
    case right.h.h Z g =>
      simp [← h_pre_eq]
      constructor
      intro h
      let h' : presieve g := by
        rw [← h_pre_eq]
        simp
        exact h
      have h_cov_g := mk_cov g h'
      constructor
      constructor
      use g
      constructor
      use h
      
      sorry

end Site

instance equivOfPretopology.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C] : Site C ≃ Pretopology C where
  toFun S := by
    sorry
