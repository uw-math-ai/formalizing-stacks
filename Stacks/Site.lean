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

namespace Precover

@[simp]
def to_presieve.{u, v} {C : Type v} [Category.{u, v} C] (X : C) (p : Precover X) : Presieve X :=
  fun ⦃Y : C⦄ => { f : Y ⟶ X | Over.mk f ∈ p }

@[simp]
def of_presieve.{u, v} {C : Type v} [Category.{u, v} C] (X : C) (P : Presieve X) : Precover X :=
  { ov | ov.hom ∈ @P ov.left }

def equiv_presieve_precov.{u, v} {C : Type v} [Category.{u, v} C]
  (X : C) : Presieve X ≃ Precover X where
  toFun := of_presieve X
  invFun := to_presieve X

end Precover

namespace Site

def toPretopology.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C]
  (S : Site C) : Pretopology C where
  -- A presieve is in the coverings if and only if it is in the pretopology
  coverings X := (Precover.to_presieve X) '' S.coverings X
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
      change Over.mk f = Over.mk f
      rfl
      intro h
      cases h
      simp
  pullbacks X {Y} f precov precov_is_cov := by
    simp_all
    obtain ⟨x, in_cov, precov_eq⟩ := precov_is_cov
    have h_in_cov_y := S.pullback (Over.mk f) x in_cov
    simp at h_in_cov_y
    use {x_1 | ∃ g ∈ x, Over.mk (pullback.snd g.hom f) = x_1}
    constructor
    exact h_in_cov_y
    cases precov_eq
    funext
    case h.right.refl.h.h Z g =>
      simp [Precover.to_presieve]
      constructor
      intro h
      change ∃ g' ∈ x, Over.mk (pullback.snd g'.hom f) = Over.mk g
      unfold Precover.to_presieve at h
      cases h
      case mp.mk Z g h =>
        exists Over.mk g
      case mpr =>
        intro h
        obtain ⟨w, ⟨w_in_x, pullback_ov_eq⟩⟩ := h
        cases pullback_ov_eq
        unfold Precover.to_presieve
        apply Presieve.pullbackArrows.mk
        exact w_in_x
  transitive {X} presieve presieve_Y is_cov mk_cov := by
    simp_all
    obtain ⟨pre, is_cov, pre_eq⟩ := is_cov
    exists pre
    constructor
    exact is_cov
    funext
    case right.h.h Y f =>
      ext
      cases pre_eq
      unfold Precover.to_presieve
      constructor
      intro h
      
      sorry

end Site
