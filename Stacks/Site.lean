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

def of_pretopology.{u, v} {C  :Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C] (pre : Pretopology C) : Site C where
  coverings X := (Precover.of_presieve X) '' pre.coverings X
  iso {X Y} f is_iso := by
    simp
    have h := pre.has_isos f
    use Presieve.singleton f
    constructor
    exact h
    ext
    constructor
    intro h
    simp at h
    cases h
    simp
    rfl
    intro h
    cases h
    simp
    change Presieve.singleton f f
    simp
  trans {X} cov in_cov mk_cov := by
    obtain ⟨pres, ⟨in_cov, cov_eq⟩⟩ := in_cov
    have h := pre.transitive pres (fun {Y} f h => by
      apply Precover.to_presieve
      have h := mk_cov (Over.mk f) (by
        rw [← cov_eq]
        unfold Precover.of_presieve
        exact h
      )
      use h.val
    )
    
    simp
    
    have ⟨precov, ⟨precov_is_cov, h_mem⟩⟩ := in_cov
    exists precov
    constructor
    exact precov_is_cov
    rw [h_mem]
    ext
    constructor
    intro h
    cases h_mem
    simp at h
    
    sorry

end Site
