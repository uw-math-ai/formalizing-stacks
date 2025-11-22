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

instance precoverage.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C]
  (S : Site C) : Precoverage C where
  coverings X := Precover.to_presieve X '' S.coverings X

def pretop_has_isos.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C]
  (S : Site C) : ∀ ⦃X Y : C⦄ (f : Y ⟶ X) [IsIso f],
    Presieve.singleton f ∈ Precoverage.coverings S.precoverage X := fun ⦃X Y⦄ f h_iso => by
  have h := S.iso f h_iso
  unfold Site.precoverage
  simp
  use {Over.mk f}
  constructor
  · exact h
  funext
  case h.right.h.h Y h =>
    simp
    constructor
    · intro h'
      cases h'
      simp
    intro h'
    cases h'
    rfl

def pretop_has_pullbacks.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C]
  (S : Site C) :
    ∀ ⦃X Y : C⦄ (f : Y ⟶ X) (Si), Si ∈ S.precoverage.coverings X
      → Presieve.pullbackArrows f Si ∈ S.precoverage.coverings Y := fun ⦃X Y⦄ f Si in_cov => by
  obtain ⟨x, in_coverings, h_eq⟩ := in_cov
  -- Set of all pullback overs that should be in coverings Y from the Site's perspective
  have h := S.pullback (Over.mk f) (Precover.of_presieve X Si) (by
    cases h_eq
    exact in_coverings
  )
  simp at h
  cases h_eq
  unfold Precover.to_presieve at *
  unfold Site.precoverage
  simp
  constructor
  constructor
  · exact h
  unfold Precover.to_presieve
  simp
  funext
  case refl.h.right.h.h Z g =>
    simp
    constructor
    · intro ⟨ov, in_x, ov_eq⟩
      cases ov_eq
      constructor
      · exact in_x
    intro ⟨A, j, h⟩
    change Over.mk (Over.mk j).hom ∈ x at h
    constructor
    constructor
    · exact h
    rfl

end Site

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
    ) in_cov (fun {Y} f in_pre => by
      simp
      have h := mk_cov 
      sorry
    )
    
    sorry

end Site
