import Mathlib

open CategoryTheory
open CategoryTheory.Limits

-- A family or morphisms with destination dst.
abbrev Precover.{u, v} {C : Type v} [Category.{u, v} C] (X : C) := Set (Over X)

structure Site.{u, v} (C : Type v) [Category.{u, v} C] [HasPullbacks.{u, v} C] where
  coverings (X : C) : Set (Precover X)
  iso {X Y : C} (f : Y ⟶ X) : IsIso f → { Over.mk f } ∈ coverings X
  trans {X : C} (U : Precover X) (hU : U ∈ coverings X)
        (V : ∀ f ∈ U, ∃ cover, cover ∈ coverings f.left) :
    { Over.mk (g.hom ≫ f.hom) | (f : Over X) (hU: f ∈ U)
    (cov : Precover f.left) (hC : cov ∈ coverings f.left)
    (_cov_eq : V f hU = ⟨cov, hC⟩) (g ∈ cov) } ∈ coverings X
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
      → Presieve.pullbackArrows f Si ∈ S.precoverage.coverings Y :=
      fun ⦃X Y⦄ f Si ⟨x, in_coverings, h_eq⟩ => by
  -- Set of all pullback overs that should be in coverings Y from the Site's perspective
  have h := S.pullback (Over.mk f) (Precover.of_presieve X Si) (by
    cases h_eq
    exact in_coverings
  )
  cases h_eq
  constructor
  constructor
  · exact h
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

def pretop_transitive.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C] (S : Site C) :
  ∀ ⦃X : C⦄ (Si : Presieve X) (Ti : ∀ ⦃Y⦄ (f : Y ⟶ X), Si f → Presieve Y),
      Si ∈ S.precoverage.coverings X → (∀ ⦃Y⦄ (f) (H : Si f), Ti f H ∈ S.precoverage.coverings Y) →
      Si.bind Ti ∈ S.precoverage.coverings X :=
  fun ⦃X⦄ Si Ti in_cov mk_cov => by
  simp [Site.precoverage] at in_cov
  let ⟨pre, in_cov, eq_si⟩ := in_cov
  choose cov h_cov h_eq using fun (f : Over X) (hf : f ∈ pre) => mk_cov f.hom (by
    rw [← eq_si]
    exact hf
  )
  let pullback_cov_mem := S.trans pre in_cov (fun ov in_pre => ⟨cov ov in_pre, h_cov ov in_pre⟩)
  refine ⟨_, pullback_cov_mem, ?_⟩
  funext
  case h.h Z g =>
    ext
    constructor
    intro ⟨ov, in_pre, pre_comp, precomp_cov, ov_comp, pre_ov, ov_mem_pre, ov_comp_eq⟩
    constructor
    cases ov_comp_eq
    refine ⟨pre_ov.hom, ov.hom, by simp [← eq_si]; exact in_pre, ?_, rfl⟩
    
    sorry

end Site
