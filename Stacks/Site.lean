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
  let ⟨precov, in_cov, precov_eq⟩ := in_cov
  let h_trans := S.trans precov in_cov (fun ov in_precov => by
    let ⟨x, in_cov, h_eq⟩ := mk_cov ov.hom (by rw [← precov_eq]; exact in_precov)
    simp at h_eq
    simp at in_cov
    use x
  )
  simp [Site.precoverage]
  simp at h_trans
  constructor
  constructor
  · exact h_trans
  funext
  case h.right.h.h Z g =>
    simp_all
    constructor
    intro h
    cases precov_eq
    let ⟨ov, in_precov, precov_comp, is_cov, ⟨ov_precomp, ov_precomp_in_precomp, ov_eq⟩⟩ := h
    simp [Presieve.bind]
    constructor
    let ov_precomp_hom := ov_precomp.hom
    cases ov_eq
    use ov_precomp.hom
    use ov.hom
    constructor
    exists in_precov
    let h' := mk_cov ov.hom (by assumption)
    simp at h'
    simp [Site.precoverage] at *
    cases ov_precomp
    simp_all
    obtain ⟨w, w_mem, h_eq⟩ := h'
    rw [← h_eq]
    simp [Precover.to_presieve]
    change Over.mk _ ∈ w
    simp_all
    change Over.mk _ ∈ precov_comp at ov_precomp_in_precomp
    apply Set.mem_of_mem_of_subset
    exact ov_precomp_in_precomp
    
    sorry

end Site
