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
    { Over.mk (g.hom ≫ f.hom) | (f ∈ U) (cov ∈ coverings f.left) (g ∈ cov) } ∈ coverings X
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
  have h_trans := S.trans precov in_cov (fun ov in_precov => by
    have ⟨x, in_cov, h_eq⟩ := mk_cov ov.hom (by rw [← precov_eq]; exact in_precov)
    simp at h_eq
    simp at in_cov
    use x
  )
  simp [Site.precoverage] at mk_cov
  simp [Site.precoverage]
  constructor
  constructor
  · exact h_trans
  funext
  case h.right.h.h Z g =>
    simp
    constructor
    intro ⟨ov, in_pre, ⟨ov_left, in_cov_left, ⟨g_ov, in_ov_left, g_eq⟩⟩⟩
    let ⟨Cov, in_cov_left', pre_eq⟩ := mk_cov ov.hom (by
      cases precov_eq
      simp [Precover.to_presieve]
      exact in_pre
    )
    let g_hom := g_ov.hom
    simp at in_cov_left'
    simp at pre_eq
    simp [Presieve.bind]
    -- ov.hom = x
    -- g_1 = Cov.hom
    -- Not sure what Y is referring to, it's completely unbound
    constructor
    cases g_eq
    exists g_ov.hom
    exists ov.hom
    constructor
    cases precov_eq
    simp [Precover.to_presieve]
    use in_pre
    rw [← pre_eq]
    simp [Precover.to_presieve]
    
    sorry

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
  trans {X} cov in_cov mk_cov' := by
    obtain ⟨pres, ⟨in_cov, cov_eq⟩⟩ := in_cov
    have h := pre.transitive pres (fun {Y} f h => by
      apply Precover.to_presieve
      have h := mk_cov' (Over.mk f) (by
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
