import Mathlib
import Stacks.Site2Mathlib

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
    (g : Over f.left) (hg : g ∈ cov) } ∈ coverings X
  pullback {X : C} (f : Over X) (U : Precover X) (hU : U ∈ coverings X) :
    { Over.mk (pullback.snd g.hom f.hom) | g ∈ U } ∈ coverings f.left

namespace Precover

@[simp]
def to_presieve.{u, v} {C : Type v} [Category.{u, v} C] (X : C) (pre : Precover X) : Presieve X :=
  fun ⦃Y⦄ => { f : Y ⟶ X | Over.mk f ∈ pre }

@[simp]
def of_presieve.{u, v} {C : Type v} [Category.{u, v} C] (X : C) (pre : Presieve X) : Precover X :=
  (Over.mk ·.snd)  '' pre.uncurry

def equiv_presieve_precov.{u, v} {C : Type v} [Category.{u, v} C]
  (X : C) : Presieve X ≃ Precover X where
  toFun := of_presieve X
  invFun := to_presieve X
  left_inv P := by
    simp only [of_presieve]
    funext Y f
    simp only [to_presieve, Set.mem_image, Sigma.exists, eq_iff_iff]
    constructor
    · intro ⟨a, b, h, heq⟩
      cases heq
      · exact h
    intro h
    exact ⟨_, f, h, rfl⟩
  right_inv P := by
    funext f
    rw [eq_iff_iff]
    constructor
    · intro ⟨w, h, ov_eq⟩
      rw [← ov_eq]
      exact h
    intro h
    refine ⟨⟨f.left, f.hom⟩, h, rfl⟩

end Precover

namespace Site

instance precoverage.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C]
  (S : Site C) : Precoverage C where
  coverings X := Precover.to_presieve X '' S.coverings X

def pretop_has_isos.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C]
  (S : Site C) : ∀ ⦃X Y : C⦄ (f : Y ⟶ X) [IsIso f],
    Presieve.singleton f ∈ Precoverage.coverings S.precoverage X := fun ⦃X Y⦄ f h_iso => by
  refine ⟨{Over.mk f}, S.iso f h_iso, ?_⟩
  funext
  · rw [eq_iff_iff]
    constructor
    · intro h'
      cases h'
      simp
    intro h'
    cases h'
    rfl

def pretop_pullbacks.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C]
  (S : Site C) {X Y : C} (f : Y ⟶ X) (U : Presieve X) (hU : U ∈ S.precoverage.coverings X) :
  Presieve.pullbackArrows f U ∈ S.precoverage.coverings Y := by
  let ⟨pre, in_cov, heq⟩ := hU
  let h := S.pullback (Over.mk f) pre in_cov
  refine ⟨{x | ∃ g ∈ pre, Over.mk (pullback.snd g.hom (Over.mk f).hom) = x}, h, ?_⟩
  unfold Precover.to_presieve at heq
  unfold Precover.to_presieve
  rw [← heq]
  funext Z j
  simp only [Over.mk_left, Functor.id_obj, Functor.const_obj_obj,
    Over.mk_hom, Set.mem_setOf_eq, eq_iff_iff]
  constructor
  · intro ⟨ov, in_pre, ov_eq⟩
    cases ov_eq
    apply Presieve.pullbackArrows.mk
    exact in_pre
  intro ⟨A, b, c⟩
  refine ⟨Over.mk b, c, ?_⟩
  rfl

def to_site'.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks.{u, v} C] (S : Site C) : Site' C where
  coverings := precoverage S
  iso {X Y : C} := @pretop_has_isos _ _ _ S X Y
  pullback {X Y : C} (f : Y ⟶ X) := by
    
    sorry

end Site

