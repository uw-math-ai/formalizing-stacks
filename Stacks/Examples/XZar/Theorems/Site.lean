import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.Topology.Defs.Basic
import Mathlib.Tactic.ApplyFun
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Defs
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Stacks.Site
import Stacks.Examples.XZar.XZarCat
import Stacks.Examples.XZar.Theorems.Pullbacks

open CategoryTheory
open CategoryTheory (Category)
open CategoryTheory (asIso)
open CategoryTheory (Iso)
open CategoryTheory (IsIso)
open CategoryTheory (Precoverage)
open CategoryTheory.Limits

namespace XZar

@[simp]
def iso.{u} {C : Type u} {Cat : XZarCat.{u}} {X Y : @Obj.{u} C Cat}
  (hom : Y ⟶ X) (h_is_iso : IsIso hom) :
    {Over.mk hom} ∈ {cover : Precover X | ⋃ ov ∈ cover, {left | left = ov.left} = {X}} := by
      match h_is_iso, hom with
      | ⟨inv, ⟨inv_left, inv_right⟩⟩, .up (.up h_in) =>
        have h_subst : X.x ⊆ Y.x := inv.down.down
        have h_subst_hom : Hom X Y := h_subst
        have h_eq : X.x = Y.x := subset_antisymm (by assumption) (by assumption)
        simp
        ext
        simp_all

@[simp]
def coverings.{u} {C : Type u} {Cat : XZarCat.{u}} (X : @Obj.{u} C Cat) :
  Set (Precover X) := { cover | (⋃ ov ∈ cover, { left | left = ov.left }) = ({X} : Set Obj) }

@[simp]
def trans.{u} {C : Type u} {Cat : XZarCat.{u}} {X : @Obj.{u} C Cat}
  (precov : Precover X) (h_precov : precov ∈ coverings X)
  (h_in_cov : (f : Over X) → f ∈ precov → { cover // cover ∈ coverings f.left }) :
  {x |
    ∃ f, ∃ (hf : f ∈ precov), ∃ g ∈ (h_in_cov f hf).val,
      Over.mk (g.hom ≫ f.hom) = x} ∈ coverings X := by
  simp_all
  ext
  constructor
  case h.mp =>
    simp
    intro
      ov_x
      ov_y
      h_y_ov_precov
      ov_mid
      h_ov_mid_precover
      ov_comp
      h_ov_x_left_eq
    rw [h_ov_x_left_eq]
    rw [← ov_comp]
    let precov_containing_ov_mid : Precover ov_y.left := (h_in_cov ov_y h_y_ov_precov).val
    let property : ⋃ ov ∈ precov_containing_ov_mid, {ov.left} = {ov_y.left} :=
      (h_in_cov ov_y h_y_ov_precov).property
    apply_fun ({ b : Obj | b = ·})
    case _ =>
      simp
      have h : ov_mid.left ∈ ({ov_y.left} : Set Obj) := by
        rw [← property]
        simp
        use ov_mid
      have h_left : ov_y.left ∈ ({X}: Set Obj) := by
        rw [← h_precov]
        simp
        use ov_y
      rw [h]
      exact h_left
    case inj =>
      simp [Function.Injective]
  case h.mpr Y =>
    -- X = Y definitionally.
    -- The precov may be empty. That is, I = ∅.

    let h_precov₀ := h_precov

    intro h_hom_Y_X

    have h_X_in_precov : X ∈ ⋃ ov ∈ precov, {ov.left} := by
      simp_all

    have ⟨witness, dom, ⟨left, h_X_in_dom⟩⟩ := Set.mem_iUnion.mp h_X_in_precov
    simp at left
    have ⟨witness_in_precov, witness_is_dom⟩ := left

    rw [← witness_is_dom] at h_X_in_dom
    simp at h_X_in_dom

    have h_Y_X_def_eq : Y = X := Set.eq_of_mem_singleton h_hom_Y_X
    have h_hom_Y_X    : Y ⟶ X := by
      apply ULift.up
      apply PLift.up
      unfold Hom
      rw [h_Y_X_def_eq]
    have h_hom_X_Y    : X ⟶ Y := by
      apply ULift.up
      apply PLift.up
      unfold Hom
      rw [h_Y_X_def_eq]

    have iso  := Iso.mk h_hom_X_Y h_hom_Y_X
    let comp_over : Over X := Over.mk (iso.hom ≫ iso.inv)

    let covering : Set (Over X) := {comp_over}

    have h_over_covering : ⋃ ov ∈ covering, {ov.left} = {X} := by
      change ⋃ ov ∈ (Set.singleton comp_over), {ov.left} = {X}
      rw [← Set.image_eq_iUnion]
      simp [Set.singleton]
      rw [CategoryTheory.Over.mk_left]

    have h_precov_covering_eq_left : ⋃ ov ∈ covering, {ov.left} = ⋃ ov ∈ precov, {ov.left} :=
      Eq.trans h_over_covering h_precov.symm

    have h_precov' : precov ∈ {cover | ⋃ ov ∈ cover, {left | left = ov.left} = {X}} := h_precov
    have h_precov_image : (·.left) '' precov = {X} := by
      rw [← h_precov']
      simp [Set.image_eq_iUnion]

    have h_covering : (·.left) '' covering = {X} := by
      rw [← h_over_covering]
      simp [Set.image_eq_iUnion]

    have h_images_eq : (·.left) '' precov = (·.left) '' covering :=
      Eq.trans h_precov_image h_covering.symm

    let precov_containing_witness : Precover witness.left :=
      (h_in_cov witness witness_in_precov).val
    let property : ⋃ ov ∈ precov_containing_witness, {ov.left} = {witness.left} :=
      (h_in_cov witness witness_in_precov).property

    have property' : witness.left ∈ (⋃ ov ∈ precov_containing_witness, {ov.left}) := by
      simp_all

    have ⟨witness_c, dom_c, ⟨left_c, h_X_in_dom_c⟩⟩ := Set.mem_iUnion.mp property'

    simp at left_c

    have ⟨in_derived_cov, _⟩ := left_c

    -- Since we have X ⟶ witness.left and witness.left ⟶ X
    -- we can make a cover
    -- since X ⟶ X is the only morphism

    let ov_comp : Over X := Over.mk (witness_c.hom ≫ witness.hom)

    simp
    use ov_comp
    constructor
    case h.left =>
      use witness
      use witness_in_precov
      change ∃ x ∈ precov_containing_witness, Over.mk (x.hom ≫ witness.hom) = ov_comp
      exact ⟨witness_c, ⟨in_derived_cov, rfl⟩⟩
    case h.right =>
      rw [Over.mk_left]
      simp_all
      rename_i right
      subst right h_covering h_Y_X_def_eq
      simp_all only [Set.setOf_eq_eq_singleton,
        Set.mem_setOf_eq,
        Set.mem_singleton_iff,
        Iso.hom_inv_id,
        Set.image_singleton,
        Over.mk_left,
        Set.iUnion_iUnion_eq_left,
        precov_containing_witness,
        covering,
        comp_over]

def pullback.{u} {C : Type u} {Cat : XZarCat.{u}} {X : @Obj.{u} C Cat}
  (ov : Over X) (precov : Precover X) (h_precov : precov ∈ coverings X)
  : {x | ∃ g ∈ precov, Over.mk (pullback.snd g.hom ov.hom) = x} ∈ coverings ov.left := by
  simp only [coverings] at *
  change ⋃ ov ∈ precov, {left | left = ov.left} = {X} at h_precov
  -- We have defined the binary product as the intersection
  -- We don't know anything about ov.left
  -- but in the pullback ⋃ f ∈ precov, pullback y.hom ov.hom,
  -- y.left = x,
  -- because h : ⋃ ov ∈ precov, {ov.left} = {x}
  -- so, the pullback in ⋃ f ∈ precov, pullback y.hom ov.hom
  have h_all_precov_left_x : ∀ ov ∈ precov, ov.left = X := fun ov h_in_precov => by
    simp_all
    have h' : ov.left ∈ (⋃ ov ∈ precov, {ov.left}) := by
      apply Set.mem_iUnion.mpr
      use ov
      simp
      exact h_in_precov
    rw [h_precov] at h'
    exact Set.eq_of_mem_singleton h'
  simp
  -- Since y ∈ precov, then y.left = X
  ext
  constructor
  case h.mp Y =>
    intro h_all_pullbacks_in_precov
    simp at h_all_pullbacks_in_precov
    have ⟨i, h_i_precov, y_def_eq_pullback⟩ := h_all_pullbacks_in_precov
    -- Since i is in precov, then its left is X
    -- therefore, it is the identity map?
    -- We can probably construct an "equivalent" over
    -- from ov.hom
    -- or we can use apply_fun and show they are equivalent?
    have h_i_left : i.left = X := h_all_precov_left_x i h_i_precov

    -- We can probably use trans or iso here
    -- since i is an Over X with left = X
    -- we just need to make an inverse, which is pretty easy
    let i_hom : i.left ⟶ X := i.hom
    let i_hom_inv : X ⟶ i.left := by
      rw [h_i_left]
      exact CategoryStruct.id X
    let i_hom_iso := Iso.mk i_hom i_hom_inv

    -- This seems like we should use the definition of our pullbacks
    -- pullback point = the intersection of the sets i.left and ov.left
    -- we can get the cone
    let cone := pullback.cone i.hom ov.hom

    let left  : cone.pt ⟶ i.left  := cone.fst
    let right : cone.pt ⟶ ov.left := cone.snd

    let pullback_left  := pullback.fst i.hom ov.hom
    let pullback_right := pullback.snd i.hom ov.hom

    simp at pullback_left
    simp at pullback_right

    rw [← y_def_eq_pullback] at pullback_left
    rw [← y_def_eq_pullback] at pullback_right

    have h_y_subset₁ : Y.x ⊆ i.left.x  := pullback_left.down.down
    have h_y_subset₂ : Y.x ⊆ ov.left.x := pullback_right.down.down

    have h := CategoryTheory.Limits.PullbackCone.eta cone

    -- We can also derive a product

    let prod₀ := prod i.left ov.left

    let π₁ : prod₀ ⟶ i.left  := prod.fst
    let π₂ : prod₀ ⟶ ov.left := prod.snd

    -- And we can induce a morphism from cone.pt to prod.pt
    have cone_pt_prod : cone.pt ⟶ prod₀ := Limits.prod.lift left right

    have prod_subset_i  : prod₀.x ⊆ i.left.x  := π₁.down.down
    have prod_subset_ov : prod₀.x ⊆ ov.left.x := π₂.down.down

    have cone_subset_i   : cone.pt.x ⊆ i.left.x  := left.down.down
    have cone_subset_ov  : cone.pt.x ⊆ ov.left.x := right.down.down

    have cone_subset_prod : cone.pt.x ⊆ prod₀.x  := cone_pt_prod.down.down

    -- and the product gives us the intersection

    -- We jut need to show that prod.P = i.left × ov.left
    -- we can probably do this with a few morphisms
    unfold Obj.x at *

    let prod' := Prod.mk' i.left ov.left

    have h : prod₀.x ⊆ i.left.x ∩ ov.left.x := by
      apply Set.subset_inter_iff.mpr
      constructor
      repeat assumption

    have hom_prod₀_prod' : prod₀ ⟶ prod'.P := ⟨⟨by
      unfold Hom
      rw [Prod.p_hom_def_eq]
      exact h⟩⟩

    have hom_prod'_prod₀ : prod'.P ⟶ prod₀ := ⟨⟨by
      unfold Hom
      unfold Obj.x
      change prod'.P.x ⊆ prod₀.x
      rw [Prod.p_hom_def_eq]
      exact fun x h => by
        unfold Obj.x at *
        apply Set.mem_of_mem_of_subset
        exact h
        exact fun x h => by
          
          sorry
    ⟩⟩

    -- Y is a subset of i.left and ov.left
    -- so Y is the intersection of i.left and ov.left

    have h_y_inter : Y.x ⊆ i.left.x ∩ ov.left.x := by
      apply Set.subset_inter_iff.mpr
      constructor
      repeat assumption

    -- So Y ⟶ Prod
    have hom_y_prod : Y ⟶ prod'.P := ⟨⟨h_y_inter⟩⟩

    -- prod is a subset of ov.left
    -- and  Y
    unfold Obj.x at *

    apply Set.mem_singleton_iff.mpr
    ext
    constructor
    case x.h.mp x =>
      intro h
      exact h_y_subset₂ h
    case x.h.mpr x =>
      intro h
      unfold Obj.x at *
      
      sorry
  sorry

instance instSiteXZar.{u} {C : Type u} {Cat : XZarCat.{u}} :
  @Site Obj (instCategoryXZar.{u} Cat) (@instHasPullbacksXZar.{u} C Cat) :=
  {
    coverings := coverings
    iso := iso
    trans := trans
    pullback := pullback
  }

end XZar
