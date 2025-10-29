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
  simp_all
  have h_all_precov_left_x : ∀ ov ∈ precov, ov.left = X := fun ov h_in_precov => by
    have h' : ov.left ∈ (⋃ ov ∈ precov, {ov.left}) := by
      apply Set.mem_iUnion.mpr
      use ov
      simp
      exact h_in_precov
    rw [h_precov] at h'
    exact Set.eq_of_mem_singleton h'

  have h_all_left_x_precov : ∀ (precov' : Precover X), ((⋃ ov ∈ precov', {ov.left}) = {X}) → precov' ∈ coverings X := by
    simp_all

  ext
  case h E =>
    constructor
    case mp =>
      intro E_in_precov
      simp at E_in_precov
      have ⟨i, h_i_in_precov, E_def_eq⟩ := E_in_precov
      rw [E_def_eq]

      -- The limit has projections to i and ov
      -- and since i has left = X,
      -- then i is in the coverings
      -- furthermore, since ov ⟶ X
      -- and X ⟶ I
      -- and I ⟶ X
      -- then {ov} ∈ coverings
      -- by the trans property

      have hom_pullback_ov_left : Limits.pullback i.hom ov.hom ⟶ ov.left :=
        pullback.snd i.hom ov.hom
      have hom_pullback_i_left  : Limits.pullback i.hom ov.hom ⟶ i.left  :=
        pullback.fst i.hom ov.hom

      let f : ov.left ⟶ X := ov.hom
      let g : i.left ⟶ X := i.hom

      -- since i ∈ precov, then i.left = X
      -- and since i : Over X
      -- then i.hom is an isomorphism X
      have i_left_X : i.left = X := h_all_precov_left_x _ h_i_in_precov
      have i_hom_iso : Iso i.left X := by
        rw [i_left_X]

      let prod := Prod.mk' i.left ov.left

      have h_pullback_inter : (Limits.pullback i.hom ov.hom) ⟶ prod.P := by
        apply ULift.up
        apply PLift.up
        change (Limits.pullback i.hom ov.hom).x ⊆ prod.P.x
        rw [Prod.p_hom_def_eq]
        apply Set.subset_inter
        exact hom_pullback_i_left.down.down
        exact hom_pullback_ov_left.down.down

      have hom_over := (Over.mk i.hom).hom
      simp at hom_over

      have h_X_inter : ov.left.x ∩ i.left.x ⊆ X.x := by
        unfold Obj.x
        subst E_def_eq
        simp_all only [Functor.id_obj,
          Functor.const_obj_obj,
          Set.subset_inter_iff,
          Set.inter_subset_right]

      have h_prod_ov_left  : prod.P ⟶ ov.left := ⟨⟨prod.π₂⟩⟩
      have h_prod_i_left   : prod.P ⟶ i.left  := ⟨⟨prod.π₁⟩⟩

      have h_prod_is_inter : prod.P.x = i.left.x ∩ ov.left.x := by
        rw [Prod.p_hom_def_eq]

      let ov_pullback := Over.mk i.hom

      -- the product has a morphism to the pullback
      have X_to_pullback : prod.P ⟶ Limits.pullback i.hom ov.hom := CategoryTheory.Limits.pullback.lift h_prod_i_left h_prod_ov_left

      have pullback_eq_inter : (Limits.pullback i.hom ov.hom).x = i.left.x ∩ ov.left.x := by
        apply Set.eq_of_subset_of_subset
        unfold Obj.x
        change (Limits.pullback i.hom ov.hom).x ⊆ (i.left.x ∩ ov.left.x)
        rw [← h_prod_is_inter]
        exact h_pullback_inter.down.down
        exact X_to_pullback.down.down

      apply Set.mem_singleton_iff.mpr
      apply_fun (·.x)
      case _ =>
        change (Limits.pullback i.hom ov.hom).x = ov.left.x
        apply Set.eq_of_subset_of_subset
        case a =>
          exact hom_pullback_ov_left.down.down
        case a =>
          unfold Obj.x
          unfold Obj.x at *
          -- ov ⊆ E
          -- and Y ⊆ E
          -- so E ⊆ ov ∩ Y
          -- ov ∩ Y is the binary product we have defined
          -- and the binary product has projections to ov and Y
          -- this suffices
          change ov.left.x ⊆ (Limits.pullback i.hom ov.hom).x
          apply PLift.down
          apply ULift.down
          change ov.left ⟶ Limits.pullback i.hom ov.hom
          simp_all
          apply CategoryTheory.Limits.pullback.lift (by apply CategoryStruct.comp; exact f; exact i_hom_iso.inv) (CategoryStruct.id ov.left)
      simp [Function.Injective]
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
