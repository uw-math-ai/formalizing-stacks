import Mathlib
import Stacks.Site

open TopologicalSpace
open CategoryTheory
open CategoryTheory.Limits

namespace XZar

@[simp]
def iso.{u} {C : Type u} [TopologicalSpace C] {X Y : Opens C}
  (hom : Y ⟶ X) (h_is_iso : IsIso hom) :
    {Over.mk hom} ∈ {cover : Precover X | ⋃ ov ∈ cover, {left | left = ov.left} = {X}} :=
      match h_is_iso, hom with
      | ⟨⟨⟨inv⟩⟩, ⟨inv_left, inv_right⟩⟩, ⟨⟨h_in⟩⟩ => by
        simp
        exact LE.le.antisymm h_in inv

@[simp]
def coverings.{u} {C : Type u} [TopologicalSpace C] (X : Opens C) :
  Set (Precover X) := { cover | (⋃ ov ∈ cover, { left | left = ov.left }) = ({X} : Set (Opens C)) }

theorem ov_comp_ext.{u} {C : Type u} [inst : TopologicalSpace C] {X : Opens C}
  (precov : Precover X)
  (h_mk_cov_left : (f : Over X) → f ∈ precov → { cover // cover ∈ coverings f.left })
  (x : Opens C)
  (h_precov_is_covering : ⋃ ov ∈ precov, {ov.left} = {X})
  (h_exists_comp_in_coverings : ∃ i : Over X,
    (∃ x, ∃ (x_1 : x ∈ precov), ∃ x_2 ∈ (h_mk_cov_left x x_1).val, Over.mk (x_2.hom ≫ x.hom) = i)
    ∧ x = i.left) : x = X := by
  let ⟨ov_comp, ⟨⟨ov_g, g_in_precov, ⟨ov_f, ⟨ov_f_in_precov_g, ov_def_eq_mk⟩⟩⟩, h⟩⟩ :=
    h_exists_comp_in_coverings
  rw [h]
  -- Note that (U : Over X) is equivalent to Opens U
  have iso_overs := TopologicalSpace.Opens.overEquivalence ov_comp
  sorry

@[simp]
def trans.{u} {C : Type u} [TopologicalSpace C] {X : Opens C}
  (precov : Precover X) (h_precov_is_covering : precov ∈ coverings X)
  (h_mk_cov_left : (f : Over X) → f ∈ precov → { cover // cover ∈ coverings f.left }) :
  {x |
    ∃ f, ∃ (hf : f ∈ precov), ∃ g ∈ (h_mk_cov_left f hf).val,
      Over.mk (g.hom ≫ f.hom) = x} ∈ coverings X := by
  ext
  case h x =>
    simp_all
    constructor
    case mp =>
      apply ov_comp_ext
      simp [h_precov_is_covering]
    case mpr =>
      sorry

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
      ext
      case x.h x =>
        constructor
        case mp =>
          intro h_in
          unfold Obj.x at *
          apply Set.mem_of_mem_of_subset
          exact h_in
          exact hom_pullback_ov_left.down.down
        case mpr =>
          intro h_in
          unfold Obj.x at *
          apply Set.mem_of_mem_of_subset
          -- ov ⊆ E
          -- and Y ⊆ E
          -- so E ⊆ ov ∩ Y
          -- ov ∩ Y is the binary product we have defined
          -- and the binary product has projections to ov and Y
          -- this suffices
          exact h_in
          change ov.left.x ⊆ (Limits.pullback i.hom ov.hom).x
          apply PLift.down
          apply ULift.down
          change ov.left ⟶ Limits.pullback i.hom ov.hom
          simp_all
          apply CategoryTheory.Limits.pullback.lift (by apply CategoryStruct.comp; exact f; exact i_hom_iso.inv) (CategoryStruct.id ov.left)
    intro h
    simp
    have h_precov' : X ∈ (⋃ ov ∈ precov, {ov.left}) := by
      simp_all
    have ⟨witness, dom, ⟨left, h_X_in_dom⟩⟩ := Set.mem_iUnion.mp h_precov'
    have ⟨witness_in_precov, x_is_dom⟩ := left
    exact ⟨witness, witness_in_precov, by
      let prod := Prod.mk' witness.left ov.left
      let pb   := Limits.pullback witness.hom ov.hom

      let p₁   := Limits.pullback.fst witness.hom ov.hom
      let p₂   := Limits.pullback.snd witness.hom ov.hom

      have pullback_to_prod : pb ⟶ prod.P := ⟨⟨by
        change pb.x ⊆ prod.P.x
        rw [Prod.p_hom_def_eq]
        unfold Obj.x
        apply Set.subset_inter_iff.mpr
        constructor
        exact p₁.down.down
        exact p₂.down.down⟩⟩
      have prod_to_pullback : prod.P ⟶ pb := CategoryTheory.Limits.pullback.lift ⟨⟨prod.π₁⟩⟩ ⟨⟨prod.π₂⟩⟩

      let h_witness_eq : witness.left = X := by
        simp_all

      simp_all
      ext
      case x.h x =>
        constructor
        case mp =>
          intro h
          unfold Obj.x at *
          apply Set.mem_of_mem_of_subset
          case hx =>
            exact h
          change ov.left.x ⊆ (Limits.pullback witness.hom ov.hom).x
          have p₁ := Limits.pullback.fst witness.hom ov.hom
          have p₂ := Limits.pullback.snd witness.hom ov.hom
          apply PLift.down
          apply ULift.down
          change ov.left ⟶ Limits.pullback witness.hom ov.hom
          simp_all
          apply CategoryTheory.Limits.pullback.lift
            (by apply CategoryStruct.comp; exact ov.hom; simp [h_witness_eq]; exact ⟨⟨Set.Subset.rfl⟩⟩)
            (CategoryStruct.id ov.left)
        case mpr =>
          intro h
          unfold Obj.x at *
          apply Set.mem_of_mem_of_subset
          exact h
          change (Limits.pullback witness.hom ov.hom).x ⊆ ov.left.x
          exact p₂.down.down
        ⟩

instance instSiteXZar.{u} {C : Type u} {Cat : XZarCat.{u}} :
  @Site Obj (instCategoryXZar.{u} Cat) (@instHasPullbacksXZar.{u} C Cat) :=
  {
    coverings := coverings
    iso := iso
    trans := trans
    pullback := pullback
  }

end XZar
