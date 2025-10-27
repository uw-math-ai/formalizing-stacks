import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.Topology.Defs.Basic
import Mathlib.Tactic.ApplyFun
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Defs
import Stacks.Site
import Stacks.Examples.XZar.XZarCat

open CategoryTheory
open CategoryTheory (Category)
open CategoryTheory (asIso)
open CategoryTheory (Iso)
open CategoryTheory (IsIso)
open CategoryTheory (Precoverage)
open CategoryTheory.Limits

namespace XZar

instance instHasBinaryProductsXZar.{u} {C : Type u} {Cat : XZarCat.{u}} :
  HasBinaryProducts.{u, u} (@Obj C Cat) where
  has_limit F : HasLimit F := by
    let { obj, map, map_id, map_comp } := F
    let f_π₁ := CategoryTheory.Discrete.mk WalkingPair.left
    let f_π₂ := CategoryTheory.Discrete.mk WalkingPair.right

    let left := obj f_π₁
    let right := obj f_π₂

    let prod := Prod.mk' left right

    let cone : Cone { obj := obj, map := map, map_id := map_id, map_comp := map_comp } := {
        pt := prod.P,
        π  := {
          app direction := (
            match direction with
            | { as := .left } => by
              repeat constructor
              change left.x ∩ right.x ⊆ left.x
              simp
            | { as := .right } => by
              repeat constructor
              change left.x ∩ right.x ⊆ right.x
              simp
            ),
          naturality dir₁ dir₂ hom := (match dir₁, dir₂ with
            | { as := .left }, { as := .left } => by
              simp
              have h_id := CategoryTheory.Discrete.id_def { as := WalkingPair.left }
              have h_comp_id := CategoryTheory.Category.id_comp hom
              cases hom
              rw [h_id, map_id]
              simp_all
            | { as := .right }, { as := .right } => by
              simp
              have h_id := CategoryTheory.Discrete.id_def { as := WalkingPair.right }
              have h_comp_id := CategoryTheory.Category.id_comp hom
              cases hom
              rw [h_id, map_id]
              simp_all
            | { as := .right }, { as := .left }
            | { as := .left }, { as := .right }=> by
              match hom with
              | .up h =>
                cases h
                contradiction)
        }
      }

    exact HasLimit.mk {
      cone := cone
      isLimit := {
        lift := fun cone' => ⟨⟨fun cone_pt h_subst => by
            -- Both cones have projections
            -- and we have a map from the projections to an actual Prod
            -- which gives X ∩ Y
            let hom_x : cone'.pt ⟶ left := cone'.π.app { as := .left }
            let hom_y : cone'.pt ⟶ right := cone'.π.app { as := .right }

            let hom_x' := prod.π₁
            let hom_y' := prod.π₂

            unfold Hom at hom_x'
            unfold Hom at hom_y'
            unfold Obj.x at hom_x'
            unfold Obj.x at hom_y'

            match hom_x, hom_y with
            | .up (.up hom_x), .up (.up hom_y) =>
              have h : cone'.pt.1 ⊆ (left.1 ∩ right.1) := by
                simp
                exact ⟨by assumption, by assumption⟩

              have hom_x : cone'.pt.1 ⊆ left.1 := by assumption
              have hom_y : cone'.pt.1 ⊆ right.1 := by assumption

              rw [Prod.p_hom_def_eq]

              constructor
              case left =>
                apply Set.mem_of_mem_of_subset
                case hx =>
                  assumption
                exact hom_x
              case right =>
                apply Set.mem_of_mem_of_subset
                case hx =>
                  assumption
                exact hom_y
         ⟩⟩
      }
    }

instance instHasPullbacksXZar.{u} {C : Type u} {Cat : XZarCat.{u}} :
  @HasPullbacks.{u, u} (@Obj.{u} C Cat) _ where
  has_limit := fun F@{ obj, map, map_id, map_comp } =>
    -- Left and right objects with morphisms to some central object
    let hom_left : (obj .left) ⟶ (obj .one)   := map WalkingCospan.Hom.inl
    let hom_right : (obj .right) ⟶ (obj .one) := map WalkingCospan.Hom.inr

    -- We also have a binary product containing left and right
    let prod := Prod.mk' (obj .left) (obj .right)

    -- Since we have Binary Products, we also have a Functor from WalkingPair to
    -- Obj and projections from left to right
    let F₂@{ obj := obj_prod, map := map_prod, map_id := map_id_prod, map_comp := map_comp_prod }
      : CategoryTheory.Functor (Discrete WalkingPair) Obj := {
      obj := fun pair => match pair with
        | .mk (.left) => obj .left
        | .mk (.right) => obj .right
      map {X Y} hom :=
        match X, Y with
        | .mk .left, .mk .left   => (instCategoryXZar Cat).id <| obj .left
        | .mk .right, .mk .right => (instCategoryXZar Cat).id <| obj .right
    }

    -- So we can compose projections from Prod to left and right, then to the span
    -- Making a diamond shape

    let π₁_lift : prod.P ⟶ (obj .left) := ⟨⟨prod.π₁⟩⟩
    let π₂_lift : prod.P ⟶ (obj .right) := ⟨⟨prod.π₂⟩⟩

    let π₁_span : Hom prod.P (obj .one) := (π₁_lift ≫ hom_left).down.down
    let π₂_span : Hom prod.P (obj .one) := (π₂_lift ≫ hom_right).down.down

    HasLimit.mk {
      cone := {
        pt := prod.P,
        π := {
          app span := match span with
            | .left => ⟨⟨prod.π₁⟩⟩
            | .right => ⟨⟨prod.π₂⟩⟩
            | .one => ⟨⟨π₁_span⟩⟩
        }
      }
      isLimit := {
        lift := fun { pt, π } => ⟨⟨fun cone_pt h_subst => by
          have hom_x := (π.app .left).down.down
          have hom_y := (π.app .right).down.down

          simp at hom_x
          simp at hom_y

          have subset_hom_x : pt.x ⊆ (obj .left).x  := hom_x
          have subset_hom_y : pt.x ⊆ (obj .right).x := hom_y

          unfold Obj.x
          simp
          apply Set.mem_of_mem_of_subset
          case hx =>
            exact h_subst
          unfold Obj.x
          simp
          apply Set.Subset.trans
          case h.ab =>
            apply Set.subset_inter
            case rs =>
              exact hom_x
            case rt =>
              exact hom_y
          conv =>
          right
          change (obj .left).x ∩ (obj .right).x
          rfl
        ⟩⟩
      }
    }

instance instSiteXZar.{u} {C : Type u} {Cat : XZarCat.{u}} :
  @Site Obj (instCategoryXZar.{u} Cat) (@instHasPullbacksXZar.{u} C Cat) :=
  have iso {X Y : Obj} (hom : Y ⟶ X) (h_is_iso : IsIso hom) :
    {Over.mk hom} ∈ {cover : Precover X | ⋃ ov ∈ cover, {left | left = ov.left} = {X}} := by
      match h_is_iso, hom with
      | ⟨inv, ⟨inv_left, inv_right⟩⟩, .up (.up h_in) =>
        have h_subst : X.x ⊆ Y.x := inv.down.down
        have h_subst_hom : Hom X Y := h_subst
        have h_eq : X.x = Y.x := subset_antisymm (by assumption) (by assumption)
        simp
        ext
        simp_all
  {
    coverings := fun X => { cover | (⋃ ov ∈ cover, { left | left = ov.left }) = ({X} : Set Obj) }
    iso := iso
    trans {X} precov h_precov h_in_cov := by
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
    pullback {X} (ov : Over X) (precov : Precover X) h:= by
      simp_all
      rw [← Set.image_eq_iUnion]
      -- We have defined the binary product as the intersection
      -- We don't know anything about ov.left
      -- but in the pullback ⋃ f ∈ precov, pullback y.hom ov.hom,
      -- y.left = x,
      -- because h : ⋃ ov ∈ precov, {ov.left} = {x}
      -- so, the pullback in ⋃ f ∈ precov, pullback y.hom ov.hom
      have h : ∀ ov ∈ precov, ov.left = X := fun ov h_in_precov => by
        have h' : ov.left ∈ (⋃ ov ∈ precov, {ov.left}) := by
          apply Set.mem_iUnion.mpr
          use ov
          simp
          exact h_in_precov
        rw [h] at h'
        exact Set.eq_of_mem_singleton h'
      sorry
  }

end XZar
