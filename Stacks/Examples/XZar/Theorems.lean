import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.Topology.Defs.Basic
import Mathlib.Tactic.ApplyFun
import Mathlib.Data.Set.Lattice.Image
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

instance instHasPullbacksXZar.{u} {C : Type u} {Cat : XZarCat.{u}} : @HasPullbacks.{u, u} (@Obj.{u} C Cat) _ where
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

instance instSiteXZar.{u} {C : Type u} {Cat : XZarCat.{u}} : @Site Obj (instCategoryXZar.{u} Cat) (@instHasPullbacksXZar.{u} C Cat) :=
  have iso {X Y : Obj} (hom : Y ⟶ X) (h_is_iso : IsIso hom) : {Over.mk hom} ∈ {cover : Precover X | ⋃ ov ∈ cover, {left | left = ov.left} = {X}} := by
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
      -- Since the Over's in precov are commutative triangles:
      -- A ⟶ T
      -- B ⟶ T
      -- where T is the domain,
      -- then T is kind of like a Pullback?
      -- and we can form A × B
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
        intro h_hom_Y_X

        have h_Y_X_def_eq : Y = X := Set.eq_of_mem_singleton h_hom_Y_X
        have h_hom_Y_X    : Y ⟶ X := by
          apply ULift.up
          apply PLift.up
          unfold Hom
          rw [h_Y_X_def_eq]

        simp_all

        let h_precov' : (·.left) '' precov = {X} := by
          rw [Set.image_eq_iUnion, h_precov]

        have ⟨⟨witness, in_over_left⟩, h⟩ := Set.eq_singleton_iff_nonempty_unique_mem.mp h_precov'

        simp_all

        sorry
  }

end XZar
