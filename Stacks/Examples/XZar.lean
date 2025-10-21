import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.Topology.Defs.Basic
import Stacks.Site

open CategoryTheory
open CategoryTheory (Category)
open CategoryTheory (asIso)
open CategoryTheory (Iso)
open CategoryTheory (IsIso)
open CategoryTheory (Precoverage)
open CategoryTheory.Limits

/-
Example 1 from Stacks project Site page.
-/

namespace XZar

@[ext]
class Obj.{v} {C : Type v} [TopologicalSpace C] where
  x : Set C
  h_open : IsOpen x

def Hom.{u} {C : Type u} [TopologicalSpace C] (X Y : @Obj C _) := X.x ⊆ Y.x

instance Hom.instQuiver.{u} {C : Type u} [TopologicalSpace C] : Quiver.{u + 1} (@Obj.{u} C _) where
  Hom X Y := Hom.{u} X Y |> PLift.{0} |> ULift

abbrev XZarCat.{u} {C : Type u} := TopologicalSpace.{u} C

instance instCategoryXZar.{u} {C : Type u} (Cat : XZarCat.{u})
  : Category.{u} (@Obj.{u} C Cat) where
  Hom X Y := @Hom.{u} C Cat X Y |> PLift.{0} |> ULift
  id X := ⟨⟨.rfl⟩⟩
  comp hom_xy hom_xz := by
    constructor
    constructor
    match hom_xy, hom_xz with
    | .up (.up hom_yz), .up (.up hom_xz) =>
      rw [Hom] at hom_yz
      rw [Hom] at hom_xz
      exact Set.Subset.trans hom_yz hom_xz

def PObj.{u} {C : Type u} {Cat : XZarCat.{u}}
  (X Y : @Obj.{u} C Cat)
  : @Obj.{u} C Cat := { x := X.x ∩ Y.x, h_open := IsOpen.inter X.h_open Y.h_open }

structure Prod.{v} {C : Type v} {Cat : XZarCat.{v}}
  (X Y : @Obj.{v} C Cat) where
  P : @Obj.{v} C Cat := PObj X Y
  p_hom_def_eq : P.x = X.x ∩ Y.x := by
    unfold PObj
    simp
  π₁       : Hom P X
  π₂       : Hom P Y

instance instObjProd.{v} {C : Type v} {Cat : XZarCat.{v}}
  (X Y : @Obj.{v} C Cat) (P : Prod X Y) : @Obj.{v} C Cat where
  x := P.P.x
  h_open := P.P.h_open

def Prod.mk'.{v} {C : Type v} {Cat : XZarCat.{v}}
  (X Y : @Obj.{v} C Cat) : Prod.{v} X Y :=
  {
    π₁ := fun inter h_subst =>
    by
      unfold Obj.x at h_subst
      unfold PObj at h_subst
      exact Set.mem_of_mem_inter_left (by assumption)
    π₂ := fun inter h_subst =>
    by
      unfold Obj.x at h_subst
      unfold PObj at h_subst
      exact Set.mem_of_mem_inter_right (by assumption)
  }

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

instance instSiteXZar.{u} {C : Type u} {Cat : XZarCat.{u}} : @Site Obj (instCategoryXZar.{u} Cat) (@instHasPullbacksXZar.{u} C Cat) where
  coverings := fun X (precov : Set (Over X)) => ∀ (over : Over X), over ∈ precov ↔ over.left = X
  iso {X Y} hom h_is_iso := by
    match h_is_iso, hom with
    | ⟨inv, ⟨inv_left, inv_right⟩⟩, .up (.up h_in) =>
      have h_subst : X.x ⊆ Y.x := inv.down.down
      have h_subst_hom : Hom X Y := h_subst
      have h_eq : X.x = Y.x := subset_antisymm (by assumption) (by assumption)
      change (fun precov ↦ ∀ (over : Over X), over ∈ precov ↔ over.left = X) {Over.mk _}
      simp
      intro ov
      constructor
      intro h
      unfold Obj.x at *
      ext
      unfold Obj.x
      rw [h_eq]
      simp_all
      intro h_eq'
      cases ov
      unfold Obj.x at *
      have h : X = Y := by
        ext
        unfold Obj.x
        rw [h_eq]
      simp_all
      rw [h] at h_in
      simp [Over.mk]
      simp [CostructuredArrow.mk]
      subst h_eq' h
      simp_all only
      rfl
  trans {X} precov h_precov V ov := by
    let { left := Y, right, hom } := ov

    simp at hom
    let prod := Prod.mk' Y X

    have h_precov' : ∀ (over : Over X), over ∈ precov ↔ over.left = X := h_precov

    have π₁ := prod.π₁
    have π₂ := prod.π₂

    let π_pullback := instHasPullbacksXZar.has_limit

    -- Since we have pullbacks, then we have a morphism from Y and X to P
    -- since P.pt = X ∩ Y, and since we also have products with projections (X ∩ Y),
    -- π₁ : X × Y ⟶ X,
    -- then X ⟶ P.pt ⟶ Y
    -- and Y ⟶ P.pt ⟶ X
    -- Since ⟶ = ⊆,
    -- then X = Y

    simp
    constructor
    intro h_ov

    obtain ⟨f, ⟨h_f_precov, ⟨g, ⟨h_g, h_comp_eq⟩⟩⟩⟩ := h_ov


    sorry

end XZar
