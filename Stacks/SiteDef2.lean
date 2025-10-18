import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.Topology.Defs.Basic

open CategoryTheory (Category)
open CategoryTheory (asIso)
open CategoryTheory (Iso)
open CategoryTheory (IsIso)
open CategoryTheory (Precoverage)
open CategoryTheory.Limits

/-
A definition of a site that attempts to use as much from mathlib as possible.
I also attempt to use encodings more native to type theory.
I think this definition is quite concise, but let me know if anything is wrong.
-/

inductive Site.Covering.{u} {C : Type u}
  [Category.{u} C] [HasBinaryProducts.{u} C] :
  C → C → Prop
  -- Axiom 1
  | iso   (X Y      : C) : Iso X Y → Site.Covering X Y
  -- Axiom 2
  | trans (X Y Z    : C) : Site.Covering X Y
    → Site.Covering Y Z
    → Site.Covering X Z
  -- Axiom 3
  | prod (X Y Z XZ  : C) : Site.Covering Y Z
    → Nonempty (X ⟶ Z)
    → HasBinaryProduct Y XZ
    → Site.Covering (prod Y XZ) X

class Site.{u} {C : Type u}
  [Category.{u} C] [HasBinaryProducts.{u} C]
  (Z : C) where
  coverings (X : C) : (X ⟶ Z) → Site.Covering X Z

/-
Example 3 from Stacks project page (https://stacks.math.columbia.edu/tag/00VG):
-/

lemma canonical_functor.{u} {C : Type u} [Category.{u} C] [HasBinaryProducts.{u} C]
  (X : C) : (∀ (Y : C) (hom : Y ⟶ X), IsIso hom) → @Site.{u} C _ _ X := fun h_isos => {
    coverings Y := fun hom =>
      Site.Covering.iso _ _ (@asIso _ _ _ _  hom (h_isos Y hom))
  }

/-
Example 1 from Stacks project page.
-/

namespace XZar

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

instance instSiteXZar.{u} {C : Type u} : @Site.{u} (@Obj C) instCategoryXZar _ { x := Set.univ } where
  sorry

end XZar

lemma top_xzar_site.{v, u} {X : Type u} [TopologicalSpace X] : 
