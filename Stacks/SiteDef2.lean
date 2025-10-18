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

def Hom.{u} {C : Type u} [TopologicalSpace C] (X Y : @Obj C _) := X.x → Y.x

instance Hom.instQuiver.{u} {C : Type u} [TopologicalSpace C] : Quiver.{u + 1} (@Obj.{u} C _) where
  Hom X Y := Hom X Y

abbrev XZarCat.{u} {C : Type u} := TopologicalSpace.{u} C

instance instCategoryXZar.{u} {C : Type u} (Cat : XZarCat.{u})
  : Category.{u} (@Obj.{u} C Cat) where
  Hom X Y := @Hom C Cat X Y
  id X := id
  comp hom_xy hom_xz := hom_xz ∘ hom_xy

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
    π₁ := fun inter =>
    by
      unfold PObj at inter
      simp at inter
      let { val := val_inter, property := h_inter } := inter
      have h_inclusion : val_inter ∈ X.x := Set.mem_of_mem_inter_left h_inter
      have h_coe : Subtype X.x := { val := val_inter, property := (by assumption) }
      exact h_coe
    π₂ := fun inter =>
    by
      unfold PObj at inter
      simp at inter
      let { val := val_inter, property := h_inter } := inter
      have h_inclusion : val_inter ∈ Y.x := Set.mem_of_mem_inter_right h_inter
      have h_coe : Subtype Y.x := { val := val_inter, property := (by assumption) }
      exact h_coe
  }

instance instHasBinaryProductsXZar.{u} {C : Type u} {Cat : XZarCat.{u}} :
  HasBinaryProducts.{u, u} (@Obj C Cat) where
  has_limit F : HasLimit F := by
    let { obj, map, map_id, map_comp } := F
    let f_π₁ := CategoryTheory.Discrete.mk WalkingPair.left
    let f_π₂ := CategoryTheory.Discrete.mk WalkingPair.left

    let left := obj f_π₁
    let right := obj f_π₂

    let prod := Prod.mk' left right

    let cone : Cone { obj := obj, map := map, map_id := map_id, map_comp := map_comp } := {
        pt := prod.P,
        π  := {
          app direction := (by
            cases direction
            case mk as =>
              cases as
              case left =>
                simp
                exact (fun h => by
                  let left := prod.π₁ (by assumption)
                  have { val, property } := left
                  exact { val := val, property := property })
              case right =>
                simp
                exact (fun h => by
                  let right := prod.π₂ (by assumption)
                  have { val, property } := right
                  exact { val := val, property := property }))
        }
      }

    exact HasLimit.mk {
      isLimit := {
        lift := fun cone' => by
          let hom : Hom cone'.pt cone.pt := fun cone_pt => by
            have h : Subtype (@Obj.x C Cat cone.pt) := by
              
              let { pt := pt₀, π } := cone'
              let { app, naturality } := π
              let left' := app <| .mk WalkingPair.left
              let right' := app <| .mk WalkingPair.right
              let { P := P₀, π₁, π₂, p_hom_def_eq } := Prod.mk' pt₀ cone.pt
              rw [Hom, p_hom_def_eq] at π₁
              rw [Hom, p_hom_def_eq] at π₂
              have { val := elem_left, property := left } := left' (by sorry)
              
              have { val := elem_right, property := right } := right' (by assumption)
              let h : ↑(@Obj.x _ _ cone.pt ∩ @Obj.x _ _ cone'.pt) := ⟨elem_left, by simp_all; exact ⟨left, right⟩⟩
              sorry
            exact h
          exact hom
      }
      cone := cone
    }

instance instSiteXZar.{u} {C : Type u} : @Site.{u} (@Obj C) instCategoryXZar _ { x := Set.univ } where
  sorry

end XZar

lemma top_xzar_site.{v, u} {X : Type u} [TopologicalSpace X] : 
