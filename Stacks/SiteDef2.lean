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

structure Obj.{v} {C : Type v} [TopologicalSpace C] where
  x : Set C
  h_open : IsOpen x

def Hom.{u} {C : Type u} [TopologicalSpace C] (X Y : @Obj C _) := X.x → Y.x

instance Hom.instQuiver.{u} {C : Type u} [TopologicalSpace C] : Quiver.{u + 1} (@Obj.{u} C _) where
  Hom X Y := Hom X Y

instance instCategoryXZar.{u} {C : Type u} [TopologicalSpace C] [Quiver.{u + 1, u} (@Obj C _)]
  : Category.{u} (@Obj C _) where
  Hom X Y := Hom X Y
  id X := id
  comp hom_xy hom_xz := hom_xz ∘ hom_xy

structure Prod.{v} {C : Type v} [TopologicalSpace C] [Category.{v + 1, v} (@Obj.{v} C _)]
  (X Y : @Obj.{v} C _) where
  P : @Obj.{v} C _ := { x := X.x ∩ Y.x, h_open := IsOpen.inter X.h_open Y.h_open }
  p_hom_def_eq : P.x = X.x ∩ Y.x := by
    simp
  π₁       : P ⟶ X
  π₂       : P ⟶ Y
  is_limit : IsLimit (@BinaryFan.mk.{v, v} (@Obj C _) _ X Y P π₁ π₂)

def Prod.mk'.{v} {C : Type v} [TopologicalSpace.{v} C] [Category.{v + 1, v} (@Obj.{v} C _)] (X Y : @Obj.{v} C _): Prod.{v} X Y :=
  let π₁ := fun inter =>
    by
      simp at inter
      let { val := val_inter, property := h_inter } := inter
      have h_inclusion : val_inter ∈ X.x := Set.mem_of_mem_inter_left h_inter
      have h_coe : Subtype X.x := { val := val_inter, property := (by assumption) }
      exact h_coe
  let π₂ := fun inter =>
    by
      simp at inter
      let { val := val_inter, property := h_inter } := inter
      have h_inclusion : val_inter ∈ Y.x := Set.mem_of_mem_inter_right h_inter
      have h_coe : Subtype Y.x := { val := val_inter, property := (by assumption) }
      exact h_coe

  {
    π₁ := π₁
    π₂ := π₂
    is_limit := IsLimit.mk
      (fun s x => (by
        simp
        match h : s with
        | .mk x₀ π =>
          match π with
          | ⟨mpr, mpl⟩ =>
            let pair₁ : CategoryTheory.Discrete WalkingPair := { as := WalkingPair.left }
            let pair₂ : CategoryTheory.Discrete WalkingPair := { as := WalkingPair.right }
            let val_in_pair₁ := π.app pair₁ (by assumption)
            let val_in_pair₂ := π.app pair₂ (by assumption)
            let { val := val₁, property } := val_in_pair₁
            let { val := val₂, property := prop₂ } := val_in_pair₂
            have h_left : val₁ ∈ X.x := property
            have h_right : val₂ ∈ Y.x := prop₂
            exact ⟨val₁, ⟨h_left, h_right⟩⟩
            ))
      sorry
      sorry
  }

instance instHasBinaryProductsXZar.{u} {C : Type u} [TopologicalSpace C] [Quiver (@Obj C _)] [Category (@Obj C _)] :
  HasBinaryProducts (@Obj C _) where
  has_limit F : HasLimit F := HasLimit.mk {
    isLimit := {
      lift := sorry
    }
    cone := {
      pt := { x := Set.univ, h_open := isOpen_univ },
      π  := {
        app X := by
          
          sorry
      }
    }
  }

instance instSiteXZar.{u} {C : Type u} : @Site.{u} (@Obj C) instCategoryXZar _ { x := Set.univ } where
  sorry

end XZar

lemma top_xzar_site.{v, u} {X : Type u} [TopologicalSpace X] : 
