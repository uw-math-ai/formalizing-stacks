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

instance instCategoryXZar.{u} {C : Type u} [TopologicalSpace C] [Quiver (@Obj C _)]
  : Category.{u} (@Obj C _) where
  Hom X Y := Hom X Y
  id X := id
  comp hom_xy hom_xz := hom_xz ∘ hom_xy

structure Prod.{v} {C : Type v} [TopologicalSpace C] [Quiver (@Obj C _)] [Category.{v, v} (@Obj C _)]
  (X Y : @Obj C _) where
  P        : @Obj C _ := { x := X.x ∩ Y.x, h_open := IsOpen.inter X.h_open Y.h_open }
  π₁       : P ⟶ X
  π₂       : P ⟶ Y
  is_limit : @IsLimit.{v, v, v, v} (@Obj C _) _ _  _ _ (@BinaryFan.mk.{v, v} (@Obj C _) _ X Y P π₁ π₂)

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
