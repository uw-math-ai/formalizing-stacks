import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.Topology.Defs.Basic
import Mathlib.Tactic.ApplyFun
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

end XZar
