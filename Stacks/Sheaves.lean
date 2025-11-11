import Mathlib
import Stacks.Site2Mathlib

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Presieve

abbrev Presheaf.{u₁, u₂, v₁, v₂} (C : Type v₁) (A : Type v₂)
  [Category.{u₁, v₁} C] [Category.{u₂, v₂} A] :=
  Cᵒᵖ ⥤ A

-- Sheaves adapted to our Sites
def IsSheaf.{u₁, u₂, v₁, v₂} {C : Type v₁} {A : Type v₂}
  [Category.{u₁, v₁} C] [Category.{u₂, v₂} A] [HasPullbacks C]
  (s : Site' C)
  (F : Presheaf.{u₁, u₂, v₁, v₂} C A) := Presheaf.IsSheaf s.toGrothendieck F

