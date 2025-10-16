import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

open CategoryTheory (Category)
open CategoryTheory (Iso)

/-
A definition of a site that attempts to use as much from mathlib as possible.
I also attempt to use encodings more native to type theory.
I think this definition is quite concise, but let me know if anything is wrong.
-/

namespace CategoryTheory

inductive Site.Covering.{v, u} {C : Type u}
  [Category.{v, u} C] [Limits.HasBinaryProducts.{v, u} C] :
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
    → Limits.HasBinaryProduct Y XZ
    → Site.Covering (Limits.prod Y XZ) X

structure Site.{v, u} {C : Type u}
  [Category.{v, u} C] [Limits.HasBinaryProducts.{v, u} C]
  (Z : C) where
  coverings (X : C) : (X ⟶ Z) → Site.Covering X Z

end CategoryTheory
