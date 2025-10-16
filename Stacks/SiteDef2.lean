import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

open CategoryTheory (Category)
open CategoryTheory (Iso)

/-
A definition of a site that attempts to use as much from mathlib as possible.
I also attempt to use encodings more native to type theory.
I fall back to Set notation if no "type-theoretic" encoding is possible.
-/

namespace CategoryTheory

inductive Site.Covering.{v, u} {C : Type u}
  [Category.{v, u} C] [Limits.HasBinaryProducts.{v, u} C] :
  C → C → Prop
  | iso   (X Y      : C) : Iso X Y → Site.Covering X Y
  | trans (X Y Z    : C) : Site.Covering X Y
    → Site.Covering Y Z
    → Site.Covering X Z
  | prod (X Y Z XZ  : C) : Site.Covering Y Z
    → Nonempty (X ⟶ Z)
    → Limits.HasBinaryProduct Y XZ
    → Site.Covering (Limits.prod Y XZ) X

structure Site.{v, u} {C : Type u}
  [Category.{v, u} C] [Limits.HasBinaryProducts.{v, u} C]
  (Z : C) where
  coverings (X : C) : (X ⟶ Z) → Site.Covering X Z

end CategoryTheory
