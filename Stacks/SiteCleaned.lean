import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type} [Category C]

-- A family or morphisms with destination dst.
abbrev Cover (dst : C) := ∀ (src : C), (src ⟶ dst) → Prop

-- A collection of covers for every object in the category.
abbrev Coverings (C : Type) [Category C] := ∀ (dst : C), Cover dst

-- The collection of objects that are sources of some morphism in a cover.
abbrev cover_domain {dst : C} (cover : Cover dst) := fun (src : C) => cover src

structure Site (C : Type) [Category C] where
  coverings : Coverings C
  -- Isomorphisms are covers unto themselves..
  iso := ∀ (src dst : C) (iso : Iso src dst), coverings dst src iso.hom
  -- Given a cover of 'dst' and a cover for every object 'mid' in the domain of dst,
  -- the composition of the morphisms of the covers forms a cover.
  compose : ∀ dst : C, ∀ cover ∈ coverings dst,
            -- A family of covers for every object in the domain of the cover.
            ∀ (src : ∀ f ∈ cover, { cover' // cover' ∈ coverings f.src }),
            -- We're looking for morphisms that are the composition of morphisms in our covers.
            { h : To dst |
              -- A morphism in the destination cover.
              ∃ f : To dst,
              ∃ f_in_cover : f ∈ cover,
              -- A morphism in the source cover.
              ∃ g ∈ (src f f_in_cover).val,
              -- h is a composition of the morphisms.
              h = To.mk g.src (CategoryStruct.comp g.f f.f)
             } ∈ coverings dst
  -- Pullbacks exist for morphisms in a cover with any other morphism in the category.
  pullback :
    ∀ {dst : C},
    ∀ g : To dst,
    ∀ cover ∈ coverings dst, ∀ f ∈ cover,
    Pullback f g
  -- The pullbacks of g with respect to a cover of dst cover the source of g.
  pullbacks_cover :
    ∀ {dst : C}, ∀ g : To dst,
    ∀ (cover : Cover dst) (cover_in : cover ∈ coverings dst),
    { h : To g.src
    | ∀ (f : To dst) (f_in : f ∈ cover),
      let pullback := pullback g cover cover_in f f_in
      h = To.mk pullback.obj pullback.snd
    } ∈ coverings g.src
