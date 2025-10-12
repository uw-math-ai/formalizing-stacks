import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type} [Category C]

-- A morphism with destimation dst.
structure To (dst : C) where
  src : C
  f : src ⟶ dst

-- A pullback of f and g.
structure Pullback {dst : C} (f : To dst) (g : To dst) where
  obj : C
  fst : obj ⟶ f.src
  snd : obj ⟶ g.src
  is_pullback : IsPullback fst snd f.f g.f

-- A family or morphisms with destination dst.
abbrev Cover (dst : C) := Set (To dst)

-- A collection of covers for every object in the category.
abbrev Coverings (C : Type) [Category C] := ∀ (dst : C), Set (Cover dst)

-- The collection of objects that are sources of some morphism in a cover.
abbrev cover_domain {dst : C} (cover : Cover dst) : Set C
  := { src : C | ∃ f ∈ cover, src = f.src }

structure Site (C : Type) [Category C] where
  coverings : Coverings C
  -- Isomorphisms are covers unto themselves..
  iso : ∀ (src dst : C) (iso : Iso src dst), { To.mk src iso.hom } ∈ coverings dst
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
