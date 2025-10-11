import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

open CategoryTheory
open CategoryTheory.Limits

variable {T : Type} [Category T] {U V W : T}

-- This is probably equivalent to Over U.
structure To (U : T) where
  V : T
  f : V ⟶ U

-- This is probably in Mathlib, but I couldn't find it.
structure PullbackOf (f : To U) (g : To U) where
  pullback : T
  fst : pullback ⟶ f.V
  snd : pullback ⟶ g.V
  is_pullback : IsPullback fst snd f.f g.f

def pullback_snd {f g : To U} (square : PullbackOf f g)
  := To.mk square.pullback square.snd

-- A family of morphisms with target U in C.
def Cover {T : Type} [Category T] (U : T) := Set (To U)

-- Why TF is this necessary???
-- Shouldn't Cover U immediately reduce to Set (To U)?
def coerce (cover : Cover U) : Set (To U) := cover
instance : Membership (To U) (Cover U) where
  mem (cover : Cover U) (f : To U) := f ∈ coerce cover

def Coverage (T : Type) [Category T] := ∀ {U : T}, Set (Cover U)

structure CoverIn (coverage : Coverage T) where
  obj : T
  cover : Cover obj
  in_coverage : cover ∈ coverage

structure CoverObj (cover : Cover U) where
  obj : T
  f : obj ⟶ U
  in_cover : To.mk obj f ∈ cover

-- A cover defined by a set of morphisms from a single source.
def single_source_cover (M : Set (V ⟶ U)) : Cover U
  := { f : To U | ∃ (p : f.V = V), match p with | Eq.refl f.V => f.f ∈ M }

inductive Lift (P : Prop) : Type where
| lift (p : P) : Lift P

class Site (T : Type) extends Category T where
  -- A set of covers for each object in C.
  coverage : ∀ {U : T}, Set (Cover U)
  -- Every isomorphism is a cover in itself.
  identity : ∀ {U V : T} (iso : Iso V U),
    single_source_cover { f : V ⟶ U | f = Iso.hom iso } ∈ coverage
  -- Transitivity/composition of covers.
  compose :
    ∀ (cover : CoverIn coverage)
    (pre_covers : ∀ (V : CoverObj cover.cover), Cover V.obj),
    (∀ (V : CoverObj cover.cover), pre_covers V ∈ coverage) →
    -- A morphism is in the composed cover if it is the composition
    -- of a morphism in the cover {g : Wᵢⱼ → Vᵢ) and a morphism in the
    -- cover {h : Vᵢ → U}.
    { f : To cover.obj |
      ∃ (h : CoverObj cover.cover) (g : f.V ⟶ h.obj),
      pre_covers h (To.mk f.V g) →
      f.f = CategoryStruct.comp g h.f } ∈ coverage
  pullback_exists :
    -- Unclear why Lean can't synthesize membership To U ∈ Cover U
    -- given that Cover U is literally defined as Set (To U).
    ∀ {U : T} {u_cover : Cover U}, u_cover ∈ coverage →
    ∀ (g : To U),
    ∀ {f : To U}, f ∈ u_cover →
    PullbackOf f g
  pullback_cover :
    ∀ {U : T} (u_cover : Cover U) (u_in_coverage : u_cover ∈ coverage),
    ∀ (g : To U),
    { snd : To g.V |
      ∃ (f : To U) (f_in_cover : f ∈ u_cover),
      snd = pullback_snd (pullback_exists u_in_coverage g f_in_cover) } ∈ coverage
