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

-- A family of morphisms with target U in C.
def Cover (U : T) := Set (To U)

-- A cover defined by a set of morphisms from a single source.
def single_source_cover (M : Set (V ⟶ U)) : Cover U
  := { f : To U | ∃ (p : f.V = V), match p with | Eq.refl f.V => f.f ∈ M }

def InCover (cover : Cover U) (V : T) : Prop
  := ∃ (f : V ⟶ U), cover (To.mk V f)

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
    ∀ {U : T} (u_cover : Cover U), u_cover ∈ coverage →
    ∀ (v_covers : ∀ {V : T}, InCover u_cover V → Cover V),
    (∀ {V} (v_in_cover : InCover u_cover V), v_covers v_in_cover ∈ coverage) →
    -- A morphism is in the composed cover if it is the composition
    -- of a morphism in the cover {g : Wᵢⱼ → Vᵢ) and a morphism in the
    -- cover {h : Vᵢ → U}.
    { f : To U |
      ∃ (h : To U) (g : f.V ⟶ h.V),
      (h_in_cover : u_cover h) → v_covers (Exists.intro h.f h_in_cover) (To.mk f.V g) →
      f.f = CategoryStruct.comp g h.f } ∈ coverage
  pullback_exists :
    -- Unclear why Lean can't synthesize membership To U ∈ Cover U
    -- given that Cover U is literally defined as Set (To U).
    ∀ {U : T} {u_cover : Set (To U)}, u_cover ∈ coverage →
    ∀ (g : To U),
    ∀ {f : To U}, f ∈ u_cover →
    Σ (Pb : T) (fst : Pb ⟶ f.V) (snd : Pb ⟶ g.V), Lift (IsPullback fst snd f.f g.f)
  pullbacks_cover :
    ∀ {U : T} (u_cover : Set (To U)) (u_in_coverage : u_cover ∈ coverage),
    ∀ (g : To U),
    { snd : To g.V |
      ∃ (f : To U) (f_in_cover : f ∈ u_cover),
      snd = To.mk (pullback_exists u_in_coverage g f_in_cover).fst
            (pullback_exists u_in_coverage g f_in_cover).snd.snd.fst} ∈ coverage
