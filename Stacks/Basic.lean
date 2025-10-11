import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
open CategoryTheory

-- A family of morphisms with target U in C.
def Cover {Obj : Type} [Category Obj] (U : Obj)
  := ∀ {V : Obj} (_f : V ⟶ U), Prop

-- A cover defined by a set of morphisms from a single source.
def single_source_cover {Obj : Type} [Category Obj] {U V : Obj} (P : (V ⟶ U) → Prop) : Cover U
  := fun {V'} (f : V' ⟶ U) ↦ ∃ (p : V = V'), match p with | Eq.refl V => P f

def InCover {Obj : Type} [Category Obj] {U : Obj} (cover : Cover U) (V : Obj) : Prop
  := ∃ (f : V ⟶ U), cover f

inductive Lift (P : Prop) : Type where
| lift (p : P) : Lift P

class Site (Obj : Type) [Category Obj] where
  -- A set of covers for each object in C.
  coverage : ∀ {U : Obj}, Cover U → Prop
  -- Every isomorphism is a cover in itself.
  identity : ∀ {U V : Obj} (iso : Iso V U),
    coverage (single_source_cover (fun f ↦ f = Iso.hom iso))
  -- Transitivity/composition of covers.
  compose :
    ∀ {U : Obj} (u_cover : Cover U), coverage u_cover →
    ∀ (v_covers : ∀ {V : Obj}, InCover u_cover V → Cover V),
    (∀ {V} (v_in_cover : InCover u_cover V), coverage (v_covers v_in_cover)) →
    -- A morphism is in the composed cover if it is the composition
    -- of a morphism in the cover {g : Wᵢⱼ → Vᵢ) and a morphism in the
    -- cover {h : Vᵢ → U}.
    coverage (fun {W} (f : W ⟶ U) ↦
      ∃ (V : Obj) (h : V ⟶ U) (g : W ⟶ V),
      (h_in_cover : u_cover h) → v_covers (Exists.intro h h_in_cover) g →
      f = CategoryStruct.comp g h)
  pullback_exists :
    ∀ {U : Obj} (u_cover : Cover U), coverage u_cover →
    ∀ {V : Obj} (f : V ⟶ U), u_cover f →
    ∀ {W : Obj} (g : W ⟶ U),
    Σ (Pb : Obj) (fst : Pb ⟶ V) (snd : Pb ⟶ W), Lift (IsPullback fst snd f g)
  pullbacks_cover :
    ∀ {U : Obj} (u_cover : Cover U) (cv : coverage u_cover)
    {W : Obj} (g : W ⟶ U),
    coverage (fun {Y} f ↦
      ∃ (V : Obj) (h : V ⟶ U),
      ∀ (uch : u_cover h),
      ∀ (pf : Sigma.fst (pullback_exists u_cover cv h uch g) = Y),
      match pf with
      | Eq.refl _ =>
          f = Sigma.fst (Sigma.snd (Sigma.snd (pullback_exists u_cover cv h uch g))))
