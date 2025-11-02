import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.Tactic.ApplyFun
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Stacks.Site
import Stacks.Examples.Cat.Instances

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor

def coverings (X : Cat) : Set (Precover X) := {
    cov | ∀ (x : X), ∃ (ov : Over X) (_h : ov ∈ cov) (y : ov.left), (ov.hom).obj y = x
  }

def iso {X Y : Cat} (hom : Y ⟶ X) (h_is_iso : IsIso hom) : {Over.mk hom} ∈ coverings X := by
  -- Since Y ⟶ X is a functor between Y and X
  -- and Y ⟶ X is isomorphic,
  -- then there is an equivalence between Y and X
  let F     := hom
  let F_inv := inv hom

  let obj     := F.obj
  let obj_inv := F_inv

  simp [coverings, Set.mem_singleton_iff]
  intro x
  use F_inv.obj x
  rw [← CategoryTheory.Functor.comp_obj]

  let iso_under : Equivalence Y X := Cat.equivOfIso (asIso hom)

  -- The equivalence says Functor.comp F F_inv
  -- is isomorphic to the identity

  rw [← CategoryTheory.Cat.comp_eq_comp]
  change ((asIso hom).inv ≫ (asIso hom).hom).obj x = x
  simp

def comp {X : Cat} (cov₀ : Precover X) (is_covering : cov₀ ∈ coverings X)
  (h_mk_cov : (f : Over X) → f ∈ cov₀ → { cover // cover ∈ coverings f.left}) :
  { Over.mk (g.hom ≫ f.hom) |
    (f : Over X) (hf : f ∈ cov₀) (g ∈ (h_mk_cov f hf).val) } ∈ coverings X := by
  simp [coverings] at *
  intro x

  unfold coverings at h_mk_cov

  let ⟨ov, in_cov, y, h_surj⟩ := is_covering x

  let val      := (h_mk_cov ov in_cov).val
  let property := (h_mk_cov ov in_cov).property

  let ⟨ov', in_val, ⟨ov_left, y_eq_ov_left⟩⟩ := property y


  use Over.mk (ov'.hom ≫ ov.hom)
  constructor
  case h.left =>
    use ov
    use in_cov
    use ov'
  case h.right =>
    rw [Over.mk_hom]
    use ov_left
    trans
    exact CategoryTheory.Functor.comp_obj ov'.hom ov.hom ov_left
    rw [y_eq_ov_left, h_surj]

