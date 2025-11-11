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
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Stacks.Site
import Stacks.Examples.Cat.Basic
import Stacks.Examples.Cat.Instances

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor

def pb {X : Cat} (ov : Over X) (precov : Precover X) (precov_is_covering : precov ∈ coverings X) :
  { Over.mk (pullback.snd g.hom ov.hom) | g ∈ precov } ∈ coverings ov.left := by
  let precov_is_covering₀ := precov_is_covering

  unfold coverings at *
  intro a

  simp

  -- Every x : X has an over in the precov
  -- whose respective functor is surjective

  -- ov.hom.obj gives us the specific X
  -- we don't really have a way to say that
  -- ov is specifically surjective
  -- since it's not guaranteed to be in the precover
  -- it's just some Over X
  -- but we can just pick any over (ov') that WOULD be in the precov
  -- then we have that every object has a mapping from X back to ov'
  -- but not necessarily the homs
  -- just the objects
  -- this is nice, since the pullback says that
  -- fst ≫ f = snd ≫ g
  -- so therefore, we can also retrieve an object in the preimage of ov ⟶ X

  -- a is a nice candidate
  -- because then we get that ov'.left = ov.left in some respect

  let ⟨ov', in_precov, ⟨y, y_def_eq⟩⟩ := precov_is_covering (ov.hom.obj a)

  let left  := ov'.hom
  let right := ov.hom

  -- see now ov'.hom.obj y = ov.hom.obj a
  -- or at least ov'.left ≅ ov.left
  -- ov'.hom.obj is a particular object in the category
  -- ov'.left
  have hom_ov'_ov_iso : ov'.hom.obj y ≅ ov.hom.obj a := {
    hom := by
      rw [y_def_eq]
      exact CategoryStruct.id ov.hom.obj a
    inv := by
      rw [y_def_eq]
      exact CategoryStruct.id ov.hom.obj a
  }

  -- we essentially need to show
  -- that there is something in
  -- the preimage for for P ⟶ ov.left
  -- which is the same as the final x
  -- we need to somehow extract
  -- the preimage for the specific a
  -- but we don't know there is a precov
  -- containing the pullback in the coverings
  -- ov'.left is a category

  -- ov is also in the coverings
  -- due to y_def_eq

  have h_ov_in_coverings : {ov} ∈ coverings X := by
    simp [coverings]
    intro x
    have ⟨ov'', in_precov, ⟨z, z_def_eq⟩⟩ := precov_is_covering (ov.hom.obj a)
    rw [← z_def_eq]
    use a
    rw [y_def_eq]
    sorry

  use ov'
  exact ⟨in_precov, by
    constructor
    case h =>
      apply CategoryTheory.Functor.congr_obj
    
  ⟩

