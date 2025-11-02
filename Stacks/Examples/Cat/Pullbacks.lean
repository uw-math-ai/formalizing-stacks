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
import Stacks.Examples.Cat.Basic
import Stacks.Examples.Cat.Instances

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor

def pb {X : Cat} (ov : Over X) (precov : Precover X) (precov_is_covering : precov ∈ coverings X) :
  { Over.mk (pullback.snd g.hom ov.hom) | g ∈ precov } ∈ coverings ov.left := by
  intro a in_precov
  simp at in_precov

  let ⟨g, h_in_precov, h_def_eq⟩ := in_precov
  have ⟨g_faithful, _⟩ := precov_is_covering g h_in_precov

  simp

  let fst : pullback g.hom ov.hom ⟶ g.left  := pullback.fst g.hom ov.hom
  let snd : pullback g.hom ov.hom ⟶ ov.left := pullback.snd g.hom ov.hom

  let left  : g.left  ⟶ X      := g.hom
  let right : ov.left ⟶ X      := ov.hom

  let left_F  := Functor.ofCatHom left
  let right_F := Functor.ofCatHom right

  -- g.hom is fully faithful, so it has an inverse
  -- that is, there is a direct equivalence between
  -- the moprhisms in the image
  -- and those in the preimage
  -- We cannot create a functor from X to g.left
  -- because we don't have a mapping between
  -- objects.
  -- furthermore, we don't have a morphism from X to g.left
  -- However, we have a morphism from the pullback to ov.left
  -- which means we have a morphism from the pullback to X
  -- so therefore, that morphism is fully faithful
  -- hopefully.

  -- Our goal is Nonempty (FullyFaithful (pullback.snd g.hom ov.hom))
  -- pullback.snd : pullback ⟶ ov.left
  -- so we have to show taht every morphism in ov.left
  -- has an equivalent moprhism in pullback
  -- Nice theorem: CategoryTheory.Functor.FullyFaithful.over
  -- Since g is fully faithful,
  -- then the functor from g (Over X) to X is fully faithful

  rw [← h_def_eq]
  rw [Over.mk_hom]

  apply Nonempty.intro

  -- It might help to prove that fst is
  -- fully faithful
  -- this doesn't necessarily help with fst
  -- we'll get to that later

  -- if we have any pair
  -- of homs in pullback
  -- then we can say they are equivalent
  -- with FullyFaithful.map_injective
  -- let hom₁ ∈ pullback
  -- and let hom₂ ∈ pullback
  -- if g.map hom₁ = g.map hom₂
  -- then hom₁ = hom₂
  -- to say fst is fully faithful
  -- we just have to map a hom in g
  -- to a hom in pullback
  -- and show that g.map preimage = f
  -- and the other way around
  -- we can probably do this with map.injective

  -- One strategy we could do
  -- is use the comp constructor
  -- since g ∈ precov ∈ coverings X
  -- we can probbably use trans
  -- to show that Over.mk pullback.fst ≫ g.hom
  -- is fully faithful therefore
  -- and then we can use fullyfaithful.ofComp
  -- to show that fst is fully faithful

  -- Note that since g.hom is fully faithful
  -- then we can use pullback.lift
  -- since we can map a morphism
  -- in X to a morphism in g
  -- and we can compose ov to get to X
  -- so we can recover a pullback
  -- where the point is g
  -- This seems like potentially a dead end
  -- because the only Z we could choose for
  -- pullback.lift is g
  -- and even then we can't make a hom from X to g and ov to G
  -- we also have no way of setting f and g to actual f and g
  -- because there is no point that goes back to ov
  -- I guess we could choose ov as W
  -- and X and Y as G and X
  -- so then the homs are
  -- G ⟶ X and X ⟶ X?
  -- this really doesn't say much though
  -- now that I think about it, we can make a fully faithful with ov
  -- since ov has a preimage in G
  -- but we don't have a hom from G to ov
  -- are there any other pullbacks we can make?
  -- any shared W ⟶ X and W ⟶ Y?
  -- I guess g is the pullback of ov and X?
  -- but even then we don't actually have a hom back to G

  -- Note that limits.pullbackSymmetry
  -- gives us some kind of equivalnece
  -- between fst and snd
  -- so we can kind of "swap" fst and snd
  -- so by proving that snd (going to g.left)
  -- is fully faithful,
  -- then we have done it for fst

  -- we can make another pullbback whose points are P and G
  -- and the pullback is X
  have pullback' := pullback g.hom (fst ≫ g.hom)
  have fst' := pullback.fst g.hom (fst ≫ g.hom)
  have snd' := pullback.snd g.hom (fst ≫ g.hom)

  simp at fst'
  simp at snd'

  have pullback_direction_iso : pullback g.hom ov.hom ≅ pullback ov.hom g.hom :=
    pullbackSymmetry left right

  -- since the two pullbacks are isomorphic
  -- then it suffices to prove pullbback.fst is fully faithful
  -- we can probably do this with .ofCompFaithful
  -- but then we still need to show there is a preimage in P
  -- given X

  -- It seems like we will have to use our comp
  -- constructor to do some assistance here
  -- we can show that the Over.mk is in the coverings
  -- and therefore that the composition of fst and left
  -- is fully faithful

  have h_full_snd : Full fst := {
    map_surjective {x y} := by
      -- x and y are points in the pullbabck
      simp [Function.Surjective]
      intro hom

      -- hom is in ov.left
      -- so we can now get a hom in X

      let hom_x   := g.hom.map hom

      -- since we have the preimage property
      -- we can also get one in g
      let hom_g := g_faithful.preimage hom_x

      
      sorry
  }

  exact {
    preimage {x y} hom_pre := by
      rw [Over.mk_left] at x
      rw [Over.mk_left] at y
      
      sorry
  }
