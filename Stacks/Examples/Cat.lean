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

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor

/-
Cat forms a site, where bijections between morphisms. Specifically the
  functors given by the morphisms are fully faithful.
  satisfy the "iso" property.
Since Cat also has limits of every shape, it should also have pullbacks?
  Thereby satisfying the "pullback" property.
Furthermore, functors compose, so the trans property should also be fulfilled.
-/

instance instCategoryCat.{v, u} : Category.{max v u, (max v u) + 1} Cat.{v, u} := by
  have h := Cat.category.{v, u}
  unfold LargeCategory at h
  exact h

instance instPullbacksCat : @HasPullbacks.{0, 1} Cat.{0, 0} instCategoryCat.{0, 0} := by
  have h : HasLimitsOfShape WalkingCospan Cat :=
    @HasLimits.has_limits_of_shape.{0, 1} Cat.{0, 0} _ Cat.instHasLimits.{0} WalkingCospan _
  unfold HasPullbacks
  exact h

def coverings (X : Cat) : Set (Precover X) := {
  cov |
    ∀ ov ∈ cov, ∃ _h : FullyFaithful ov.hom, true
  }

def iso {X Y : Cat} (hom : Y ⟶ X) (h_is_iso : IsIso hom) : {Over.mk hom} ∈ coverings X := by
  -- Since Y ⟶ X is a functor between Y and X
  -- and Y ⟶ X is isomorphic,
  -- then there is an equivalence between Y and X
  let F     := hom
  let F_inv := inv hom

  let obj     := F.obj
  let obj_inv := F_inv

  unfold coverings
  simp [Set.mem_singleton_iff]
  apply Nonempty.intro

  let iso_under : Equivalence Y X := Cat.equivOfIso (asIso hom)

  let h_equiv_F     : iso_under.functor = F     := rfl
  let h_equiv_F_inv : iso_under.inverse = F_inv := rfl

  change FullyFaithful hom

  -- The equivalence says Functor.comp F F_inv
  -- is isomorphic to the identity

  exact {
    preimage {A B} hom_map := by
      -- Given a hom in X, we should be able to recover a hom in Y
      have h : F_inv.obj (F.obj A) ⟶ F_inv.obj (F.obj B) :=
        obj_inv.map hom_map

      change F.obj A ⟶ F.obj B at hom_map

      -- The identity functor with Y on B is isomoprhic to the composition of our functor
      -- and the inverse
      -- and for A

      have iso_X_A_id := iso_under.unitIso.app A
      have iso_X_B_id := iso_under.unitIso.app B

      rw [h_equiv_F, h_equiv_F_inv] at iso_X_A_id
      rw [h_equiv_F, h_equiv_F_inv] at iso_X_B_id

      apply CategoryStruct.comp iso_X_A_id.hom
      apply CategoryStruct.comp h
      apply CategoryStruct.comp iso_X_B_id.inv
      exact CategoryStruct.id B

    map_preimage {A B} hom := by
      simp

      conv =>
        left
        rw [← Category.assoc]
        left
        change iso_under.functor.map (iso_under.unitIso.hom.app A) ≫
          iso_under.functor.map (iso_under.inverse.map hom)
        simp
        rfl

      rw [Category.assoc]
      conv =>
        left
        right
        change iso_under.counitInv.app (iso_under.functor.obj B) ≫
          iso_under.functor.map (iso_under.unitIso.inv.app B)
        simp
        rfl
      exact Category.comp_id hom
    preimage_map {A B} hom := by
      dsimp

      conv =>
        left
        rw [← Category.assoc]
        left
        change _ ≫ iso_under.inverse.map (iso_under.functor.map hom)
        rw [CategoryTheory.Equivalence.unit_naturality]
        rfl

      simp
  }

def comp {X : Cat} (cov₀ : Precover X) (is_covering : cov₀ ∈ coverings X)
  (h_mk_cov : (f : Over X) → f ∈ cov₀ → { cover // cover ∈ coverings f.left}) :
  { Over.mk (g.hom ≫ f.hom) |
    (f : Over X) (hf : f ∈ cov₀) (g ∈ (h_mk_cov f hf).val) } ∈ coverings X := fun ov h_ov => by
  have ⟨f, ⟨f_in_cov₀, ⟨g, ⟨g_in_precov', h_ov_eq⟩⟩⟩⟩ := h_ov

  let precov'  := (h_mk_cov f f_in_cov₀).val
  let property : ∀ ov ∈ precov',  ∃ _h : FullyFaithful ov.hom, true :=
    (h_mk_cov f f_in_cov₀).property

  have ⟨f_faithful, _⟩ := is_covering f f_in_cov₀
  have ⟨g_faithful, _⟩ := property g g_in_precov'

  have h_g_in_precov' : g ∈ precov' := by
    change (h_mk_cov f f_in_cov₀).val g
    exact g_in_precov'

  have over_comp_in_coverings : {Over.mk (g.hom ≫ f.hom)} ∈ coverings X := by
    unfold coverings
    simp [exists_const_iff]
    apply Nonempty.intro
    apply CategoryTheory.Functor.FullyFaithful.comp
    repeat assumption

  rw [← h_ov_eq, Over.mk_hom]

  unfold coverings at over_comp_in_coverings
  simp at over_comp_in_coverings

  rw [exists_const]

def pb {X : Cat} (ov : Over X) (precov : Precover X) (precov_is_covering : precov ∈ coverings X) :
  { Over.mk (pullback.snd g.hom ov.hom) | g ∈ precov } ∈ coverings ov.left := by
  intro a in_precov
  simp at in_precov

  let ⟨g, h_in_precov, h_def_eq⟩ := in_precov
  have ⟨g_faithful, _⟩ := precov_is_covering g h_in_precov

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

  simp
  rw [← h_def_eq]
  rw [Over.mk_hom]

  apply Nonempty.intro

  -- FullyFaithful has a nice theorem
  -- FullyFaithful.map_inj
  -- if g.map hom₁ = g.map hom₂
  -- then hom₁ = hom₂
  -- 

  sorry

instance instSiteCat : @Site Cat _ instPullbacksCat where
  -- In the coverings if the functor is bijective
  coverings := coverings
  iso := iso
  trans := comp
  pullback := pb


