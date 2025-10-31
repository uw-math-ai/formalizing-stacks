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

@[simp]
def coverings (X : Cat) : Set (Precover X) := {
  cov |
    ∀ ov ∈ cov, ∃ _h : FullyFaithful (Functor.ofCatHom ov.hom), true
  }

@[simp]
def iso {X Y : Cat} (hom : Y ⟶ X) (h_is_iso : IsIso hom) : {Over.mk hom} ∈ coverings X := by
  -- Since Y ⟶ X is a functor between Y and X
  -- and Y ⟶ X is isomorphic,
  -- then there is an equivalence between Y and X
  let F     := Functor.ofCatHom hom
  let F_inv := (Functor.ofCatHom <| inv hom)

  let obj     := F.obj
  let obj_inv := F_inv

  unfold coverings
  simp
  apply Nonempty.intro

  let iso_under : Equivalence Y X := Cat.equivOfIso (asIso hom)

  let h_equiv_F     : iso_under.functor = F     := rfl
  let h_equiv_F_inv : iso_under.inverse = F_inv := rfl

  change FullyFaithful (Functor.ofCatHom hom)

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

      simp at iso_X_A_id
      simp at iso_X_B_id

      apply CategoryStruct.comp iso_X_A_id.hom
      apply CategoryStruct.comp h
      apply CategoryStruct.comp iso_X_B_id.inv
      exact CategoryStruct.id B

    map_preimage {A B} hom := by
      simp

      let h : F_inv.obj (F.obj A) ⟶ F_inv.obj (F.obj B) :=
        obj_inv.map hom

      have iso_X_B_id : (B ≅ (F ⋙ F_inv).obj B) :=
        iso_under.unitIso.app B

      change (F.map (iso_under.unitIso.hom.app A)
        ≫ F.map (F_inv.map hom) ≫ F.map (iso_under.unitIso.inv.app B) = hom)

      simp_all
--
      let h_comp_id :
        (F.map (iso_under.unitIso.hom.app A)
          ≫ iso_under.counitIso.hom.app (F.obj A)
        = 𝟙 (F.obj A)) := iso_under.functor_unitIso_comp A

      let hom_eq_comp_id : hom = (𝟙 (F.obj A)) ≫ hom := by
        simp_all only [Category.id_comp, F]

      simp at h_comp_id

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
    preimage_map := sorry
  }

instance instSiteCat : @Site Cat _ instPullbacksCat where
  -- In the coverings if the functor is bijective
  coverings := coverings
  iso := iso
  trans {X} cov₀ is_covering h_mk_cov := fun ov h_ov => by
    simp at h_ov
    have ⟨f, ⟨f_in_cov₀, ⟨g, ⟨g_in_precov', h_ov_eq⟩⟩⟩⟩ := h_ov
    simp_all

    let precov'  := (h_mk_cov f f_in_cov₀).val
    let property : ∀ ov ∈ precov', IsIso ov.hom := (h_mk_cov f f_in_cov₀).property

    have f_iso : IsIso f.hom := is_covering f f_in_cov₀
    have g_iso : IsIso g.hom := property g g_in_precov'

    have h_g_in_precov' : g ∈ precov' := by
      change (h_mk_cov f f_in_cov₀).val g
      exact g_in_precov'

    have over_comp_in_coverings : {Over.mk (g.hom ≫ f.hom)} ∈ coverings X := by
      simp
      apply CategoryTheory.IsIso.comp_isIso

    rw [← h_ov_eq]
    rw [Over.mk_hom]

    unfold coverings at over_comp_in_coverings
    simp at over_comp_in_coverings

    exact over_comp_in_coverings
  pullback {X} ov precov precov_is_covering := by
    simp
    intro a in_precov
    simp at precov_is_covering

    let h_a_iso : IsIso a.hom := precov_is_covering a in_precov

    let fst : pullback a.hom ov.hom ⟶ a.left  := pullback.fst a.hom ov.hom
    let snd : pullback a.hom ov.hom ⟶ ov.left := pullback.snd a.hom ov.hom

    let left  : a.left  ⟶ X      := a.hom
    let right : ov.left ⟶ X      := ov.hom

    let ov_left_a  : ov.left ⟶ a.left  := ov.hom ≫ inv a.hom
    let id_ov_left : ov.left ⟶ ov.left := CategoryStruct.id ov.left

    let hom_a_pullback : ov.left ⟶ pullback a.hom ov.hom := pullback.lift ov_left_a id_ov_left

    constructor
    use hom_a_pullback
    constructor
    apply CategoryTheory.Limits.pullback.hom_ext
    simp
    
    sorry


