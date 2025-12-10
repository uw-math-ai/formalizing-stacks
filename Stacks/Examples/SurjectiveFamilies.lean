import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Stacks.Site

open CategoryTheory
open CategoryTheory.Limits

abbrev JointlySurjective.{u} {Y : Type u} (U : Precover Y)
  := ∀ y : Y, ∃ f ∈ U, ∃ x : f.left, y = f.hom x

namespace JointlySurjective

namespace HasPullbacks

@[simp]
def cone.pt.t_p.{u} (F : WalkingCospan ⥤ Type u) : Type u :=
  (F.obj .left) × (F.obj .right)

@[simp]
def cone_pt.{u} (F : WalkingCospan ⥤ Type u) : Type u := {
  p : cone.pt.t_p F // F.map WalkingCospan.Hom.inl p.fst = F.map WalkingCospan.Hom.inr p.snd }

@[simp]
def π.app.{u} (F : WalkingCospan ⥤ Type u) (span : WalkingCospan) :
  ((Functor.const WalkingCospan).obj (cone_pt F)).obj span ⟶ F.obj span :=
  match span with
  | .left => fun X => by
    simp at X
    exact X.val.fst
  | .right => fun X => by
    simp at X
    exact X.val.snd
  | .one => by
    simp only [Functor.const_obj_obj]
    exact (fun X => X.val.fst) ≫ F.map WalkingCospan.Hom.inl

@[simp]
def π.naturality.{u} (F : WalkingCospan ⥤ Type u)
  ⦃X Y : WalkingCospan⦄
  (f : X ⟶ Y) :
  ((Functor.const WalkingCospan).obj (cone_pt F)).map f ≫ π.app F Y = π.app F X ≫ F.map f := by
  unfold π.app at *
  change WalkingCospan.Hom _ _ at f
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
  cases f
  · rw [CategoryTheory.Limits.WidePullbackShape.hom_id]
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  case term j =>
    cases j
    · rfl
    ext a
    let f_eq : F.map WalkingCospan.Hom.inl a.val.fst = F.map WalkingCospan.Hom.inr a.val.snd :=
      a.property
    simp only [cone_pt, cone.pt.t_p, id_eq, types_comp_apply, f_eq]

@[simp]
def cone.{u} (F : WalkingCospan ⥤ Type u) : Cone F where
  pt := cone_pt F
  π := {
    app := π.app F
    naturality := π.naturality F
  }

@[simp]
def isLimit.lift.{u} (F : WalkingCospan ⥤ Type u) (s : Cone F) (point : s.pt) : (cone F).pt :=
  match s with
  | .mk pt' π' => by
    let map_left := π'.naturality WalkingCospan.Hom.inl
    let map_right := π'.naturality WalkingCospan.Hom.inr
    simp at map_left
    simp only [Functor.const_obj_obj, Functor.const_obj_map,
      map_left, Category.id_comp] at map_right
    refine ⟨⟨π'.app .left point, π'.app .right point⟩, ?_⟩
    change (π'.app WalkingCospan.left ≫ F.map WalkingCospan.Hom.inl) point  =
           (π'.app WalkingCospan.right ≫ F.map WalkingCospan.Hom.inr) point
    rw [map_right]

@[simp]
def isLimit.fac.{u} (F : WalkingCospan ⥤ Type u) (s : Cone F)
  (span : WalkingCospan) : isLimit.lift F s ≫ (cone F).π.app span = s.π.app span := by
  simp only [cone, cone_pt, cone.pt.t_p, Functor.const_obj_obj, π.app, id_eq]
  cases span
  · ext a
    change (s.π.app WalkingCospan.left ≫ F.map WalkingCospan.Hom.inl) a = s.π.app none a
    rw [← s.π.naturality WalkingCospan.Hom.inl]
    simp only [Functor.const_obj_obj, Functor.const_obj_map, types_comp_apply, types_id_apply]
  case some val =>
    cases val
    repeat (ext; simp)

def isLimit.uniq.{u} (F : WalkingCospan ⥤ Type u) (s : Cone F) (m : s.pt ⟶ (cone F).pt)
  (h : (∀ (j : WalkingCospan), m ≫ (cone F).π.app j = s.π.app j)) : m = isLimit.lift F s := by
  ext a
  simp only [lift, cone]
  conv =>
    right
    left
    left
    rw [← h .left]
    rfl
  conv =>
    right
    left
    right
    rw [← h .right]
    rfl
  rfl

def has_limit.{u} : ∀ (x : WalkingCospan ⥤ Type u), HasLimit x := fun F =>
  ⟨⟨{
      cone := cone F
      isLimit := {
        lift := isLimit.lift F
        fac := isLimit.fac F
        uniq := isLimit.uniq F
      }
  }⟩⟩

end HasPullbacks

instance instHasPullbacks.{u} : HasPullbacks (Type u) where
  has_limit := HasPullbacks.has_limit

def SurjectiveFamiliesSite.{u} : Site (Type u) := {
  coverings X := setOf JointlySurjective
  iso {X Y : Type u} (f : Y ⟶ X) (hf : IsIso f) x := by
    exists Over.mk f
    refine ⟨by simp, inv f x, by
      change x = (inv f ≫ f) x
      rw [(CategoryTheory.inv_comp_eq_id f).mpr]
      repeat rfl⟩      
  trans U U_jointly_surjective V y := by
    obtain ⟨ f, f_in_U, x, y_is_f_x ⟩ := U_jointly_surjective y
    obtain ⟨ g, g_in_V_f, z, x_is_g_z ⟩ := (V f f_in_U).property x
    exists (Over.mk (g.hom ≫ f.hom))
    apply And.intro
    · exists f
      exists f_in_U
      exists g
    · exists z
      simp
      rw [y_is_f_x, x_is_g_z]
  pullback f U U_jointly_surjective y := by
    obtain ⟨ g, g_in_U, x, f_y_is_g_x ⟩ := U_jointly_surjective (f.hom y)
    exists Over.mk pullback.snd g.hom f.hom
    apply And.intro
    · exists g
    · exists by
        exists (x, y)
        rw [f_y_is_g_x]
}

end JointlySurjective
