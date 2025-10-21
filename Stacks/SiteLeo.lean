import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
open CategoryTheory
open CategoryTheory.Limits

structure Precover {C : Type} [Category C] (X : C) where
  I : Type
  obj : I → C
  hom (i : I) : (obj i) ⟶ X

--given a morphism Y → X, construct the precover {Y → X}
def SingletonPrecover {C : Type} [Category C] {X Y : C} (f : Y ⟶ X) : Precover X :=
{
  I := Unit
  obj _ := Y
  hom _ := f
}

--given a precover {X_i → X} and precovers {X_ij → X_i} for all i,
--construct the precover {X_ij → X}
def CompPrecover {C : Type} [Category C] {X : C} (U : Precover X)
  (V : ∀ i : U.I, Precover (U.obj i)) : Precover X :=
{
  I := (i : U.I) × (V i).I
  obj i := (V i.1).obj i.2
  hom i := ((V i.1).hom i.2) ≫ U.hom i.1
}

--given a precover {X_i → X} and a morphism Y → X, construct the
--precover {Y_i → X}, where Y_i is the fiber product of X_i and Y over X
noncomputable
def PullbackCover {C : Type} [Category C] [HasPullbacks C] {X : C} (U : Precover X) {Y : C} (f : Y ⟶ X)
  : Precover Y :=
{
  I := U.I
  obj i := pullback (U.hom i) f
  hom i := pullback.snd (U.hom i) f
}

structure Site (C : Type) [Category C] [HasPullbacks C] where
  coverings (X : C) : Set (Precover X)
  iso {X Y : C} {f : Y ⟶ X} : IsIso f → SingletonPrecover f ∈ coverings X
  trans {X : C} {U : Precover X} (hU : U ∈ coverings X) {V : ∀ i : U.I, Precover (U.obj i)} :
    ∀ i, V i ∈ coverings (U.obj i) → CompPrecover U V ∈ coverings X
  pullback {X : C} {U : Precover X} (hU : U ∈ coverings X) {Y : C} (f : Y ⟶ X) :
    PullbackCover U f ∈ coverings Y

--the Cover structure needs to be defined after the Site structure
structure Cover {C : Type} [Category C] [HasPullbacks C] (S : Site C) (X : C) extends Precover X where
  cover : U ∈ S.coverings X
