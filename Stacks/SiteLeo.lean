import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Topology.Sets.Opens

open CategoryTheory
open CategoryTheory.Limits


structure Precover₂.{u, v} {C : Type v} [Category.{u, v} C] (X : C) where
  I : Type
  obj : I → C
  hom (i : I) : (obj i) ⟶ X

--given a morphism Y → X, construct the precover {Y → X}
def SingletonPrecover.{u, v} {C : Type v} [Category.{u, v} C] {X Y : C} (f : Y ⟶ X) : Precover₂ X :=
{
  I := ULift Unit
  obj _ := Y
  hom _ := f
}

--given a precover {X_i → X} and precovers {X_ij → X_i} for all i,
--construct the precover {X_ij → X}
def CompPrecover.{u, v} {C : Type v} [Category.{u, v} C] {X : C} (U : Precover₂ X)
  (V : ∀ i : U.I, Precover₂ (U.obj i)) : Precover₂ X :=
{
  I := (i : U.I) × (V i).I
  obj i := (V i.1).obj i.2
  hom i := ((V i.1).hom i.2) ≫ U.hom i.1
}

--given a precover {X_i → X} and a morphism Y → X, construct the
--precover {Y_i → X}, where Y_i is the fiber product of X_i and Y over X
noncomputable
def PullbackCover.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks C] {X : C}
  (U : Precover₂ X) {Y : C} (f : Y ⟶ X) : Precover₂ Y :=
{
  I := U.I
  obj i := pullback (U.hom i) f
  hom i := pullback.snd (U.hom i) f
}

structure Site₂.{u, v} (C : Type v) [Category.{u, v} C] [HasPullbacks C] where
  coverings (X : C) : Set (Precover₂ X)
  iso {X Y : C} {f : Y ⟶ X} : IsIso f → SingletonPrecover f ∈ coverings X
  trans {X : C} {U : Precover₂ X} (hU : U ∈ coverings X) {V : ∀ i : U.I, Precover₂ (U.obj i)} :
    ∀ i, V i ∈ coverings (U.obj i) → CompPrecover U V ∈ coverings X
  pullback {X : C} {U : Precover₂ X} (hU : U ∈ coverings X) {Y : C} (f : Y ⟶ X) :
    PullbackCover U f ∈ coverings Y

--the Cover structure needs to be defined after the Site structure
structure Cover.{u, v} {C : Type v} [Category.{u, v} C] [HasPullbacks C] (S : Site₂ C)
  (X : C) extends Precover₂ X where
  cover U : U ∈ S.coverings X
