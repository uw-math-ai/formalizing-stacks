import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic
import Stacks.Site

open CategoryTheory

abbrev JointlySurjective.{u} {Y : Type u} (U : Precover Y)
  := ∀ y : Y, ∃ f ∈ U, ∃ x : f.left, y = f.hom x

def SurjectiveFamiliesSite.{u} : Site (Type u) := {
  coverings X := setOf JointlySurjective
  iso f hf y := Exists.intro (Over.mk f) (And.intro rfl (Exists.intro (inv f y) sorry))
  trans U hU V y := match hU y with
    | Exists.intro w (And.intro hw (Exists.intro x p)) => match V w sorry with
      | Subtype.mk a q => match q x with
        | Exists.intro f (And.intro o (Exists.intro j l)) =>
          Exists.intro (Over.mk (f.hom ≫ w.hom))
            (And.intro (Exists.intro w (Exists.intro hw (by
              constructor
              constructor
              · exact sorry
              · exact sorry
              · exact f
            )))
            (Exists.intro j (by
              rw [p]
              rw [l]
              rfl
            )))
  pullback := sorry
}

#check SurjectiveFamiliesSite.coverings
