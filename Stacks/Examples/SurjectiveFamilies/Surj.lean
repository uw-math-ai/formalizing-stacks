import Stacks.Site

abbrev JointlySurjective.{u} {Y : Type u} (U : Precover Y)
  := ∀ y : Y, ∃ f ∈ U, ∃ x : f.left, y = f.hom x
