import Mathlib
import Stacks.Site2Mathlib

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Presieve

-- A presheaf is usually a functor from the opposite category of C to Set.
-- In Lean, we use Type v to denote Set.
abbrev Presheaf.{u, v} (C : Type v) [Category.{u, v} C] :=
  Cᵒᵖ ⥤ (Type v)

def IsSheaf.{u, v} (C : Type v)
  [Category.{u, v} C] [HasPullbacks C] [h_site : Site'.{u, v} C]
  (F : Presheaf C) := ∀ (U : C) (pre : Presieve U)
    (_in_cov : pre ∈ h_site.coverings U)
    (fam : FamilyOfElements F pre)
    (_comp : fam.Compatible),
    ∃! s : (F.obj (.op U)),
      ∀ (Ui : C)
      (hom : Ui ⟶ U)
      (in_cov : hom ∈ @pre Ui), fam hom in_cov = F.map (.op hom) s

