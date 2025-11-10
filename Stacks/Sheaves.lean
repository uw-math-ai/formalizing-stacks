import Mathlib
import Stacks.Site2Mathlib

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Presieve

abbrev Presheaf.{u, v} (C : Type v) [Category.{u, v} C]:=
  Cᵒᵖ ⥤ (Type v)

def Sheaf.{u, v} (C : Type v)
  [Category.{u, v} C] [HasPullbacks C] [h_site : Site'.{u, v} C]
  (F : Presheaf.{u, v} C) := ∀ (U : C) (pre : Presieve U)
    (in_cov : pre ∈ h_site.coverings U)
    (Uj Uk K : C)
    (p_j : Uj ⟶ U)
    (p_k : Uk ⟶ U)
    (f : K ⟶ Uj)
    (g : K ⟶ Uk)
    (in_cov_j : p_j ∈ @pre Uj)
    (in_cov_k : p_k ∈ @pre Uk)
    (comp_eq : f ≫ p_j = g ≫ p_k)
    (fam : FamilyOfElements F pre)
    (fam_eq : F.map (.op f) (fam p_j in_cov_j) =
      F.map (.op g) (fam p_k in_cov_k)),
    ∀ (Ui : C)
    (hom : Ui ⟶ U)
    (in_cov : hom ∈ @pre Ui), ∃! s : (F.obj (.op U)), fam hom in_cov = F.map (.op hom) s
