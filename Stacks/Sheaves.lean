import Mathlib
import Stacks.Site2Mathlib

open CategoryTheory
open CategoryTheory.Limits

abbrev Presheaf.{u, v} (C : Type v) [Category.{u, v} C]:=
  Cᵒᵖ ⥤ (Type v)

class Sheaf.{u, v, m, n} (C : Type v) (S : Type n)
  [Category.{u, v} C] [Category.{m, n} S] [HasPullbacks C] [h_site : Site'.{u, v} C] where
  pre : Presheaf.{u, v} C
  elem_families (U Ui : C) (f : Ui ⟶ U)
    (in_cov : Presieve.singleton f ∈ h_site.coverings U) : pre.obj (.op Ui)
  family_pairs_comp_eq (U Uj Uk : C) (p_j : Uj ⟶ U) (p_k : Uk ⟶ U)
    (in_cov_f : Presieve.singleton p_j ∈ h_site.coverings U)
    (in_cov_g : Presieve.singleton p_k ∈ h_site.coverings U)
    (K : C) (f : K ⟶ Uj) (g : K ⟶ Uk)
    (comp_eq : f ≫ p_j = g ≫ p_k) :
      pre.map (.op f) (elem_families U Uj p_j in_cov_f) =
        pre.map (.op g) (elem_families U Uk p_k in_cov_g)
  unique_map (U Ui : C) (f : Ui ⟶ U)
    (in_cov : Presieve.singleton f ∈ h_site.coverings U)
    (s : pre.obj (.op U))
    : (pre.map (.op f) s) = (elem_families U Ui f in_cov) ∧
      (@default (pre.obj (.op U)) (Inhabited.mk s) = s)

