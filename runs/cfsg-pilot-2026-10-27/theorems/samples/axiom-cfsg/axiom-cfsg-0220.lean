public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.ABGLocalTools

open CFSG.Open

open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

namespace Pre49

variable {A T S Q H : Subgroup X}

variable {N : Subgroup X} [N.Normal]

theorem not_le_quotient (p : Pre49 A T S Q H) (hN : N = (CFSG.oddCore A).map A.subtype) :
    ¬ A.map (QuotientGroup.mk' N) ≤ H.map (QuotientGroup.mk' N) := by
  intro hle
  apply p.not_le
  intro a ha
  have h1 : a ∈ H ⊔ N := mk_mem_map_iff.mp (hle (Subgroup.mem_map_of_mem _ ha))
  have hNH : N ≤ H := by rw [hN]; exact p.oddCore_le
  rwa [sup_eq_left.mpr hNH] at h1

end Pre49
end CFSG.ComponentClassification.AschbacherTheorem3
end
