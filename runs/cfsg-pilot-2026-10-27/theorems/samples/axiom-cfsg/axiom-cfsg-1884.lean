public section

namespace CFSG.QuasithinUnique.A6Facts

open Equiv

theorem normData_P0 {r π : P10} {e : List ℕ × List (List ℕ) × List (List ℕ)} (he : e ∈ Core.normData)
    (her : e.1 = code r) :
    code π ∈ e.2.2 ↔ π ∈ P0 ∧ NormKlein r π := by
  have hall := Core.norm_data_ok
  rw [List.all_eq_true] at hall
  have h := hall e he
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [h.2, List.mem_filter, ← mem_P0_iff, her, ← normKlein_iff]

end CFSG.QuasithinUnique.A6Facts
end
