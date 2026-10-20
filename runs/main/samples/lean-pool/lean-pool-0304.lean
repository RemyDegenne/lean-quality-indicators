@[expose] public section

open Metric Set

namespace Schoenflies

open Plane

namespace PolyArc

variable {n : ℕ} (A : PolyArc n) (i j : ℕ) (c t s : ℝ)

variable {A i j c t s}

theorem trimmed_subset_edge {lam : ℝ} (hlam : 0 < lam) : A.trimmed i lam ⊆ A.edge i := by
  rintro _ ⟨c, hc, rfl⟩
  exact pt_mem_edge ⟨le_trans hlam.le hc.1, le_trans hc.2 (by linarith)⟩

end PolyArc
end Schoenflies
end
