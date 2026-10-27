public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion

open Subgroup

open scoped commutatorElement

namespace DihedralTimesTwo

variable {X : Type*} [Group X]

namespace Data

variable {T : Subgroup X} {r u e : X} {n : ℕ}

theorem e_not_mem_D' (h : Data T r u e n) : e ∉ zpowers r ⊔ zpowers (u * e) := by
  intro he
  rcases h.mem_D' he with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact (h.eD i).1 hi
  · apply h.u_not_mem
    have h1 : u * r ^ i = 1 := by
      calc u * r ^ i = u * r ^ i * e * e⁻¹ := by group
        _ = 1 := by rw [← hi, mul_inv_cancel]
    have : u = r ^ (-i) := by
      calc u = u * r ^ i * (r ^ i)⁻¹ := by group
        _ = r ^ (-i) := by rw [h1, one_mul, zpow_neg]
    rw [this]
    exact zpow_mem (mem_zpowers r) _

end Data
end DihedralTimesTwo
end CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion
end
