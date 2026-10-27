public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem u62DistOK_spec {n : ℕ} {O : Array (Array ℕ)} (h : Native.u62DistOK n O = true) :
    O.size = n ∧ (∀ R ∈ O, Native.validM R = true) ∧
      ∀ i < n, ∀ k < i, O.getD i #[] ≠ O.getD k #[] := by
  rw [Native.u62DistOK, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨beq_iff_eq.1 h1, Array.all_eq_true_iff_forall_mem.1 h2, fun i hi k hk => ?_⟩
  exact bne_iff_ne.1 (List.all_eq_true.1 (List.all_eq_true.1 h3 i (List.mem_range.2 hi)) k
    (List.mem_range.2 hk))

end CFSG.Sporadic.Co2Smith
end
