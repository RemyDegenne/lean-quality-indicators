public section

namespace CFSG.ComponentClassification.GMS78.RuN

open Subgroup CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuN

open CFSG.ComponentClassification.GMS78.RuSimCode CFSG.CosetTable

open CFSG.ComponentClassification.GMS78.RuPi7 CFSG.ComponentClassification.GMS78.RuAsm

local instance : Std.Associative (α := Fin 8) (· ^^^ ·) := ⟨by decide⟩

local instance : Std.Commutative (α := Fin 8) (· ^^^ ·) := ⟨by decide⟩

section Cert

theorem exists_linApply_eq {t t' : Fin 8} (ht : t ≠ 0) (ht' : t' ≠ 0) :
    ∃ s ∈ glList, linApply s t = t' := by
  have h := Certificates.certificate15109.2.2.2.1
  simp only [nFaithCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_finRange,
    Bool.or_eq_true, beq_iff_eq, forall_const] at h
  rcases h.2 t t' with (h0 | h0) | ⟨s, hs, e⟩
  · exact absurd h0 ht
  · exact absurd h0 ht'
  · exact ⟨s, hs, e⟩

end Cert
end CFSG.ComponentClassification.GMS78.RuN
end
