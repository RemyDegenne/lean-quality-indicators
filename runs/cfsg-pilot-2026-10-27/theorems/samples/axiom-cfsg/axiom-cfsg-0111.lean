public noncomputable section

namespace CFSG.Quasithin.H13.Tits614

open CFSG.Sporadic.Schreier.Tits CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.ChainArrays

open scoped commutatorElement

theorem mem_titsE614_iff_inE
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) :
    inE a = true ↔ g ∈ titsE614 := by
  rw [mem_titsE614_iff_eProd]
  constructor
  · intro h
    obtain ⟨c, hc, hcg⟩ := exists_mem_of_anyEq614 h ha
    obtain ⟨v, hv, rfl⟩ := mem_eArrs.mp hc
    exact ⟨v, hv, (eProd_rep v).unique hcg⟩
  · rintro ⟨v, hv, rfl⟩
    rw [inE, anyEq, List.any_eq_true]
    exact ⟨eProdArr v, mem_eArrs.mpr ⟨v, hv, rfl⟩, (eqA_iff ha (eProd_rep v)).mpr rfl⟩

end CFSG.Quasithin.H13.Tits614
end
