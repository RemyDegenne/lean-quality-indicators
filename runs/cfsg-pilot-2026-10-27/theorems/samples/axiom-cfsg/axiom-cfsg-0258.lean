public section

namespace CFSG.Quasithin.VolI

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13

open scoped commutatorElement

namespace E54

theorem pCore_two_quotient_eq_bot {H : Type*} [Group H] :
    CFSG.pCore 2 (H ⧸ CFSG.pCore 2 H) = ⊥ := by
  set Q := CFSG.pCore 2 H with hQ
  set O := CFSG.pCore 2 (H ⧸ Q) with hO
  set π := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hK : IsPGroup 2 ↥(O.comap π) := by
    refine (CFSG.pCore_isPGroup (p := 2) (G := H ⧸ Q)).comap_of_ker_isPGroup π ?_
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup (p := 2) (G := H)
  have hKn : (O.comap π).Normal := (inferInstance : O.Normal).comap π
  have hKQ : O.comap π ≤ Q := le_sSup ⟨hKn, hK⟩
  rw [eq_bot_iff]
  calc O = (O.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπs O).symm
    _ ≤ Q.map π := Subgroup.map_mono hKQ
    _ = ⊥ := QuotientGroup.map_mk'_self Q

end E54
end CFSG.Quasithin.VolI
end
