public section

namespace CFSG.Quasithin.H13.L829N

open Matrix

theorem s9c3_ind_rank {E : Type} [Field E] {d : ℕ} {N : Subgroup (GL (Fin d) E)}
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B) (t : N)
    (u : Fin d → E) (hu : u ∈ B) (huA : u ∉ A)
    (hcov : ∀ v : Fin d → E,
      ∃ c : E, ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v = c • u)
    (hT1 : s9cIndHom (s9cOfN hA hB t) ≠ 1) :
    (LinearMap.toMatrix (Module.finBasis E (s9cSub A B)) (Module.finBasis E (s9cSub A B))
        (s9cIndHom (s9cOfN hA hB t)) - 1).rank = 1 := by
  have h1 : LinearMap.toMatrix (Module.finBasis E (s9cSub A B)) (Module.finBasis E (s9cSub A B))
      (s9cIndHom (s9cOfN hA hB t) - 1) = LinearMap.toMatrix (Module.finBasis E (s9cSub A B))
        (Module.finBasis E (s9cSub A B)) (s9cIndHom (s9cOfN hA hB t)) - 1 := by
    rw [map_sub, LinearMap.toMatrix_one]
  rw [← h1, Matrix.rank_eq_finrank_range_toLin _ (Module.finBasis E (s9cSub A B))
    (Module.finBasis E (s9cSub A B)), Matrix.toLin_toMatrix]
  have hSne : s9cIndHom (s9cOfN hA hB t) - 1 ≠ 0 := fun h => hT1 (sub_eq_zero.mp h)
  have hpos : 1 ≤ Module.finrank E (LinearMap.range (s9cIndHom (s9cOfN hA hB t) - 1)) :=
    Submodule.one_le_finrank_iff.mpr (fun h => hSne (LinearMap.range_eq_bot.mp h))
  have hu0 : (Submodule.Quotient.mk (⟨u, hu⟩ : ↥B) : s9cSub A B) ≠ 0 :=
    fun h => huA (Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero
      (A.comap B.subtype)).mp h))
  have hsub : LinearMap.range (s9cIndHom (s9cOfN hA hB t) - 1) ≤
      Submodule.span E {(Submodule.Quotient.mk (⟨u, hu⟩ : ↥B) : s9cSub A B)} := by
    rintro _ ⟨q, rfl⟩
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨c, hc⟩ := hcov (y : Fin d → E)
      have hx : (⟨((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ (y : Fin d → E),
          s9cFlag_mapB (s9cOfN hA hB t) y.2⟩ : ↥B) - y = c • (⟨u, hu⟩ : ↥B) :=
        Subtype.ext hc
      have hy : (s9cIndHom (s9cOfN hA hB t) - 1) (Submodule.Quotient.mk y : s9cSub A B) =
          c • (Submodule.Quotient.mk (⟨u, hu⟩ : ↥B) : s9cSub A B) := by
        rw [← Submodule.Quotient.mk_smul, ← hx, Submodule.Quotient.mk_sub]
        rfl
      rw [hy]
      exact (Submodule.span E _).smul_mem c (Submodule.mem_span_singleton_self _)
  have hle := Submodule.finrank_mono hsub
  rw [finrank_span_singleton hu0] at hle
  exact le_antisymm hle hpos

end CFSG.Quasithin.H13.L829N
end
