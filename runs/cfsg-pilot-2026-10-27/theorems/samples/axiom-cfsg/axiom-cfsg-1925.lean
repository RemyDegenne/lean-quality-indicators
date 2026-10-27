public section

namespace CFSG.Quasithin.X1469.Blk

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.ModF CFSG.Quasithin.ModV
  CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {I S Iz K₁ K₂ : Subgroup G} {P : AppC.A5Pi K₁} {p : Fin 5} (X : Ctx I S Iz K₁ K₂ P p)

include X

theorem fix_E : ∀ e ∈ Esub K₁ Iz, (∀ y ∈ K₁ ⊓ Iz, e * y * e⁻¹ * y⁻¹ ∈ Zsub S K₁) →
    e ∈ Zsub S K₁ := by
  intro e he h
  obtain ⟨heU, hep⟩ := X.mem_E_iff.mp he
  refine X.mem_Z_iff.mpr ⟨heU, ?_⟩
  by_contra hne
  obtain ⟨hne0, hne1⟩ := not_or.mp hne
  obtain ⟨σ, hσs, hσp, h1, h2⟩ :=
    exists_not_line p _ ((mem_evenWeight_iff _).mp (P.toPiData.bf e).2) hep hne0 hne1
  obtain ⟨y, hy, hpfy⟩ := X.exists_lift_Y hσs hσp
  obtain ⟨-, hz⟩ := X.mem_Z_iff.mp (h y hy)
  rw [X.cfg.bf_comm P heU hy.1, hpfy] at hz
  rcases hz with hz | hz
  · exact h1 hz
  · exact h2 hz

end Ctx
end CFSG.Quasithin.X1469.Blk
end
