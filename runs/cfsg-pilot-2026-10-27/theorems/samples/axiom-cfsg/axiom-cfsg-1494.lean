public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair

section RootGroup

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

theorem aptRoot_smul_of_adj {t : ZMod (2 * n) → V} {g : D} {k : ℤ}
    (hg : g ∈ aptRoot D Γ n t k) {i : ℤ} (h1 : 1 ≤ i) (h2 : i ≤ (n : ℤ) - 1) {w : V}
    (hw : Γ.Adj (apt t (k + i)) w) : g • w = w :=
  (mem_aptRoot.mp hg) i h1 h2 w hw

end RootGroup
end CFSG.Quasithin.Stroth
end
