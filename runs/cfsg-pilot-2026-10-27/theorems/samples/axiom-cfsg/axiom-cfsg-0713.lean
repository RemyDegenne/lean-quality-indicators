public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129KN2

open Sec4

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem pow_qSubPi_eq_one_of_mem (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {M : GL (Fin 3) K}
    (hM : M ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ}) :
    M ^ qSubPi π (p ^ f) = 1 := by
  obtain ⟨x, y, hx, hy, rfl⟩ := exists_torusHom_of_mem hK hq hτ hτ1 hM
  rw [← map_pow, Prod.pow_mk, hx, hy]
  exact map_one _

end Hering129KN2
end CFSG.RankThree.PartTwo.Sec12
end
