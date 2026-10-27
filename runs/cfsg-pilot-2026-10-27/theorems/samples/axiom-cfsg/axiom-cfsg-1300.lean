public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126FE S126L22F Equiv

namespace S126L28

open S8E S8F

variable {B : Subgroup (Perm (Fin 8))}

theorem fixD_pair_ne (hE : ∀ σ ∈ B, σ * σ = 1) {ps : List (Perm (Fin 8))}
    (hps : ∀ p ∈ ps, p ∈ B) {b c : Perm (Fin 8)} (hbB : b ∈ B) (hcB : c ∈ B) {u : List Nat}
    (h : SepW [L b, L c] (ps.map L) u) :
    cls u (h.1) ∈ fixD (Subgroup.closure ({b, c} : Set (Perm (Fin 8)))) ∧
      cls u (h.1) ∉ fixD B := by
  obtain ⟨hu, hfix, hsep⟩ := h
  refine ⟨mem_fixD_closure fun s hs => ?_, not_mem_fixD hE hps hu hsep⟩
  rcases hs with rfl | rfl
  · exact fix_cls (hE s hbB) hu (hfix _ (by simp))
  · exact fix_cls (hE s hcB) hu (hfix _ (by simp))

end S126L28
end CFSG.Quasithin.H13
end
