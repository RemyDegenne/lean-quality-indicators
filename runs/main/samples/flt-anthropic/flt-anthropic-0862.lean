namespace P2MW.S_CerednikDrinfeld_Omega_exists_fin_ballEdges

set_option autoImplicit false

open scoped MatrixGroups

open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

namespace BallEdgesL2

variable {R : Type} [CommRing R] (K₀ : Type) [Field K₀] [Algebra R K₀] (ϖ₀ : R)

theorem blist_nodup [Finite (R ⧸ Ideal.span {ϖ₀})] (n : ℕ) (hπ : algebraMap R K₀ ϖ₀ ≠ 0)
    (hinj : Function.Injective (algebraMap R K₀)) : (blist K₀ ϖ₀ n).Nodup := by
  rw [blist, List.nodup_flatten]
  constructor
  · intro l hl
    obtain ⟨i, -, hil⟩ := List.mem_map.1 hl
    rw [← hil]
    exact (nodup_qlist ϖ₀ (i + 1)).map (entry_injective K₀ ϖ₀ n (i + 1) hπ hinj)
  · rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp ?_
    intro i j hij x hx hy
    obtain ⟨q, -, hqx⟩ := List.mem_map.1 hx
    obtain ⟨q', -, hq'⟩ := List.mem_map.1 hy
    have := congrArg Prod.snd (hq'.trans hqx.symm)
    simp only [entry] at this
    omega

end BallEdgesL2
end P2MW.S_CerednikDrinfeld_Omega_exists_fin_ballEdges
