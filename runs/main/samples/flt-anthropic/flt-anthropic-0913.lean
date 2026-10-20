namespace P2MW.S_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0

open Matrix UpperHalfPlane CongruenceSubgroup

p2m_open_scoped

noncomputable section

namespace ModularForm

p2m_open

p2m_open

variable {M q : ℕ} (W : AtkinLehnerDatum M q)

lemma alSlash_isBoundedAt {k : ℤ} [NeZero M] {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      IsBoundedAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsBoundedAt c (alSlash W k f) k :=
  IsBoundedAt.smul_iff.mp (hf _ (isCusp_alGL_smul W hc))

end ModularForm
end
end P2MW.S_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0
