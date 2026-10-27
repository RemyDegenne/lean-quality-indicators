public section

namespace CFSG.SectionRank.QTK.CentreFact

open CFSG.Open CFSG.Blueprint CFSG.SectionRank.QTK.CoverB

section List

variable {p f r : ℕ}

theorem not_tablePrime_psl_two_one {n : ℕ} (hr : r.Prime) : ¬ TablePrime .PSL n 2 1 r := by
  intro h
  rcases tablePrime_psl_iff.1 h with ⟨-, h1⟩ | ⟨-, -, hp, -⟩
  · exact hr.not_dvd_one (by simpa using h1)
  · omega

end List
end CFSG.SectionRank.QTK.CentreFact
end
