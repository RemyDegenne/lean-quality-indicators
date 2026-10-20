@[expose] public section

namespace Nikodym.LowerBound

open MvPolynomial

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {d : ℕ}

local notation "ι" => (MvPolynomial.map (algebraMap K K') :
  MvPolynomial (Fin d) K →+* MvPolynomial (Fin d) K')

section Comap

theorem map_eq_top_iff (I : Ideal (MvPolynomial (Fin d) K)) : I.map ι = ⊤ ↔ I = ⊤ := by
  rw [← Ideal.map_top ι]
  exact map_injective.eq_iff

end Comap
end Nikodym.LowerBound
end
