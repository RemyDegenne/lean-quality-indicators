@[expose] public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix

theorem sec12_conj_fin : ∀ A : Sec12M, A.det = 1 →
    ∃ g : Sec12M, g.det = 1 ∧ ∃ R ∈ sec12Reps, g * A = R * g := by
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
end
