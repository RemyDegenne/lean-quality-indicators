namespace P2MW.S_NumberField_exists_completedDedekindZeta_package

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 6400000

section

set_option maxHeartbeats 6400000

p2m_reactivate

p2m_reactivate

section

set_option maxHeartbeats 6400000

p2m_reactivate

section

set_option maxHeartbeats 6400000

p2m_reactivate

section

set_option maxHeartbeats 6400000

p2m_reactivate

section

set_option maxHeartbeats 6400000

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

set_option maxHeartbeats 6400000

namespace FLT

namespace KwDyf2XiOrderBoundDecomp

open FLT.KwDyf2XiEntireOrderDecomp

open FLT.Gapsw80T9ClassSumA1Closure

p2m_open

p2m_open_scoped

def kwDyf2_XiStripBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ C : ℝ, ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 3/2 → 2 ≤ ‖s‖ →
      Real.log ‖kwDyf2_xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖

end KwDyf2XiOrderBoundDecomp
end FLT
end
end
end
end
end
end
end P2MW.S_NumberField_exists_completedDedekindZeta_package
