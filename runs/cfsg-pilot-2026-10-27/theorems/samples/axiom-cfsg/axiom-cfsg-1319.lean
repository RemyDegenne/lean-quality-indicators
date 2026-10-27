public section

namespace CFSG.OddStandard.SmallF3.L33.KD

open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open CFSG.ComponentClassification.HSFLit.Sec8

namespace MB

open CFSG.ComponentClassification.HSFLit.Sec8.MB

theorem Z2_of_gens_2 : ∀ x : MB, inQ1 x = true →
    (∀ g ∈ gensT2 (0, 10), inZ (applyQ1 g x * x⁻¹) = true) → x ∈ Z2L := by decide +kernel

end MB
end Sec8
end CFSG.OddStandard.SmallF3.L33.KD
end
