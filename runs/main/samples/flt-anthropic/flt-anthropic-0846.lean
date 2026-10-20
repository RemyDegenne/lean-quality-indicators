namespace P2MW.S_EisensteinWeightOne_e1Chi3IsModular

namespace S17E1

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section File_FLT_AnalyticCore_SplitPrimePowCount

namespace FLT

namespace AnalyticCore

open Finset

theorem reprCount_mul_mul {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) {a b : ℤ}
    (hπ : hexForm a b = (p : ℤ)) (m : ℕ) :
    reprCount (p * (p * m)) + reprCount m = 2 * reprCount (p * m) := by
  have hπ' : hexForm (a + b) (-b) = (p : ℤ) := (hexForm_conj a b).trans hπ
  have hcui := Finset.card_union_add_card_inter
    ((reprSols (p * m)).image (emul (a, b)))
    ((reprSols (p * m)).image (emul (a + b, -b)))
  rw [inter_image_eq_dilate hp h1 hπ m, card_image_dilate hp, card_image_emul hp hπ,
    card_image_emul hp hπ'] at hcui
  show (reprSols (p * (p * m))).card + (reprSols m).card = 2 * (reprSols (p * m)).card
  rw [reprSols_mul_eq_union hp hπ (p * m)]
  omega

end AnalyticCore
end FLT
end File_FLT_AnalyticCore_SplitPrimePowCount
end S17E1
end P2MW.S_EisensteinWeightOne_e1Chi3IsModular
