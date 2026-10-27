public section

namespace CFSG.Sporadic.Th.Recog.MFactsB

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Recognition.PresentedWords

open Equiv Equiv.Perm

section Basic

theorem y₁_comm_tLetter : y₁ * tLetter = tLetter * y₁ := by
  have hx : Commute (ω₁ * x₁) tLetter :=
    Commute.mul_left (a := ω₁) (b := x₁) (c := tLetter) ω₁_comm_tLetter x₁_comm_tLetter
  have hi : Commute ω₁⁻¹ tLetter :=
    Commute.inv_left (a := ω₁) (b := tLetter) ω₁_comm_tLetter
  simpa only [y₁] using
    (Commute.mul_left (a := ω₁ * x₁) (b := ω₁⁻¹) (c := tLetter) hx hi).eq

end Basic
end CFSG.Sporadic.Th.Recog.MFactsB
end
