public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open scoped Matrix TensorProduct

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

include hirrQ in
theorem omMinus_two_outer_four_le_of_finrank_eq_sixteen (hK : Nat.card K = 2) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ)
    (hρ1 : ∃ g, ρ g ≠ 1) (h16 : Module.finrank (ZMod 2) V = 16)
    (s : V ≃ₗ[ZMod 2] V) (hs : ∀ v, s (s v) = v) (α : MulAut (spinGroup (quadMinus 4 K b c)))
    (hα : ∀ g v, s (ρ g (s.symm v)) = ρ (α g) v) (hα2 : α * α = 1)
    (houter : ∀ g₀ : spinGroup (quadMinus 4 K b c), α ≠ MulAut.conj g₀) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) := by
  by_contra hlt
  have hlt' : Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) < 4 :=
    not_le.mp hlt
  have hsmall : 2 * Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) <
      Module.finrank (ZMod 2) V := by
    rw [h16]; omega
  have hE := omMinusTwo_card_endRing_eq_two_of_small hirrQ hK hρ s hs α hα hα2 houter hsmall
  exact omMinus_two_false_of_card_endRing_eq_two hirrQ hK hρ hρ1 hE h16

end CFSG.LocalAnalysis.WeakClosure81
end
