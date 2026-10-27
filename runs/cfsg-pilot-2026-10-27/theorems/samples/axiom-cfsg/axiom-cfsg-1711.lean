public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix

open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)

variable {F : Type} [Field F] [CharP F 2]

theorem qr_smul (r : ↥(cayleyGroup F)) (c : F) (x : Ix3 → F) :
    qr r (c • x) = c * c * qr r x := by
  simp only [qr]
  rw [g2Act_smul, polarQ_smul_left, polarQ_smul_right]
  ring

end CFSG.Quasithin.Vol2.Ch11.G2Q8
end
