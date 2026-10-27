public section

namespace CFSG.StandardType

namespace RCSTOm

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega

open CFSG.RankThree.Classical2 (orthDerived)

open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)

open CFSG.LieType.Universal.Spin (HypFrame)

section SL

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ P₃ P₄ : HypPair Q}

theorem orth_flip {P P' : HypPair Q} (h : P.Orth P') : P.Orth (flipPair P') :=
  ⟨h.ef, h.ee, h.ff, h.fe⟩

end SL
end RCSTOm
end CFSG.StandardType
end
