public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Isogeny

section Ad

variable
  {τ : Tag} [M27Ok τ] [E6Sub τ] {k : Type} [Field k] [Finite k]

theorem e6Ad_surjective : Function.Surjective (e6Ad τ k) :=
  (e6Isogeny_surjective k).comp (m27Equiv τ k).surjective

end Ad
end CFSG.LocalAnalysis.GLTheoremA.K155X
end
