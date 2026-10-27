public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

open CFSG.RankThree.PartTwo.KFacts

open Matrix

section PglHomSub

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool} {e : L ≃* slPi π 3 (p ^ f) K} {S : Subfield K}

variable (S)

variable {S} {hK : PiField π p f K} {hq : ModThree π (p ^ f)} {A' : Subgroup G}
  {hA' : ∀ a ∈ A', ∃ y₀ : GL (Fin 3) S, IsPGLAt e a (subGL S y₀)}

theorem pglHomSub_apply (a : A') {y₀ : GL (Fin 3) S} (hy : IsPGLAt e a (subGL S y₀)) :
    pglHomSub S hK hq A' hA' a = (y₀ : GL (Fin 3) S ⧸ StatedScalars (Fin 3) S) := by
  change ((Classical.choose (hA' a a.2) : GL (Fin 3) S) :
    GL (Fin 3) S ⧸ StatedScalars (Fin 3) S) = y₀
  rw [QuotientGroup.eq]
  exact subGL_inv_mul_mem hK hq (Classical.choose_spec (hA' a a.2)) hy

end PglHomSub
end CFSG.RankThree.PartTwo.Sec4
end
