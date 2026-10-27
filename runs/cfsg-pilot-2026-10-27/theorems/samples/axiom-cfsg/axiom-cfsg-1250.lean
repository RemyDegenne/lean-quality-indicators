public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434CharThree

open CFSG Matrix

open CFSG.SectionRank.OddCover (u3Mat)

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section SU

variable {F : Type} [Field F] {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c}

theorem coe_mul_comm_of_commute {g g' : SU σ 3} (h : g * g' = g' * g) :
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((g' : GL (Fin 3) F) : Matrix _ _ F) =
      ((g' : GL (Fin 3) F) : Matrix _ _ F) * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have := congrArg (fun k : SU σ 3 => ((k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
  simpa using this

end SU
end CFSG.RankThree.PartTwo.Sec4.Item434CharThree
end
