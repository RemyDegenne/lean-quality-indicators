public section

namespace CFSG.RankThree.PartOne.KCSpFull

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

open scoped commutatorElement

variable {r : ℕ} {K : Type} [Field K]

variable {ℓ f p : ℕ} {Ahat : Subgroup (StatedSp r K)}

theorem SpPlaneDecomp.ker_eq_sup (D : SpPlaneDecomp p Ahat) {M : Subgroup ↥Ahat}
    (hM : Nat.card M = p) {x : StatedSp r K} (hxA : x ∈ Ahat)
    (hxM : (⟨x, hxA⟩ : ↥Ahat) ∈ M) (hx1 : x ≠ 1) :
    LinearMap.ker (spEnd x - 1) = spPlaneFix Ahat ⊔ spLineSpace M := by
  have h := D.ker_eq M hM ⟨x, hxA⟩ hxM (fun h' => hx1 (congrArg Subtype.val h'))
  exact h.1.trans h.2

end CFSG.RankThree.PartOne.KCSpFull
end
