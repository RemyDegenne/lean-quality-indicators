public section

namespace CFSG.StandardType.SmallU

open scoped commutatorElement

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.StandardType.TableBUE

variable {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

open scoped Classical in
theorem mem_cls {σ : Fin d → Kˣ} {i k : Fin d} : k ∈ cls σ i ↔ σ k = σ i := by
  simp [cls]

end CFSG.StandardType.SmallU
end
