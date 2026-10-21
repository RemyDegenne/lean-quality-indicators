namespace OAI

section

section

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology

section UpperProof

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal RealInnerProductSpace Topology

open Function MeasureTheory Set Filter

open scoped Topology NNReal

namespace LogConcaveSampling

open MeasureTheory

open scoped RealInnerProductSpace NNReal

namespace PolySmooth

variable {d : ℕ} {f g H : Point d → ℝ}

lemma sum {ι : Type*} (s : Finset ι) {f : ι → Point d → ℝ}
    (hf : ∀i∈s,PolySmooth (f i)) : PolySmooth (fun x => ∑i∈s,f i x) := by
  refine ⟨ContDiff.sum (fun i hi => (hf i hi).smooth),fun l => ?_⟩
  rw [JetCalculus.jet_sum s (fun i hi => (hf i hi).smooth)]
  exact Appell.HasGrowth.sum s (fun i hi => (hf i hi).growth l)

end PolySmooth
end LogConcaveSampling
end UpperProof
end
end
end
end OAI
