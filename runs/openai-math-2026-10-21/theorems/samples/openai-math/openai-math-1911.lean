namespace OAI

noncomputable section

namespace CKSMixedGeometry

noncomputable section

open CKSCalculus Set Filter

open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

section SmoothRules

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[fun_prop] lemma productJet_contDiffAt {f g : E → ScalarJet} {x : E} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (fun y => productJet (f y) (g y)) x := productJet_smooth.contDiffAt.comp x (hf.prodMk hg)

end SmoothRules
end
end CKSMixedGeometry
end
end OAI
