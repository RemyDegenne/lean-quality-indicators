namespace P2MW.S_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half

set_option Elab.async false

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

noncomputable section

p2m_open

open scoped Classical

namespace AutomorphicForm

namespace WeylIntegrable

p2m_open

section R2

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

local notation "HOS" => HeightOneSpectrum (𝓞 F)

def stepElt (k : HOS →₀ ℕ) (v₀ : HOS) (r : 𝓞 F) : 𝔸f := singleFin F v₀ (toCompl F v₀ ((r : F) * unif F v₀ ^ (-((k v₀ : ℤ) + 1))))

end R2
end WeylIntegrable
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half
