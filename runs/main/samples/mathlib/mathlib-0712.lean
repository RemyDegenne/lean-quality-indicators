@[expose] public section

open Metric Set WithTop

open scoped Topology Pointwise

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {g : 𝕜 → 𝕜}
  {x : 𝕜}
  {U : Set 𝕜}

theorem MeromorphicNFOn.zero_set_eq_divisor_support (h₁f : MeromorphicNFOn f U)
    (h₂f : ∀ u : U, meromorphicOrderAt f u ≠ ⊤) :
    U ∩ f ⁻¹' {0} = Function.support (MeromorphicOn.divisor f U) := by
  ext u
  constructor <;> intro hu
  · simp_all only [ne_eq, Subtype.forall, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Function.mem_support, h₁f.meromorphicOn, MeromorphicOn.divisor_apply,
      WithTop.untop₀_eq_zero, (h₁f hu.1).meromorphicOrderAt_eq_zero_iff, not_true_eq_false, or_self,
      not_false_eq_true]
  · simp only [Function.mem_support, ne_eq] at hu
    constructor
    · exact (MeromorphicOn.divisor f U).supportWithinDomain hu
    · rw [Set.mem_preimage, Set.mem_singleton_iff]
      have := h₁f ((MeromorphicOn.divisor f U).supportWithinDomain hu)
        |>.meromorphicOrderAt_eq_zero_iff.not
      simp only [h₁f.meromorphicOn, (MeromorphicOn.divisor f U).supportWithinDomain hu,
        MeromorphicOn.divisor_apply, WithTop.untop₀_eq_zero, not_or] at hu
      simp_all [hu.1]

end
