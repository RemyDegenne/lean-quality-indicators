@[expose] public section

open scoped BigOperators Topology goldenRatio

open Filter Set

namespace Erdos346

noncomputable section

lemma prefixSubsetSums_mono_index {a : ℕ → ℕ} {I : Set ℕ} {m n : ℕ}
    (hmn : m ≤ n) :
    prefixSubsetSums a I m ⊆ prefixSubsetSums a I n := by
  intro t ht
  rcases ht with ⟨F, hFI, hsum⟩
  refine ⟨F, ?_, hsum⟩
  intro i hi
  exact ⟨hFI hi |>.1, le_trans (hFI hi |>.2) hmn⟩

end
end Erdos346
end
