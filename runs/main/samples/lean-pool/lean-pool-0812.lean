@[expose] public section

namespace ScottishBook155

open ENNReal WithLp

noncomputable section

universe u v

theorem protectedExtensionSourceEmbedding_preservesUpTo
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {N : Type v} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V : M → N} {a : M} {y : N} {L H r : ℝ}
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L)
    (hr : 0 < r) (hH : 2 * r + dist (V a) y < H)
    (hshort : PreservesUpTo r V) :
    PreservesUpTo r
      (protectedExtensionSourceEmbedding V a y L H hattach hLH hL hV hgap) := by
  intro x z hd
  have hx : (toLp 1 (x.fst, x.snd) : OneSum M) = x := rfl
  have hz : (toLp 1 (z.fst, z.snd) : OneSum M) = z := rfl
  rw [← hx, ← hz] at hd ⊢
  exact protectedExtensionSourceEmbedding_dist_eq_of_short hattach hLH hL
    hV hgap hr hH hshort x.fst z.fst hd

end
end ScottishBook155
end
