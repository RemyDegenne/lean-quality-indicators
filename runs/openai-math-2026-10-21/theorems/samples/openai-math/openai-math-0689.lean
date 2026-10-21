namespace OAI

section

namespace PlanarL1.Columns.Model.MainCell

open PlanarL1.Interpolation

open scoped NNReal

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

variable (F : M.Field I 1) (hJI : J ⊆ I)

variable (R : Point.RadialTree (M := M) (J := J) (root := root)) (q : ℝ)

variable (C : Cell R q)

lemma localClipPair_probability {k : ℕ} (A : R.Node k) (v x : M.Point J root)
    (E lo B : ℝ) (hB : 0 < B) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    (i j : ℕ) (hi : i ∈ clipNames (R.recentNames A R.lookback))
    (hj : j ∈ clipNames (R.recentNames A R.lookback)) (hij : i ≠ j)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : Point.RadialTree.GridSample (n := n) cap m × Fin (m+1) =>
      |localClipAtom F hJI R q C A v (R.gridNoise cap m ω.1) E (B/m*ω.2.val) lo i x-
       localClipAtom F hJI R q C A v (R.gridNoise cap m ω.1) E (B/m*ω.2.val) lo j x| ≤ t) ≤
      (2*t+R.q/m)/R.q + (2*t+B/m)/B := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact localClipPair_probability_lt F hJI R q C A v x E lo B hB cap m hk hm i j hi hj hij ht
  · simpa only [abs_sub_comm] using
      localClipPair_probability_lt F hJI R q C A v x E lo B hB cap m hk hm j i hj hi hji ht

end PlanarL1.Columns.Model.MainCell
end
end OAI
