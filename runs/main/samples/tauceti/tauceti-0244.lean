public section

open scoped DirectSum

namespace TauCeti

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

@[simp]
theorem bigradedChainEquiv_single (R : Type*) [Semiring R] (x : GridState n) (r : R) :
    G.bigradedChainEquiv R (Finsupp.single x r) =
      DirectSum.lof R (ℤ × ℤ) (fun g => G.BigradedChainPiece R g) (G.bidegree x)
        (DirectSum.lof R {y : GridState n // G.bidegree y = G.bidegree x}
          (fun _ => R) ⟨x, rfl⟩ r) := by
  rw [bigradedChainEquiv, LinearEquiv.trans_apply, finsuppLEquivDirectSum_single,
    sigmaFiberLinearEquiv_apply]
  simpa only [DirectSum.lof_eq_of] using
    (DirectSum.sigmaFiberAddEquiv_of (β := fun _ : GridState n => R) G.bidegree x r)

end OddComponentGridDiagram
end TauCeti
end
