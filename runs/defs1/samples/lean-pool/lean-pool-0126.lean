@[expose] public section

namespace FD1D

noncomputable section

namespace LocalHazard

/-- Parent deletion mass under the invariant `q = N h`. -/
def q (h : ℝ) (x y : ℕ) : ℝ := N x y * h

end LocalHazard
end
end FD1D
end
