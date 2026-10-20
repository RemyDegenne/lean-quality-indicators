@[expose] public section

namespace FD1D

namespace BellmanCertificate

@[simp] theorem eval1_one (z : ℝ) : eval1 1 z = 1 := by
  simp [eval1, DPoly.eval, DPoly.evalCoeffs]

end BellmanCertificate
end FD1D
end
