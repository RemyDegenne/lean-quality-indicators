@[expose] public noncomputable section

open Filter

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

theorem PerronLowerEnvelopeBentQuadraticBallPatch.boundaryAwayOpenPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch : PerronLowerEnvelopeBentQuadraticBallPatch C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticBoundaryAwayOpenPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).boundaryAwayOpenPatchAt

end ViscositySolns
end
