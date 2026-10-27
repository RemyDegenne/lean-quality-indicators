public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GLn
  HeckeRing.GL2

open scoped MatrixGroups ModularForm TauCeti.ExactDivisor

namespace HeckeRing.GL2

open TauCeti

variable {N Q R : ℕ} [NeZero N] {k : ℤ}

namespace Newform

/-- **A newform of trivial nebentypus, as a cusp form on `Γ₀(N)`**: the same function on `ℍ`,
re-read as a form for the bare group `Γ₀(N)` under the identification `S_k(N, 1) ≃ S_k(Γ₀(N))`.
This is the carrier on which the Atkin–Lehner operators act. -/
noncomputable def toCuspFormGamma0 (f : Newform N k) (hχ : f.χ = 1) :
    CuspForm ((Gamma0 N).map (mapGL ℝ)) k :=
  cuspFormCharSpaceOneEquiv N k ⟨f.toCuspForm, hχ ▸ f.mem_charSpace⟩

end Newform
end HeckeRing.GL2
end
