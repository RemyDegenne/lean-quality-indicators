public section

open Topology

section

open Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]

attribute [-instance] Units.mulAction'

protected theorem Complex.isQuotientCoveringMap_npow (n : ℕ) [NeZero n] :
    IsQuotientCoveringMap (fun z : ℂˣ ↦ z ^ n) (powMonoidHom (α := ℂˣ) n).ker :=
  isQuotientCoveringMap_npow n (by simp [NeZero.ne]) fun _ ↦ ⟨_, cpow_nat_inv_pow _ (NeZero.ne n)⟩

end
end
