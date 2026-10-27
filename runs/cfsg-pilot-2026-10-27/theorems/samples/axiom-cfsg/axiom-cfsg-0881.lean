public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Open

open scoped Pointwise

theorem rhoH_pow_apply_e (g : ↥stdMH) (n : ℕ) (x : Fin 24) (hx : x ∈ stdH) :
    ((rhoH g) ^ n) (heptadEquiv ⟨x, hx⟩) =
      heptadEquiv ⟨((g : S24) ^ n) x, pow_mem_stdH g n x hx⟩ := by
  have h1 : (rhoH g) ^ n = heptadEquiv.permCongr ((rhoSub g) ^ n) := by
    change (heptadEquiv.permCongrHom.toMonoidHom (rhoSub g)) ^ n =
      heptadEquiv.permCongr ((rhoSub g) ^ n)
    rw [← map_pow (heptadEquiv.permCongrHom.toMonoidHom) (rhoSub g) n]
    rfl
  rw [h1, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact congrArg heptadEquiv (Subtype.ext
    (Equiv.Perm.subtypePerm_apply_pow_of_mem (g := (g : S24)) (s := stdH)
      (mem_smul_stdH_iff (g : S24) (stab_smul g)) (n := n) hx))

end CFSG.Quasithin.AppendixH.H14
end
