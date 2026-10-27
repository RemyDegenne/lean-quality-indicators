public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

open CFSG.ClassicalInvolution.Q3.AE.Wr

open Finset

open scoped commutatorElement

namespace E8Pkg

variable {Y : Type} [Group Y] {I D : Subgroup Y} (P : E8Pkg I D)

theorem vec_of_mem_D {d : Y} (hd : d ∈ D) : ∃ S : Finset (Fin 8), Even S.card ∧ P.ph d = vq S := by
  have hdI := P.le hd
  exact exists_vq_of_ker (P.ph_mem hdI) (P.rho_eq_one_of_mem_D hd)

end E8Pkg
end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
end
