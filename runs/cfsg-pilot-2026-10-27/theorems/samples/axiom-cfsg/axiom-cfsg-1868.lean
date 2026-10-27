public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.L34Amalgam

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G} {s : G}

namespace S6Model

variable (M : S6Model z s)

theorem eq_one_of_mem_hsB_comm {x : ↥(hsNB z s)} (hπx : M.π x = σS0) {b : G}
    (hb : b ∈ hsB z s) (hbx : b * x = x * b) : b = 1 := by
  obtain ⟨u, rfl⟩ := M.surj b hb
  have h1 := M.act x u
  rw [hπx] at h1
  have h2 : (x : G) * M.Φ u * (x : G)⁻¹ = M.Φ u := by rw [← hbx, mul_inv_cancel_right]
  rw [h2] at h1
  rw [eq_zero_of_actS6_σS0 u (M.inj h1).symm, M.Φ_zero]

end S6Model
end HSSetting
end CFSG.Quasithin.HSType
end
