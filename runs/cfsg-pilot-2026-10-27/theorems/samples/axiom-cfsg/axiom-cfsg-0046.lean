public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

theorem comm_mul_mem_V {G : Type} [Group G] {V : Subgroup G} {q a v : G}
    (hq : q ∈ Subgroup.centralizer (V : Set G)) (hv : v ∈ V) :
    q * (a * v) * q⁻¹ * (a * v)⁻¹ = q * a * q⁻¹ * a⁻¹ := by
  have h : v * q = q * v := Subgroup.mem_centralizer_iff.mp hq v hv
  have h' : v * q⁻¹ = q⁻¹ * v := by
    calc v * q⁻¹ = q⁻¹ * (q * v) * q⁻¹ := by group
      _ = q⁻¹ * (v * q) * q⁻¹ := by rw [h]
      _ = q⁻¹ * v := by group
  calc q * (a * v) * q⁻¹ * (a * v)⁻¹ = q * a * (v * q⁻¹) * v⁻¹ * a⁻¹ := by group
    _ = q * a * (q⁻¹ * v) * v⁻¹ * a⁻¹ := by rw [h']
    _ = q * a * q⁻¹ * a⁻¹ := by group

end CFSG.Quasithin.H13.A6
end
