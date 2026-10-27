public section

namespace CFSG.GF2Type.Aschbacher1976Full.Z4Q8

open CFSG CFSG.Blueprint

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem comm_mem_zpowers_Fz {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {x y : G}
    (hx : x ∈ Fz z) (hy : y ∈ Fz z) : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers z := by
  obtain ⟨Z, A, -, hZc, -, hzZ, hA, hA8, hzA, hAc, hsup, -⟩ := unpack hZ hz
  have hxF : x ∈ Z ⊔ A := by rw [hsup]; exact hx
  have hyF : y ∈ Z ⊔ A := by rw [hsup]; exact hy
  obtain ⟨c, hc, a, ha, rfl⟩ := (mem_sup_iff' hAc).mp hxF
  obtain ⟨c', hc', a', ha', rfl⟩ := (mem_sup_iff' hAc).mp hyF
  have e1 : c * a * (c' * a') = (c * c') * (a * a') := by
    calc c * a * (c' * a') = c * (a * c') * a' := by group
      _ = c * (c' * a) * a' := by rw [hAc c' hc' a ha]
      _ = (c * c') * (a * a') := by group
  have e2 : c' * a' * (c * a) = (c * c') * (a' * a) := by
    calc c' * a' * (c * a) = c' * (a' * c) * a := by group
      _ = c' * (c * a') * a := by rw [← hAc c hc a' ha']
      _ = (c' * c) * (a' * a) := by group
      _ = (c * c') * (a' * a) := by rw [comm_of_mem_cyclic hZc hc' hc]
  have hd : a * a' * a⁻¹ * a'⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem (A.mul_mem ha ha') (A.inv_mem ha)) (A.inv_mem ha')
  have hcc : (c * c') * (a * a' * a⁻¹ * a'⁻¹) = (a * a' * a⁻¹ * a'⁻¹) * (c * c') :=
    hAc (c * c') (Z.mul_mem hc hc') _ hd
  have key : c * a * (c' * a') * (c * a)⁻¹ * (c' * a')⁻¹ =
      (c * c') * (a * a' * a⁻¹ * a'⁻¹) * (c * c')⁻¹ := by
    calc c * a * (c' * a') * (c * a)⁻¹ * (c' * a')⁻¹
        = (c * a * (c' * a')) * (c' * a' * (c * a))⁻¹ := by group
      _ = ((c * c') * (a * a')) * ((c * c') * (a' * a))⁻¹ := by rw [e1, e2]
      _ = (c * c') * (a * a' * a⁻¹ * a'⁻¹) * (c * c')⁻¹ := by group
  rw [key, hcc]
  have h3 : (a * a' * a⁻¹ * a'⁻¹) * (c * c') * (c * c')⁻¹ = a * a' * a⁻¹ * a'⁻¹ := by group
  rw [h3]
  exact comm_mem_zpowers_of_extraspecial hA hA8 hzA hz (fun b hb => hAc z hzZ b hb) ha ha'

end CFSG.GF2Type.Aschbacher1976Full.Z4Q8
end
