public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed

open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem swap_not_mem_centralizer_modelBase {n : ℕ} (hn : 1 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom S e (Original.z (2 ^ n)) ∉
      Subgroup.centralizer (modelBase S e : Set G) := by
  intro h
  have hc := Subgroup.mem_centralizer_iff.mp h _ (modelHom_x2_mem_modelBase S e)
  have h' : (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ * wreathModelHom S e (Original.x2 (2 ^ n)) *
      wreathModelHom S e (Original.z (2 ^ n)) = wreathModelHom S e (Original.x2 (2 ^ n)) := by
    rw [mul_assoc, hc]
    group
  rw [modelHom_swap_conj_x2] at h'
  exact modelHom_x2_ne_t_half S e hn h'.symm

end CFSG.Wreathed.BrauerWong
end
