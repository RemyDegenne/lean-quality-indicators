public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF.O3CX

open scoped Pointwise

variable {G : Type} [Group G] {W W' C : Subgroup G}

section Act

variable [(dQ W W' C).Normal]

namespace Frame

variable (hF : Frame W W' C)

include hF

omit hF in
theorem eq_of_mul_eq {a a' b b' : G} (ha : a ∈ W ⊓ C) (ha' : a' ∈ W ⊓ C) (hb : b ∈ W' ⊓ C)
    (hb' : b' ∈ W' ⊓ C)
    (h : qA W W' C a ha * qB W W' C b hb = qA W W' C a' ha' * qB W W' C b' hb') :
    qA W W' C a ha = qA W W' C a' ha' ∧ qB W W' C b hb = qB W W' C b' hb' := by
  have h1 : (qA W W' C a' ha')⁻¹ * qA W W' C a ha =
      qB W W' C b' hb' * (qB W W' C b hb)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
  have h2 : qA W W' C (a'⁻¹ * a) ((W ⊓ C).mul_mem ((W ⊓ C).inv_mem ha') ha) =
      qB W W' C (b' * b⁻¹) ((W' ⊓ C).mul_mem hb' ((W' ⊓ C).inv_mem hb)) := h1
  have hD := mem_D_of_qc_eq _ _ h2
  have hA : qA W W' C a ha = qA W W' C a' ha' := by
    rw [qc_eq_qc_iff]
    have := (W ⊓ W').inv_mem hD
    simpa using this
  refine ⟨hA, ?_⟩
  rw [hA] at h
  exact mul_left_cancel h

end Frame
end Act
end CFSG.Quasithin.Vol2.Ch11.SecF.O3CX
end
