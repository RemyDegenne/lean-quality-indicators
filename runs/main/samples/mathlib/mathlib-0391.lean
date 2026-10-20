public section

namespace GenContFract

variable {K : Type*} [Field K]

variable {n : ℕ} {h : K} {ρ : Stream'.Seq K} {g : GenContFract K}

@[simp]
theorem partDen_euler_zero : (euler h ρ).partDens.get? 0 = (ρ.get? 0).map (fun _ => 1) := by
  rw [partDens, @Stream'.Seq.map_get?, euler_s_zero]
  rcases ρ.get? 0 with _ | _ <;> simp

end GenContFract
end
