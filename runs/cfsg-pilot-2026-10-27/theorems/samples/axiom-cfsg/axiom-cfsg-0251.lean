public section

namespace CFSG.Goldschmidt.Sec89

theorem neumannKappa_balanced_of_commutes {Q : Type*} [Group Q] (phi : MulAut Q)
    (hcomm : ∀ q : Q, Commute q (phi q)) (x y : Q) :
    neumannKappa (phi x) y = neumannKappa x (phi y) := by
  have hp := (hcomm (x * y⁻¹)).eq
  simp only [map_mul, map_inv] at hp
  have hp' := congrArg (fun t : Q => (phi x)⁻¹ * x⁻¹ * t * y * phi y) hp
  group at hp'
  have hba_inv : Commute (phi x) x⁻¹ := Commute.inv_right_iff.mpr (hcomm x).symm
  have hp'' : (phi x)⁻¹ * y⁻¹ * phi x * (phi y)⁻¹ * y = x⁻¹ * (phi y)⁻¹ * x := by
    simpa [hba_inv.inv_mul_cancel] using hp'
  calc neumannKappa (phi x) y = ((phi x)⁻¹ * y⁻¹ * phi x * (phi y)⁻¹ * y) * phi y := by
        simp [neumannKappa, mul_assoc, (hcomm y).symm.inv_mul_cancel]
    _ = (x⁻¹ * (phi y)⁻¹ * x) * phi y := congrArg (fun t : Q => t * phi y) hp''
    _ = neumannKappa x (phi y) := by simp [neumannKappa, mul_assoc]

end CFSG.Goldschmidt.Sec89
end
