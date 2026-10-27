set_option maxRecDepth 100000

public section

namespace CFSG.Sporadic.HN.Local

open CFSG.Sporadic.F5 Equiv CFSG.Sporadic.HN.LocalK

theorem Hx_mapsTo : ∀ h ∈ Hx, ∀ v ∈ wSet, h • v ∈ wSet := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem g hg =>
    rintro _ ⟨k, rfl⟩
    rcases hg with rfl | rfl
    · exact ⟨pi2 k, (alt_certificate.2.2.2.1 k).symm⟩
    · exact ⟨pi3 k, (alt_certificate.2.2.2.2.1 k).symm⟩
  | one => intro v hv; simpa using hv
  | mul a b _ _ ha hb => intro v hv; rw [mul_smul]; exact ha _ (hb v hv)
  | inv a _ ha => exact inv_mapsTo_of_finite wSet_finite ha

end CFSG.Sporadic.HN.Local
end
