public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3

theorem smallLeafR_u4_of_split {r : ℕ} (h₃ : SmallLeafR r fun F _ => LieModel F .PSU 4 3 1)
    (h : SmallLeafR r SmallU4Ne3) : SmallLeafR r SmallU4 := by
  refine SmallLeafR.of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hc, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, hc, h3, hm⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4
end
