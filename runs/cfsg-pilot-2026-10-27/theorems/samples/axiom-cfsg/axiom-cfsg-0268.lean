public section

namespace CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem c26_2_of_claims (h752 : L7_5_2 p f) (hMu : Ih8MuTableSect p f) (hT : S26XTop p f)
    (hZ : S26XMuZ2 p f) : C26_2 p f :=
  c26_2_of_c26_3 (c26_3_S4_of_claims h752 hMu hT hZ)

end CFSG.ClassicalInvolution.Asc77
end
