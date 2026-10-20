public section

open Order

variable {ι : Type*} [LinearOrder ι]

section toZ

variable [SuccOrder ι] [IsSuccArchimedean ι] [PredOrder ι] {i0 i : ι}

@[simp]
theorem toZ_inj {i j : ι} : toZ i0 i = toZ i0 j ↔ i = j :=
  injective_toZ.eq_iff

end toZ
end
