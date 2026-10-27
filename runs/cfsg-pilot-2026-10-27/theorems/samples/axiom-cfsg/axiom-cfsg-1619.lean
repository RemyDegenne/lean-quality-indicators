public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace E6ThreeEnd

section General

variable {R R' : Type*} [Group R] [Group R']

theorem map_congr_symm_map_congr (e : R ≃* R') (A : Subgroup (MulAut R)) :
    (A.map (MulAut.congr e).toMonoidHom).map (MulAut.congr e.symm).toMonoidHom = A := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id A
  ext φ x
  simp [MulAut.congr]

end General
end E6ThreeEnd
end CFSG.StandardType
end
