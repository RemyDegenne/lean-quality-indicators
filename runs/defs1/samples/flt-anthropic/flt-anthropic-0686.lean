namespace P2MW.S_DeligneSerre_exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range

set_option autoImplicit false

open Polynomial

namespace DSRed

section CaseA

variable {G : Type} [Group G] {κ : Type} [Field κ] {Ω : Type} [Field Ω] (ι : κ →+* Ω)

noncomputable def diagRep (c₁ c₂ : G →* κˣ) : G →* GL (Fin 2) κ where
  toFun g := diagGL (c₁ g) (c₂ g)
  map_one' := by
    apply Units.ext
    simp only [diagGL_val, map_one, Units.val_one]
    rw [← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp
  map_mul' g h := by
    apply Units.ext
    simp only [diagGL_val, map_mul, Units.val_mul, Matrix.diagonal_mul_diagonal]
    congr 1; ext i; fin_cases i <;> simp

end CaseA
end DSRed
end P2MW.S_DeligneSerre_exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range
