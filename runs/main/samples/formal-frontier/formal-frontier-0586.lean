set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
  {R : Type v} [Ring R]

theorem blockDiagonalUnit_mem_elementarySubgroup (g : GL ι R) :
    blockDiagonalUnit g ∈ elementarySubgroup (ι ⊕ ι) R := by
  rw [blockDiagonalUnit_eq]
  exact (elementarySubgroup (ι ⊕ ι) R).mul_mem
    ((elementarySubgroup (ι ⊕ ι) R).mul_mem
      ((elementarySubgroup (ι ⊕ ι) R).mul_mem
        (upperUnit_mem_elementarySubgroup (g : Matrix ι ι R))
        (lowerUnit_mem_elementarySubgroup ((g⁻¹ : GL ι R) : Matrix ι ι R)))
      (upperUnit_mem_elementarySubgroup (g : Matrix ι ι R)))
    swapUnit_mem_elementarySubgroup

end Matrix.GeneralLinearGroup
end
