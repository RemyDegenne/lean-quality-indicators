public section

namespace CFSG.RankThree.PartOne.OddIso

open Module

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V}

variable {A : Module.End K V} {p : ℕ}

section Odd

variable [CharP K 2]

theorem eq_zero_of_fixed_range (hp : Odd p) (hA : A ^ p = 1) {w : V}
    (hw : w ∈ LinearMap.range (A - 1)) (hAw : A w = w) : w = 0 := by
  have h1 : w ∈ LinearMap.ker (A - 1) :=
    LinearMap.mem_ker.mpr (by rw [LinearMap.sub_apply, hAw, Module.End.one_apply, sub_self])
  have : w ∈ LinearMap.ker (A - 1) ⊓ LinearMap.range (A - 1) := ⟨h1, hw⟩
  rw [ker_inf_range hp hA] at this
  exact this

end Odd
end CFSG.RankThree.PartOne.OddIso
end
