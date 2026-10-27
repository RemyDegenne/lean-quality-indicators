public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X : Type} [Group X] {E : Set X} {P : Type}

namespace LocalPoints

variable {M : LocalModel P} {d : X} (L : LocalPoints M E d)

variable (hP : Pair X E) (hd : d ∈ E)

include hP hd

theorem muImg_conj {c : X} (hc : c ∈ E) (hcd : c * d ≠ d * c) :
    L.muImg (d * c * d) = L.muImg c := by
  ext p
  rw [mem_muImg, mem_muImg]
  have h := Pair.muSet_eq_muSet_mul_mul hP hd hc hcd
  constructor
  · intro hp
    have : (L.χ.symm p : X) ∈ muSet E d (d * c * d) := ⟨(L.χ.symm p).2, hp⟩
    rw [← h] at this
    exact this.2
  · intro hp
    have : (L.χ.symm p : X) ∈ muSet E d c := ⟨(L.χ.symm p).2, hp⟩
    rw [h] at this
    exact this.2

end LocalPoints
end CFSG.Fischer
end
