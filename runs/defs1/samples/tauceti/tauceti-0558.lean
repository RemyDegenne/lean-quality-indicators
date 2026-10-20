public section

open DoubleCoset Subgroup

variable {G : Type*} [Group G] {Δ : Submonoid G} {H : Subgroup G}

namespace HeckeCoset

section Orbit

open scoped Pointwise

variable [IsHeckeTriple Δ H H]

open Classical in
/-- The orbit of a left coset representative `β` under a double coset representative `g`:
the left cosets `βσᵢgH` over the decomposition `HgH = ⊔ᵢ σᵢgH`. -/
noncomputable def smulOrbit (H : Subgroup G) [IsHeckeTriple Δ H H] (g β : Δ) :
    Finset (HeckeCoset Δ ⊥ H) :=
  Finset.univ.image fun i : DecompQuotient H H (g : G) ↦
    mk ⊥ H ⟨(β : G) * i.out * g,
      Δ.mul_mem (Δ.mul_mem β.2 (IsHeckeTriple.mem_of_mem_left H i.out.2)) g.2⟩

end Orbit
end HeckeCoset
end
