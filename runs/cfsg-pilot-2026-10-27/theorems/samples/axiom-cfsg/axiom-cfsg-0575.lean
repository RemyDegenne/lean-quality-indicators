public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace ResM24T

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (r : ResM24T c)

theorem exists_conj_z_or_tE {e : G} (he : e ∈ c.E)
    (he1 : e ≠ 1) : (∃ m ∈ c.G1, m * z * m⁻¹ = e) ∨ ∃ m ∈ c.G1, m * r.tE * m⁻¹ = e := by
  have hw : r.todd ⟨e, he⟩ ≠ 1 := by
    intro h
    apply he1
    have h' : (⟨e, he⟩ : ↥c.E) = 1 := r.todd.injective (h.trans (map_one r.todd).symm)
    exact congrArg Subtype.val h'
  rcases M24G.isDuadClass_or_isSextClass hw with hd | hs
  · exact Or.inr ((r.isDuadClass_todd_iff he).1 hd)
  · exact Or.inl ((r.isSextClass_todd_iff he).1 hs)

end ResM24T
end CFSG.Quasithin.H13.AS91
end
