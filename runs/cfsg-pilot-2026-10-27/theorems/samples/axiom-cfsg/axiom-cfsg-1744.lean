public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims126b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

section Sylow3

variable {G : Type} [Group G] [Finite G]

theorem comm_of_mem_centerOf {R : Subgroup G} {z : G} (hz : z ∈ centerOf R) {r : G} (hr : r ∈ R) :
    r * z = z * r := by
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.1 hz
  have hcr := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨r, hr⟩)
  have hc' : (c : G) = z := hcz
  have h3 : r * (c : G) = (c : G) * r := by simpa using hcr
  rw [← hc']
  exact h3

end Sylow3
end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims126b
end
