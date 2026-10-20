@[expose] public section

open Metric Set

namespace Schoenflies

variable {Ω C D S : Set Plane} {a b z : Plane}

theorem exists_crosscut_of_biUnion_finite {ι : Type*} {s : Set ι} {A : ι → Set Plane}
    (hs : s.Finite) (hA : ∀ i ∈ s, IsPolygonal (A i))
    (hconn : IsPreconnected (⋃ i ∈ s, A i)) (hab : a ≠ b)
    (haC : a ∈ C) (hbC : b ∈ C)
    (ha : a ∈ ⋃ i ∈ s, A i) (hb : b ∈ ⋃ i ∈ s, A i)
    (hmeet : (⋃ i ∈ s, A i) ∩ C ⊆ {a, b}) (hD : (⋃ i ∈ s, A i) \ C ⊆ D) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ (⋃ i ∈ s, A i) ∧ IsArcBetween (poly ws) a b ∧
      poly ws ∩ C = {a, b} ∧ poly ws \ {a, b} ⊆ D := by
  obtain ⟨ws, hws, hhead, hlast, hsub, harc⟩ :=
    exists_simple_poly_of_biUnion_finite hs hA hconn hab ha hb
  have haw : a ∈ poly ws := hhead ▸ head_mem_poly hws
  have hbw : b ∈ poly ws := hlast ▸ getLast_mem_poly hws
  refine ⟨ws, hws, hhead, hlast, hsub, harc, ?_, ?_⟩
  · refine subset_antisymm (fun x hx => hmeet ⟨hsub hx.1, hx.2⟩) ?_
    rintro x (rfl | rfl)
    exacts [⟨haw, haC⟩, ⟨hbw, hbC⟩]
  · -- Off its two endpoints the arc misses `C`, since the union meets `C` only there.
    rintro x ⟨hx, hxab⟩
    exact hD ⟨hsub hx, fun hxC => hxab (hmeet ⟨hsub hx, hxC⟩)⟩

end Schoenflies
end
