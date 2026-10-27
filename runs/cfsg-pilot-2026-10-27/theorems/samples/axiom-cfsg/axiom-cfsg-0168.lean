public section

namespace CFSG.Quasithin.B3

open scoped commutatorElement

variable {n : ℕ} {k : Mod}

theorem gmap_fixV {H : Subgroup (Gp n)} {g : Gp n} (hg : g ∈ H) :
    gmap g (fixV (H.map (Mod.act n k))) = fixV (H.map (Mod.act n k)) := by
  ext w
  rw [mem_gmap, mem_fixV, mem_fixV]
  constructor
  · intro h x hx
    have h1 := h (Mod.act n k g) (Subgroup.mem_map_of_mem _ hg)
    rw [act_act_inv] at h1
    have h2 := h x hx
    rw [← h1] at h2
    exact h2
  · intro h x hx
    have h1 := h (Mod.act n k g⁻¹) (Subgroup.mem_map_of_mem _ (H.inv_mem hg))
    rw [h1]
    exact h x hx

end CFSG.Quasithin.B3
end
