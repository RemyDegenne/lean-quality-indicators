@[expose] public section

universe u v

namespace OrderIso

variable {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β]

theorem isCompactElement (e : α ≃o β) {k : α} (hk : IsCompactElement k) :
    IsCompactElement (e k) := by
  intro s z hs hd hz hkz
  have hs' : (e.symm '' s).Nonempty := by
    obtain ⟨y, hy⟩ := hs
    exact ⟨e.symm y, y, hy, rfl⟩
  have hd' : DirectedOn (· ≤ ·) (e.symm '' s) := by
    exact DirectedOn.mono_comp e.symm.monotone hd
  have hz' : IsLUB (e.symm '' s) (e.symm z) := e.symm.isLUB_image'.mpr hz
  have hkz' : k ≤ e.symm z := e.le_symm_apply.mpr hkz
  obtain ⟨x, ⟨y, hy, rfl⟩, hky⟩ := hk (e.symm '' s) (e.symm z) hs' hd' hz' hkz'
  exact ⟨y, hy, e.le_symm_apply.mp hky⟩

end OrderIso
end
