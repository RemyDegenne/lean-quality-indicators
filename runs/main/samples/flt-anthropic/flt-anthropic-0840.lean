namespace P2MW.S_fermatLastTheoremFive

namespace FLT5

namespace Zphi

scoped instance : Zero Zphi := ⟨⟨0, 0⟩⟩

scoped instance : One Zphi := ⟨⟨1, 0⟩⟩

scoped instance : Inhabited Zphi := ⟨0⟩

@[scoped simp] theorem im_zero : (0 : Zphi).im = 0 := rfl

end Zphi
end FLT5
end P2MW.S_fermatLastTheoremFive
