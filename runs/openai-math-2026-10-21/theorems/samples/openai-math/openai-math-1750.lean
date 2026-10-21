namespace OAI

open scoped commutatorElement

namespace LittleFinitistic

namespace Presentation

theorem shiftHom_zero : shiftHom 0 = MonoidHom.id AuxiliaryGroup := by
  apply PresentedGroup.ext
  intro s
  cases s <;> simp [shiftHom,shiftData,data,evaluate]

end Presentation
end LittleFinitistic
end OAI
