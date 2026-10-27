public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

namespace FourGroupOddUnitary

open FourGroupOddBilinear

section General

variable {E : Type*} [Field E] {σ : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
  (h : V →ₛₗ[σ] V →ₗ[E] E)

theorem mem_unitaryScalars {g : sesqSpecialUnitaryGroup h} :
    g ∈ unitaryScalars h ↔ ∃ c : Eˣ,
      ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) = (c : E) • LinearMap.id :=
  Iff.rfl

end General
end FourGroupOddUnitary
end CFSG.LocalAnalysis.ComponentInitial
end
