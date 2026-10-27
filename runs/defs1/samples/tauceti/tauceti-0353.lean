public section

noncomputable section

open Filter MeasureTheory Set

open scoped unitInterval

namespace TauCeti

/-- Two measurable maps that push `μ` and `ν` forward onto one another and that are mutually
inverse outside a null set: a measure-preserving isomorphism of the two measured spaces modulo
null sets. -/
structure Mod0MeasureIso (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) where
  /-- The forward map, which pushes `μ` forward to `ν`. -/
  toFun : α → β
  /-- The backward map, which pushes `ν` forward to `μ`. -/
  invFun : β → α
  measurable_toFun : Measurable toFun
  measurable_invFun : Measurable invFun
  map_toFun : Measure.map toFun μ = ν
  map_invFun : Measure.map invFun ν = μ
  left_inv_ae : (fun x => invFun (toFun x)) =ᵐ[μ] id
  right_inv_ae : (fun y => toFun (invFun y)) =ᵐ[ν] id

end TauCeti
end
end
