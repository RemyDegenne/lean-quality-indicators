@[expose] public section

open Function Topology

section Lift

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : C(X, Y)}

/-- `Setoid.quotientKerEquivOfRightInverse` as a homeomorphism. -/
@[simps!]
def Function.RightInverse.homeomorph {f' : C(Y, X)} (hf : Function.RightInverse f' f) :
    Quotient (Setoid.ker f) ≃ₜ Y where
  toEquiv := Setoid.quotientKerEquivOfRightInverse _ _ hf
  continuous_toFun := isQuotientMap_quot_mk.continuous_iff.mpr (map_continuous f)
  continuous_invFun := continuous_quotient_mk'.comp (map_continuous f')

end Lift
end
