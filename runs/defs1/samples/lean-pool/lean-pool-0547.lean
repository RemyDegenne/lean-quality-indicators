@[expose] public section

namespace V7.Stage8Main

/-- The report of the selected certified local trial execution. -/
noncomputable def controllerReport (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (hcached : data.cached.observation = inst.oracle.observe data.input.x0)
    (hlarge : data.input.eps < lpNorm (conjugateExponent data.input.p)
      (inst.oracle.gradient data.input.x0))
    (state : RuntimeControllerState d) : TrialReport d :=
  (controllerLocalSpec data state inst hcached hlarge).report

end V7.Stage8Main
end
