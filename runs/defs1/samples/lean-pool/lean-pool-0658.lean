@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Embed a body configuration in the body phase of `forBinaryWorkTM`. -/
def forBinaryWorkBodyWrap (driverIdx : Fin n) (body : TM n)
    (cfg : Cfg n body.Q) : Cfg n (forBinaryWorkTM driverIdx body).Q :=
  { state := .inr cfg.state
    input := cfg.input
    work := cfg.work
    output := cfg.output }

end TM
end Complexity
end
