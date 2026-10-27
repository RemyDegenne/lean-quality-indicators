@[expose] public section

noncomputable section

section

@[expose] public section

namespace LeanCert.Engine

open LeanCert.Core

/-- Computable (Bool) domain validity check for Dyadic evaluation. -/
def checkDomainValidDyadic (e : Expr) (ρ : IntervalDyadicEnv) (cfg : DyadicConfig := {}) : Bool :=
  match e with
  | Expr.const _ => true
  | Expr.var _ => true
  | Expr.add e₁ e₂ => checkDomainValidDyadic e₁ ρ cfg && checkDomainValidDyadic e₂ ρ cfg
  | Expr.mul e₁ e₂ => checkDomainValidDyadic e₁ ρ cfg && checkDomainValidDyadic e₂ ρ cfg
  | Expr.neg e => checkDomainValidDyadic e ρ cfg
  | Expr.inv e => checkDomainValidDyadic e ρ cfg &&
      (decide ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.lo > 0) ||
       decide ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.hi < 0))
  | Expr.exp e => checkDomainValidDyadic e ρ cfg
  | Expr.sin e => checkDomainValidDyadic e ρ cfg
  | Expr.cos e => checkDomainValidDyadic e ρ cfg
  | Expr.log e => checkDomainValidDyadic e ρ cfg &&
      decide ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.lo > 0)
  | Expr.atan e => checkDomainValidDyadic e ρ cfg
  | Expr.arsinh e => checkDomainValidDyadic e ρ cfg
  | Expr.atanh e => checkDomainValidDyadic e ρ cfg &&
      decide ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.lo > -1) &&
      decide ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.hi < 1)
  | Expr.sinc e => checkDomainValidDyadic e ρ cfg
  | Expr.erf e => checkDomainValidDyadic e ρ cfg
  | Expr.sinh e => checkDomainValidDyadic e ρ cfg
  | Expr.cosh e => checkDomainValidDyadic e ρ cfg
  | Expr.tanh e => checkDomainValidDyadic e ρ cfg
  | Expr.sqrt e => checkDomainValidDyadic e ρ cfg
  | Expr.namedConst _ => true

end LeanCert.Engine
end
end
end
end
