public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology MeasureTheory Module.End Set TopologicalSpace

open scoped ENNReal InnerProduct InnerProductSpace

section Domain

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} {C : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

/-- **The solution operator of the Dirichlet problem**: the map sending `f ∈ L²(Ω)` to the
value of the unique weak solution of `L u = f` in `Ω`, `u = 0` on `∂Ω`.  It inverts the
Dirichlet problem, and it is the operator whose spectrum carries the Dirichlet eigenvalue
problem; `TauCeti.PDE.dirichletSolutionOperator_apply` identifies its value with the
Lax--Milgram solution. -/
def dirichletSolutionOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    Lp ℝ 2 (mu.restrict Omega) →L[ℝ] Lp ℝ 2 (mu.restrict Omega) :=
  hcoercive.formSolutionOperator W1p0.valueL

end Domain
end PDE
end TauCeti
end
end
