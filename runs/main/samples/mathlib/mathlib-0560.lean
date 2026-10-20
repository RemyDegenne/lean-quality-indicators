open Bundle FiberBundle Function NormedSpace VectorField

open scoped Manifold ContDiff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

variable
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {X X' X'' Y Y' Y'' Z Z' : Π x : M, TangentSpace I x}

open scoped RealInnerProductSpace

variable (cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _))

local syntax:max "∇" term:arg term:arg : term

local macro_rules | `(∇ $X $σ) => `(fun (x : M) ↦ cov $σ x ($X x))

local syntax:max "∇'" term:arg term:arg : term

local macro_rules | `(∇' $X $σ) => `(fun (x : M) ↦ cov' $σ x ($X x))

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

local notation "⟪" X ", " Y "⟫" => fun x ↦ inner ℝ (X x) (Y x)

namespace CovariantDerivative

variable {x : M}

variable [FiniteDimensional ℝ E]

section existence

public theorem leviCivitaConnection_apply_inner
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    ⟪leviCivitaConnection I M Y x (X x), Z x⟫ =
      (d% ⟪Y, Z⟫ x (X x) + d% ⟪Z, X⟫ x (Y x) - d% ⟪X, Y⟫ x (Z x)
      - ⟪Y, VectorField.mlieBracket I X Z⟫ x
      - ⟪Z, VectorField.mlieBracket I Y X⟫ x
      + ⟪X, VectorField.mlieBracket I Z Y⟫ x) / 2 :=
  leviCivitaAux_apply_inner _ hX hY hZ

end existence
end CovariantDerivative
