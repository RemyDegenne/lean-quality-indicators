public section

variable {α E G : Type*}

open Filter Bornology

open ENNReal Filter NNReal

export Norm (norm)

export NNNorm (nnnorm)

export ENorm (enorm)

@[inherit_doc] notation "‖" e "‖" => norm e

@[inherit_doc] notation "‖" e "‖₊" => nnnorm e

@[inherit_doc] notation "‖" e "‖ₑ" => enorm e

attribute [instance 10] ESeminormedAddMonoid.toAddMonoid

attribute [instance 10] ESeminormedMonoid.toMonoid

/-- An e-seminormed commutative monoid is an additive commutative monoid endowed with a continuous
enorm.

We don't have `ESeminormedAddCommMonoid` extend `EMetricSpace`, since the canonical instance `ℝ≥0∞`
is not an `EMetricSpace`. This is because `ℝ≥0∞` carries the order topology, which is distinct from
the topology coming from `edist`. -/
class ESeminormedAddCommMonoid (E : Type*) [TopologicalSpace E]
  extends ESeminormedAddMonoid E, AddCommMonoid E where

end
