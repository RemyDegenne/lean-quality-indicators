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

attribute [instance 10] ESeminormedAddCommMonoid.toAddCommMonoid

/-- An e-seminormed commutative monoid is a commutative monoid endowed with a continuous enorm. -/
@[to_additive]
class ESeminormedCommMonoid (E : Type*) [TopologicalSpace E]
  extends ESeminormedMonoid E, CommMonoid E where

end
