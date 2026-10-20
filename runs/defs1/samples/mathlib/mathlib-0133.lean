@[expose] public section

notation:25 (name := «MulActionHomLocal≺») X " →ₑ[" φ:25 "] " Y:0 => MulActionHom φ X Y

notation:25 (name := «MulActionHomIdLocal≺») X " →[" M:25 "] " Y:0 => MulActionHom (@id M) X Y

notation:25 (name := «AddActionHomLocal≺») X " →ₑ[" φ:25 "] " Y:0 => AddActionHom φ X Y

notation:25 (name := «AddActionHomIdLocal≺») X " →[" M:25 "] " Y:0 => AddActionHom (@id M) X Y

section DistribMulAction

variable {M : Type*} [Monoid M]

variable {N : Type*} [Monoid N]

variable {P : Type*} [Monoid P]

variable (φ : M →* N) (φ' : N →* M) (ψ : N →* P) (χ : M →* P)

variable (A : Type*) [Monoid A] [MulDistribMulAction M A]

variable (B : Type*) [Monoid B] [MulDistribMulAction N B]

variable (B₁ : Type*) [Monoid B₁] [MulDistribMulAction M B₁]

variable (C : Type*) [Monoid C] [MulDistribMulAction P C]

variable (A' : Type*) [Group A'] [MulDistribMulAction M A']

variable (B' : Type*) [Group B'] [MulDistribMulAction N B']

@[inherit_doc]
notation:25 (name := «DistribMulActionHomLocal≺»)
  A " →ₑ+[" φ:25 "] " B:0 => DistribMulActionHom φ A B

@[inherit_doc]
notation:25 (name := «DistribMulActionHomIdLocal≺»)
  A " →+[" M:25 "] " B:0 => DistribMulActionHom (MonoidHom.id M) A B

@[inherit_doc]
notation:25 (name := «MulDistribMulActionHomLocal≺»)
  A " →ₑ*[" φ:25 "] " B:0 => MulDistribMulActionHom φ A B

@[inherit_doc]
notation:25 (name := «MulDistribMulActionHomIdLocal≺»)
  A " →*[" M:25 "] " B:0 => MulDistribMulActionHom (MonoidHom.id M) A B

variable (R : Type*) [Semiring R] [MulSemiringAction M R]

variable (R' : Type*) [Ring R'] [MulSemiringAction M R']

variable (S : Type*) [Semiring S] [MulSemiringAction N S]

variable (S' : Type*) [Ring S'] [MulSemiringAction N S']

variable (T : Type*) [Semiring T] [MulSemiringAction P T]

@[inherit_doc]
notation:25 (name := «MulSemiringActionHomLocal≺»)
  R " →ₑ+*[" φ:25 "] " S:0 => MulSemiringActionHom φ R S

@[inherit_doc]
notation:25 (name := «MulSemiringActionHomIdLocal≺»)
  R " →+*[" M:25 "] " S:0 => MulSemiringActionHom (MonoidHom.id M) R S

/-- `MulSemiringActionHomClass F φ R S` states that `F` is a type of morphisms preserving
the ring structure and equivariant with respect to `φ`.

You should extend this class when you extend `MulSemiringActionHom`. -/
class MulSemiringActionSemiHomClass (F : Type*)
    {M N : outParam Type*} [Monoid M] [Monoid N]
    (φ : outParam (M → N))
    (R S : outParam Type*) [Semiring R] [Semiring S]
    [DistribMulAction M R] [DistribMulAction N S] [FunLike F R S] : Prop
    extends DistribMulActionSemiHomClass F φ R S, RingHomClass F R S

end DistribMulAction
end
