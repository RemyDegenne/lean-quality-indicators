/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.QuotientTorsion
public import GroupTheory.IndexNSmul

/-!
# Finite torsion in additive quotients

Let `V` be any additive commutative group and `L` a finitely generated additive
subgroup. If multiplication by `n : ℕ` is bijective on `V`, its kernel on `V / L`
is finite and has natural cardinality `n ^ Module.finrank ℤ L`.
Here integer module finrank is torsion-free rank, not the minimum number of
additive generators. The subgroup need not be free, and no finite-generation
assumption is imposed on the ambient group or its quotient. Bijectivity is
required only at the specified scalar.

The underlying identification is
`QuotientAddGroup.nsmulTorsionEquivQuotient : (V / L)[n] ≃+ L / nL`.
Mathlib already supplies finite index of `nL` for nonzero `n` and finitely
generated `L`; the cardinality formula uses the injective scalar-index result
`AddSubgroup.index_range_nsmul_of_injective`. No new torsion carrier is used.
All natural scalars are allowed: at zero the ambient bijectivity hypothesis
forces `V` to be trivial, and the cardinality equation is `1 = 0 ^ 0`.

Finite generation is essential to the cardinality formula. For `V = L = ℚ`
and `n = 2`, doubling is bijective and the quotient kernel is trivial, but
`Module.finrank ℤ ℚ = 1`, so the proposed count without finite generation
would be two rather than one.

Ambient injectivity alone does not suffice for the cardinality formula. For
`V = L = ℤ` and `n = 2`, doubling is injective but not surjective, and the
quotient kernel has cardinality one whereas `2 ^ Module.finrank ℤ ℤ = 2`.

For a full lattice in a complex vector space of dimension `g`, separately
supplying the lattice rank `2 * g` recovers the finite-level count `n ^ (2 * g)`.
The free lattice case can also use Mathlib's existing free scalar-index formula
directly. No complex uniformization, lattice-rank theorem, tensor comparison,
inverse limit, Tate-module construction or scheme-point correspondence is asserted.

## References

* Mathlib's `Mathlib.GroupTheory.FiniteAbelian.Basic` and
  `Mathlib.GroupTheory.IndexNSmul` for the finite-index and free-index providers.
* J. S. Milne, *Abelian Varieties*, I.10, Remark 10.7, p. 45, for the
  motivating complex-torus finite-level calculation.
-/

@[expose] public section

universe u

namespace QuotientAddGroup

variable {V : Type u} [AddCommGroup V] (L : AddSubgroup V) [AddGroup.FG L]
  (n : ℕ)

/-- If multiplication by `n` is bijective on `V` and `L` is finitely generated,
the `n`-torsion subgroup of `V / L` is finite. This includes `n = 0`, when the
bijectivity hypothesis forces the ambient group to be trivial. -/
theorem finite_ker_nsmul_quotient
    (hn : Function.Bijective (nsmulAddMonoidHom (α := V) n)) :
    Finite (nsmulAddMonoidHom (α := V ⧸ L) n).ker := by
  by_cases hn0 : n = 0
  · subst n
    let : Subsingleton V := ⟨fun a b => hn.1 (by simp)⟩
    infer_instance
  · let : (nsmulAddMonoidHom (α := L) n).range.FiniteIndex :=
      AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg L hn0
    exact Finite.of_equiv _ (nsmulTorsionEquivQuotient L n hn).symm.toEquiv

/-- The `n`-torsion subgroup of `V / L` has cardinality `n` to the integer
module finrank of `L`. Only finite generation of `L` and ambient bijectivity at
this scalar are required, not freeness or global torsion-freeness. -/
theorem natCard_ker_nsmul_quotient
    (hn : Function.Bijective (nsmulAddMonoidHom (α := V) n)) :
    Nat.card (nsmulAddMonoidHom (α := V ⧸ L) n).ker = n ^ Module.finrank ℤ L := by
  have hinjL : Function.Injective (nsmulAddMonoidHom (α := L) n) := by
    intro a b hab
    exact Subtype.ext (hn.1 (congrArg Subtype.val hab))
  calc
    _ = Nat.card (L ⧸ (nsmulAddMonoidHom (α := L) n).range) :=
      Nat.card_congr (nsmulTorsionEquivQuotient L n hn).toEquiv
    _ = (nsmulAddMonoidHom (α := L) n).range.index :=
      (AddSubgroup.index_eq_card _).symm
    _ = n ^ Module.finrank ℤ L :=
      AddSubgroup.index_range_nsmul_of_injective (A := L) n hinjL

end QuotientAddGroup
