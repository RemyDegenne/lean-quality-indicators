/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.PadicInt
public import AdicModules.AdicCompletion.Topology
public import AdicModules.Topology.Algebra.AdicTopology
public import AdicModules.Topology.Algebra.PadicInt

/-!
# Topology of the integer completion comparison

The existing residue-normalized algebra equivalence from the `(p)`-adic completion of
`ℤ` to `ℤ_[p]` is a homeomorphism for the explicitly specified mapped-ideal adic topology
on the completion and the existing norm topology on the p-adic integers. The domain
choice is the one used by `AdicCompletion.abstractCompletion`; it does not depend on the
comparison map. No global topology instance, new carrier or new equivalence is introduced.

## References

* Mathlib's adic topology construction and `WithIdeal.uniformEquiv` by Patrick Massot.
* Mathlib's p-adic residue universal property by Johan Commelin and Robert Y. Lewis,
  used by `AdicCompletion.padicIntEquiv`.
-/

@[expose] public section

namespace AdicCompletion

/-- The existing algebraic comparison is a homeomorphism from the mapped-ideal adic
topology on the integer completion to the usual norm topology on the p-adic integers. -/
theorem isHomeomorph_padicIntEquiv (p : ℕ) [Fact p.Prime] :
    @IsHomeomorph (AdicCompletion (Ideal.span {(p : ℤ)}) ℤ) ℤ_[p]
      (((Ideal.span {(p : ℤ)}).map
        (algebraMap ℤ (AdicCompletion (Ideal.span {(p : ℤ)}) ℤ))).adicTopology)
      (inferInstance : TopologicalSpace ℤ_[p]) (padicIntEquiv p) := by
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  let C := AdicCompletion I ℤ
  let J : Ideal C := I.map (algebraMap ℤ C)
  have htop : (inferInstance : TopologicalSpace ℤ_[p]) =
      (Ideal.span {(p : ℤ_[p])}).adicTopology := PadicInt.isAdic_span_p p
  rw [htop]
  let : WithIdeal C := ⟨J⟩
  let : WithIdeal ℤ_[p] := ⟨Ideal.span {(p : ℤ_[p])}⟩
  let : UniformSpace ℤ_[p] := WithIdeal.instUniformSpace ℤ_[p]
  have hmap : J.map (padicIntEquiv p).toRingEquiv.toRingHom =
      Ideal.span {(p : ℤ_[p])} := by
    simp [J, I, Ideal.map_span]
  exact (WithIdeal.uniformEquiv (padicIntEquiv p).toRingEquiv hmap).toHomeomorph.isHomeomorph

end AdicCompletion
