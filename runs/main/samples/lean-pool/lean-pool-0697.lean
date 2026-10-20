@[expose] public section

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}

namespace LineageMassMaps

variable {Φ : ℕ → FlagDecomposition p d f}

variable (D : LineageMassMaps Φ)

variable {L : ℕ} (hL : ∀ i, L ≤ D.cutoff i)

theorem mapOfSameAncestry_real_preimage {i j : ℕ} (h : i ≤ j)
    (x : D.system.LowNode L i) (y : D.system.LowNode L j)
    (heq : D.system.ancestry (D.system_injectiveBelow hL) i x =
      D.system.ancestry (D.system_injectiveBelow hL) j y)
    (S : Set (RealCoord ((Φ i).flag.rank x))) :
    (D.mapOfSameAncestry hL h x y heq).coord.real ⁻¹' S =
      (D.transport hL h).subdivision.fibre y ⁻¹'
        ((D.transport_node_eq_of_ancestry_eq hL h x y heq).symm ▸ S) :=
  (D.transport hL h).stableAt_real_preimage y x.val
    (D.transport_node_eq_of_ancestry_eq hL h x y heq) S

end LineageMassMaps
end EGZ.FlagDecomposition
end
