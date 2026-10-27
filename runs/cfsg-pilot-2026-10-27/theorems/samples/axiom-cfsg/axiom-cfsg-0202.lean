public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

open scoped Matrix

namespace Z3D

section Unpack

variable {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}

theorem exists_column_of_binaryNaturalSL {m a : ℕ} (h : BinaryNaturalSL H ⊤ ⊥ m a) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
      ∃ (π : ↥(StatedSL m K) →* ↥H) (b : W ≃* Multiplicative (Fin m → K)),
        Function.Surjective π ∧ ∀ (γ : ↥(StatedSL m K)) (w : W),
          b ((π γ : MulAut W) w) = Multiplicative.ofAdd
            (((γ : Matrix.GeneralLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
              Multiplicative.toAdd (b w)) := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := h
  obtain ⟨b, hb⟩ := exists_column_of_nat_realizes hπ
  exact ⟨K, hK, hf, hc, π, b, hπ.1, hb⟩

end Unpack
end Z3D
end CFSG.Quasithin
end
