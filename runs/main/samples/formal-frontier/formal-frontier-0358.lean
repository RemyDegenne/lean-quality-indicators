@[expose] public section

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem powerImage_index_eq_iff_exponents (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (n : ℕ) (hn : 0 < n) :
    (powerImage G hG n : Subgroup G).index = n ↔
      ∀ p : Nat.Primes, (n.factorization p.1 : ℕ∞) ≤ hG.exponents p := by
  let _ : NeZero n := ⟨hn.ne'⟩
  let hH := finiteCyclic_isProcyclic n
  have hcard : Nat.card (finiteCyclic n) = n := by
    change Nat.card (Multiplicative (ZMod n)) = n
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  constructor
  · intro hindex
    let g := hG.choose
    have hg : IsTopologicalGenerator G g := hG.choose_spec
    let e := powerImage_zmodContinuousMulEquiv G hG g hg n hn hindex
    let f : G →ₜ* finiteCyclic n :=
      ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' (powerImage G hG n : Subgroup G)),
        e.symm.continuous_toFun.comp QuotientGroup.continuous_mk⟩
    have hf : Function.Surjective f :=
      e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
    have hbound := (exists_surjective_continuousHom_iff_exponents_le hG hH).mp ⟨f, hf⟩
    intro p
    rw [← finiteCyclic_exponents_eq_factorization n p]
    exact hbound p
  · intro hbound
    obtain ⟨f, hf⟩ := (exists_surjective_continuousHom_iff_exponents_le hG hH).mpr
      (fun p ↦ by rw [finiteCyclic_exponents_eq_factorization]; exact hbound p)
    have hker : (powerImage G hG n : Subgroup G) ≤ f.toMonoidHom.ker := by
      intro x hx
      obtain ⟨y, rfl⟩ := (mem_powerImage_iff G hG n x).mp hx
      change f (y ^ n) = 1
      rw [map_pow]
      exact (congrArg (fun exponent : ℕ ↦ f y ^ exponent) hcard).symm.trans
        (pow_card_eq_one' (x := f y))
    have hsurj : f.toMonoidHom.ker.index = n := by
      rw [Subgroup.index_ker]
      have hrange : Function.Surjective
          ((↑) : f.toMonoidHom.range → finiteCyclic n) := by
        intro y
        exact ⟨⟨y, hf y⟩, rfl⟩
      calc
        Nat.card f.toMonoidHom.range = Nat.card (finiteCyclic n) :=
          Nat.card_congr (Equiv.ofBijective Subtype.val
            ⟨Subtype.coe_injective, hrange⟩)
        _ = n := hcard
    have hindex_dvd : n ∣ (powerImage G hG n : Subgroup G).index := by
      calc
        n = f.toMonoidHom.ker.index := hsurj.symm
        _ ∣ _ := Subgroup.index_dvd_of_le hker
    exact Nat.dvd_antisymm (powerImage_index_dvd G hG n hn) hindex_dvd

end ProfiniteGrp
end
