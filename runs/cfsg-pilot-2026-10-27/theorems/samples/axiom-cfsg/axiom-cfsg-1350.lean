public section

namespace CFSG.StandardType.QTwo

theorem qTwoGlobBnd_vx_ne_zero
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G} {m : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥Bs ≃+ V}
    (hLM : QTwoLocalModel m Bs L x) (hx1 : x ≠ 1) :
    ι (Additive.ofMul (⟨x, hLM.mem⟩ : ↥Bs)) ≠ 0 := by
  intro h0
  have hzero : ι ((1 : ↥Bs) : Additive ↥Bs) = 0 := map_zero ι
  have hι : ι (⟨x, hLM.mem⟩ : ↥Bs) = ι (1 : ↥Bs) := h0.trans hzero.symm
  have h1 : (⟨x, hLM.mem⟩ : ↥Bs) = 1 := ι.injective hι
  exact hx1 (congrArg Subtype.val h1)

end CFSG.StandardType.QTwo
end
