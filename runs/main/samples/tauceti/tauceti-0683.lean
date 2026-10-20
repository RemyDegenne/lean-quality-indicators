public section

namespace TauCeti

namespace ZMod

theorem exists_isPrimitiveRoot_of_dvd_sub_one {p d : ℕ} (hp : p.Prime) (hd : d ∣ p - 1) :
    ∃ ζ : ZMod p, IsPrimitiveRoot ζ d :=
  have := hasEnoughRootsOfUnity_of_dvd_sub_one hp hd
  HasEnoughRootsOfUnity.exists_isPrimitiveRoot (ZMod p) d

end ZMod
end TauCeti
end
