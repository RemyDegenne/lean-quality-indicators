@[expose] public section

namespace Zeta32.ArithSum

noncomputable section

theorem block_16 : blockSum 16 = 85354574727978923 / 235376990336648160 := by
  unfold blockSum; decide +kernel

end
end Zeta32.ArithSum
end
