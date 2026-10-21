namespace OAI

namespace MUB6.TaoCertificate

open TaoArithmetic

theorem source216_checked : normalize (row ![-1, 1, -1, 0, 1, 0] ![0, -1, 0, 0, 1, 0] (3, 3)) = source216 := by
  decide +kernel

end MUB6.TaoCertificate
end OAI
