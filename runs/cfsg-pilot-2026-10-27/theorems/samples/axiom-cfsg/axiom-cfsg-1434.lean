public section

namespace CFSG.Quasithin.KGC31.He

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31 CFSG.Sporadic.HeldB
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Quasithin.KGC31.Native
  _root_.Certificates

theorem no_o2_16 : ∀ m ∈ Ch1.SporLat.He.heMems, m.o2 ≠ 16 := by
  intro m hm
  simp only [Ch1.SporLat.He.heMems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end CFSG.Quasithin.KGC31.He
end
