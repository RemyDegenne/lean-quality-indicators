public section

namespace CFSG.Sporadic.Fi23.Native

open CFSG.F3.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem W.toV_ofV {v : V} (hp : v.p < 2 ^ 256) (hm : v.m < 2 ^ 256) : (ofV v).toV = v := by
  simp only [ofV, W.toV, join_ofV _ hp, join_ofV _ hm]

end CFSG.Sporadic.Fi23.Native
end
