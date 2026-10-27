public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7.VL

variable {G : Type} [Group G]

theorem comm_zpw {u v : G} (huv : u * v = v * u) (m n : ZMod 3) :
    zpw u m * zpw v n = zpw v n * zpw u m :=
  (Commute.pow_pow (show Commute u v from huv) m.val n.val).eq

end CFSG.GH74.QTGen4.Recog.G23.P7.VL
end
