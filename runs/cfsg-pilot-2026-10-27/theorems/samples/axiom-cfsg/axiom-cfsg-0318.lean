public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Certificates

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

theorem prep_onSevenPow {x : Array ℕ} {X : Equiv.Perm (Fin N)} (hx : PRep N x X) :
    ∀ e, PRep N (onSevenPow x e) (X ^ e)
  | 0 => by simpa [onSevenPow] using (prep_pid (n := N))
  | e + 1 => by
    rw [onSevenPow, pow_succ']
    exact prep_pcomp hx (prep_onSevenPow hx e)

end CFSG.RankThree.Native
end
