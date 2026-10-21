namespace OAI

namespace PowerSaving.RAM

open Ty Selection Spectral

noncomputable section

namespace Bench

universe U V

variable {ι : Type U} {κ : Type V} {m : Bool} {b : Bench m ι} {q : Bench m κ}
  {s t : Ty} {S n N : ι→ℕ} {ret : Bool}

lemma table_scale {x y : ι→Line} {cl} (h : b.Nick N)
    (hx : b.Moves (fun _ => 0) (a sc) fun i => Tape.tab (N i) (x i))
    (hy : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (N i) (y i)) :
    b.Moves N (a (c cl)) fun i => Tape.tab (N i) fun j => x i j*y i j := by
  have F := Instant.scan b N
  refine arrayNow h _ ((Moves.pick (t:=sc) (n:=fun i : During N => N i.i)
    (k:=During.j) (fun i j => x i.i j) (hx.transfer F) (chop h).close During.hj).mul
    (Moves.pick (t:=c cl) (n:=fun i : During N => N i.i) (k:=During.j) (fun i j => y i.i j)
      (hy.transfer F) (chop h).close During.hj))

end Bench
end
end PowerSaving.RAM
end OAI
