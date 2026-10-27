public section

namespace CFSG.Quasithin.ModG

open scoped Pointwise

open MulAction CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.L239

theorem smul_blk_eq (g : Equiv.Perm (Fin 22)) (l : List ℕ) (h : ∀ x : Fin 22, x.val ∈ l → (g x).val ∈ l) :
    g • M22Insp.blk l = M22Insp.blk l :=
  smul_eq_of_forall g _ fun x hx => (mem_blk l _).2 (h x ((mem_blk l x).1 hx))

end CFSG.Quasithin.ModG
end
