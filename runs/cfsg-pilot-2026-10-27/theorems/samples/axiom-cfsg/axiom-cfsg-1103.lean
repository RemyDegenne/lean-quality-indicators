public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_map_conj {X : Subgroup G} (hX : IsElemAbelian 2 X) (g : G) :
    IsElemAbelian 2 (X.map (MulAut.conj g).toMonoidHom) := CFSG.Open.IsElemAbelian.map hX _

end CFSG.CGT.PushingUpLit.T2K
end
