public section

namespace CFSG.Quasithin.J4M3

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.Sporadic.J4.Native Matrix

open CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Fam CFSG.Quasithin.KGC31 CFSG.Quasithin.Special2

open scoped commutatorElement

section Mat

theorem Mx_y3J : Mx y3J = rowsMatrix (wordRows (locMats ()) (locInvs ()) y3Word) :=
  Mx_wordProd j4Facts.mat _

end Mat
end CFSG.Quasithin.J4M3
end
