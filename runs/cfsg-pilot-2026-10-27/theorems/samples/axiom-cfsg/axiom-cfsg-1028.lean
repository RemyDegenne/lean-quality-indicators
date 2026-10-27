public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.CosetTable CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

section Cert

theorem sHom_injective : Function.Injective sHom :=
  pgHom_injective sGen_rels (card_PG_le false).1 (card_PG_le false).2 le_card_closure_sGen

end Cert
end CFSG.Quasithin.Background.Harris.R1.J2Vert
end
