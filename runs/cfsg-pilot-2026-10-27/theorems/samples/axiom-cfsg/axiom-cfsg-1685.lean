public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem excCoreNormalizer_E7 : ExcCoreNormalizer 4 .E7 :=
  excCoreNormalizer_of_simplyLaced (by decide) (Or.inr (Or.inl rfl)) ExcRaw.rootSep_four

end CFSG.StandardType.GGQ2Frame.ExcPlacement
end
