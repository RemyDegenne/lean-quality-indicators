public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 CFSG.Blueprint

open CFSG.Sporadic.Ru.Native (ruData)

theorem twoExtensionFor_Ru :
    TwoExtensionFor .Ru := by
  obtain ⟨R, hRp, hRi, hmodel⟩ := ru_charPair
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  intro X _ _ T K hK hT hTi hKT ⟨e⟩
  have : K.Normal := hK
  exact @twoExtension_of_charPair_of_equiv (J ruData) (NativeSporadic.Carrier .Ru) inferInstance
    inferInstance inferInstance (seedEquiv hF.toBaseFacts).symm R hRp hRi hmodel X inferInstance
    inferInstance T K inferInstance hT hTi hKT e

end CFSG.QuasithinUnique.Setup.X1
end
