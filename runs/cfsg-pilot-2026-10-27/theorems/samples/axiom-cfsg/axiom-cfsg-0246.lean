public section

namespace CFSG.StandardType

theorem ggBstarBoundDeltaUnitaryDvdInput_holds :
    GGBstarBoundDeltaUnitaryDvdInput := by
  intro K _ _ n d p hK hn hd5 hp hpq _
  exact TableBUDL.ggBstarBoundDelta_unitary hK hn hd5 hp hpq _

end CFSG.StandardType
end
