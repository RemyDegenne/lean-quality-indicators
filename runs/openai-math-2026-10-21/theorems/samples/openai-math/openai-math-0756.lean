namespace OAI

namespace PartitionPilot.Forcing

open Cardinal Compression.RecursiveMaps

open scoped Cardinal

namespace Rows

open CountableColumns

universe u

open MainStage.OrdinalRun

theorem positions_cardinal_lt (κ : Cardinal.{1}) (inaccessible : κ.IsInaccessible) : #Position < κ :=
  SizeBounds.subtype_lt κ (countableOrdinalLabels_final_cardinal_bounds κ inaccessible).1 _

end Rows
end PartitionPilot.Forcing
end OAI
