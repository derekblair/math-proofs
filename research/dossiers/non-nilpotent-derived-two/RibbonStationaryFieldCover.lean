import RibbonStationaryFieldFinal
import RibbonStationaryFieldAdapter
namespace RibbonStationaryField
universe u v
theorem field_cover : RibbonP11.FieldCover.{u,v} RibbonP11Adapters.Bad :=
  field_adapter (fun a b n two odd no3 an bn a1 => field_words a b n two odd no3 an bn a1)
end RibbonStationaryField
#print axioms RibbonStationaryField.field_cover
