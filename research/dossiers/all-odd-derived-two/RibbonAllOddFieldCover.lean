import RibbonAllOddAdapter
import RibbonAllOddFieldCore
import RibbonAllOddSlopeFinal
namespace RibbonAllOddField
universe u v
theorem field_cover : RibbonOdd.FieldCover.{u,v} RibbonOddFinite.Bad :=
  field_adapter (fun a b n two odd an bn a1 => field_words_of slope_full a b n two odd an bn a1)
end RibbonAllOddField
#print axioms RibbonAllOddField.field_cover
