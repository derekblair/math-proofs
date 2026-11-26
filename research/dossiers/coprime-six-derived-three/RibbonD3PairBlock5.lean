import RibbonD3PairCheck5
import RibbonD3Orbit
namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock5 (i : Fin 30) : let z := pairLabel (⟨150+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact ⟨_,pairChecked150⟩
  · exact ⟨_,pairChecked151⟩
  · exact ⟨_,pairChecked152⟩
  · exact ⟨_,pairChecked153⟩
  · exact ⟨_,pairChecked154⟩
  · exact ⟨_,pairChecked155⟩
  · exact ⟨_,pairChecked156⟩
  · exact ⟨_,pairChecked157⟩
  · exact ⟨_,pairChecked158⟩
  · exact ⟨_,pairChecked159⟩
  · exact ⟨_,pairChecked160⟩
  · exact ⟨_,pairChecked161⟩
  · exact ⟨_,pairChecked162⟩
  · exact ⟨_,pairChecked163⟩
  · exact ⟨_,pairChecked164⟩
  · exact ⟨_,pairChecked165⟩
  · exact ⟨_,pairChecked166⟩
  · exact ⟨_,pairChecked167⟩
  · exact ⟨_,pairChecked168⟩
  · exact ⟨_,pairChecked169⟩
  · exact ⟨_,pairChecked170⟩
  · exact ⟨_,pairChecked171⟩
  · exact ⟨_,pairChecked172⟩
  · exact ⟨_,pairChecked173⟩
  · exact ⟨_,pairChecked174⟩
  · exact ⟨_,pairChecked175⟩
  · exact ⟨_,pairChecked176⟩
  · exact ⟨_,pairChecked177⟩
  · exact ⟨_,pairChecked178⟩
  · exact ⟨_,pairChecked179⟩
end RibbonD3Finite
