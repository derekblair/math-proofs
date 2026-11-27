import RibbonD3WidePairCheck9
import RibbonD3WideOrbit
namespace RibbonD3WideFinite
open RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem pairBlock9 (i : Fin 30) : let z := pairLabel (⟨270+i.val,by have := i.isLt; omega⟩); ∃ w : Cert, good w (z.1.inp 0 0) (z.2.inp 0 0) := by
  fin_cases i
  · exact pairChecked270
  · exact pairChecked271
  · exact pairChecked272
  · exact pairChecked273
  · exact pairChecked274
  · exact pairChecked275
  · exact pairChecked276
  · exact pairChecked277
  · exact pairChecked278
  · exact pairChecked279
  · exact pairChecked280
  · exact pairChecked281
  · exact pairChecked282
  · exact pairChecked283
  · exact pairChecked284
  · exact pairChecked285
  · exact pairChecked286
  · exact pairChecked287
  · exact pairChecked288
  · exact pairChecked289
  · exact pairChecked290
  · exact pairChecked291
  · exact pairChecked292
  · exact pairChecked293
  · exact pairChecked294
  · exact pairChecked295
  · exact pairChecked296
  · exact pairChecked297
  · exact pairChecked298
  · exact pairChecked299
end RibbonD3WideFinite
