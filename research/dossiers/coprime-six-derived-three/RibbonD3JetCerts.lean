import RibbonD3JetBlock0
import RibbonD3JetBlock1
import RibbonD3JetBlock2
import RibbonD3JetBlock3
import RibbonD3JetBlock4

namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
def JetCerts : Prop := ∀ c : JJ,
  let z := jetLabel c; ∃ w : Cert, good w (z.1.inp z.2.1 z.2.2) (z.1.inp z.2.1 z.2.2)

theorem jet_certs : JetCerts := by
  intro c
  have hc := c.isLt
  by_cases h0 : c.val<30
  · let j : Fin 30 := ⟨c.val-0,by omega⟩
    let d : JJ := ⟨0+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 0+(c.val-0)=c.val; omega)
    have T := jetBlock0 j
    rw [←e]
    exact T
  by_cases h1 : c.val<60
  · let j : Fin 30 := ⟨c.val-30,by omega⟩
    let d : JJ := ⟨30+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 30+(c.val-30)=c.val; omega)
    have T := jetBlock1 j
    rw [←e]
    exact T
  by_cases h2 : c.val<90
  · let j : Fin 30 := ⟨c.val-60,by omega⟩
    let d : JJ := ⟨60+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 60+(c.val-60)=c.val; omega)
    have T := jetBlock2 j
    rw [←e]
    exact T
  by_cases h3 : c.val<120
  · let j : Fin 30 := ⟨c.val-90,by omega⟩
    let d : JJ := ⟨90+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 90+(c.val-90)=c.val; omega)
    have T := jetBlock3 j
    rw [←e]
    exact T
  let j : Fin 17 := ⟨c.val-120,by omega⟩
  let d : JJ := ⟨120+j.val,by have := j.isLt; omega⟩
  have e : d = c := Fin.ext (by change 120+(c.val-120)=c.val; omega)
  have T := jetBlock4 j
  rw [←e]
  exact T
end RibbonD3Finite
