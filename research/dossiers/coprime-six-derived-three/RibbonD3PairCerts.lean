import RibbonD3PairBlock0
import RibbonD3PairBlock1
import RibbonD3PairBlock2
import RibbonD3PairBlock3
import RibbonD3PairBlock4
import RibbonD3PairBlock5
import RibbonD3PairBlock6
import RibbonD3PairBlock7

namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
def PairCerts : Prop := ∀ c : PP,
  ∃ w : Cert, good w ((pairLabel c).1.inp 0 0) ((pairLabel c).2.inp 0 0)

theorem pair_certs : PairCerts := by
  intro c
  have hc := c.isLt
  by_cases h0 : c.val<30
  · let j : Fin 30 := ⟨c.val-0,by omega⟩
    let d : PP := ⟨0+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 0+(c.val-0)=c.val; omega)
    have T := pairBlock0 j
    rw [←e]
    exact T
  by_cases h1 : c.val<60
  · let j : Fin 30 := ⟨c.val-30,by omega⟩
    let d : PP := ⟨30+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 30+(c.val-30)=c.val; omega)
    have T := pairBlock1 j
    rw [←e]
    exact T
  by_cases h2 : c.val<90
  · let j : Fin 30 := ⟨c.val-60,by omega⟩
    let d : PP := ⟨60+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 60+(c.val-60)=c.val; omega)
    have T := pairBlock2 j
    rw [←e]
    exact T
  by_cases h3 : c.val<120
  · let j : Fin 30 := ⟨c.val-90,by omega⟩
    let d : PP := ⟨90+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 90+(c.val-90)=c.val; omega)
    have T := pairBlock3 j
    rw [←e]
    exact T
  by_cases h4 : c.val<150
  · let j : Fin 30 := ⟨c.val-120,by omega⟩
    let d : PP := ⟨120+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 120+(c.val-120)=c.val; omega)
    have T := pairBlock4 j
    rw [←e]
    exact T
  by_cases h5 : c.val<180
  · let j : Fin 30 := ⟨c.val-150,by omega⟩
    let d : PP := ⟨150+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 150+(c.val-150)=c.val; omega)
    have T := pairBlock5 j
    rw [←e]
    exact T
  by_cases h6 : c.val<210
  · let j : Fin 30 := ⟨c.val-180,by omega⟩
    let d : PP := ⟨180+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 180+(c.val-180)=c.val; omega)
    have T := pairBlock6 j
    rw [←e]
    exact T
  let j : Fin 3 := ⟨c.val-210,by omega⟩
  let d : PP := ⟨210+j.val,by have := j.isLt; omega⟩
  have e : d = c := Fin.ext (by change 210+(c.val-210)=c.val; omega)
  have T := pairBlock7 j
  rw [←e]
  exact T
end RibbonD3Finite
