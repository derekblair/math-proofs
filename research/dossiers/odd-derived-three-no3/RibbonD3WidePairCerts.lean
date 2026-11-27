import RibbonD3WidePairBlock0
import RibbonD3WidePairBlock1
import RibbonD3WidePairBlock2
import RibbonD3WidePairBlock3
import RibbonD3WidePairBlock4
import RibbonD3WidePairBlock5
import RibbonD3WidePairBlock6
import RibbonD3WidePairBlock7
import RibbonD3WidePairBlock8
import RibbonD3WidePairBlock9
import RibbonD3WidePairBlock10
import RibbonD3WidePairBlock11
import RibbonD3WidePairBlock12
import RibbonD3WidePairBlock13
import RibbonD3WidePairBlock14
import RibbonD3WidePairBlock15
import RibbonD3WidePairBlock16
import RibbonD3WidePairBlock17
import RibbonD3WidePairBlock18
import RibbonD3WidePairBlock19
import RibbonD3WidePairBlock20
import RibbonD3WidePairBlock21
import RibbonD3WidePairBlock22
import RibbonD3WidePairBlock23

namespace RibbonD3WideFinite
open RibbonD3Finite
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
  by_cases h7 : c.val<240
  · let j : Fin 30 := ⟨c.val-210,by omega⟩
    let d : PP := ⟨210+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 210+(c.val-210)=c.val; omega)
    have T := pairBlock7 j
    rw [←e]
    exact T
  by_cases h8 : c.val<270
  · let j : Fin 30 := ⟨c.val-240,by omega⟩
    let d : PP := ⟨240+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 240+(c.val-240)=c.val; omega)
    have T := pairBlock8 j
    rw [←e]
    exact T
  by_cases h9 : c.val<300
  · let j : Fin 30 := ⟨c.val-270,by omega⟩
    let d : PP := ⟨270+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 270+(c.val-270)=c.val; omega)
    have T := pairBlock9 j
    rw [←e]
    exact T
  by_cases h10 : c.val<330
  · let j : Fin 30 := ⟨c.val-300,by omega⟩
    let d : PP := ⟨300+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 300+(c.val-300)=c.val; omega)
    have T := pairBlock10 j
    rw [←e]
    exact T
  by_cases h11 : c.val<360
  · let j : Fin 30 := ⟨c.val-330,by omega⟩
    let d : PP := ⟨330+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 330+(c.val-330)=c.val; omega)
    have T := pairBlock11 j
    rw [←e]
    exact T
  by_cases h12 : c.val<390
  · let j : Fin 30 := ⟨c.val-360,by omega⟩
    let d : PP := ⟨360+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 360+(c.val-360)=c.val; omega)
    have T := pairBlock12 j
    rw [←e]
    exact T
  by_cases h13 : c.val<420
  · let j : Fin 30 := ⟨c.val-390,by omega⟩
    let d : PP := ⟨390+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 390+(c.val-390)=c.val; omega)
    have T := pairBlock13 j
    rw [←e]
    exact T
  by_cases h14 : c.val<450
  · let j : Fin 30 := ⟨c.val-420,by omega⟩
    let d : PP := ⟨420+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 420+(c.val-420)=c.val; omega)
    have T := pairBlock14 j
    rw [←e]
    exact T
  by_cases h15 : c.val<480
  · let j : Fin 30 := ⟨c.val-450,by omega⟩
    let d : PP := ⟨450+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 450+(c.val-450)=c.val; omega)
    have T := pairBlock15 j
    rw [←e]
    exact T
  by_cases h16 : c.val<510
  · let j : Fin 30 := ⟨c.val-480,by omega⟩
    let d : PP := ⟨480+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 480+(c.val-480)=c.val; omega)
    have T := pairBlock16 j
    rw [←e]
    exact T
  by_cases h17 : c.val<540
  · let j : Fin 30 := ⟨c.val-510,by omega⟩
    let d : PP := ⟨510+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 510+(c.val-510)=c.val; omega)
    have T := pairBlock17 j
    rw [←e]
    exact T
  by_cases h18 : c.val<570
  · let j : Fin 30 := ⟨c.val-540,by omega⟩
    let d : PP := ⟨540+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 540+(c.val-540)=c.val; omega)
    have T := pairBlock18 j
    rw [←e]
    exact T
  by_cases h19 : c.val<600
  · let j : Fin 30 := ⟨c.val-570,by omega⟩
    let d : PP := ⟨570+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 570+(c.val-570)=c.val; omega)
    have T := pairBlock19 j
    rw [←e]
    exact T
  by_cases h20 : c.val<630
  · let j : Fin 30 := ⟨c.val-600,by omega⟩
    let d : PP := ⟨600+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 600+(c.val-600)=c.val; omega)
    have T := pairBlock20 j
    rw [←e]
    exact T
  by_cases h21 : c.val<660
  · let j : Fin 30 := ⟨c.val-630,by omega⟩
    let d : PP := ⟨630+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 630+(c.val-630)=c.val; omega)
    have T := pairBlock21 j
    rw [←e]
    exact T
  by_cases h22 : c.val<690
  · let j : Fin 30 := ⟨c.val-660,by omega⟩
    let d : PP := ⟨660+j.val,by have := j.isLt; omega⟩
    have e : d = c := Fin.ext (by change 660+(c.val-660)=c.val; omega)
    have T := pairBlock22 j
    rw [←e]
    exact T
  let j : Fin 29 := ⟨c.val-690,by omega⟩
  let d : PP := ⟨690+j.val,by have := j.isLt; omega⟩
  have e : d = c := Fin.ext (by change 690+(c.val-690)=c.val; omega)
  have T := pairBlock23 j
  rw [←e]
  exact T
end RibbonD3WideFinite
