import HaarClass7ParallelCycle
import HaarP3LayerGenBridge

namespace HaarClass7ParallelActual
open HaarClass7Parallel HaarClass7ParallelCycle
open HaarUniversal36 HaarClass4Table HaarClass4Normal HaarClass4Generate
open HaarClass4Ports HaarP3LayerGen HaarP3Class4Order
open HaarReducedWalkCycle HaarAllNoncommuting HaarHalfCollision
open HaarClass5TemplateCycles (cycle_of_vertices)
variable {G H K : Type*} [Group G] [Group H] [Group K]

theorem witness (nil : L G 7=⊥) (x y : G) (t : Fin 3)
    (f : G →* H) (cls4 : L H 4=⊥) (q : H →* K)
    (kill : HaarClass4Projection.KillsTail (make cls4 (f x) (f y)) q)
    (csmall : ∀ k : ℤ, cSmall k →
      (QuotientGroup.mk' (L H 2) (portC (f x) (f y)))^k=1 → k=0)
    (dsmall : ∀ k : ℤ, bSmall k →
      (q (portU (f x) (f y)))^(if t=0 then 0 else if t=1 then -k else k) *
        (q (portV (f x) (f y)))^(if t=2 then 0 else k)=1 → k=0)
    (diffAB : prodFrom x y 0 (A t) ≠ prodFrom x y 0 (B t)) :
    HasCycle x y 64 := by
  let M := make cls4 (f x) (f y)
  let φ := QuotientGroup.mk' (L H 2)
  have hm : HaarClass4Projection.KillsMid M φ := small_projection cls4 (f x) (f y)
  apply cycle_of_vertices x y (W t) (len t) (closes nil x y t)
  let v (i : Fin 64) := HaarClass5TemplateCycles.vertex x y (W t) i.val
  have no (i j : Fin 64) (ij : i.val<j.val) (eq : v i=v j) : False := by
    have ps := congrArg Prod.fst eq
    change decide (i.val%2=1) = decide (j.val%2=1) at ps
    have par : i.val%2=j.val%2 := by
      by_cases a : i.val%2=1 <;> by_cases b : j.val%2=1 <;> simp [a,b] at ps <;> omega
    have h := congrArg (fun d : Bool × G => f d.2) eq
    change f (path x y (W t) i.val) = f (path x y (W t) j.val) at h
    rw [HaarClass5TemplateClosure.map_path,HaarClass5TemplateClosure.map_path,
      prefix_eval cls4 _ _ _ (r t) (start t) (step t) _ (by rw [len]; omega),
      prefix_eval cls4 _ _ _ (r t) (start t) (step t) _ (by rw [len]; omega)] at h
    let p := r t i.val
    let s := r t j.val
    let d := diff p s
    change eval M p=eval M s at h
    have ⟨ei,ej,ec⟩ := HaarClass4Projection.projections_of_equal M φ hm p s h
    have ⟨bi,bj,N⟩ := all_pairs t i j
    change bSmall d.i at bi
    change bSmall d.j at bj
    have di := csmall d.i (by unfold bSmall at bi; unfold cSmall; omega) ei
    have dj := csmall d.j (by unfold bSmall at bj; unfold cSmall; omega) ej
    have ⟨bc,N⟩ := N ij par di dj
    change cSmall d.c at bc
    have dc := csmall d.c bc (ec di dj)
    let k := dir t d
    have ⟨bk,du,dv,win⟩ := N dc
    have e := HaarClass4Projection.equal_diff M p s di dj h
    change eval M d=1 at e
    have hq := congrArg q e
    have ka : q M.a=1 := kill.a
    have kb : q M.b=1 := kill.b
    have kd : q M.d=1 := kill.d
    change d.u=(if t=0 then 0 else if t=1 then -k else k) at du
    change d.v=(if t=2 then 0 else k) at dv
    have hq' : (q M.u)^(if t=0 then 0 else if t=1 then -k else k) *
        (q M.v)^(if t=2 then 0 else k)=1 := by
      simpa only [eval,di,dj,dc,du,dv,mid,HaarClass4Normal.tail,map_mul,map_zpow,map_one,zpow_zero,one_zpow,one_mul,mul_one,ka,kb,kd] using hq
    have kz : k=0 := dsmall k bk hq'
    have ⟨li,ui,js⟩ := win kz
    have ce := congrArg Prod.snd eq
    change path x y (W t) i.val = path x y (W t) j.val at ce
    rw [js] at ce
    exact neq_window x y t li ui (window_of_factors x y t diffAB) ce
  intro i j e
  by_contra hij
  have e' : v i=v j := e
  rcases lt_or_gt_of_ne (fun t => hij (Fin.ext t)) with lt|lt
  · exact no i j lt e'
  · exact no j i lt e'.symm

end HaarClass7ParallelActual
#print axioms HaarClass7ParallelActual.witness
