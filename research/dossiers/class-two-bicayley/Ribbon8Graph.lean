import Ribbon8Chart
import Ribbon8Gap

namespace Ribbon8
open Ribbon5Bridge HaarClass4Structure HaarClass4Ports HaarUniversal36
open scoped commutatorElement
variable {G : Type*} [Group G]
set_option maxRecDepth 32000
set_option maxHeartbeats 0

private theorem widen {a b : Q} (h : low a b) : separated7 a b := by
  rcases h with h|⟨pos,sz⟩|⟨pos,sz⟩|h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨pos,by omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨pos,by omega⟩))
  · exact Or.inr (Or.inr (Or.inr h))

private theorem low_sep (x y : G)
    (good : ∀ k : Nat, 1≤k → k≤7 → (QuotientGroup.mk' (LS G 2) (portC x y))^k ≠ 1)
    (w : Array P) (tab : Array Q)
    (h0 : tab[0]! = (false,0,0,0))
    (step : ∀ i, i<w.size → push tab[i]! w[i]! = tab[i+1]!)
    (i j : Nat) (hi : i≤w.size) (hj : j≤w.size)
    (h : low tab[i]! tab[j]!) :
    pathAt x y w i ≠ pathAt x y w j := by
  let f := QuotientGroup.mk' (LS G 2)
  let C := f (portC x y)
  have U' : f (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_u x y)
  have V' : f (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_v x y)
  have cx : Commute C (f x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C,portU,map_commutatorElement] using U'
  have cy : Commute C (f y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C,portV,map_commutatorElement] using V'
  have xy : f x*f y=f y*f x*C := by simpa only [C,map_mul] using congrArg f (ports_xy x y)
  let F : Bool×G → Bool × (G ⧸ LS G 2) := fun u => (u.1,f u.2)
  intro E
  have T := transported f x y w tab C cx cy xy h0 step
  have e : vert (f x) (f y) C tab[i]! = vert (f x) (f y) C tab[j]! :=
    (T i hi).symm.trans ((congrArg F E).trans (T j hj))
  exact sep_sound (f x) (f y) C cx cy xy good _ _ (widen h) e

private theorem aclose (x y : G) (h : R x y=1) : pathAt x y wa 32=pathAt x y wa 0 := by
  apply Prod.ext
  · rfl
  · change (run x y (start G) la).2=1
    rw [run_trace]
    change 1*Ribbon5Law.trace x y false la=1
    rw [one_mul,←Ribbon8Free.ev_encode,show Ribbon8Free.encode false la=origA from by decide +kernel,a_eq,h]

private theorem wclose (x y : G) (h : Z x y=1) : pathAt x y ww 64=pathAt x y ww 0 := by
  apply Prod.ext
  · rfl
  · change (run x y (start G) lw).2=1
    rw [run_trace]
    change 1*Ribbon5Law.trace x y false lw=1
    rw [one_mul,←Ribbon8Free.ev_encode,show Ribbon8Free.encode false lw=origW from by decide +kernel,w_eq,h]

private theorem tclose (x y : G) (h : Commute (Z x y) (U x y)) :
    pathAt x y wt 128=pathAt x y wt 0 := by
  apply Prod.ext
  · rfl
  · change (run x y (start G) lt).2=1
    rw [run_trace]
    change 1*Ribbon5Law.trace x y false lt=1
    rw [one_mul,t_close_if x y h]

private theorem mate_ne (x y : G) (k : Fin 60) (nz : target x y (row k).kind≠1) :
    pathAt x y wt (row k).i ≠ pathAt x y wt (row k).j := by
  intro E
  have e := congrArg Prod.snd E
  simp only [pathAt,wt,List.toList_toArray,run_trace,start,one_mul] at e
  have m := mate_sound x y k
  dsimp only at m
  rw [e,inv_mul_cancel] at m
  apply nz
  let c := Ribbon8Free.ev x y (row k).conjugator
  change 1=c*target x y (row k).kind*c⁻¹ at m
  calc
    target x y (row k).kind = c⁻¹*(c*target x y (row k).kind*c⁻¹)*c := by group
    _ = 1 := by rw [←m]; group

private theorem prefixes (x y : G) (i : Nat) (H : i≤64) :
    pathAt x y ww i = pathAt x y wt i := by
  have E : lw=lt.take 64 := by decide +kernel
  simp only [pathAt,ww,wt,List.toList_toArray,E,List.take_take,Nat.min_eq_left H]

private theorem both_nonzero (x y : G) (r : R x y≠1) (z : Z x y≠1)
    (diff : R x y ≠ Z x y) (k : Fin 6) :
    target x y k≠1 := by
  fin_cases k <;> simp [target,r,z,diff,diff.symm,mul_inv_eq_one,inv_mul_eq_one]

private theorem short_nonzero (x y : G) (r : R x y≠1)
    (k : Fin 6) (l : k.val≤1) : target x y k≠1 := by
  fin_cases k <;> simp_all [target]

theorem cases_of_good (x y : G)
    (good : ∀ k : Nat, 1≤k → k≤7 → (QuotientGroup.mk' (LS G 2) (portC x y))^k ≠ 1)
    (C : Commute (Z x y) (U x y)) (D : Z x y ≠ 1 → R x y ≠ Z x y) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  by_cases r : R x y=1
  · left
    apply cycle_from_at x y wa (by decide) (aclose x y r)
    intro i j l
    exact low_sep x y good wa ta (by decide +kernel) (fun n hn => astep ⟨n,hn⟩) _ _
      i.isLt.le j.isLt.le (achart i j l)
  · right
    by_cases z : Z x y=1
    · left
      apply cycle_from_at x y ww (by decide) (wclose x y z)
      intro i j l
      rcases wchart i j l with h|⟨k,hi,hj,hc⟩
      · exact low_sep x y good ww tw (by decide +kernel) (fun n hn => wstep ⟨n,hn⟩) _ _
          i.isLt.le j.isLt.le h
      · rw [prefixes x y _ i.isLt.le,prefixes x y _ j.isLt.le,←hi,←hj]
        exact mate_ne x y k (short_nonzero x y r _ hc)
    · right
      apply cycle_from_at x y wt (by decide) (tclose x y C)
      intro i j l
      rcases tchart i j l with h|⟨k,hi,hj⟩
      · exact low_sep x y good wt tt (by decide +kernel) (fun n hn => tstep ⟨n,hn⟩) _ _
          i.isLt.le j.isLt.le h
      · rw [←hi,←hj]
        exact mate_ne x y k (both_nonzero x y r z (D z) _)

end Ribbon8
#print axioms Ribbon8.cases_of_good
