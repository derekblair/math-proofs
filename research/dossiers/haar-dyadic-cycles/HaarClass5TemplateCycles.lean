import HaarClass5DirPairs
import HaarClass5TemplateClosure
import HaarClass3Separation64
import HaarVoltage

namespace HaarClass5TemplateCycles
open HaarAllNoncommuting HaarReducedWalkCycle HaarHalfCollision HaarVoltage HaarClass5DirTables
open HaarClass5DirectionCover HaarUniversal36 HaarClass5TemplateClosure
open HaarClass4Ports
open scoped commutatorElement
variable {G : Type*} [Group G]

def vertex (x y : G) (w : List (Fin 3)) (i : ℕ) : Bool × G :=
  (decide (i%2=1),path x y w i)

theorem vert_step (x y : G) (w : List (Fin 3)) (i : ℕ) :
    HaarCycle.haarAdj x y (vertex x y w i) (vertex x y w (i+1)) := by
  apply adj_of_labeled x y _ _ (port x y (label w i))
  · generalize label w i = j
    fin_cases j <;> simp [withLabel,port]
  · change decide (i%2=1) ≠ decide ((i+1)%2=1)
    by_cases h : i%2=1
    · have z : (i+1)%2≠1 := by omega
      simp [h,z]
    · have z : (i+1)%2=1 := by omega
      simp [h,z]
  · change path x y w (i+1)=path x y w i*stepLabel (decide (i%2=1)) _
    by_cases h : i%2=1
    · have z : i%2≠0 := by omega
      simp [path,stepLabel,signPort,h,z]
    · have z : i%2=0 := by omega
      simp [path,stepLabel,signPort,h,z]

theorem cycle_of_vertices (x y : G) (w : List (Fin 3)) (len : w.length=64)
    (closed : prodFrom x y 0 w=1)
    (hinj : Function.Injective (fun i : Fin 64 => vertex x y w i.val)) : HasCycle x y 64 := by
  refine ⟨fun i => vertex x y w i.val,hinj,?_⟩
  have hp := path_full x y w
  rw [len,closed] at hp
  have h64 : vertex x y w 64=vertex x y w 0 := by
    apply Prod.ext
    · rfl
    · exact hp
  intro i
  change HaarCycle.haarAdj x y (vertex x y w i.val) (vertex x y w ((i.val+1)%64))
  have et := vert_step x y w i.val
  by_cases h : i.val+1<64
  · simpa only [Nat.mod_eq_of_lt h] using et
  · rw [show i.val+1=64 by omega,Nat.mod_self]
    rwa [show i.val+1=64 by omega,h64] at et

theorem projected_no_C (nil : L G 3=⊥) (x y : G)
    (h : ¬ ((portU x y)^(3:ℕ)=1 ∧ (portV x y)^(3:ℕ)=1)) :
    portC x y ∉ L G 2 := by
  intro hC
  have e := next hC x
  have f := next hC y
  change portU x y ∈ L G 3 at e
  change portV x y ∈ L G 3 at f
  rw [nil] at e f
  exact h ⟨by rw [Subgroup.mem_bot.mp e,one_pow],by rw [Subgroup.mem_bot.mp f,one_pow]⟩

theorem matched_rel (u v : G) (h : Commute u v) (ds : Fin 4 → Vec) {a b : ℤ}
    (test : matchesDir ds a b) (eq : u^a*v^b=1) : ∃ j, rel u v (ds j) := by
  obtain ⟨j, s | s⟩ := test
  · exact ⟨j,by simpa [rel,s.1,s.2] using eq⟩
  · have g : (u^(ds j).1 * v^(ds j).2)⁻¹=1 := by
      rw [s.1,s.2,zpow_neg,zpow_neg] at eq
      rw [mul_inv_rev,((h.zpow_zpow _ _).inv_left.inv_right).eq.symm]
      exact eq
    exact ⟨j,inv_eq_one.mp g⟩

theorem projected_rows (nil : L G 3=⊥) (x y : G) (t : Fin 4) (i : Fin 64) :
    path x y (W t) i.val = HaarClass3Separation64.eval x y (rowsW t i.val) := by
  exact path_matches nil x y (W t) (rowsW t) 64 (W_zero t)
    (fun j h => W_steps t ⟨j,h⟩) _ (Nat.le_of_lt i.isLt)

theorem flip_small {a b : ℤ} (h : small2 (b-a)) :
    HaarClass3Separation64.small (a-b) := by
  unfold HaarClass3Separation64.small
  rw [show a-b=-(b-a) by ring,Int.natAbs_neg]
  exact h

theorem template_cycle (nil : L G 5=⊥) (odd : Odd (Nat.card G)) (x y : G) (t : Fin 4)
    (hc : portC ((QuotientGroup.mk' (L G 3)) x) ((QuotientGroup.mk' (L G 3)) y)
      ∉ L (G ⧸ L G 3) 2)
    (clean : ∀ j : Fin 4,
      ¬ rel (portU ((QuotientGroup.mk' (L G 3)) x) ((QuotientGroup.mk' (L G 3)) y))
            (portV ((QuotientGroup.mk' (L G 3)) x) ((QuotientGroup.mk' (L G 3)) y)) (dirs t j)) :
    HasCycle x y 64 := by
  let S := L G 3
  let f := QuotientGroup.mk' S
  let X := f x
  let Y := f y
  have nil3 : L (G ⧸ S) 3=⊥ := quote_nil 3
  have oddQ : Odd (Nat.card (G ⧸ S)) := Odd.of_dvd_nat odd S.card_quotient_dvd_card
  apply cycle_of_vertices x y (W t) (W_len t) (all_closed nil x y t)
  intro i j he
  have sides := congrArg Prod.fst he
  change decide (i.val%2=1) = decide (j.val%2=1) at sides
  have side_eq : i.val%2=j.val%2 := by
    by_cases h : i.val%2=1 <;> by_cases b : j.val%2=1 <;> simp [h,b] at sides <;> omega
  have hP := congrArg (fun p : Bool × G => f p.2) he
  change f (path x y (W t) i.val) = f (path x y (W t) j.val) at hP
  rw [map_path,map_path] at hP
  rw [projected_rows nil3 X Y t i,projected_rows nil3 X Y t j] at hP
  let p := rowsW t i.val
  let q := rowsW t j.val
  have test := pairs t i j
  change (i=j ∨ i.val%2≠j.val%2 ∨ small2 (q.1-p.1) ∨ small2 (q.2.1-p.2.1) ∨
    (q.1-p.1=0 ∧ q.2.1-p.2.1=0 ∧ small2 (q.2.2.1-p.2.2.1)) ∨
    (q.1-p.1=0 ∧ q.2.1-p.2.1=0 ∧ q.2.2.1-p.2.2.1=0 ∧
      matchesDir (dirs t) (q.2.2.2.1-p.2.2.2.1) (q.2.2.2.2-p.2.2.2.2))) at test
  rcases test with e|e|e|e|⟨ei,ej,e⟩|⟨ei,ej,ek,e⟩
  · exact e
  · exact (e side_eq).elim
  · exact (HaarClass3Separation64.reject_i X Y nil3 oddQ hc p q hP (flip_small e)).elim
  · exact (HaarClass3Separation64.reject_j X Y nil3 oddQ hc p q hP (flip_small e)).elim
  · exact (HaarClass3Separation64.reject_c X Y nil3 oddQ hc p q hP
      (sub_eq_zero.mp ei).symm (sub_eq_zero.mp ej).symm (flip_small e)).elim
  · have g := HaarClass3Separation64.tail_relation X Y nil3 p q hP
      (sub_eq_zero.mp ei).symm (sub_eq_zero.mp ej).symm (sub_eq_zero.mp ek).symm
    obtain ⟨k,hw⟩ := matched_rel (portU X Y) (portV X Y)
      (central_2 nil3 (layer_u X Y) _) _ e g
    exact (clean k hw).elim

theorem no_cube_case (nil : L G 5=⊥) (odd : Odd (Nat.card G)) (x y : G)
    (h : let f := QuotientGroup.mk' (L G 3)
         ¬ ((portU (f x) (f y))^(3:ℕ)=1 ∧ (portV (f x) (f y))^(3:ℕ)=1)) :
    HasCycle x y 64 := by
  classical
  let S := L G 3
  let f := QuotientGroup.mk' S
  let X := f x
  let Y := f y
  let u := portU X Y
  let v := portV X Y
  have h3 : ¬ (u^(3:ℕ)=1 ∧ v^(3:ℕ)=1) := h
  have nil3 : L (G ⧸ S) 3=⊥ := quote_nil 3
  have oddQ : Odd (Nat.card (G ⧸ S)) := Odd.of_dvd_nat odd S.card_quotient_dvd_card
  have cuv : Commute u v := central_2 nil3 (layer_u X Y) _
  have nc : portC X Y ∉ L (G ⧸ S) 2 := projected_no_C nil3 X Y h3
  by_contra hc
  have bad (t : Fin 4) : ∃ j : Fin 4, rel u v (dirs t j) := by
    by_contra! he
    exact hc (template_cycle nil odd x y t nc he)
  obtain ⟨i,p⟩ := bad 0
  obtain ⟨j,q⟩ := bad 1
  obtain ⟨k,r⟩ := bad 2
  obtain ⟨l,s⟩ := bad 3
  exact h3 (four_collisions_force_cubes u v cuv
    (Odd.of_dvd_nat oddQ (orderOf_dvd_natCard _)) (Odd.of_dvd_nat oddQ (orderOf_dvd_natCard _))
    i j k l p q r s)

end HaarClass5TemplateCycles
#print axioms HaarClass5TemplateCycles.no_cube_case
