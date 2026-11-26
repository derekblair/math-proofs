import RibbonClass3Data
import RibbonAbelian

namespace RibbonClass3

open HaarClass4Ports HaarClass4Structure HaarClass3Collector64
open HaarClass3Separation64
open RibbonClass3Data
open scoped commutatorElement
variable {G : Type*} [Group G]

private theorem central_u (x y : G) (nil : LS G 3=⊥) (g : G) : Commute (portU x y) g :=
  (Subgroup.mem_center_iff.mp
    ((Subgroup.commutator_top_right_eq_bot_iff_le_center.mp nil) (layer_u x y)) g).symm
private theorem central_v (x y : G) (nil : LS G 3=⊥) (g : G) : Commute (portV x y) g :=
  (Subgroup.mem_center_iff.mp
    ((Subgroup.commutator_top_right_eq_bot_iff_le_center.mp nil) (layer_v x y)) g).symm

private theorem xu (x y : G) (nil : LS G 3=⊥) :
    portC x y*x=x*portC x y*portU x y := by
  calc
    _ = portU x y * (x*portC x y) := by simp only [portU,commutatorElement_def]; group
    _ = _ := (central_u x y nil (x*portC x y)).eq

private theorem yv (x y : G) (nil : LS G 3=⊥) :
    portC x y*y=y*portC x y*portV x y := by
  calc
    _ = portV x y * (y*portC x y) := by simp only [portV,commutatorElement_def]; group
    _ = _ := (central_v x y nil (y*portC x y)).eq

private theorem proj_c (x y : G) (nil : LS G 3=⊥)
    (h : portU x y≠1 ∨ portV x y≠1) : portC x y ∉ LS G 2 := by
  intro H
  have u : portU x y∈LS G 3 := Subgroup.commutator_mem_commutator H (Subgroup.mem_top x)
  have v : portV x y∈LS G 3 := Subgroup.commutator_mem_commutator H (Subgroup.mem_top y)
  rw [nil,Subgroup.mem_bot] at u v
  exact h.elim (fun q => q u) (fun q => q v)

/-- A square in the central third layer would force this selected triple
commutator to be an involution (or trivial). -/
private theorem square_reject (c x u : G) (r : c*x=x*c*u)
    (un : Commute u c) (hu : u*u≠1) (hs : Commute (c*c) x) : False := by
  have movement : c*c*x = (x*(c*c))*(u*u) := calc
    c*c*x = c*(c*x) := mul_assoc _ _ _
    _ = c*(x*c*u) := congrArg (c*·) r
    _ = (c*x)*c*u := by simp only [mul_assoc]
    _ = (x*c*u)*c*u := by rw [r]
    _ = (x*c)*(u*c)*u := by simp only [mul_assoc]
    _ = (x*c)*(c*u)*u := by rw [un.eq]
    _ = (x*(c*c))*(u*u) := by simp only [mul_assoc]
  apply hu
  apply mul_left_cancel (a:=x*(c*c))
  rw [← movement,hs.eq,mul_one]

private theorem projected_square (x y : G) (nil : LS G 3=⊥) (pickU : Bool)
    (h : if pickU then portU x y*portU x y≠1 else portV x y*portV x y≠1) :
    portC x y*portC x y ∉ LS G 2 := by
  intro H
  have center : LS G 2 ≤ Subgroup.center G :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mp nil
  have commute (z : G) : Commute (portC x y*portC x y) z :=
    (Subgroup.mem_center_iff.mp (center H) z).symm
  cases pickU
  · exact square_reject _ _ _ (yv x y nil) (central_v x y nil _) h (commute y)
  · exact square_reject _ _ _ (xu x y nil) (central_u x y nil _) h (commute x)

private theorem projected_pow (x y : G) (nil : LS G 3=⊥) (pickU : Bool)
    (h : if pickU then portU x y*portU x y≠1 else portV x y*portV x y≠1)
    (u v : ℤ) (diff : small (u-v)) :
    (QuotientGroup.mk' (LS G 2) (portC x y))^u ≠
      (QuotientGroup.mk' (LS G 2) (portC x y))^v := by
  let f := QuotientGroup.mk' (LS G 2)
  let C := f (portC x y)
  have hu : if pickU then portU x y≠1 else portV x y≠1 := by
    cases pickU <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h ⊢ <;> intro e <;> exact h (by simp [e])
  have hc := proj_c x y nil (by cases pickU <;> simp_all)
  have nc : C≠1 := fun eq => hc ((QuotientGroup.eq_one_iff _).mp eq)
  have ns : C^2≠1 := by
    intro eq
    apply projected_square x y nil pickU h
    apply (QuotientGroup.eq_one_iff _).mp
    change f (portC x y*portC x y)=1
    simpa only [C,pow_two,map_mul] using eq
  apply HaarCycle.centralNE C nc ns
  have ab : |u-v| = ((u-v).natAbs:ℤ) := (Int.natCast_natAbs _).symm
  rcases abs_choice (u-v) with ea|ea <;> rcases diff with d|d <;> omega

theorem inject_rows (x y : G) (nil : LS G 3=⊥)
    (pickU : Bool) (sq : if pickU then portU x y*portU x y≠1 else portV x y*portV x y≠1) :
    Function.Injective (fun t : Fin 16 => eval x y (P pickU t)) := by
  intro r s eq
  by_contra neq
  let p := P pickU r
  let q := P pickU s
  have h : if pickU then portU x y≠1 else portV x y≠1 := by
    cases pickU <;> simp only [Bool.false_eq_true, ite_false, ite_true] at sq ⊢ <;> intro e <;> exact sq (by simp [e])
  have layer := two_layer x y p q eq
  have ij : i p=i q ∧ j p=j q := by
    constructor
    · by_contra h'
      exact projected_pow x y nil pickU sq _ _ (i_bound pickU r s h') layer.1
    · by_contra h'
      exact projected_pow x y nil pickU sq _ _ (j_bound pickU r s h') layer.2.1
  have kk : k p=k q := by
    by_contra h'
    exact projected_pow x y nil pickU sq _ _ (k_bound pickU r s ij.1 ij.2 h') (layer.2.2 ij.1 ij.2)
  have E := collision pickU r s neq
  change ClashFree pickU p q at E
  have tails := tail_relation x y nil p q eq ij.1 ij.2 kk
  rcases E with C|C|C|C
  · exact projected_pow x y nil pickU sq _ _ C layer.1
  · exact projected_pow x y nil pickU sq _ _ C layer.2.1
  · exact projected_pow x y nil pickU sq _ _ C (layer.2.2 ij.1 ij.2)
  · cases pickU
    · simp only [Bool.false_eq_true,ite_false] at C h
      rw [C.2, zpow_zero, one_mul] at tails
      rcases C.1 with D|D
      · exact h (by simpa [D] using tails)
      · exact h (by simpa [D] using tails)
    · simp only [ite_true] at C h
      rw [C.2, zpow_zero, mul_one] at tails
      rcases C.1 with D|D
      · exact h (by simpa [D] using tails)
      · exact h (by simpa [D] using tails)

private theorem initial (x y : G) : eval x y base=1 := by
  simp [eval,base,HaarClass3Collect.norm]

private theorem eval_step (x y : G) (nil : LS G 3=⊥)
    (pickU : Bool) (n : Nat) (hn : n<16) :
    eval x y (row pickU (n+1)) = eval x y (row pickU n) *
      (if signs pickU n then (if n%2=0 then x else y)
         else (if n%2=0 then x else y)⁻¹) := by
  have R : Range (row pickU n).1 := range pickU ⟨n,hn⟩
  have Q := norm_move x y (portC x y) (portU x y) (portV x y)
    (central_u x y nil) (central_v x y nil) (ports_xy x y) (xu x y nil) (yv x y nil)
    (signs pickU n) (port n) (row pickU n) (fun _ => R)
  by_cases E : n%2=0 <;> simpa only [eval,row,port,E,ite_true,ite_false,HaarHalfCollision.port,
    Fin.isValue,show (1:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 0 by decide,
    show (2:Fin 3) ≠ 1 by decide] using Q

private def side (n : Nat) : Bool := decide ((n/2)%2=1)

private def walk (x y : G) (pickU : Bool) (n : Nat) : Bool×G :=
  (side n,eval x y (row pickU ((n+1)/2)))

private theorem walk_step (x y : G) (nil : LS G 3=⊥)
    (pickU : Bool) (n : Nat) (hn : n<32) :
    Ribbon.Adj x y (walk x y pickU n) (walk x y pickU (n+1)) := by
  let t := n/2
  by_cases E : n%2=0
  · have f : (n+1)/2=t := by dsimp [t]; omega
    have g : (n+1+1)/2=t+1 := by dsimp [t]; omega
    have s : (n+1)/2%2=n/2%2 := by rw [f]
    have Q := eval_step x y nil pickU t (by dsimp [t]; omega)
    change Ribbon.Adj x y (side n,eval x y (row pickU ((n+1)/2)))
      (side (n+1),eval x y (row pickU ((n+1+1)/2)))
    rw [f,g]
    by_cases even : t%2=0
    · have ss : side n=false := by simp [side,←show t=n/2 from rfl,even]
      have tt : side (n+1)=false := by simp [side,f,even]
      left
      refine ⟨ss,tt,?_⟩
      by_cases sign : signs pickU t
      · exact Or.inl (by simpa [even,sign] using Q.symm)
      · exact Or.inr (by rw [Q,ite_eq_right sign,ite_eq_left even,mul_assoc,inv_mul_cancel,mul_one])
    · have hodd : t%2=1 := by omega
      have ss : side n=true := by simp [side,←show t=n/2 from rfl,hodd]
      have tt : side (n+1)=true := by simp [side,f,hodd]
      right; left
      refine ⟨ss,tt,?_⟩
      by_cases sign : signs pickU t
      · exact Or.inl (by simpa [even,sign] using Q.symm)
      · exact Or.inr (by rw [Q,ite_eq_right sign,ite_eq_right even,mul_assoc,inv_mul_cancel,mul_one])
  · have e : (n+1+1)/2=(n+1)/2 := by omega
    have f : (n+1)/2=t+1 := by dsimp [t]; omega
    right; right
    refine ⟨?_,congrArg (fun j => eval x y (row pickU j)) e.symm⟩
    change decide ((n/2)%2=1) ≠ decide (((n+1)/2)%2=1)
    rw [f]
    change decide (t%2=1) ≠ decide ((t+1)%2=1)
    by_cases h : t%2=1
    · simp [h,show (t+1)%2≠1 by omega]
    · simp [h,show (t+1)%2=1 by omega]

def wrap (i : Fin 32) : Fin 16 := ⟨((i.val+1)/2)%16,Nat.mod_lt _ (by decide)⟩

private theorem geometry : ∀ r s : Fin 32, side r.val=side s.val → wrap r=wrap s → r=s :=
  by decide +kernel

private theorem normalization (pickU : Bool) (i : Fin 32) :
    row pickU ((i.val+1)/2) = P pickU (wrap i) := by
  change row pickU ((i.val+1)/2) = row pickU (((i.val+1)/2)%16)
  by_cases hi : (i.val+1)/2<16
  · rw [Nat.mod_eq_of_lt hi]
  · have e : (i.val+1)/2=16 := by omega
    rw [e,Nat.mod_self,closed]
    rfl

theorem cycle32_of_triple_square (x y : G) (nil : LS G 3=⊥)
    (pickU : Bool) (h : if pickU then portU x y*portU x y≠1 else portV x y*portV x y≠1) :
    Ribbon.Cycle x y 32 := by
  let f : Fin 32 → Bool×G := fun i => walk x y pickU i.val
  refine ⟨f,?_,?_⟩
  · intro r s E
    apply geometry r s (congrArg Prod.fst E)
    apply inject_rows x y nil pickU h
    have F : eval x y (row pickU ((r.val+1)/2)) =
        eval x y (row pickU ((s.val+1)/2)) := congrArg Prod.snd E
    rw [normalization,normalization] at F
    exact F
  · intro i
    have F := walk_step x y nil pickU i.val i.isLt
    change Ribbon.Adj x y (walk x y pickU i.val) (walk x y pickU ((i.val+1)%32))
    by_cases E : i.val+1<32
    · simpa [Nat.mod_eq_of_lt E] using F
    · have H : i.val+1=32 := by omega
      have K : walk x y pickU 32=walk x y pickU 0 := by
        apply Prod.ext
        · rfl
        · change eval x y (row pickU 16)=eval x y (row pickU 0)
          rw [closed]
          rfl
      rw [H,Nat.mod_self]
      rwa [H,K] at F

theorem cycle32 (x y : G) (nil : LS G 3=⊥) (odd : Odd (Nat.card G))
    (pickU : Bool) (h : if pickU then portU x y≠1 else portV x y≠1) :
    Ribbon.Cycle x y 32 := by
  apply cycle32_of_triple_square x y nil pickU
  cases pickU
  · change portV x y * portV x y ≠ 1
    simpa only [pow_two] using HaarClass3Odd.odd_no_involution odd h
  · change portU x y * portU x y ≠ 1
    simpa only [pow_two] using HaarClass3Odd.odd_no_involution odd h

theorem involution_free_class3 (x y : G) (nil : LS G 3=⊥)
    (noinvol : ∀ {g : G}, g≠1 → g*g≠1) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨ Ribbon.Cycle x y 32 := by
  by_cases hu : portU x y=1
  · by_cases hv : portV x y=1
    · have ca := commutatorElement_eq_one_iff_commute.mp hu
      have cb := commutatorElement_eq_one_iff_commute.mp hv
      exact (Ribbon.class2_pair x y (portC x y) ca cb (ports_xy x y) hx
        (noinvol hy)).imp_right (fun p => p.imp_right Or.inl)
    · exact Or.inr (Or.inr (Or.inr (cycle32_of_triple_square x y nil false (noinvol hv))))
  · exact Or.inr (Or.inr (Or.inr (cycle32_of_triple_square x y nil true (noinvol hu))))

theorem odd_class3 (x y : G) (nil : LS G 3=⊥) (odd : Odd (Nat.card G))
    (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨ Ribbon.Cycle x y 32 := by
  by_cases hu : portU x y=1
  · by_cases hv : portV x y=1
    · have ca := commutatorElement_eq_one_iff_commute.mp hu
      have cb := commutatorElement_eq_one_iff_commute.mp hv
      exact (Ribbon.class2_pair x y (portC x y) ca cb (ports_xy x y) hx
        (by simpa [pow_two] using HaarClass3Odd.odd_no_involution odd hy)).imp_right (fun p => p.imp_right Or.inl)
    · exact Or.inr (Or.inr (Or.inr (cycle32 x y nil odd false hv)))
  · exact Or.inr (Or.inr (Or.inr (cycle32 x y nil odd true hu)))

end RibbonClass3
#print axioms RibbonClass3.odd_class3
#print axioms RibbonClass3.cycle32_of_triple_square
#print axioms RibbonClass3.involution_free_class3
