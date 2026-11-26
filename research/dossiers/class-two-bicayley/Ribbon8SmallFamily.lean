import Ribbon8SmallCross
import Ribbon8SmallGap

namespace Ribbon8Small
open Ribbon5Bridge HaarClass4Ports HaarClass4Structure HaarClass4Generate
open scoped commutatorElement
variable {G : Type*} [Group G]
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def prefix32 (k : Fin 3) : Array P := ![Ribbon8AltA.wa,Ribbon8AltB.wa,Ribbon8AltC.wa] k
def U (k : Fin 3) (x y : G) : G := ![Ribbon8AltA.U x y,Ribbon8AltB.U x y,Ribbon8AltC.U x y] k
def R (k : Fin 3) (x y : G) : G := ![Ribbon8AltA.R x y,Ribbon8AltB.R x y,Ribbon8AltC.R x y] k
def Z (k : Fin 3) (x y : G) : G := ![Ribbon8AltA.Z x y,Ribbon8AltB.Z x y,Ribbon8AltC.Z x y] k

def mi (k : Fin 3) (m : Fin 60) : Nat :=
  ![(Ribbon8AltA.row m).i,(Ribbon8AltB.row m).i,(Ribbon8AltC.row m).i] k
def mj (k : Fin 3) (m : Fin 60) : Nat :=
  ![(Ribbon8AltA.row m).j,(Ribbon8AltB.row m).j,(Ribbon8AltC.row m).j] k
def mk (k : Fin 3) (m : Fin 60) : Fin 6 :=
  ![(Ribbon8AltA.row m).kind,(Ribbon8AltB.row m).kind,(Ribbon8AltC.row m).kind] k
def mm (k : Fin 3) (m : Fin 60) : List Ribbon8Free.Ltr :=
  ![(Ribbon8AltA.row m).conjugator,(Ribbon8AltB.row m).conjugator,(Ribbon8AltC.row m).conjugator] k

def target (r z : G) (k : Fin 6) : G :=
  ![r,r⁻¹,z,z⁻¹,r*z⁻¹,r⁻¹*z] k

theorem size32 : ∀ k : Fin 3, (prefix32 k).size=32 := by decide +kernel
theorem size64 : ∀ k : Fin 3, (prefix64 k).size=64 := by decide +kernel
private theorem pre32eq : ∀ k : Fin 3, (word k).toList.take 32=(prefix32 k).toList :=
  by decide +kernel

private theorem pre32path (x y : G) (k : Fin 3) (i : Nat) (h : i≤32) :
    pathAt x y (prefix32 k) i=pathAt x y (word k) i := by
  unfold pathAt
  rw [←pre32eq,List.take_take]
  simp [Nat.min_eq_left h,Nat.min_eq_right h]

private theorem aEnd (k : Fin 3) (x y : G) : pathAt x y (prefix32 k) 32=(false,R k x y) := by
  fin_cases k
  · exact Ribbon8AltA.a_end x y
  · exact Ribbon8AltB.a_end x y
  · exact Ribbon8AltC.a_end x y

private theorem wEnd (k : Fin 3) (x y : G) : pathAt x y (prefix64 k) 64=(false,Z k x y) := by
  fin_cases k
  · exact Ribbon8AltA.w_end x y
  · exact Ribbon8AltB.w_end x y
  · exact Ribbon8AltC.w_end x y

private theorem tClose (k : Fin 3) (nil : LS G 8=⊥) (x y : G) :
    pathAt x y (word k) 128=pathAt x y (word k) 0 := by
  rw [actual_word]
  fin_cases k
  · exact Ribbon8AltA.t_close nil x y
  · exact Ribbon8AltB.t_close nil x y
  · exact Ribbon8AltC.t_close nil x y

private theorem zConj (k : Fin 3) (x y : G) :
    Z k x y=(U k x y)⁻¹*⁅U k x y,R k x y⁆*U k x y := by
  fin_cases k
  · exact Ribbon8AltA.z_conjugate x y
  · exact Ribbon8AltB.z_conjugate x y
  · exact Ribbon8AltC.z_conjugate x y

private theorem zComm (k : Fin 3) (nil : LS G 8=⊥) (x y : G) :
    Commute (Z k x y) (U k x y) := by
  fin_cases k
  · exact Ribbon8AltA.commute nil x y
  · exact Ribbon8AltB.commute nil x y
  · exact Ribbon8AltC.commute nil x y

private theorem rule32 : ∀ (k : Fin 3) (i j : Fin 32), i.val<j.val →
    Ribbon8.low (altChart k)[i.val]! (altChart k)[j.val]! := by decide +kernel
private theorem rule64 : ∀ (k : Fin 3) (i j : Fin 64), i.val<j.val →
    Ribbon8.low (altChart k)[i.val]! (altChart k)[j.val]! ∨
    (∃ m : Fin 60, mi k m=i.val ∧ mj k m=j.val ∧ (mk k m).val≤1) := by decide +kernel
private theorem rule128 : ∀ (k : Fin 3) (i j : Fin 128), i.val<j.val →
    Ribbon8.low (altChart k)[i.val]! (altChart k)[j.val]! ∨
    (∃ m : Fin 60, mi k m=i.val ∧ mj k m=j.val) := by decide +kernel

private theorem base : ∀ k : Fin 3, (altChart k)[0]! = (false,0,0,0) := by decide +kernel
private theorem step : ∀ k : Fin 3, ∀ i : Fin 128,
    push (altChart k)[i.val]! (word k)[i.val]! = (altChart k)[i.val+1]! := by decide +kernel

private theorem mate_eq (k : Fin 3) (m : Fin 60) (x y : G) :
    let g := Ribbon8Free.ev x y (mm k m)
    (pathAt x y (word k) (mi k m)).2⁻¹*(pathAt x y (word k) (mj k m)).2 =
      g*target (R k x y) (Z k x y) (mk k m)*g⁻¹ := by
  rw [actual_word]
  fin_cases k
  · change (pathAt x y Ribbon8AltA.wt (Ribbon8AltA.row m).i).2⁻¹ *
      (pathAt x y Ribbon8AltA.wt (Ribbon8AltA.row m).j).2 =
        Ribbon8Free.ev x y (Ribbon8AltA.row m).conjugator * Ribbon8AltA.target x y (Ribbon8AltA.row m).kind *
        (Ribbon8Free.ev x y (Ribbon8AltA.row m).conjugator)⁻¹
    simpa only [pathAt,Ribbon8AltA.wt,run_trace,start,one_mul] using
      Ribbon8AltA.mate_sound x y m
  · change (pathAt x y Ribbon8AltB.wt (Ribbon8AltB.row m).i).2⁻¹ *
      (pathAt x y Ribbon8AltB.wt (Ribbon8AltB.row m).j).2 =
        Ribbon8Free.ev x y (Ribbon8AltB.row m).conjugator * Ribbon8AltB.target x y (Ribbon8AltB.row m).kind *
        (Ribbon8Free.ev x y (Ribbon8AltB.row m).conjugator)⁻¹
    simpa only [pathAt,Ribbon8AltB.wt,run_trace,start,one_mul] using
      Ribbon8AltB.mate_sound x y m
  · change (pathAt x y Ribbon8AltC.wt (Ribbon8AltC.row m).i).2⁻¹ *
      (pathAt x y Ribbon8AltC.wt (Ribbon8AltC.row m).j).2 =
        Ribbon8Free.ev x y (Ribbon8AltC.row m).conjugator * Ribbon8AltC.target x y (Ribbon8AltC.row m).kind *
        (Ribbon8Free.ev x y (Ribbon8AltC.row m).conjugator)⁻¹
    simpa only [pathAt,Ribbon8AltC.wt,run_trace,start,one_mul] using
      Ribbon8AltC.mate_sound x y m

private theorem exclude_mate (k : Fin 3) (m : Fin 60) (x y : G)
    (N : target (R k x y) (Z k x y) (mk k m)≠1) :
    pathAt x y (word k) (mi k m) ≠ pathAt x y (word k) (mj k m) := by
  intro eq
  have E := mate_eq k m x y
  dsimp only at E
  rw [eq,inv_mul_cancel] at E
  apply N
  let g := Ribbon8Free.ev x y (mm k m)
  calc
    _ = g⁻¹*(g*target (R k x y) (Z k x y) (mk k m)*g⁻¹)*g := by group
    _ = 1 := by rw [←E]; group

private theorem r_only (r z : G) (k : Fin 6) (h : k.val≤1) (N : r≠1) :
    target r z k≠1 := by
  fin_cases k <;> simp_all [target]

private theorem all_nonzero (r z u : G) (rN : r≠1) (zN : z≠1)
    (Z : z=u⁻¹*⁅u,r⁆*u) (C : Commute z u) (k : Fin 6) : target r z k≠1 := by
  have diff : r≠z := by
    intro eq
    have com : Commute u r := eq ▸ C.symm
    apply zN
    rw [Z,com.commutator_eq,mul_one,inv_mul_cancel]
  fin_cases k
  · exact rN
  · exact inv_ne_one.mpr rN
  · exact zN
  · exact inv_ne_one.mpr zN
  · exact fun h => diff (mul_inv_eq_one.mp h)
  · exact fun h => diff (inv_mul_eq_one.mp h)

theorem low_collision_of_equal (p : Fin 2) (k : Fin 3) (x y : G)
    (order : orderOf (QuotientGroup.mk' (LS G 2) (portC x y))=prime p)
    (i j : Fin 128) (ij : i.val<j.val)
    (lo : Ribbon8.low (altChart k)[i.val]! (altChart k)[j.val]!)
    (eq : pathAt x y (word k) i.val=pathAt x y (word k) j.val) :
    LowCollision p k x y := by
  let f := QuotientGroup.mk' (LS G 2)
  let c := f (portC x y)
  have u : f (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_u x y)
  have v : f (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_v x y)
  have cx : Commute c (f x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [c,portU,map_commutatorElement] using u
  have cy : Commute c (f y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [c,portV,map_commutatorElement] using v
  have xy : f x*f y=f y*f x*c := by simpa only [c,map_mul] using congrArg f (ports_xy x y)
  have T := transported f x y (word k) (altChart k) c cx cy xy (base k)
    (fun n hn => step k ⟨n,by rwa [size] at hn⟩)
  have F : vert (f x) (f y) c (altChart k)[i.val]! =
      vert (f x) (f y) c (altChart k)[j.val]! := by
    rw [←T i.val (by rw [size]; exact i.isLt.le),←T j.val (by rw [size]; exact j.isLt.le),eq]
  obtain ⟨_,a,b,h⟩ := gap_of_equal p (f x) (f y) c cx cy xy order _ _ lo F
  rw [←projected_rows k i,←projected_rows k j] at a b h
  exact ⟨i,j,ij, sub_eq_zero.mpr a.symm, sub_eq_zero.mpr b.symm,h,eq⟩

theorem absence_forces (nil : LS G 8=⊥) (p : Fin 2) (x y : G)
    (order : orderOf (QuotientGroup.mk' (LS G 2) (portC x y))=prime p)
    (none32 : ¬ Ribbon.Cycle x y 32) (none64 : ¬ Ribbon.Cycle x y 64)
    (none128 : ¬ Ribbon.Cycle x y 128) (k : Fin 3) :
    LowCollision p k x y := by
  by_contra B
  by_cases r : R k x y=1
  · apply none32
    apply cycle_from_at x y (prefix32 k) (size32 k) (by rw [aEnd k x y,r]; rfl)
    intro i j ij eq
    rw [pre32path x y k i.val i.isLt.le,pre32path x y k j.val j.isLt.le] at eq
    exact B (low_collision_of_equal p k x y order
      ⟨i.val,by omega⟩ ⟨j.val,by omega⟩ ij (rule32 k i j ij) eq)
  by_cases z : Z k x y=1
  · apply none64
    apply cycle_from_at x y (prefix64 k) (size64 k) (by rw [wEnd k x y,z]; rfl)
    intro i j ij eq
    rw [prefix_path x y k i.val i.isLt.le,prefix_path x y k j.val j.isLt.le] at eq
    rcases rule64 k i j ij with h|⟨m,hi,hj,hm⟩
    · exact B (low_collision_of_equal p k x y order
        ⟨i.val,by omega⟩ ⟨j.val,by omega⟩ ij h eq)
    · rw [←hi,←hj] at eq
      exact exclude_mate k m x y (r_only _ _ _ hm r) eq
  · apply none128
    apply cycle_from_at x y (word k) (size k) (tClose k nil x y)
    intro i j ij eq
    rcases rule128 k i j ij with h|⟨m,hi,hj⟩
    · exact B (low_collision_of_equal p k x y order i j ij h eq)
    · rw [←hi,←hj] at eq
      exact exclude_mate k m x y (all_nonzero _ _ _ r z (zConj k x y) (zComm k nil x y) _) eq

theorem projected_order_5_or_7 (nil : LS G 8=⊥) (p : Fin 2) (x y : G)
    (gen : Generates x y) (hx : x≠1) (hy : y*y≠1)
    (order : orderOf (QuotientGroup.mk' (LS G 2) (portC x y))=prime p) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
      Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  by_cases h32 : Ribbon.Cycle x y 32
  · exact Or.inr (Or.inr (Or.inr (Or.inl h32)))
  by_cases h64 : Ribbon.Cycle x y 64
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h64))))
  by_cases h128 : Ribbon.Cycle x y 128
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h128))))
  let f := QuotientGroup.mk' (LS G 2)
  have mem : (portC x y)^(prime p)∈LS G 2 := by
    apply (QuotientGroup.eq_one_iff _).mp
    change f ((portC x y)^(prime p))=1
    rw [map_pow,←order,pow_orderOf_eq_one]
  have N := descent p 8 nil (by decide) x y gen mem (absence_forces nil p x y order h32 h64 h128)
  have u := layer_u x y
  have v := layer_v x y
  rw [N,Subgroup.mem_bot] at u v
  have J := Ribbon.class2_pair x y (portC x y) (commutatorElement_eq_one_iff_commute.mp u)
    (commutatorElement_eq_one_iff_commute.mp v) (ports_xy x y) hx hy
  exact J.imp_right (fun K => K.imp_right Or.inl)

end Ribbon8Small
#print axioms Ribbon8Small.absence_forces
#print axioms Ribbon8Small.projected_order_5_or_7
