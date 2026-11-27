import HaarK33OddCover
import HaarAllNoncommuting
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Coset.Card

namespace HaarK33Haar
open HaarK33Voltage
variable {G : Type*} [Group G] (π : G →* Multiplicative (ZMod 3)) (x y : G)

def rep : B → G := ![1,x,y,1,x,y]
def port : P → G := ![1,x,y]
def label (u v : B) : P := ⟨(v.val+6-u.val)%3,by omega⟩
def side (u : B) : Bool := decide (3 ≤ u.val)
def raw (u v : B) : G := rep x y u * port x y (label u v) * (rep x y v)⁻¹

variable (hx : (π x).toAdd=1) (hy : (π y).toAdd=2)
include hx hy in
theorem rep_image (u : B) : (π (rep x y u)).toAdd = (u.val : ZMod 3) := by
  fin_cases u <;> simp [rep,hx,hy,toAdd_one] <;> decide

include hx hy in
theorem port_image (j : P) : (π (port x y j)).toAdd = (j.val : ZMod 3) := by
  fin_cases j <;> simp [port,hx,hy,toAdd_one]

include hx hy in
theorem raw_mem (u v : B) : raw x y u v ∈ π.ker := by
  change π (raw x y u v) = 1
  apply Multiplicative.toAdd.injective
  change (π (raw x y u v)).toAdd = (0 : ZMod 3)
  simp only [raw,map_mul,map_inv,toAdd_mul,toAdd_inv,
    rep_image π x y hx hy,port_image π x y hx hy]
  fin_cases u <;> fin_cases v <;> decide

variable [hc : Fact (∀ (a b : π.ker), a*b=b*a)]
local instance commKernel : CommGroup π.ker where
  __ := (inferInstance : Group π.ker)
  mul_comm := hc.out
local instance addCommKernel : AddCommGroup (Additive π.ker) := inferInstance

include hx hy in
def edgeVoltage (u v : B) : Additive π.ker :=
  if u.val<3 ∧ 3≤v.val then Additive.ofMul ⟨raw x y u v,raw_mem π x y hx hy u v⟩
  else if v.val<3 ∧ 3≤u.val then -Additive.ofMul ⟨raw x y v u,raw_mem π x y hx hy v u⟩
  else 0

include hx hy in
theorem anti (u v : B) : edgeVoltage π x y hx hy v u = - edgeVoltage π x y hx hy u v := by
  unfold edgeVoltage
  by_cases a : u.val<3 ∧ 3≤v.val
  · have b : ¬ (v.val<3 ∧ 3≤u.val) := by omega
    simp [a,b]
  · by_cases b : v.val<3 ∧ 3≤u.val <;> simp [a,b]

def point (s : B × Additive π.ker) : Bool × G :=
  (side s.1,(s.2.toMul : G) * rep x y s.1)

include hx hy in
theorem point_inj : Function.Injective (point π x y) := by
  rintro ⟨u,a⟩ ⟨v,b⟩ h
  have s : side u = side v := congrArg Prod.fst h
  have t : (a.toMul : G) * rep x y u = (b.toMul : G) * rep x y v := congrArg Prod.snd h
  have ta : π a.toMul = 1 := (a.toMul).property
  have tb : π b.toMul = 1 := (b.toMul).property
  have e := congrArg π t
  rw [map_mul,map_mul,ta,tb,one_mul,one_mul] at e
  have ee : (u.val : ZMod 3) = (v.val : ZMod 3) := by
    simpa only [rep_image π x y hx hy] using congrArg Multiplicative.toAdd e
  have uv : u=v := by fin_cases u <;> fin_cases v <;> revert s ee <;> decide
  subst v
  have ab : a=b := Subtype.ext (mul_right_cancel t)
  rw [ab]

theorem flip_lt (u : B) (j : P) : (next u j).val<3 ↔ 3≤u.val := by
  fin_cases u <;> fin_cases j <;> decide
theorem forward_label (u : B) (j : P) (h : u.val<3) : label u (next u j) = j := by
  fin_cases u <;> fin_cases j <;> revert h <;> decide
theorem reverse_label (u : B) (j : P) (h : 3≤u.val) : label (next u j) u = j := by
  fin_cases u <;> fin_cases j <;> revert h <;> decide

include hx hy hc in
theorem point_adj {s t : B × Additive π.ker}
    (e : HaarK33Gauge.adj (edgeVoltage π x y hx hy) s t) :
    HaarCycle.haarAdj x y (point π x y s) (point π x y t) := by
  rcases s with ⟨u,a⟩
  rcases t with ⟨v,b⟩
  obtain ⟨j,hj,eq⟩ := e
  change next u j = v at hj
  subst v
  have f := (flip_lt u j)
  change a + edgeVoltage π x y hx hy u (next u j) = b at eq
  by_cases h : u.val<3
  · have v : 3≤(next u j).val := by omega
    have not : ¬ ((next u j).val<3 ∧ 3≤u.val) := by omega
    simp only [edgeVoltage,if_pos (show u.val<3 ∧ 3≤(next u j).val from ⟨h,v⟩)] at eq
    have eG : (a.toMul : G) * raw x y u (next u j) = (b.toMul : G) :=
      congrArg (fun z : Additive π.ker => (z.toMul : G)) eq
    have s0 : side u=false := by unfold side; simpa using (show ¬ 3≤u.val by omega)
    have s1 : side (next u j)=true := by simp [side,v]
    simp only [point,HaarCycle.haarAdj,s0,s1,if_false,true_and]
    have E : (b.toMul : G) * rep x y (next u j) =
        ((a.toMul : G) * rep x y u) * port x y j := by
      rw [← eG]
      unfold raw
      rw [forward_label u j h]
      group
    fin_cases j
    · exact Or.inl (by simpa [port] using E)
    · exact Or.inr (Or.inl (by simpa [port] using E))
    · exact Or.inr (Or.inr (by simpa [port] using E))
  · have s : 3≤u.val := by omega
    have v : (next u j).val<3 := f.mpr s
    have not : ¬ (u.val<3 ∧ 3≤(next u j).val) := by omega
    simp only [edgeVoltage,if_neg not,if_pos (show (next u j).val<3 ∧ 3≤u.val from ⟨v,s⟩)] at eq
    have eG : (a.toMul : G) * (raw x y (next u j) u)⁻¹ = (b.toMul : G) :=
      congrArg (fun z : Additive π.ker => (z.toMul : G)) eq
    have s0 : side u=true := by simp [side,s]
    have s1 : side (next u j)=false := by unfold side; simpa using (show ¬ 3≤(next u j).val by omega)
    simp only [point,HaarCycle.haarAdj,s0,s1,if_true,true_and]
    have E : (a.toMul : G) * rep x y u =
        ((b.toMul : G) * rep x y (next u j)) * port x y j := by
      rw [← eG]
      unfold raw
      rw [reverse_label u j s]
      group
    fin_cases j
    · exact Or.inl (by simpa [port] using E)
    · exact Or.inr (Or.inl (by simpa [port] using E))
    · exact Or.inr (Or.inr (by simpa [port] using E))

include hx hy hc in
theorem haar_cycle (noTwo : ∀ a : Additive π.ker, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HaarAllNoncommuting.HasCycle x y n := by
  obtain ⟨n,hn,v,vinj,cv⟩ := HaarK33OddCover.any_cover (edgeVoltage π x y hx hy)
    (anti π x y hx hy) noTwo
  refine ⟨n,hn,point π x y ∘ v,(point_inj π x y hx hy).comp vinj,?_⟩
  intro i
  exact point_adj π x y hx hy (cv i)

include hx hy hc in
theorem kernel_odd [Finite G] (hodd : Odd (Nat.card π.ker)) :
    ∃ n, n ∈ [4,8,16,32] ∧ HaarAllNoncommuting.HasCycle x y n :=
  haar_cycle π x y hx hy (HaarK33OddCover.finite_odd_noTwo hodd)

omit hc in
theorem swap_cycle {n : ℕ} (h : HaarAllNoncommuting.HasCycle y x n) :
    HaarAllNoncommuting.HasCycle x y n := by
  obtain ⟨v,hv,e⟩ := h
  exact ⟨v,hv,fun j => by simpa only [HaarCycle.haarAdj,or_comm,or_left_comm] using e j⟩

include hc in
theorem odd_group_distinct_ports [Finite G] (hodd : Odd (Nat.card G))
    (nx : (π x).toAdd ≠ 0) (ny : (π y).toAdd ≠ 0) (ne : (π x).toAdd ≠ (π y).toAdd) :
    ∃ n, n ∈ [4,8,16,32] ∧ HaarAllNoncommuting.HasCycle x y n := by
  have cardK : Odd (Nat.card π.ker) := Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card π.ker)
  have casesBoth : ∀ a b : ZMod 3, a≠0 → b≠0 → a≠b →
      (a=1 ∧ b=2) ∨ (a=2 ∧ b=1) := by decide
  rcases casesBoth _ _ nx ny ne with ⟨a,b⟩ | ⟨a,b⟩
  · exact kernel_odd π x y a b cardK
  · obtain ⟨n,hn,C⟩ := kernel_odd π y x b a cardK
    exact ⟨n,hn,swap_cycle x y C⟩

end HaarK33Haar
#print axioms HaarK33Haar.kernel_odd
#print axioms HaarK33Haar.odd_group_distinct_ports
