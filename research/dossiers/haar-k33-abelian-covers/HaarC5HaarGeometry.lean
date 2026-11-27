import HaarC5Gauge
import HaarAllNoncommuting
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Coset.Card

namespace HaarC5Haar
open HaarC5Voltage
variable {G : Type*} [Group G] (π : G →* Multiplicative (ZMod 5)) (x y : G)

def rep (x : G) (u : B) : G := x^(u.val%5)
def port : P → G := ![1,x,y]
def diff (u v : B) : Nat := (v.val+10-u.val)%5
def label (u v : B) : P := ⟨diff u v % 3,by omega⟩
def side (u : B) : Bool := decide (5 ≤ u.val)
def good (u v : B) : Prop := u.val<5 ∧ 5≤v.val ∧ diff u v<3
instance (u v : B) : Decidable (good u v) := by unfold good; infer_instance
def raw (u v : B) : G := rep x u * port x y (label u v) * (rep x v)⁻¹

variable (hx : (π x).toAdd=1) (hy : (π y).toAdd=2)
include hx in
theorem rep_image (u : B) : (π (rep x u)).toAdd = (u.val : ZMod 5) := by
  simp only [rep,map_pow,toAdd_pow,hx]
  fin_cases u <;> decide

include hx hy in
theorem port_image (j : P) : (π (port x y j)).toAdd = (j.val : ZMod 5) := by
  fin_cases j <;> simp [port,hx,hy,toAdd_one]

include hx hy in
theorem raw_mem (u v : B) (hh : diff u v<3) : raw x y u v ∈ π.ker := by
  change π (raw x y u v) = 1
  apply Multiplicative.toAdd.injective
  change (π (raw x y u v)).toAdd = (0 : ZMod 5)
  simp only [raw,map_mul,map_inv,toAdd_mul,toAdd_inv,
    rep_image π x hx,port_image π x y hx hy]
  fin_cases u <;> fin_cases v <;> revert hh <;> decide

variable [hc : Fact (∀ (a b : π.ker), a*b=b*a)]
local instance commKernel : CommGroup π.ker where
  __ := (inferInstance : Group π.ker)
  mul_comm := hc.out
local instance addCommKernel : AddCommGroup (Additive π.ker) := inferInstance

include hx hy in
def edgeVoltage (u v : B) : Additive π.ker :=
  if h : good u v then Additive.ofMul ⟨raw x y u v,raw_mem π x y hx hy u v h.2.2⟩
  else if h : good v u then -Additive.ofMul ⟨raw x y v u,raw_mem π x y hx hy v u h.2.2⟩
  else 0

include hx hy in
theorem anti (u v : B) : edgeVoltage π x y hx hy v u = - edgeVoltage π x y hx hy u v := by
  unfold edgeVoltage
  by_cases a : good u v
  · have b : ¬ good v u := by unfold good at a ⊢; omega
    simp [a,b]
  · by_cases b : good v u <;> simp [a,b]

def point (s : B × Additive π.ker) : Bool × G :=
  (side s.1,(s.2.toMul : G) * rep x s.1)

include hx in
theorem point_inj : Function.Injective (point π x) := by
  rintro ⟨u,a⟩ ⟨v,b⟩ h
  have s : side u = side v := congrArg Prod.fst h
  have t : (a.toMul : G) * rep x u = (b.toMul : G) * rep x v := congrArg Prod.snd h
  have ta : π a.toMul = 1 := (a.toMul).property
  have tb : π b.toMul = 1 := (b.toMul).property
  have e := congrArg π t
  rw [map_mul,map_mul,ta,tb,one_mul,one_mul] at e
  have ee : (u.val : ZMod 5) = (v.val : ZMod 5) := by
    simpa only [rep_image π x hx] using congrArg Multiplicative.toAdd e
  have uv : u=v := by fin_cases u <;> fin_cases v <;> revert s ee <;> decide
  subst v
  have ab : a=b := Subtype.ext (mul_right_cancel t)
  rw [ab]

theorem flip_lt (u : B) (j : P) : (next u j).val<5 ↔ 5≤u.val := by
  fin_cases u <;> fin_cases j <;> decide
theorem forward_label (u : B) (j : P) (h : u.val<5) :
    good u (next u j) ∧ label u (next u j) = j := by
  fin_cases u <;> fin_cases j <;> revert h <;> decide
theorem reverse_label (u : B) (j : P) (h : 5≤u.val) :
    good (next u j) u ∧ label (next u j) u = j := by
  fin_cases u <;> fin_cases j <;> revert h <;> decide

include hx hy hc in
theorem point_adj {s t : B × Additive π.ker}
    (e : HaarC5Gauge.adj (edgeVoltage π x y hx hy) s t) :
    HaarCycle.haarAdj x y (point π x s) (point π x t) := by
  rcases s with ⟨u,a⟩
  rcases t with ⟨v,b⟩
  obtain ⟨j,hj,eq⟩ := e
  change next u j = v at hj
  subst v
  have f := (flip_lt u j)
  change a + edgeVoltage π x y hx hy u (next u j) = b at eq
  by_cases h : u.val<5
  · have v : 5≤(next u j).val := by omega
    have ok := forward_label u j h
    simp only [edgeVoltage,dite_eq_left ok.1] at eq
    have eG : (a.toMul : G) * raw x y u (next u j) = (b.toMul : G) :=
      congrArg (fun z : Additive π.ker => (z.toMul : G)) eq
    have s0 : side u=false := by unfold side; simpa using (show ¬ 5≤u.val by omega)
    have s1 : side (next u j)=true := by simp [side,v]
    simp only [point,HaarCycle.haarAdj,s0,s1,ite_false,true_and]
    have E : (b.toMul : G) * rep x (next u j) =
        ((a.toMul : G) * rep x u) * port x y j := by
      rw [← eG]
      unfold raw
      rw [ok.2]
      group
    fin_cases j
    · exact Or.inl (by simpa [port] using E)
    · exact Or.inr (Or.inl (by simpa [port] using E))
    · exact Or.inr (Or.inr (by simpa [port] using E))
  · have s : 5≤u.val := by omega
    have v : (next u j).val<5 := f.mpr s
    have ok := reverse_label u j s
    have not : ¬ good u (next u j) := by unfold good; omega
    simp only [edgeVoltage,dite_eq_right not,dite_eq_left ok.1] at eq
    have eG : (a.toMul : G) * (raw x y (next u j) u)⁻¹ = (b.toMul : G) :=
      congrArg (fun z : Additive π.ker => (z.toMul : G)) eq
    have s0 : side u=true := by simp [side,s]
    have s1 : side (next u j)=false := by unfold side; simpa using (show ¬ 5≤(next u j).val by omega)
    simp only [point,HaarCycle.haarAdj,s0,s1,ite_true,true_and]
    have E : (a.toMul : G) * rep x u =
        ((b.toMul : G) * rep x (next u j)) * port x y j := by
      rw [← eG]
      unfold raw
      rw [ok.2]
      group
    fin_cases j
    · exact Or.inl (by simpa [port] using E)
    · exact Or.inr (Or.inl (by simpa [port] using E))
    · exact Or.inr (Or.inr (by simpa [port] using E))

end HaarC5Haar
