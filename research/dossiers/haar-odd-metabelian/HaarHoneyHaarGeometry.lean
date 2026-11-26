import HaarHoneyGauge
import HaarAllNoncommuting
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Group

namespace HaarHoneyHaar
open HaarHoneyVoltage
variable {G Q : Type*} [Group G] [Group Q]
variable (f : G →* Q) (x y : G)

def index (u : B) : Fin 16 := ⟨u.val%16,by omega⟩
def rep0 (t : Fin 16) : G := x^(t.val/4)*y^(t.val%4)
def rep (u : B) : G := rep0 x y (index u)
def port : P → G := ![1,x,y]
def side (u : B) : Bool := decide (16≤u.val)

def tag (u v : B) : P :=
  if v.val=u.val+16 then 0 else if v.val=u.val+20 then 1 else 2
def good (u v : B) : Prop := u.val<16 ∧ u≠v ∧ ∃ j, next u j=v
instance (u v : B) : Decidable (good u v) := by unfold good; infer_instance

def dx (j : P) : ℕ := if j.val=1 then 1 else 0
def dy (j : P) : ℕ := if j.val=2 then 1 else 0

set_option maxHeartbeats 0 in
theorem forward (u : B) (j : P) (h : u.val<16) (n : u≠next u j) :
    16≤(next u j).val ∧ tag u (next u j)=j ∧
      (index (next u j)).val/4=(index u).val/4+dx j ∧
      (index (next u j)).val%4=(index u).val%4+dy j := by
  fin_cases u <;> fin_cases j <;> revert h n <;> decide

set_option maxHeartbeats 0 in
theorem reverse (u : B) (j : P) (h : 16≤u.val) (n : u≠next u j) :
    (next u j).val<16 ∧ next (next u j) j=u := by
  fin_cases u <;> fin_cases j <;> revert h n <;> decide

def raw (u v : B) : G := rep x y u * port x y (tag u v) * (rep x y v)⁻¹

variable (cm : Commute (f x) (f y))
include cm in
theorem raw_mem (u v : B) (ok : good u v) : raw x y u v ∈ f.ker := by
  obtain ⟨hp,hn,j,rfl⟩ := ok
  obtain ⟨_,labels,e0,e1⟩ := forward u j hp hn
  change f (raw x y u (next u j)) = 1
  unfold raw
  rw [map_mul,map_inv,mul_inv_eq_one, map_mul,labels]
  simp only [rep,rep0,map_mul,map_pow,e0,e1,pow_add]
  fin_cases j
  · simp [port,dx,dy]
  · simp only [port,dx,dy]
    change (f x)^((index u).val/4)*(f y)^((index u).val%4)*f x =
      ((f x)^((index u).val/4)*f x^1)*((f y)^((index u).val%4)*f y^0)
    have h := (cm.pow_right ((index u).val%4)).eq
    simp only [pow_one,pow_zero,mul_one,mul_assoc]
    rw [← h]
  · simp [port,dx,dy,mul_assoc]

variable [hc : Fact (∀ (a b : f.ker), a*b=b*a)]
local instance commKernel : CommGroup f.ker where
  __ := (inferInstance : Group f.ker)
  mul_comm := hc.out
local instance addCommKernel : AddCommGroup (Additive f.ker) := inferInstance

include cm in
def weight (u v : B) : Additive f.ker :=
  if h : good u v then Additive.ofMul ⟨raw x y u v,raw_mem f x y cm u v h⟩
  else if h : good v u then -Additive.ofMul ⟨raw x y v u,raw_mem f x y cm v u h⟩
  else 0

include cm in
theorem anti (u v : B) : weight f x y cm v u = - weight f x y cm u v := by
  unfold weight
  by_cases a : good u v
  · obtain ⟨j,e⟩ := a.2.2
    have e' := (forward u j a.1 (by rw [e]; exact a.2.1)).1
    rw [e] at e'
    have b : ¬ good v u := by unfold good; omega
    simp [a,b]
  · by_cases b : good v u <;> simp [a,b]

def point (s : B × Additive f.ker) : Bool × G :=
  (side s.1,(s.2.toMul : G)*rep x y s.1)

set_option maxHeartbeats 0 in
theorem point_inj
    (inj : Function.Injective (fun t : Fin 16 => f (rep0 x y t))) :
    Function.Injective (point f x y) := by
  rintro ⟨u,a⟩ ⟨v,b⟩ E
  have s : side u = side v := congrArg Prod.fst E
  have e : (a.toMul : G)*rep x y u=(b.toMul : G)*rep x y v := congrArg Prod.snd E
  have pa : f a.toMul=1 := (a.toMul).property
  have pb : f b.toMul=1 := (b.toMul).property
  have q := congrArg f e
  rw [map_mul,map_mul,pa,pb,one_mul,one_mul] at q
  have h := inj q
  have v' : u=v := by
    apply Fin.ext
    have iv := congrArg Fin.val h
    change u.val % 16 = v.val % 16 at iv
    unfold side at s
    by_cases uh : 16≤u.val
    · have vh : 16≤v.val := by simpa [uh] using s.symm
      omega
    · have vh : ¬16≤v.val := by simpa [uh] using s.symm
      omega
  subst v
  have ab : a=b := Subtype.ext (mul_right_cancel e)
  rw [ab]

include cm hc in
theorem point_edge {s t : B × Additive f.ker}
    (ne : s.1≠t.1) (j : P) (hj : next s.1 j=t.1)
    (eq : s.2+weight f x y cm s.1 t.1=t.2) :
    HaarCycle.haarAdj x y (point f x y s) (point f x y t) := by
  rcases s with ⟨u,a⟩
  rcases t with ⟨v,b⟩
  change next u j = v at hj
  subst v
  change u≠next u j at ne
  change a + weight f x y cm u (next u j) = b at eq
  by_cases h : u.val<16
  · obtain ⟨vb,z,-⟩ := forward u j h ne
    have ok : good u (next u j) := ⟨h,ne,j,rfl⟩
    simp only [weight,dite_eq_left ok] at eq
    have eG : (a.toMul : G)*raw x y u (next u j)=(b.toMul : G) :=
      congrArg (fun z : Additive f.ker => (z.toMul : G)) eq
    have s0 : side u=false := by unfold side; simpa using (show ¬16≤u.val by omega)
    have s1 : side (next u j)=true := by simp [side,vb]
    simp only [point,HaarCycle.haarAdj,s0,s1,true_and]
    have E : (b.toMul : G)*rep x y (next u j)=((a.toMul : G)*rep x y u)*port x y j := by
      rw [←eG]; unfold raw; rw [z]; group
    fin_cases j
    · exact Or.inl (by simpa [port] using E)
    · exact Or.inr (Or.inl (by simpa [port] using E))
    · exact Or.inr (Or.inr (by simpa [port] using E))
  · have s0' : 16≤u.val := by omega
    obtain ⟨vb,rev⟩ := reverse u j s0' ne
    have no : ¬ good u (next u j) := fun z => h z.1
    have ok : good (next u j) u := ⟨vb,ne.symm,j,rev⟩
    have z : tag (next u j) u=j := by
      have H := (forward (next u j) j vb (by rw [rev]; exact ne.symm)).2.1
      rwa [rev] at H
    simp only [weight,dite_eq_right no,dite_eq_left ok] at eq
    have eG : (a.toMul : G)*(raw x y (next u j) u)⁻¹=(b.toMul : G) :=
      congrArg (fun z : Additive f.ker => (z.toMul : G)) eq
    have s0 : side u=true := by simp [side,s0']
    have s1 : side (next u j)=false := by unfold side; simpa using (show ¬16≤(next u j).val by omega)
    simp only [point,HaarCycle.haarAdj,s0,s1,ite_true,true_and]
    have E : (a.toMul : G)*rep x y u=((b.toMul : G)*rep x y (next u j))*port x y j := by
      rw [←eG]; unfold raw; rw [z]; group
    fin_cases j
    · exact Or.inl (by simpa [port] using E)
    · exact Or.inr (Or.inl (by simpa [port] using E))
    · exact Or.inr (Or.inr (by simpa [port] using E))

end HaarHoneyHaar
