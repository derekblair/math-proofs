import HaarStripGauge
import HaarAllNoncommuting
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Group

namespace HaarStripHaar
open HaarStripVoltage
variable {G Q : Type*} [Group G] [Group Q]
variable (f : G →* Q) (x y : G)

def index (u : B) : Fin 6 := ⟨u.val%6,by omega⟩
def rep0 (t : Fin 6) : G := x^t.val
def rep (u : B) : G := rep0 x (index u)
def port : P → G := ![1,x,y]
def side (u : B) : Bool := decide (6≤u.val)

def tag (u v : B) : P :=
  if v.val=u.val+6 then 0 else if v.val=u.val+7 then 1 else 2
def good (u v : B) : Prop := u.val<6 ∧ u≠v ∧ ∃ j, next u j=v
instance (u v : B) : Decidable (good u v) := by unfold good; infer_instance

set_option maxHeartbeats 0 in
theorem forward (u : B) (j : P) (h : u.val<6) (n : u≠next u j) :
    6≤(next u j).val ∧ tag u (next u j)=j ∧
      (index (next u j)).val=(index u).val+j.val := by
  fin_cases u <;> fin_cases j <;> revert h n <;> decide

set_option maxHeartbeats 0 in
theorem reverse (u : B) (j : P) (h : 6≤u.val) (n : u≠next u j) :
    (next u j).val<6 ∧ next (next u j) j=u := by
  fin_cases u <;> fin_cases j <;> revert h n <;> decide

def raw (u v : B) : G := rep x u * port x y (tag u v) * (rep x v)⁻¹

variable (sq : f y=(f x)^2)
include sq in
theorem raw_mem (u v : B) (ok : good u v) : raw x y u v ∈ f.ker := by
  obtain ⟨hp,hn,j,rfl⟩ := ok
  obtain ⟨_,labels,e⟩ := forward u j hp hn
  change f (raw x y u (next u j)) = 1
  unfold raw
  rw [map_mul,map_inv,mul_inv_eq_one,map_mul,labels]
  simp only [rep,rep0,map_pow,e,pow_add]
  fin_cases j <;> simp [port,sq]

variable [hc : Fact (∀ (a b : f.ker), a*b=b*a)]
local instance commKernel : CommGroup f.ker where
  __ := (inferInstance : Group f.ker)
  mul_comm := hc.out
local instance addCommKernel : AddCommGroup (Additive f.ker) := inferInstance

include sq in
def weight (u v : B) : Additive f.ker :=
  if h : good u v then Additive.ofMul ⟨raw x y u v,raw_mem f x y sq u v h⟩
  else if h : good v u then -Additive.ofMul ⟨raw x y v u,raw_mem f x y sq v u h⟩
  else 0

include sq in
theorem anti (u v : B) : weight f x y sq v u = - weight f x y sq u v := by
  unfold weight
  by_cases a : good u v
  · obtain ⟨j,e⟩ := a.2.2
    have e' := (forward u j a.1 (by rw [e]; exact a.2.1)).1
    rw [e] at e'
    have b : ¬ good v u := by unfold good; omega
    simp [a,b]
  · by_cases b : good v u <;> simp [a,b]

def point (s : B × Additive f.ker) : Bool × G :=
  (side s.1,(s.2.toMul : G)*rep x s.1)

set_option maxHeartbeats 0 in
theorem point_inj
    (inj : Function.Injective (fun t : Fin 6 => f (rep0 x t))) :
    Function.Injective (point f x) := by
  rintro ⟨u,a⟩ ⟨v,b⟩ E
  have s : side u = side v := congrArg Prod.fst E
  have e : (a.toMul : G)*rep x u=(b.toMul : G)*rep x v := congrArg Prod.snd E
  have pa : f a.toMul=1 := (a.toMul).property
  have pb : f b.toMul=1 := (b.toMul).property
  have q := congrArg f e
  rw [map_mul,map_mul,pa,pb,one_mul,one_mul] at q
  have h := inj q
  have v' : u=v := by
    apply Fin.ext
    have iv := congrArg Fin.val h
    change u.val % 6 = v.val % 6 at iv
    unfold side at s
    by_cases uh : 6≤u.val
    · have vh : 6≤v.val := by simpa [uh] using s.symm
      omega
    · have vh : ¬6≤v.val := by simpa [uh] using s.symm
      omega
  subst v
  have ab : a=b := Subtype.ext (mul_right_cancel e)
  rw [ab]

include sq hc in
theorem point_edge {s t : B × Additive f.ker}
    (ne : s.1≠t.1) (j : P) (hj : next s.1 j=t.1)
    (eq : s.2+weight f x y sq s.1 t.1=t.2) :
    HaarCycle.haarAdj x y (point f x s) (point f x t) := by
  rcases s with ⟨u,a⟩
  rcases t with ⟨v,b⟩
  change next u j = v at hj
  subst v
  change u≠next u j at ne
  change a + weight f x y sq u (next u j) = b at eq
  by_cases h : u.val<6
  · obtain ⟨vb,z,-⟩ := forward u j h ne
    have ok : good u (next u j) := ⟨h,ne,j,rfl⟩
    simp only [weight,dite_eq_left ok] at eq
    have eG : (a.toMul : G)*raw x y u (next u j)=(b.toMul : G) :=
      congrArg (fun z : Additive f.ker => (z.toMul : G)) eq
    have s0 : side u=false := by unfold side; simpa using (show ¬6≤u.val by omega)
    have s1 : side (next u j)=true := by simp [side,vb]
    simp only [point,HaarCycle.haarAdj,s0,s1,true_and]
    have E : (b.toMul : G)*rep x (next u j)=((a.toMul : G)*rep x u)*port x y j := by
      rw [←eG]; unfold raw; rw [z]; group
    fin_cases j
    · exact Or.inl (by simpa [port] using E)
    · exact Or.inr (Or.inl (by simpa [port] using E))
    · exact Or.inr (Or.inr (by simpa [port] using E))
  · have s0' : 6≤u.val := by omega
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
    have s1 : side (next u j)=false := by unfold side; simpa using (show ¬6≤(next u j).val by omega)
    simp only [point,HaarCycle.haarAdj,s0,s1,ite_true,true_and]
    have E : (a.toMul : G)*rep x u=((b.toMul : G)*rep x (next u j))*port x y j := by
      rw [←eG]; unfold raw; rw [z]; group
    fin_cases j
    · exact Or.inl (by simpa [port] using E)
    · exact Or.inr (Or.inl (by simpa [port] using E))
    · exact Or.inr (Or.inr (by simpa [port] using E))

end HaarStripHaar
