import HaarMetaNineGauge
import HaarAllNoncommuting
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Coset.Card

set_option maxHeartbeats 0
namespace HaarMetaNineHaar
open HaarMetaNineVoltage
variable {G : Type*} [Group G] (π : G →* Multiplicative (ZMod 9)) (x y : G)

abbrev Q := ZMod 9
def coord (u : B) : Q := (u.val : ZMod 9)
def portCoord : P → Q := ![0,1,3]

variable (surj : Function.Surjective π)
noncomputable def rep (u : B) : G := Classical.choose (surj (Multiplicative.ofAdd (coord u)))
def port : P → G := ![1,x,y]
def label (u v : B) : P := if next u 0=v then 0 else if next u 1=v then 1 else 2
def side (u : B) : Bool := decide (9 ≤ u.val)
def good (u v : B) : Prop := u.val<9 ∧ 9≤v.val ∧ next u (label u v)=v
instance (u v : B) : Decidable (good u v) := by unfold good; infer_instance
noncomputable def raw (u v : B) : G := rep π surj u * port x y (label u v) * (rep π surj v)⁻¹

variable (hx : (π x).toAdd=1) (hy : (π y).toAdd=3)
theorem rep_image (u : B) : (π (rep π surj u)).toAdd = coord u :=
  congrArg Multiplicative.toAdd (Classical.choose_spec (surj (Multiplicative.ofAdd (coord u))))

include hx hy in
theorem port_image (j : P) : (π (port x y j)).toAdd = portCoord j := by
  fin_cases j <;> simp [port,portCoord,hx,hy,toAdd_one] <;> rfl

theorem next_coord (u : B) (j : P) (h : u.val<9) :
    coord u + portCoord j = coord (next u j) := by
  fin_cases u <;> fin_cases j <;> revert h <;> decide

include hx hy in
theorem raw_mem (u v : B) (hh : good u v) : raw π x y surj u v ∈ π.ker := by
  change π (raw π x y surj u v) = 1
  apply Multiplicative.toAdd.injective
  change (π (raw π x y surj u v)).toAdd = (0 : Q)
  simp only [raw,map_mul,map_inv,toAdd_mul,toAdd_inv,
    rep_image π surj,port_image π x y hx hy]
  have he := next_coord u (label u v) hh.1
  rw [hh.2.2] at he
  rw [he,add_neg_cancel]

variable [hc : Fact (∀ (a b : π.ker), a*b=b*a)]
local instance commKernel : CommGroup π.ker where
  __ := (inferInstance : Group π.ker)
  mul_comm := hc.out
local instance addCommKernel : AddCommGroup (Additive π.ker) := inferInstance

include hx hy in
noncomputable def edgeVoltage (u v : B) : Additive π.ker :=
  if h : good u v then Additive.ofMul ⟨raw π x y surj u v,raw_mem π x y surj hx hy u v h⟩
  else if h : good v u then -Additive.ofMul ⟨raw π x y surj v u,raw_mem π x y surj hx hy v u h⟩
  else 0

include hx hy in
theorem anti (u v : B) : edgeVoltage π x y surj hx hy v u = - edgeVoltage π x y surj hx hy u v := by
  unfold edgeVoltage
  by_cases a : good u v
  · have b : ¬ good v u := by unfold good at a ⊢; omega
    simp [a,b]
  · by_cases b : good v u <;> simp [a,b]

noncomputable def point (s : B × Additive π.ker) : Bool × G :=
  (side s.1,(s.2.toMul : G) * rep π surj s.1)

theorem point_inj : Function.Injective (point π surj) := by
  rintro ⟨u,a⟩ ⟨v,b⟩ h
  have s : side u = side v := congrArg Prod.fst h
  have t : (a.toMul : G) * rep π surj u = (b.toMul : G) * rep π surj v := congrArg Prod.snd h
  have ta : π a.toMul = 1 := (a.toMul).property
  have tb : π b.toMul = 1 := (b.toMul).property
  have e := congrArg π t
  rw [map_mul,map_mul,ta,tb,one_mul,one_mul] at e
  have ee : coord u = coord v := by
    simpa only [rep_image π surj] using congrArg Multiplicative.toAdd e
  have uv : u=v := by fin_cases u <;> fin_cases v <;> revert s ee <;> decide
  subst v
  have ab : a=b := Subtype.ext (mul_right_cancel t)
  rw [ab]

theorem flip_lt (u : B) (j : P) : (next u j).val<9 ↔ 9≤u.val := by
  fin_cases u <;> fin_cases j <;> decide
theorem forward_label (u : B) (j : P) (h : u.val<9) :
    good u (next u j) ∧ label u (next u j) = j := by
  fin_cases u <;> fin_cases j <;> revert h <;> decide
theorem reverse_label (u : B) (j : P) (h : 9≤u.val) :
    good (next u j) u ∧ label (next u j) u = j := by
  fin_cases u <;> fin_cases j <;> revert h <;> decide

include hx hy hc in
theorem point_adj {s t : B × Additive π.ker}
    (e : HaarMetaNineGauge.adj (edgeVoltage π x y surj hx hy) s t) :
    HaarCycle.haarAdj x y (point π surj s) (point π surj t) := by
  rcases s with ⟨u,a⟩
  rcases t with ⟨v,b⟩
  obtain ⟨j,hj,eq⟩ := e
  change next u j = v at hj
  subst v
  have f := (flip_lt u j)
  change a + edgeVoltage π x y surj hx hy u (next u j) = b at eq
  by_cases h : u.val<9
  · have v : 9≤(next u j).val := by omega
    have ok := forward_label u j h
    simp only [edgeVoltage,dite_eq_left ok.1] at eq
    have eG : (a.toMul : G) * raw π x y surj u (next u j) = (b.toMul : G) :=
      congrArg (fun z : Additive π.ker => (z.toMul : G)) eq
    have s0 : side u=false := by unfold side; simpa using (show ¬ 9≤u.val by omega)
    have s1 : side (next u j)=true := by simp [side,v]
    simp only [point,HaarCycle.haarAdj,s0,s1,ite_false,true_and]
    have E : (b.toMul : G) * rep π surj (next u j) =
        ((a.toMul : G) * rep π surj u) * port x y j := by
      rw [← eG]
      unfold raw
      rw [ok.2]
      group
    fin_cases j
    · exact Or.inl (by simpa [port] using E)
    · exact Or.inr (Or.inl (by simpa [port] using E))
    · exact Or.inr (Or.inr (by simpa [port] using E))
  · have s : 9≤u.val := by omega
    have v : (next u j).val<9 := f.mpr s
    have ok := reverse_label u j s
    have not : ¬ good u (next u j) := by unfold good; omega
    simp only [edgeVoltage,dite_eq_right not,dite_eq_left ok.1] at eq
    have eG : (a.toMul : G) * (raw π x y surj (next u j) u)⁻¹ = (b.toMul : G) :=
      congrArg (fun z : Additive π.ker => (z.toMul : G)) eq
    have s0 : side u=true := by simp [side,s]
    have s1 : side (next u j)=false := by unfold side; simpa using (show ¬ 9≤(next u j).val by omega)
    simp only [point,HaarCycle.haarAdj,s0,s1,ite_true,true_and]
    have E : (a.toMul : G) * rep π surj u =
        ((b.toMul : G) * rep π surj (next u j)) * port x y j := by
      rw [← eG]
      unfold raw
      rw [ok.2]
      group
    fin_cases j
    · exact Or.inl (by simpa [port] using E)
    · exact Or.inr (Or.inl (by simpa [port] using E))
    · exact Or.inr (Or.inr (by simpa [port] using E))

end HaarMetaNineHaar
