import HaarClassFourAll

namespace HaarAnyPorts

open HaarAllNoncommuting HaarClass4Structure

variable {G : Type*} [Group G]

def adj (r s t : G) (a b : Bool × G) : Prop :=
  if a.1 then b.1=false ∧ (a.2=b.2*r ∨ a.2=b.2*s ∨ a.2=b.2*t)
  else b.1=true ∧ (b.2=a.2*r ∨ b.2=a.2*s ∨ b.2=a.2*t)

def unnormalize (r : G) (p : Bool × G) : Bool × G :=
  (p.1,if p.1 then p.2*r else p.2)

theorem unnormalize_inj (r : G) : Function.Injective (unnormalize r) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ h
  have e : a=b := congrArg Prod.fst h
  subst b
  have c := congrArg Prod.snd h
  have xy : x=y := by
    cases a
    · exact c
    · exact mul_right_cancel c
  exact Prod.ext rfl xy

theorem adj_map (r s t : G) {a b : Bool × G}
    (h : HaarCycle.haarAdj (s*r⁻¹) (t*r⁻¹) a b) :
    adj r s t (unnormalize r a) (unnormalize r b) := by
  rcases a with ⟨a,x⟩
  rcases b with ⟨b,y⟩
  cases a <;> cases b <;> simp [HaarCycle.haarAdj] at h
  · rcases h with e|e|e <;> simp [adj,unnormalize,e,mul_assoc]
  · rcases h with e|e|e <;> simp [adj,unnormalize,e,mul_assoc]

def HasPortCycle (r s t : G) (k : ℕ) : Prop :=
  ∃ w : Fin k → Bool × G, Function.Injective w ∧
    ∀ i, adj r s t (w i) (w ⟨(i.val+1)%k,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

theorem map_cycle (r s t : G) {k : ℕ} (h : HasCycle (s*r⁻¹) (t*r⁻¹) k) :
    HasPortCycle r s t k := by
  obtain ⟨w,i,a⟩ := h
  exact ⟨unnormalize r ∘ w,(unnormalize_inj r).comp i, fun j => adj_map r s t (a j)⟩

theorem as_three (r s t : G) (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    s*r⁻¹≠1 ∧ t*r⁻¹≠1 ∧ s*r⁻¹≠t*r⁻¹ := by
  refine ⟨?_ ,?_,fun e => hs (mul_right_cancel e)⟩
  · intro e
    exact hr ((mul_inv_eq_one.mp e).symm)
  · intro e
    exact ht ((mul_inv_eq_one.mp e).symm)

theorem odd_order (h : LS G 4=⊥) (odd : Odd (Nat.card G)) (r s t : G)
    (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    HasPortCycle r s t 4 ∨ HasPortCycle r s t 8 ∨ HasPortCycle r s t 16 ∨ HasPortCycle r s t 32 := by
  obtain ⟨i,j,k⟩ := as_three r s t hr ht hs
  rcases HaarClassFourOdd.odd_class_four h (s*r⁻¹) (t*r⁻¹) odd i j k with w|w|w|w
  · exact Or.inl (map_cycle r s t w)
  · exact Or.inr (Or.inl (map_cycle r s t w))
  · exact Or.inr (Or.inr (Or.inl (map_cycle r s t w)))
  · exact Or.inr (Or.inr (Or.inr (map_cycle r s t w)))

theorem finite_group [Finite G] (h : LS G 4=⊥) (r s t : G)
    (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    ∃ j, 2 ≤ j ∧ j ≤ 5+Nat.factorization (Nat.card G) 2 ∧ HasPortCycle r s t (2^j) := by
  obtain ⟨i,j,k⟩ := as_three r s t hr ht hs
  obtain ⟨j,l,u,w⟩ := HaarClassFourAll.finite_class_four h (s*r⁻¹) (t*r⁻¹) i j k
  exact ⟨j,l,u,map_cycle r s t w⟩

end HaarAnyPorts

#print axioms HaarAnyPorts.finite_group
