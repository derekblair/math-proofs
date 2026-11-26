import HeawoodGirthFiftyFour

namespace HeawoodDoubleDeck
open HeawoodDouble HomologyThree
open HaarOrbitC7Voltage (B)
abbrev K := Lamp B
abbrev M := Lamp V1

def move (d : K) (u : V1) : V1 := (u.1,d+u.2)

theorem move_add (d e : K) (u : V1) : move (d+e) u=move d (move e u) := by
  refine Prod.ext ?_ ?_
  · rfl
  · simp [move,add_assoc]

theorem move_neg (d : K) (u : V1) : move (-d) (move d u)=u := by
  refine Prod.ext ?_ ?_
  · rfl
  · simp [move]

theorem move_neg' (d : K) (u : V1) : move d (move (-d) u)=u := by
  simpa using move_neg (-d) u

theorem move_iff (d : K) (u v : V1) :
    u = move (-d) v ↔ move d u=v := by
  constructor
  · intro e; rw [e,move_neg']
  · intro e; rw [←e,move_neg]

theorem move_edge (d : K) {u v : V1} (h : Edge1 u v) : Edge1 (move d u) (move d v) := by
  refine ⟨h.1,?_⟩
  change d+u.2+bump u.1 v.1 = d+v.2
  rw [add_assoc,h.2]

def shift (d : K) (g : M) : M := fun uv => g (move (-d) uv.1,move (-d) uv.2)

theorem shift_add (d : K) (u v : M) : shift d (u+v)=shift d u+shift d v := rfl

theorem shift_comp (d e : K) (u : M) : shift (d+e) u=shift d (shift e u) := by
  funext uv
  change u (move (-(d+e)) uv.1,move (-(d+e)) uv.2) =
    u (move (-e) (move (-d) uv.1),move (-e) (move (-d) uv.2))
  rw [neg_add_rev,move_add,move_add]

theorem shift_bump (d : K) (u v : V1) :
    shift d (bump u v)=bump (move d u) (move d v) := by
  funext r
  obtain ⟨r,s⟩ := r
  simp only [shift,bump,Prod.mk.injEq,move_iff]

def act (d : K) (g : M) (u : V2) : V2 := (move d u.1,g+shift d u.2)

theorem act_edge (d : K) (g : M) {u v : V2} (h : Edge2 u v) :
    Edge2 (act d g u) (act d g v) := by
  refine ⟨move_edge d h.1,?_⟩
  change g+shift d u.2+bump (move d u.1) (move d v.1) = g+shift d v.2
  rw [←shift_bump,add_assoc,←shift_add,h.2]

theorem act_fiber (u v : V2) (h : u.1.1=v.1.1) :
    ∃! dg : K × M, act dg.1 dg.2 u=v := by
  let d := v.1.2-u.1.2
  let g := v.2-shift d u.2
  refine ⟨⟨d,g⟩,?_,?_⟩
  · apply Prod.ext
    · change move d u.1=v.1
      refine Prod.ext ?_ ?_
      · exact h
      · change d+u.1.2=v.1.2; simp [d]
    · change g+shift d u.2=v.2; simp [g]
  · intro w e
    have first := congrArg (fun t : V2 => t.1.2) e
    have second := congrArg (fun t : V2 => t.2) e
    change w.1+u.1.2=v.1.2 at first
    change w.2+shift w.1 u.2=v.2 at second
    have ed : w.1=d := eq_sub_of_add_eq first
    rw [ed] at second
    exact Prod.ext ed (eq_sub_of_add_eq second)

end HeawoodDoubleDeck
#print axioms HeawoodDoubleDeck.act_fiber
#print axioms HeawoodDoubleDeck.act_edge
