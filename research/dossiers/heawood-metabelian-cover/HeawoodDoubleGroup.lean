import HeawoodDoubleDeck
import Mathlib.GroupTheory.Abelianization.Defs

namespace HeawoodDoubleDeck
open HeawoodDouble

theorem shift_id (u : M) : shift 0 u=u := by
  funext r
  obtain ⟨r,s⟩ := r
  simp [shift,move]
theorem shift_zero (d : K) : shift d (0:M)=0 := rfl

structure Deck where
  phase : K
  lamp : M

@[ext] theorem Deck.ext' {a b : Deck} (h : a.phase=b.phase) (k : a.lamp=b.lamp) : a=b := by
  cases a
  cases b
  simp_all

def mul (a b : Deck) : Deck := ⟨a.phase+b.phase,a.lamp+shift a.phase b.lamp⟩
def unit : Deck := ⟨0,0⟩
def inv (u : Deck) : Deck := ⟨-u.phase,-shift (-u.phase) u.lamp⟩

instance : Group Deck where
  mul := mul
  one := unit
  inv := inv
  mul_assoc a b c := by
    change mul (mul a b) c = mul a (mul b c)
    refine Deck.ext' ?_ ?_
    · simp [mul,add_assoc]
    · simp [mul,shift_add,shift_comp,add_assoc]
  one_mul a := by
    change mul unit a = a
    refine Deck.ext' ?_ ?_ <;> simp [mul,unit,shift_id]
  mul_one a := by
    change mul a unit = a
    refine Deck.ext' ?_ ?_ <;> simp [mul,unit,shift_zero]
  inv_mul_cancel a := by
    change mul (inv a) a = unit
    refine Deck.ext' ?_ ?_ <;> simp [mul,inv,unit]

def projection : Deck →* Multiplicative K where
  toFun a := Multiplicative.ofAdd a.phase
  map_one' := rfl
  map_mul' _ _ := rfl

theorem kernel_comm (a b : Deck) (ha : a∈projection.ker) (hb : b∈projection.ker) : a*b=b*a := by
  change a.phase=0 at ha
  change b.phase=0 at hb
  refine Deck.ext' ?_ ?_
  · change a.phase+b.phase=b.phase+a.phase; rw [add_comm]
  · change a.lamp+shift a.phase b.lamp=b.lamp+shift b.phase a.lamp
    simp [ha,hb,shift_id,add_comm]

theorem metabelian : ∀ a b : commutator Deck, a*b=b*a := by
  intro a b
  apply Subtype.ext
  exact kernel_comm a.val b.val (Abelianization.commutator_subset_ker projection a.property)
    (Abelianization.commutator_subset_ker projection b.property)

def coords : Deck ≃ K × M := ⟨fun a => (a.phase,a.lamp),fun p => ⟨p.1,p.2⟩,by intro a; cases a; rfl,by intro a; cases a; rfl⟩
instance : Finite Deck := Finite.of_equiv _ coords.symm

def action (d : Deck) (u : V2) : V2 := act d.phase d.lamp u
theorem action_one (u : V2) : action 1 u=u := by
  refine Prod.ext ?_ ?_
  · change move 0 u.1=u.1
    refine Prod.ext ?_ ?_
    · rfl
    · simp [move]
  · change (0:M)+shift 0 u.2=u.2; simp [shift_id]

theorem action_mul (a b : Deck) (u : V2) : action (a*b) u=action a (action b u) := by
  refine Prod.ext ?_ ?_
  · exact move_add a.phase b.phase u.1
  · change (a.lamp+shift a.phase b.lamp)+shift (a.phase+b.phase) u.2 =
      a.lamp+shift a.phase (b.lamp+shift b.phase u.2)
    simp [shift_add,shift_comp,add_assoc]

theorem action_regular (u v : V2) (h : u.1.1=v.1.1) :
    ∃! d : Deck, action d u=v := by
  obtain ⟨p,hp,unique⟩ := act_fiber u v h
  refine ⟨coords.symm p,hp,?_⟩
  intro d hd
  apply coords.injective
  exact unique (coords d) hd

theorem action_edge (d : Deck) {u v : V2} (e : Edge2 u v) : Edge2 (action d u) (action d v) :=
  act_edge d.phase d.lamp e

end HeawoodDoubleDeck
#print axioms HeawoodDoubleDeck.metabelian
#print axioms HeawoodDoubleDeck.action_regular
