import HaarSharpHeawood

namespace HaarSharpHeawood
open HaarSharpPortGeometry
local notation "x" => port 1
local notation "y" => port 2

abbrev Base := Bool × S

def displacement (c : Fin 3) : S := ![0,1,3] c

def next (b : Base) (c : Fin 3) : Base :=
  (!b.1, if b.1 then b.2 - displacement c else b.2 + displacement c)

def voltage (b : Base) (c : Fin 3) : A :=
  if c = 2 then
    if b.1 then -scale (b.2-3) else scale b.2
  else 0

def liftNext (a : Base × A) (c : Fin 3) : Base × A :=
  (next a.1 c, a.2 + voltage a.1 c)

theorem next_rev (b : Base) (c : Fin 3) : next (next b c) c = b := by
  obtain ⟨i,j⟩ := b
  cases i <;> simp [next,sub_add_cancel]

theorem next_inj (b : Base) : Function.Injective (next b) := by
  revert b
  unfold Function.Injective
  decide +kernel

theorem antisymmetric (b : Base) (c : Fin 3) : voltage (next b c) c = -voltage b c := by
  obtain ⟨i,j⟩ := b
  fin_cases c <;> cases i <;> simp [voltage,next,displacement,Matrix.cons_val_one,Matrix.cons_val_zero]
 
def coverCoordinates : Bool × G ≃ Base × A where
  toFun a := ((a.1,a.2.shift),a.2.lamp)
  invFun a := (a.1.1,⟨a.2,a.1.2⟩)
  left_inv := by intro a; rcases a with ⟨b,⟨s,t⟩⟩; rfl
  right_inv := by intro a; rcases a with ⟨⟨b,s⟩,t⟩; rfl

private theorem mul_shift (a b : G) : (a*b).shift = a.shift+b.shift := rfl
private theorem mul_lamp (a b : G) : (a*b).lamp = a.lamp+scale a.shift*b.lamp := rfl
private theorem inv_shift (a : G) : a⁻¹.shift = -a.shift := rfl
private theorem inv_lamp (a : G) : a⁻¹.lamp = -(scale (-a.shift)*a.lamp) := rfl

/-- Exact coordinate conjugacy with the usual abelian voltage lift. -/
theorem coordinates_step (a : Bool × G) (c : Fin 3) :
    coverCoordinates (step a c) = liftNext (coverCoordinates a) c := by
  obtain ⟨b,a⟩ := a
  obtain ⟨u,v⟩ := a
  have h : scale (v-3) = scale v * scale (-3) := by
    simpa [sub_eq_add_neg] using scale_add v (-3)
  fin_cases c <;> cases b <;>
    change _ = _ <;>
    simp [coverCoordinates, liftNext, next, voltage, displacement, step, oriented,
      Matrix.cons_val_one, Matrix.cons_val_zero, port]
  all_goals
    simp [mul_shift,mul_lamp,inv_shift,inv_lamp,sub_eq_add_neg,scale_add]

theorem adj_iff_lift (a b : Bool × G) :
    HaarCycle.haarAdj x y a b ↔ ∃ c, coverCoordinates b = liftNext (coverCoordinates a) c := by
  constructor
  · intro e
    obtain ⟨hb,c,hc⟩ := adj_label port port0 e
    have eq : b = step a c := Prod.ext hb hc
    exact ⟨c,eq ▸ coordinates_step a c⟩
  · rintro ⟨c,hc⟩
    rw [← coordinates_step a c] at hc
    rw [coverCoordinates.injective hc]
    exact step_adj a c

theorem projection_surjective : Function.Surjective projection := by
  intro q
  exact ⟨⟨0,q.toAdd⟩,rfl⟩

theorem projection_kernel_abelian : ∀ a b : projection.ker, a*b=b*a := by
  intro a b
  apply Subtype.ext
  have ha : a.val.shift = 0 := a.property
  have hb : b.val.shift = 0 := b.property
  apply G.ext'
  · change (mul a.val b.val).lamp = (mul b.val a.val).lamp
    simp [mul,ha,hb,scale_zero,add_comm]
  · change (mul a.val b.val).shift = (mul b.val a.val).shift
    simp [mul,ha,hb]

theorem graph_cardinality : Nat.card (Bool × G) = 3346 := by
  rw [Nat.card_prod, cardinality]
  simp

/-- A check of the cyclic Fano incidence presentation: distinct left
 vertices have exactly one common right vertex. The difference set is 013. -/
theorem cyclicFano :
    ∀ i j : S, i ≠ j →
      ∃! k : S, (∃ c : Fin 3, k = i + displacement c) ∧
        (∃ c : Fin 3, k = j + displacement c) := by
  unfold ExistsUnique
  decide +kernel

def translate (u : A) (a : Base × A) : Base × A := (a.1,u+a.2)

theorem translate_step (u : A) (a : Base × A) (c : Fin 3) :
    translate u (liftNext a c) = liftNext (translate u a) c := by
  simp [translate,liftNext,add_assoc]

theorem translate_regular (a b : Base × A) (hb : a.1 = b.1) :
    ∃! u, translate u a = b := by
  refine ⟨b.2-a.2, Prod.ext hb (sub_add_cancel ..), fun u hu => ?_⟩
  have e := congrArg Prod.snd hu
  rw [← e]
  exact (add_sub_cancel_right u a.2).symm

def VoltageCycle (n : Nat) : Prop :=
  ∃ v : Fin n → Base × A, Function.Injective v ∧
    ∀ i, ∃ c : Fin 3, v ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ = liftNext (v i) c

theorem voltage_cycle_iff (n : Nat) :
    VoltageCycle n ↔ HaarAllNoncommuting.HasCycle x y n := by
  constructor
  · rintro ⟨v,hv,he⟩
    refine ⟨coverCoordinates.symm ∘ v, coverCoordinates.symm.injective.comp hv, fun i => ?_⟩
    apply (adj_iff_lift _ _).mpr
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using he i
  · rintro ⟨v,hv,he⟩
    exact ⟨coverCoordinates ∘ v, coverCoordinates.injective.comp hv, fun i => (adj_iff_lift _ _).mp (he i)⟩

/-- This explicit abelian voltage cover of Heawood attains the bound 32. -/
theorem voltage_sharp :
    VoltageCycle 32 ∧ ¬ VoltageCycle 4 ∧ ¬ VoltageCycle 8 ∧ ¬ VoltageCycle 16 := by
  simpa only [voltage_cycle_iff] using sharp

def walk : List (Fin 3) → Base × A → Base × A
  | [], a => a
  | c::w, a => walk w (liftNext a c)

theorem walk_append (u v : List (Fin 3)) (a : Base × A) :
    walk (u++v) a = walk v (walk u a) := by
  induction u generalizing a with
  | nil => rfl
  | cons c u ih => exact ih (liftNext a c)

def blocks (u : List (Fin 3)) : Nat → List (Fin 3)
  | 0 => []
  | n+1 => u ++ blocks u n

private theorem walk_lamp (a : A) :
    walk [2,0,0,1,0,1,0,1] ((false,0),a) = ((false,0),a+1) := by
  simp [walk,liftNext,next,voltage,displacement,scale_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
  decide +kernel

private theorem walk_shift (a : A) (s : S) :
    walk [1,0] ((false,s),a) = ((false,s+1),a) := by
  simp [walk,liftNext,next,voltage,displacement]

private theorem blocks_lamp (n : Nat) (a : A) :
    walk (blocks [2,0,0,1,0,1,0,1] n) ((false,0),a) = ((false,0),a+(n:A)) := by
  induction n generalizing a with
  | zero => simp [blocks,walk]
  | succ n ih => rw [blocks,walk_append,walk_lamp,ih]; simp only [Nat.cast_succ]; congr 1; abel

private theorem blocks_shift (n : Nat) (a : A) (s : S) :
    walk (blocks [1,0] n) ((false,s),a) = ((false,s+(n:S)),a) := by
  induction n generalizing s with
  | zero => simp [blocks,walk]
  | succ n ih => rw [blocks,walk_append,walk_shift,ih]; simp only [Nat.cast_succ]; congr 1; abel

/-- Every vertex is reached from the basepoint by an explicit port word. -/
theorem reachable (w : Base × A) :
    ∃ u : List (Fin 3), walk u ((false,0),0) = w := by
  obtain ⟨⟨b,s⟩,a⟩ := w
  let u := blocks [2,0,0,1,0,1,0,1] a.val ++ blocks [1,0] s.val
  have h : walk u ((false,0),0) = ((false,s),a) := by
    dsimp [u]
    rw [walk_append,blocks_lamp]
    simp only [zero_add,ZMod.natCast_zmod_val]
    rw [blocks_shift]
    simp
  cases b
  · exact ⟨u,h⟩
  · exact ⟨u++[0],by rw [walk_append,h]; simp [walk,liftNext,next,voltage,displacement]⟩

#print axioms adj_iff_lift
#print axioms antisymmetric
#print axioms cyclicFano
#print axioms voltage_sharp
#print axioms reachable
end HaarSharpHeawood
