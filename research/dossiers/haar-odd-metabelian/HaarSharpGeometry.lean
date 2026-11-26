import HaarSharpLamp
import Mathlib.Data.Nat.ModEq

namespace HaarSharpLamp
open HaarCycle HaarAllNoncommuting

def oriented (p : Bool) (c : Fin 3) : G := if p then (port c)⁻¹ else port c

theorem port0 : port 0 = 1 := by rfl

theorem adj_label {a b : Bool × G} (h : haarAdj x y a b) :
    b.1 = !a.1 ∧ ∃ c : Fin 3, b.2 = a.2 * oriented a.1 c := by
  rcases a with ⟨a,g⟩
  rcases b with ⟨b,k⟩
  cases a <;> simp only [haarAdj, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
    Bool.not_true, oriented] at h ⊢
  · refine ⟨h.1,?_⟩
    rcases h.2 with eq | eq | eq
    · exact ⟨0, by simpa [port0] using eq⟩
    · exact ⟨1, eq⟩
    · exact ⟨2, eq⟩
  · refine ⟨h.1,?_⟩
    rcases h.2 with eq | eq | eq
    · exact ⟨0, by simpa [port0] using eq.symm⟩
    · exact ⟨1, by rw [eq]; simp [x,mul_assoc]⟩
    · exact ⟨2, by rw [eq]; simp [y,mul_assoc]⟩

theorem adj_symm {a b : Bool × G} (h : haarAdj x y a b) : haarAdj x y b a := by
  rcases a with ⟨a,g⟩; rcases b with ⟨b,k⟩
  cases a <;> cases b <;> simpa [haarAdj] using h

def segment (f : Nat → Fin 3) (i : Nat) : Nat → List (Fin 3)
  | 0 => []
  | n+1 => f i :: segment f (i+1) n

theorem segment_mem (f : Nat → Fin 3) (n i : Nat) (p : Option (Fin 3))
    (first : n ≠ 0 → p ≠ some (f i))
    (reduced : ∀ j, i ≤ j → j+1 < i+n → f j ≠ f (j+1)) :
    segment f i n ∈ words n p := by
  induction n generalizing i p with
  | zero => simp [segment,words]
  | succ n ih =>
    unfold segment words
    apply List.mem_flatMap.mpr
    refine ⟨f i, ?_, ?_⟩
    · generalize f i = c; fin_cases c <;> simp
    · simp only [if_neg (first (by omega)), List.mem_map]
      refine ⟨segment f (i+1) n, ?_, rfl⟩
      apply ih
      · intro hn eq
        cases n with
        | zero => exact (hn rfl).elim
        | succ n =>
          exact reduced i (by omega) (by omega) (Option.some.inj eq)
      · intro j hj hj'
        exact reduced j (by omega) (by omega)

theorem segment_head (f : Nat → Fin 3) (i n : Nat) :
    (segment f i (n+1)).head? = some (f i) := rfl

theorem segment_last (f : Nat → Fin 3) (i n : Nat) :
    (segment f i (n+1)).getLast? = some (f (i+n)) := by
  induction n generalizing i with
  | zero => simp [segment]
  | succ n ih =>
    simp only [segment, List.getLast?_cons_cons]
    have e : i + (n+1) = i+1+n := by omega
    rw [e]
    exact ih (i+1)

theorem oriented_inv (p : Bool) (c : Fin 3) :
    oriented (!p) c = (oriented p c)⁻¹ := by cases p <;> simp [oriented]

theorem segment_val (v : Nat → Bool × G) (f : Nat → Fin 3) (i n : Nat)
    (side : ∀ j, i ≤ j → j < i+n → (v (j+1)).1 = !(v j).1)
    (edge : ∀ j, i ≤ j → j < i+n → (v (j+1)).2 = (v j).2 * oriented (v j).1 (f j)) :
    (v (i+n)).2 = (v i).2 * value (!(v i).1) (segment f i n) := by
  induction n generalizing i with
  | zero => simp [segment,value]
  | succ n ih =>
    have e := ih (i+1) (fun j hj hj' => side j (by omega) (by omega))
                        (fun j hj hj' => edge j (by omega) (by omega))
    rw [show i+(n+1) = i+1+n by omega, e, edge i (by omega) (by omega),
        side i (by omega) (by omega)]
    cases h : (v i).1 <;> simp [h,segment,value,oriented,mul_assoc]

theorem port_neighbor (a b c : Bool × G) (p : Fin 3)
    (hs₁ : b.1 = !a.1) (hs₂ : c.1 = !a.1)
    (he₁ : b.2 = a.2 * oriented a.1 p) (he₂ : c.2 = a.2 * oriented a.1 p) : b = c :=
  Prod.ext (hs₁.trans hs₂.symm) (he₁.trans he₂.symm)

theorem rev_label {a b : Bool × G} (c : Fin 3)
    (s : b.1 = !a.1) (e : b.2 = a.2 * oriented a.1 c) :
    a.2 = b.2 * oriented b.1 c := by
  rw [s,oriented_inv,e,mul_assoc,mul_inv_cancel,mul_one]

theorem path_reduced (v : Nat → Bool × G) (f : Nat → Fin 3) {j : Nat}
    (hs : ∀ k, k = j ∨ k = j+1 → (v (k+1)).1 = !(v k).1)
    (he : ∀ k, k = j ∨ k = j+1 →
      (v (k+1)).2 = (v k).2 * oriented (v k).1 (f k))
    (sep : v j ≠ v (j+1+1)) : f j ≠ f (j+1) := by
  intro eq
  apply sep
  apply port_neighbor (v (j+1)) _ _ (f j)
  · rw [hs j (Or.inl rfl), Bool.not_not]
  · exact hs (j+1) (Or.inr rfl)
  · exact rev_label _ (hs j (Or.inl rfl)) (he j (Or.inl rfl))
  · simpa only [eq] using he (j+1) (Or.inr rfl)


theorem cross_paths (n : Nat) (hn : 1 < n) (ok : scan (table n) = true)
    (v w : Nat → Bool × G) (same₀ : v 0 = w 0) (side₀ : (v 0).1 = false)
    (sameN : v n = w n)
    (adjV : ∀ j, j < n → haarAdj x y (v j) (v (j+1)))
    (adjW : ∀ j, j < n → haarAdj x y (w j) (w (j+1)))
    (sepV : ∀ j, j+2 ≤ n → v j ≠ v (j+2))
    (sepW : ∀ j, j+2 ≤ n → w j ≠ w (j+2))
    (first : v 1 ≠ w 1) (last : v (n-1) ≠ w (n-1)) : False := by
  classical
  let f (j : Nat) := if h : j < n then (adj_label (adjV j h)).2.choose else 0
  let g (j : Nat) := if h : j < n then (adj_label (adjW j h)).2.choose else 0
  have sv j (h : j < n) : (v (j+1)).1 = !(v j).1 := (adj_label (adjV j h)).1
  have sw j (h : j < n) : (w (j+1)).1 = !(w j).1 := (adj_label (adjW j h)).1
  have ev j (h : j < n) : (v (j+1)).2 = (v j).2 * oriented (v j).1 (f j) := by
    dsimp [f]; rw [dif_pos h]; exact (adj_label (adjV j h)).2.choose_spec
  have ew j (h : j < n) : (w (j+1)).2 = (w j).2 * oriented (w j).1 (g j) := by
    dsimp [g]; rw [dif_pos h]; exact (adj_label (adjW j h)).2.choose_spec
  have rv j (_ : 0 ≤ j) (h : j+1 < 0+n) : f j ≠ f (j+1) := by
    apply path_reduced v f
    · intro k hk; exact sv k (by rcases hk with rfl|rfl <;> omega)
    · intro k hk; exact ev k (by rcases hk with rfl|rfl <;> omega)
    · exact sepV j (by omega)
  have rw' j (_ : 0 ≤ j) (h : j+1 < 0+n) : g j ≠ g (j+1) := by
    apply path_reduced w g
    · intro k hk; exact sw k (by rcases hk with rfl|rfl <;> omega)
    · intro k hk; exact ew k (by rcases hk with rfl|rfl <;> omega)
    · exact sepW j (by omega)
  have hv := segment_mem f n 0 none (by simp) rv
  have hw := segment_mem g n 0 none (by simp) rw'
  have uv := segment_val v f 0 n (fun j _ h => sv j (by omega)) (fun j _ h => ev j (by omega))
  have uw := segment_val w g 0 n (fun j _ h => sw j (by omega)) (fun j _ h => ew j (by omega))
  rw [Nat.zero_add, sameN] at uv
  rw [Nat.zero_add, ← same₀] at uw
  simp only [side₀, Bool.not_false] at uv uw
  have hvw := mul_left_cancel (uv.symm.trans uw)
  have endpoints := cert_sound ok hv hw hvw
  have nn : n = (n-1)+1 := by omega
  rw [nn] at endpoints
  simp only [segment_head,segment_last,Nat.zero_add] at endpoints
  rcases endpoints with e | e
  · apply first
    have eq := Option.some.inj e
    apply port_neighbor (v 0) _ _ (f 0)
    · exact sv 0 (by omega)
    · simpa only [same₀] using sw 0 (by omega)
    · exact ev 0 (by omega)
    · simpa only [same₀,eq] using ew 0 (by omega)
  · apply last
    have eq := Option.some.inj e
    have h : n-1 < n := by omega
    have r : n-1+1 = n := nn.symm
    have sv' := sv (n-1) h
    have sw' := sw (n-1) h
    have ev' := ev (n-1) h
    have ew' := ew (n-1) h
    rw [r] at sv' sw' ev' ew'
    apply port_neighbor (v n) _ _ (f (n-1))
    · rw [sv', Bool.not_not]
    · rw [sameN, sw', Bool.not_not]
    · exact rev_label _ sv' ev'
    · simpa only [sameN,eq] using rev_label _ sw' ew'


theorem no_cycle_of_check (n : Nat) (hn : 1 < n) (ok : scan (table n) = true) :
    ¬ HasCycle x y (2*n) := by
  intro ⟨v,inj,adj⟩
  let k := 2*n
  have kp : 0 < k := by dsimp [k]; omega
  let u (i : Nat) := v ⟨i%k,Nat.mod_lt _ kp⟩
  have ua i : haarAdj x y (u i) (u (i+1)) := by
    have h := adj ⟨i%k,Nat.mod_lt _ kp⟩
    simpa only [u, k, Nat.mod_add_mod] using h
  let s := if (u 0).1 then 1 else 0
  let t (i : Nat) := u (i+s)
  have t0 : (t 0).1 = false := by
    dsimp [t,s]
    split
    · simpa [*] using (adj_label (ua 0)).1
    · simpa using ‹¬ (u 0).1 = true›
  have ta i : haarAdj x y (t i) (t (i+1)) := by
    dsimp [t]; rw [show i+1+s = i+s+1 by omega]; exact ua _
  have period : t k = t 0 := by
    unfold t u
    congr 1
    apply Fin.ext
    simpa only [Fin.val_mk,Nat.zero_add] using Nat.add_mod_left k s
  have ti {i j : Nat} (hi : i < k) (hj : j < k) (h : t i = t j) : i = j := by
    have e := congrArg Fin.val (inj h)
    have hh : i+s ≡ j+s [MOD k] := e
    have e' := Nat.ModEq.add_right_cancel' s hh
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using e'
  let w (i : Nat) := t (k-i)
  have tail : k-n = n := by dsimp [k]; omega
  apply cross_paths n hn ok t w
  · simpa [w] using period.symm
  · exact t0
  · dsimp [w]; rw [tail]
  · exact fun j _ => ta j
  · intro j hj
    dsimp [w]
    have e : k-(j+1)+1 = k-j := by dsimp [k] at *; omega
    apply adj_symm
    rw [← e]
    exact ta _
  · intro j hj eh
    have absurd := ti (i:=j) (j:=j+2) (by dsimp [k]; omega) (by dsimp [k]; omega) eh
    omega
  · intro j hj
    dsimp [w]
    by_cases jz : j = 0
    · subst j
      rw [Nat.sub_zero,period]
      intro e
      have en := ti (i:=0) (j:=k-(0+2)) kp (by dsimp [k]; omega) e
      dsimp [k] at en
      omega
    · intro e
      have en := ti (i:=k-j) (j:=k-(j+2)) (by dsimp [k]; omega) (by dsimp [k]; omega) e
      dsimp [k] at en
      omega
  · intro e
    have en := ti (i:=1) (j:=k-1) (by dsimp [k]; omega) (by dsimp [k]; omega) e
    dsimp [k] at en
    omega
  · intro e
    have en := ti (i:=n-1) (j:=k-(n-1)) (by dsimp [k]; omega) (by dsimp [k]; omega) e
    dsimp [k] at en
    omega

theorem no_short_cycles : ¬ HasCycle x y 4 ∧ ¬ HasCycle x y 8 ∧ ¬ HasCycle x y 16 :=
  ⟨no_cycle_of_check 2 (by decide) check2,
    no_cycle_of_check 4 (by decide) check4,
    no_cycle_of_check 8 (by decide) check8⟩

#print axioms no_short_cycles
end HaarSharpLamp
