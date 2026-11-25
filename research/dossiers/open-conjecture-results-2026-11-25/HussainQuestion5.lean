import Mathlib

/-!
Hussain's Question 5: the complexity of classifying a complete DFA whose
language is promised to be closed under taking scattered subwords.
Source: arXiv:2611.27454v1, Table 1 and Section 6.
https://arxiv.org/html/2611.27454v1#S6

For N states and k letters the answer is Theta(N*k) in the explicit
transition-table model with one state label per cell. The lower bound is a
deterministic transition-probe bound with a one-entry perturbation witness.
The upper bound is in the indexed-array word-RAM work model specified in
classLinear. The pure Lean operations specify array contents, not the
compiled Lean program's wall-clock time. The algorithm uses forward and
reverse worklists, letter endpoints, and tables of target multiplicities.
Check with Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
-/

namespace HussainQ5
open Function

structure DFA (Q A : Type) where
  step : Q → A → Q
  start : Q
  accept : Q → Bool

def DFA.run {Q A : Type} (M : DFA Q A) (s : Q) (w : List A) : Q :=
  w.foldl M.step s

def DFA.accepts {Q A : Type} (M : DFA Q A) (w : List A) : Prop :=
  M.accept (M.run M.start w) = true

theorem run_append {Q A : Type} (M : DFA Q A) (s : Q) (u v : List A) :
    M.run s (u++v) = M.run (M.run s u) v := by
  simp [DFA.run,List.foldl_append]

theorem run_power {Q A : Type} (M : DFA Q A) (s : Q) (a : A) (n : Nat) :
    M.run s (List.replicate n a) = (fun q => M.step q a)^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    change M.run (M.step s a) (List.replicate n a) = _
    rw [ih,Function.iterate_succ_apply]

/-- In at most the number of states, any orbit has reached a periodic state. -/
theorem orbit_repeat {Q : Type} [Fintype Q] (f : Q → Q) (x : Q) :
    ∃ i j, i<j ∧ j≤Fintype.card Q ∧ f^[i] x = f^[j] x := by
  classical
  let N := Fintype.card Q
  let e (i : Fin (N+1)) := f^[i.val] x
  have h : ¬ Function.Injective e := by
    intro he
    have hn : N+1 ≤ N := by
      simpa [N] using (Fintype.card_le_of_injective e he)
    omega
  obtain ⟨i,j,he,hne⟩ := Function.not_injective_iff.mp h
  have hneq : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_trichotomy i.val j.val with hi | hij | hj
  · exact ⟨i.val,j.val,hi,by have h := j.isLt; omega,he⟩
  · exact False.elim (hneq hij)
  · exact ⟨j.val,i.val,hj,by have h := i.isLt; omega,he.symm⟩

theorem orbit_period_after_card {Q : Type} [Fintype Q] (f : Q → Q) (x : Q) :
    ∃ p>0, ∀ t : Nat, f^[Fintype.card Q+t*p] x = f^[Fintype.card Q] x := by
  obtain ⟨i,j,hij,hj,he⟩ := orbit_repeat f x
  let N := Fintype.card Q
  let p := j-i
  have hp : 0 < p := by dsimp [p]; omega
  refine ⟨p,hp,?_⟩
  have hfix : f^[N+p] x = f^[N] x := by
    have he' := congrArg (f^[N-i]) he
    rw [← Function.iterate_add_apply,← Function.iterate_add_apply] at he'
    have h₁ : N-i+i=N := by omega
    have h₂ : N-i+j=N+p := by dsimp [p]; omega
    simpa only [h₁,h₂] using he'.symm
  intro t
  induction t with
  | zero => simp
  | succ t ht =>
    rw [Nat.succ_mul,← Nat.add_assoc,Nat.add_comm (N+t*p) p,Function.iterate_add_apply,ht,
      ← Function.iterate_add_apply,Nat.add_comm p N]
    exact hfix

end HussainQ5

namespace HussainQ5
open Function

def DFA.subwordClosed {Q A : Type} (M : DFA Q A) : Prop :=
  ∀ ⦃u v : List A⦄, u.Sublist v → M.accepts v → M.accepts u

def sand {A : Type} (a b : A) (p : Nat) :=
  List.replicate p a ++ [b] ++ List.replicate p a

def pairWord {A : Type} (a b : A) (p : Nat) :=
  List.replicate p a ++ List.replicate p b

theorem replicate_sublist {A : Type} (a : A) {n m : Nat} (h : n ≤ m) :
    (List.replicate n a).Sublist (List.replicate m a) := by
  induction m with
  | zero =>
    have he : n=0 := by omega
    subst n
    exact List.Sublist.refl _
  | succ m ih =>
    by_cases he : n=m+1
    · subst n; exact List.Sublist.refl _
    · rw [List.replicate_succ]
      exact List.Sublist.cons _ (ih (by omega))

theorem sand_sublist {A : Type} (a b : A) {n m : Nat} (h : n ≤ m) :
    (sand a b n).Sublist (sand a b m) :=
  ((replicate_sublist a h).append (List.Sublist.refl [b])).append (replicate_sublist a h)

theorem pair_sublist {A : Type} (a b : A) {n m : Nat} (h : n ≤ m) :
    (pairWord a b n).Sublist (pairWord a b m) :=
  (replicate_sublist a h).append (replicate_sublist b h)

theorem sand_accept_at_all {Q A : Type} [Fintype Q]
    (M : DFA Q A) (closed : M.subwordClosed) (a b : A)
    (h : M.accepts (sand a b (Fintype.card Q))) :
    ∀ n, M.accepts (sand a b n) := by
  let N := Fintype.card Q
  let fa : Q → Q := fun q => M.step q a
  let mid := M.step (fa^[N] M.start) b
  obtain ⟨p,hp,hpFix⟩ := orbit_period_after_card fa M.start
  obtain ⟨q,hq,hqFix⟩ := orbit_period_after_card fa mid
  intro n
  let H := N+n*(p*q)
  have hn : n≤H := by
    have hh : n*1 ≤ n*(p*q) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.mul_pos hp hq))
    dsimp [H]
    omega
  have hleft : fa^[H] M.start = fa^[N] M.start := by
    have he : H = N+(n*q)*p := by dsimp [H]; ring
    rw [he]
    exact hpFix _
  have hright : fa^[H] mid = fa^[N] mid := by
    have he : H = N+(n*p)*q := by dsimp [H]; ring
    rw [he]
    exact hqFix _
  apply closed (sand_sublist a b hn)
  have he : ∀ d, M.run M.start (sand a b d) = fa^[d] (M.step (fa^[d] M.start) b) := by
    intro d
    simp only [sand,run_append,run_power]
    rfl
  unfold DFA.accepts at *
  rw [he,hleft]
  change M.accept (fa^[H] mid) = true
  rw [hright]
  simpa only [he] using h

theorem pair_accept_at_all {Q A : Type} [Fintype Q]
    (M : DFA Q A) (closed : M.subwordClosed) (a b : A)
    (h : M.accepts (pairWord a b (Fintype.card Q))) :
    ∀ n, M.accepts (pairWord a b n) := by
  let N := Fintype.card Q
  let fa : Q → Q := fun q => M.step q a
  let fb : Q → Q := fun q => M.step q b
  let mid := fa^[N] M.start
  obtain ⟨p,hp,hpFix⟩ := orbit_period_after_card fa M.start
  obtain ⟨q,hq,hqFix⟩ := orbit_period_after_card fb mid
  intro n
  let H := N+n*(p*q)
  have hn : n≤H := by
    have hh : n*1 ≤ n*(p*q) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.mul_pos hp hq))
    dsimp [H]
    omega
  have hleft : fa^[H] M.start = mid := by
    have he : H = N+(n*q)*p := by dsimp [H]; ring
    rw [he]
    exact hpFix _
  have hright : fb^[H] mid = fb^[N] mid := by
    have he : H = N+(n*p)*q := by dsimp [H]; ring
    rw [he]
    exact hqFix _
  apply closed (pair_sublist a b hn)
  have he : ∀ d, M.run M.start (pairWord a b d) = fb^[d] (fa^[d] M.start) := by
    intro d
    simp [pairWord,run_append,run_power,fa,fb]
  unfold DFA.accepts at *
  rw [he,hleft,hright]
  simpa only [he] using h

end HussainQ5

namespace HussainQ5

def HomInfinite {Q A : Type} (D : DFA Q A) : Prop :=
  ∀ n, ∃ a b : A, a ≠ b ∧ D.accepts (sand a b n)

def HetInfinite {Q A : Type} (D : DFA Q A) : Prop :=
  ∀ n, ∃ a b : A, a ≠ b ∧ D.accepts (pairWord a b n)

theorem hom_test {Q A : Type} [Fintype Q] (D : DFA Q A) (closed : D.subwordClosed) :
    HomInfinite D ↔ ∃ a b : A, a ≠ b ∧ D.accepts (sand a b (Fintype.card Q)) := by
  constructor
  · intro h; exact h (Fintype.card Q)
  · rintro ⟨a,b,ha,hb⟩ n
    exact ⟨a,b,ha,sand_accept_at_all D closed a b hb n⟩

theorem het_test {Q A : Type} [Fintype Q] (D : DFA Q A) (closed : D.subwordClosed) :
    HetInfinite D ↔ ∃ a b : A, a ≠ b ∧ D.accepts (pairWord a b (Fintype.card Q)) := by
  constructor
  · intro h; exact h (Fintype.card Q)
  · rintro ⟨a,b,ha,hb⟩ n
    exact ⟨a,b,ha,pair_accept_at_all D closed a b hb n⟩

end HussainQ5


namespace HussainQ5
open Function

def nextState {N : Nat} (s : Fin (N+2)) : Fin (N+2) :=
  ⟨min (N+1) (s.val+1),by omega⟩

def chain {A : Type} (N : Nat) : DFA (Fin (N+2)) A :=
  ⟨fun s _ => nextState s,0,fun s => decide (s.val ≤ N)⟩

def edited {A : Type} [DecidableEq A] {N : Nat} (i : Fin (N+1)) (a : A) :
    DFA (Fin (N+2)) A :=
  ⟨fun s b => if s.val=i.val ∧ b=a then s else nextState s,0,fun s => decide (s.val ≤ N)⟩

theorem run_cons {Q A : Type} (D : DFA Q A) (s : Q) (a : A) (w : List A) :
    D.run s (a::w) = D.run (D.step s a) w := rfl

theorem run_nil {Q A : Type} (D : DFA Q A) (s : Q) : D.run s [] = s := rfl

theorem chain_run {A : Type} (N : Nat) (s : Fin (N+2)) (w : List A) :
    ((chain N).run s w).val = min (N+1) (s.val+w.length) := by
  induction w generalizing s with
  | nil =>
    rw [run_nil]
    have hs := s.isLt
    simp [Nat.min_eq_right (by omega : s.val ≤ N+1)]
  | cons a w ih =>
    rw [run_cons,ih]
    change min (N+1) (min (N+1) (s.val+1)+w.length) = min (N+1) (s.val+(w.length+1))
    omega

theorem chain_accepts_iff {A : Type} (N : Nat) (w : List A) :
    (chain N).accepts w ↔ w.length ≤ N := by
  change decide (((chain N).run (0 : Fin (N+2)) w).val ≤ N) = true ↔ _
  rw [decide_eq_true_eq,chain_run]
  change min (N+1) (0+w.length) ≤ N ↔ _
  omega

theorem chain_closed {A : Type} (N : Nat) : (chain (A:=A) N).subwordClosed := by
  intro u v h hv
  exact (chain_accepts_iff N u).2 (h.length_le.trans ((chain_accepts_iff N v).1 hv))

theorem edited_step_le {A : Type} [DecidableEq A] {N : Nat} (i : Fin (N+1)) (a b : A)
    (s : Fin (N+2)) : ((edited i a).step s b).val ≤ s.val+1 := by
  by_cases h : s.val=i.val ∧ b=a <;> simp [edited,h,nextState]

theorem edited_run_le {A : Type} [DecidableEq A] {N : Nat} (i : Fin (N+1)) (a : A)
    (s : Fin (N+2)) (w : List A) : ((edited i a).run s w).val ≤ s.val+w.length := by
  induction w generalizing s with
  | nil => simp [run_nil]
  | cons b w ih =>
    rw [run_cons]
    have hh := ih ((edited i a).step s b)
    have h := edited_step_le i a b s
    simp only [List.length_cons]
    omega

theorem edited_accepts_short {A : Type} [DecidableEq A] {N : Nat} (i : Fin (N+1)) (a : A)
    (w : List A) (h : w.length ≤ N) : (edited i a).accepts w := by
  change decide (((edited i a).run (0 : Fin (N+2)) w).val ≤ N) = true
  rw [decide_eq_true_eq]
  exact (show ((edited i a).run 0 w).val ≤ w.length by simpa using edited_run_le i a (0 : Fin (N+2)) w).trans h

theorem edited_run_under {A : Type} [DecidableEq A] {N : Nat} (i : Fin (N+1)) (a : A)
    (s : Fin (N+2)) (w : List A) (h : s.val+w.length ≤ i.val) :
    ((edited i a).run s w).val = s.val+w.length := by
  induction w generalizing s with
  | nil => simp [run_nil]
  | cons b w ih =>
    simp only [List.length_cons] at h ⊢
    have hi : i.val ≤ N := by have hh := i.isLt; omega
    have hn : s.val+1 ≤ N+1 := by omega
    have hne : ¬(s.val=i.val ∧ b=a) := by omega
    have hstep : ((edited i a).step s b).val=s.val+1 := by
      simp only [edited,ite_eq_right hne,nextState,Nat.min_eq_right hn]
    rw [run_cons,ih _ (by omega),hstep]
    omega

theorem edited_run_over {A : Type} [DecidableEq A] {N : Nat} (i : Fin (N+1)) (a : A)
    (s : Fin (N+2)) (w : List A) (h : i.val<s.val) :
    ((edited i a).run s w).val = min (N+1) (s.val+w.length) := by
  induction w generalizing s with
  | nil =>
    rw [run_nil]
    have hs := s.isLt
    simp [Nat.min_eq_right (by omega : s.val ≤ N+1)]
  | cons b w ih =>
    have hs := s.isLt
    have hne : ¬(s.val=i.val ∧ b=a) := by omega
    have hstep : ((edited i a).step s b).val=min (N+1) (s.val+1) := by
      simp [edited,hne,nextState]
    rw [run_cons,ih _ (by omega),hstep]
    simp only [List.length_cons]
    omega

theorem edited_run_loop {A : Type} [DecidableEq A] {N : Nat} (i : Fin (N+1)) (a : A)
    (s : Fin (N+2)) (h : s.val=i.val) (r : Nat) :
    (edited i a).run s (List.replicate r a) = s := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.replicate_succ,run_cons]
    simpa [edited,h] using ih

theorem initial_run_split {A : Type} [DecidableEq A] (a : A) (w : List A) :
    ∃ r v, w=List.replicate r a++v ∧ (v=[] ∨ ∃ b t, b≠a ∧ v=b::t) := by
  induction w with
  | nil => exact ⟨0,[],rfl,Or.inl rfl⟩
  | cons b w ih =>
    by_cases h : b=a
    · subst b
      obtain ⟨r,v,he,hv⟩ := ih
      exact ⟨r+1,v,by rw [List.replicate_succ,List.cons_append,← he],hv⟩
    · exact ⟨0,b::w,rfl,Or.inr ⟨b,w,h,rfl⟩⟩

end HussainQ5

namespace HussainQ5

theorem edited_accepts_iff {A : Type} [DecidableEq A] {N : Nat} (i : Fin (N+1))
    (a : A) (w : List A) : (edited i a).accepts w ↔
      w.length ≤ N ∨ ∃ x r y, w=x++List.replicate r a++y ∧ x.length=i.val ∧ y.length ≤ N-i.val := by
  have hi : i.val ≤ N := by have h := i.isLt; omega
  have under (x : List A) (hx : x.length=i.val) :
      ((edited i a).run (0 : Fin (N+2)) x).val = i.val := by
    have h := edited_run_under i a (0 : Fin (N+2)) x (by simp [hx])
    simpa [hx] using h
  constructor
  · intro h
    by_cases hh : w.length ≤ N
    · exact Or.inl hh
    · right
      let x := w.take i.val
      let y₀ := w.drop i.val
      have hxy : x++y₀=w := List.take_append_drop _ _
      have hx : x.length=i.val := by simp [x,Nat.min_eq_left (by omega : i.val ≤ w.length)]
      obtain ⟨r,y,hy,hy'⟩ := initial_run_split a y₀
      have he : w=x++List.replicate r a++y := by rw [List.append_assoc,← hy,hxy]
      refine ⟨x,r,y,he,hx,?_⟩
      change decide (((edited i a).run (0 : Fin (N+2)) w).val ≤ N) = true at h
      rw [decide_eq_true_eq,he,run_append,run_append,edited_run_loop i a _ (under x hx)] at h
      rcases hy' with rfl | ⟨b,ys,hb,rfl⟩
      · simp
      · rw [run_cons] at h
        let s := (edited i a).run (0 : Fin (N+2)) x
        have hs : s.val = i.val := under x hx
        have hstep : ((edited i a).step s b).val=i.val+1 := by
          simp [edited,hb,nextState,hs,hi]
        have hv := edited_run_over i a ((edited i a).step s b) ys (by omega)
        change ((edited i a).run ((edited i a).step s b) ys).val ≤ N at h
        rw [hv,hstep] at h
        simp only [List.length_cons]
        omega
  · rintro (h | ⟨x,r,y,rfl,hx,hy⟩)
    · exact edited_accepts_short i a w h
    · change decide (((edited i a).run (0 : Fin (N+2)) (x++List.replicate r a++y)).val ≤ N) = true
      rw [decide_eq_true_eq,run_append,run_append,edited_run_loop i a _ (under x hx)]
      have hs := edited_run_le i a ((edited i a).run (0 : Fin (N+2)) x) y
      rw [under x hx] at hs
      omega

end HussainQ5

namespace HussainQ5

theorem edited_closed {A : Type} [DecidableEq A] {N : Nat} (i : Fin (N+1)) (a : A) :
    (edited i a).subwordClosed := by
  intro u v hv hu
  rcases (edited_accepts_iff i a v).1 hu with hv' | ⟨x,r,y,he,hx,hy⟩
  · exact edited_accepts_short i a u (hv.length_le.trans hv')
  · rw [he,List.append_assoc] at hv
    obtain ⟨u₁,u₂,he',hu₁,hu₂⟩ := List.sublist_append_iff.mp hv
    obtain ⟨m,v₂,hv',hm,hv₂⟩ := List.sublist_append_iff.mp hu₂
    have hmem : ∀ b∈m, b=a := by
      intro b hb
      exact (List.mem_replicate.mp (hm.subset hb)).2
    have hrep : m=List.replicate m.length a := List.eq_replicate_of_mem hmem
    have hl₁ : u₁.length ≤ i.val := by simpa only [hx] using hu₁.length_le
    have hl₂ : v₂.length ≤ N-i.val := hv₂.length_le.trans hy
    let d := i.val-u₁.length
    by_cases h : d ≤ m.length
    · apply (edited_accepts_iff i a u).2
      right
      refine ⟨u₁++List.replicate d a,m.length-d,v₂,?_,?_,hl₂⟩
      · have hsplit : m = List.replicate d a ++ List.replicate (m.length-d) a := by
          rw [← List.replicate_add,show d+(m.length-d)=m.length by omega]
          exact hrep
        calc
          u = u₁++(m++v₂) := by rw [he',hv']
          _ = u₁++((List.replicate d a ++ List.replicate (m.length-d) a)++v₂) :=
            congrArg (fun z => u₁++(z++v₂)) hsplit
          _ = _ := by simp only [List.append_assoc]
      · simp only [List.length_append,List.length_replicate]
        dsimp [d]
        omega
    · apply edited_accepts_short i a u
      rw [he',hv',List.length_append,List.length_append]
      dsimp [d] at h
      have hi := i.isLt
      omega

def Unbounded {Q A : Type} (D : DFA Q A) : Prop :=
  ∀ n, ∃ w, D.accepts w ∧ n ≤ w.length

theorem unbounded_edited {A : Type} [DecidableEq A] {N : Nat} (i : Fin (N+1)) (a : A) :
    Unbounded (edited i a) := by
  intro n
  let x := List.replicate i.val a
  let w := x++List.replicate n a
  refine ⟨w,?_,by simp [w,x]⟩
  apply (edited_accepts_iff i a w).2
  right
  exact ⟨x,n,[],by simp [w],by simp [x],by simp⟩

theorem bounded_chain {A : Type} (N : Nat) : ¬ Unbounded (chain (A:=A) N) := by
  intro h
  obtain ⟨w,hw,hwn⟩ := h (N+1)
  have hh := (chain_accepts_iff N w).1 hw
  omega

end HussainQ5


namespace HussainQ5

inductive ProbeTree (I V O : Type) where
  | leaf : O → ProbeTree I V O
  | probe : I → (V → ProbeTree I V O) → ProbeTree I V O

def ProbeTree.eval {I V O : Type} (t : ProbeTree I V O) (w : I → V) : O :=
  match t with
  | .leaf o => o
  | .probe i k => (k (w i)).eval w

def ProbeTree.trace {I V O : Type} (t : ProbeTree I V O) (w : I → V) : List I :=
  match t with
  | .leaf _ => []
  | .probe i k => i :: (k (w i)).trace w

theorem eval_agreement {I V O : Type} (t : ProbeTree I V O) (w v : I → V)
    (h : ∀ i∈t.trace w, v i=w i) : t.eval v = t.eval w := by
  induction t with
  | leaf o => rfl
  | probe i k ih =>
    have hi : v i=w i := h i (by simp [ProbeTree.trace])
    simp only [ProbeTree.eval,hi]
    exact ih (w i) (fun j hj => h j (by simp [ProbeTree.trace,hj]))

abbrev ChainTable (N : Nat) (A : Type) := (Fin (N+2) × A) → Fin (N+2)
def chainDFA {N : Nat} {A : Type} (x : ChainTable N A) : DFA (Fin (N+2)) A :=
  ⟨fun s a => x (s,a),0,fun s => decide (s.val≤N)⟩
def baseTable {N : Nat} {A : Type} : ChainTable N A := fun j => nextState j.1
def editedTable {N : Nat} {A : Type} [DecidableEq A] (i : Fin (N+1)) (a : A) :
    ChainTable N A := fun j => (edited i a).step j.1 j.2
def entry {N : Nat} {A : Type} (p : Fin (N+1) × A) : (Fin (N+2) × A) :=
  (⟨p.1.val,by have h := p.1.isLt; omega⟩,p.2)

theorem entry_inj {N : Nat} {A : Type} : Function.Injective (@entry N A) := by
  intro x y h
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun p : Fin (N+2) × A => p.1.val) h
  · exact congrArg (fun p : Fin (N+2) × A => p.2) h

theorem table_agreement {N : Nat} {A : Type} [DecidableEq A]
    (p : Fin (N+1) × A) (j : Fin (N+2) × A) (h : j≠entry p) :
    editedTable p.1 p.2 j = baseTable j := by
  have hh : ¬(j.1.val=p.1.val ∧ j.2=p.2) := by
    intro hx
    exact h (Prod.ext (Fin.ext hx.1) hx.2)
  simp [editedTable,edited,baseTable,hh]

theorem lower_probes {N : Nat} {A : Type} [Fintype A] [DecidableEq A]
    (t : ProbeTree (Fin (N+2) × A) (Fin (N+2)) Bool)
    (correct : ∀ x : ChainTable N A, (chainDFA x).subwordClosed →
      (t.eval x = true ↔ Unbounded (chainDFA x))) :
    (N+1)*Fintype.card A ≤ (t.trace baseTable).toFinset.card := by
  classical
  have baseEq : chainDFA (@baseTable N A) = chain N := rfl
  have editEq (p : Fin (N+1) × A) : chainDFA (editedTable p.1 p.2) = edited p.1 p.2 := rfl
  have miss (p : Fin (N+1) × A) : entry p ∈ t.trace baseTable := by
    by_contra h
    have eq := eval_agreement t baseTable (editedTable p.1 p.2)
      (fun j hj => table_agreement p j (by intro hh; apply h; rwa [← hh]))
    have htrue : t.eval (editedTable p.1 p.2) = true :=
      (correct _ (by rw [editEq]; exact edited_closed p.1 p.2)).2 (by
        rw [editEq]
        exact unbounded_edited p.1 p.2)
    have hfalse := (correct _ (by rw [baseEq]; exact chain_closed N)).1 (eq ▸ htrue)
    exact bounded_chain N (baseEq ▸ hfalse)
  have hcard := Finset.card_le_card_of_injOn (@entry N A) (s:=Finset.univ)
    (t:=(t.trace baseTable).toFinset)
    (by intro p _; exact List.mem_toFinset.mpr (miss p)) entry_inj.injOn
  simpa using hcard

end HussainQ5


namespace HussainQ5

theorem word_loop {Q A : Type} [Fintype Q] (D : DFA Q A) (w : List A)
    (hn : Fintype.card Q ≤ w.length) :
    ∃ x y z, w=x++y++z ∧ 0<y.length ∧ D.run D.start (x++y)=D.run D.start x := by
  classical
  let N := Fintype.card Q
  let f (i : Fin (N+1)) := D.run D.start (w.take i.val)
  have h : ¬ Function.Injective f := by
    intro hi
    have hh : N+1 ≤ N := by simpa [N] using Fintype.card_le_of_injective f hi
    omega
  obtain ⟨i,j,he,hne⟩ := Function.not_injective_iff.mp h
  have ordered (i j : Fin (N+1)) (hlt : i.val<j.val) (hEq : f j=f i) :
      ∃ x y z, w=x++y++z ∧ 0<y.length ∧ D.run D.start (x++y)=D.run D.start x := by
    let x := w.take i.val
    let y := (w.drop i.val).take (j.val-i.val)
    let z := (w.drop i.val).drop (j.val-i.val)
    have hlen : j.val ≤ w.length := by have hh := j.isLt; omega
    have hy : 0<y.length := by
      dsimp [y]
      rw [List.length_take,List.length_drop]
      omega
    have hxy : x++y=w.take j.val := by
      have he' := List.take_add (l:=w) (i:=i.val) (j:=j.val-i.val)
      rw [show i.val+(j.val-i.val)=j.val by omega] at he'
      exact he'.symm
    refine ⟨x,y,z,?_,hy,?_⟩
    · rw [List.append_assoc,List.take_append_drop,List.take_append_drop]
    · rw [hxy]
      exact hEq
  rcases lt_trichotomy i.val j.val with hij | hh | hji
  · exact ordered i j hij he.symm
  · exact False.elim (hne (Fin.ext hh))
  · exact ordered j i hji he

def repeatWord {A : Type} (w : List A) : Nat → List A
  | 0 => []
  | r+1 => w++repeatWord w r

theorem repeat_len {A : Type} (w : List A) (t : Nat) : (repeatWord w t).length=t*w.length := by
  induction t with
  | zero => simp [repeatWord]
  | succ t ih => simp [repeatWord,ih,Nat.succ_mul,Nat.add_comm]

theorem repeat_loop {Q A : Type} (D : DFA Q A) (s : Q) (w : List A)
    (h : D.run s w=s) (t : Nat) : D.run s (repeatWord w t)=s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [repeatWord,run_append,h,ih]

theorem unbounded_test {Q A : Type} [Fintype Q] (D : DFA Q A) (closed : D.subwordClosed) :
    Unbounded D ↔ ∃ w, w.length=Fintype.card Q ∧ D.accepts w := by
  constructor
  · intro h
    obtain ⟨w,hw,hn⟩ := h (Fintype.card Q)
    exact ⟨w.take (Fintype.card Q),by simp [List.length_take,hn],closed (List.take_sublist ..) hw⟩
  · rintro ⟨w,hl,ha⟩ t
    obtain ⟨x,y,z,he,hy,hlp⟩ := word_loop D w hl.ge
    rw [run_append] at hlp
    refine ⟨x++repeatWord y t++z,?_,?_⟩
    · unfold DFA.accepts at *
      rw [he,run_append,run_append,hlp] at ha
      rwa [run_append,run_append,repeat_loop D _ _ hlp]
    · simp only [List.length_append,repeat_len]
      have hm : t*1 ≤ t*y.length := Nat.mul_le_mul_left t hy
      omega

def Universal {Q A : Type} (D : DFA Q A) : Prop := ∀ w, D.accepts w

theorem nonuniversal_test {Q A : Type} [Fintype Q] (D : DFA Q A) :
    ¬ Universal D ↔ ∃ w, w.length<Fintype.card Q ∧ ¬D.accepts w := by
  classical
  constructor
  · intro h
    have hex : ∃ n, ∃ w : List A, w.length=n ∧ ¬D.accepts w := by
      have h' : ∃ w, ¬ D.accepts w := not_forall.mp h
      obtain ⟨w,hw⟩ := h'
      exact ⟨w.length,w,rfl,hw⟩
    let n := Nat.find hex
    obtain ⟨w,hw,hn⟩ := Nat.find_spec hex
    refine ⟨w,?_,hn⟩
    by_contra! hlen
    obtain ⟨x,y,z,he,hy,hlp⟩ := word_loop D w hlen
    rw [run_append] at hlp
    have hne : ¬D.accepts (x++z) := by
      unfold DFA.accepts at *
      rw [run_append]
      rwa [he,run_append,run_append,hlp] at hn
    have hlt : (x++z).length<n := by
      rw [he] at hw
      simp only [List.length_append] at hw ⊢
      omega
    exact Nat.find_min hex hlt ⟨x++z,rfl,hne⟩
  · rintro ⟨w,_,hw⟩ h
    exact hw (h w)

end HussainQ5


namespace HussainQ5

def reachableAt {Q A : Type} [Fintype A] [DecidableEq Q] (D : DFA Q A) : Nat → Finset Q
  | 0 => {D.start}
  | n+1 => (reachableAt D n).biUnion (fun s => Finset.univ.image (D.step s))

theorem mem_reachableAt {Q A : Type} [Fintype A] [DecidableEq Q]
    (D : DFA Q A) (n : Nat) (q : Q) :
    q ∈ reachableAt D n ↔ ∃ w, w.length=n ∧ D.run D.start w=q := by
  induction n generalizing q with
  | zero => simp [reachableAt,run_nil,eq_comm]
  | succ n ih =>
    simp only [reachableAt,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨s,hs,a,ha⟩
      obtain ⟨w,hlen,hw⟩ := (ih s).1 hs
      exact ⟨w++[a],by simp [hlen],by rw [run_append,hw]; exact ha⟩
    · rintro ⟨w,hlen,hw⟩
      induction w using List.reverseRecOn with
      | nil => simp at hlen
      | append_singleton w a _ =>
        have hlen' : w.length=n := by simp at hlen; omega
        let s := D.run D.start w
        exact ⟨s,(ih s).2 ⟨w,hlen',rfl⟩,a,by rw [run_append] at hw; exact hw⟩

inductive Class | c1 | c2 | c3 | c4 | c5 deriving DecidableEq, Repr

noncomputable def classSpec {Q A : Type} (D : DFA Q A) : Class := by
  classical
  exact if Universal D then .c2 else
    if HomInfinite D then .c1 else
    if HetInfinite D then .c3 else
    if Unbounded D then .c4 else .c5

instance acceptsDecidable {Q A : Type} (D : DFA Q A) (w : List A) : Decidable (D.accepts w) :=
  inferInstanceAs (Decidable (D.accept (D.run D.start w)=true))

def classFinite {Q A : Type} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (D : DFA Q A) : Class :=
  let N := Fintype.card Q
  let reachableShort := (Finset.range N).biUnion (reachableAt D)
  if ∀ s∈reachableShort, D.accept s=true then .c2 else
  if ∃ a∈(Finset.univ : Finset A), ∃ b∈(Finset.univ : Finset A),
      a≠b ∧ D.accepts (sand a b N) then .c1 else
  if ∃ a∈(Finset.univ : Finset A), ∃ b∈(Finset.univ : Finset A),
      a≠b ∧ D.accepts (pairWord a b N) then .c3 else
  if ∃ s∈reachableAt D N, D.accept s=true then .c4 else .c5

theorem classFinite_correct {Q A : Type}
    [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (D : DFA Q A) (closed : D.subwordClosed) :
    classFinite D=classSpec D := by
  classical
  let N := Fintype.card Q
  let R := (Finset.range N).biUnion (reachableAt D)
  have h1 : (∀ s∈R, D.accept s=true) ↔ Universal D := by
    constructor
    · intro hh
      by_contra hn
      obtain ⟨w,hw,hr⟩ := (nonuniversal_test D).1 hn
      have hw' : D.run D.start w ∈ reachableAt D w.length :=
        (mem_reachableAt D w.length _).2 ⟨w,rfl,rfl⟩
      exact hr (hh _ (Finset.mem_biUnion.mpr ⟨w.length,Finset.mem_range.mpr hw,hw'⟩))
    · intro hh s hs
      obtain ⟨n,_,hn⟩ := Finset.mem_biUnion.mp hs
      obtain ⟨w,_,hw⟩ := (mem_reachableAt D n s).1 hn
      rw [← hw]
      exact hh w
  have h2 : (∃ a∈(Finset.univ : Finset A), ∃ b∈(Finset.univ : Finset A),
      a≠b ∧ D.accepts (sand a b N)) ↔ HomInfinite D := by
    simpa only [Finset.mem_univ,true_and] using (hom_test D closed).symm
  have h3 : (∃ a∈(Finset.univ : Finset A), ∃ b∈(Finset.univ : Finset A),
      a≠b ∧ D.accepts (pairWord a b N)) ↔ HetInfinite D := by
    simpa only [Finset.mem_univ,true_and] using (het_test D closed).symm
  have h4 : (∃ s∈reachableAt D N, D.accept s=true) ↔ Unbounded D := by
    rw [unbounded_test D closed]
    constructor
    · rintro ⟨s,hs,ha⟩
      obtain ⟨w,hw,he⟩ := (mem_reachableAt D N s).1 hs
      exact ⟨w,hw,by unfold DFA.accepts; rw [he]; exact ha⟩
    · rintro ⟨w,hw,ha⟩
      exact ⟨D.run D.start w,(mem_reachableAt D N _).2 ⟨w,hw,rfl⟩,ha⟩
  unfold classFinite classSpec
  dsimp only
  by_cases h : Universal D
  · rw [ite_eq_left (h1.2 h),ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (h1.1 h')),ite_eq_right h]
    by_cases hh : HomInfinite D
    · rw [ite_eq_left (h2.2 hh),ite_eq_left hh]
    · rw [ite_eq_right (fun h' => hh (h2.1 h')),ite_eq_right hh]
      by_cases hk : HetInfinite D
      · rw [ite_eq_left (h3.2 hk),ite_eq_left hk]
      · rw [ite_eq_right (fun h' => hk (h3.1 h')),ite_eq_right hk]
        by_cases hl : Unbounded D
        · rw [ite_eq_left (h4.2 hl),ite_eq_left hl]
        · rw [ite_eq_right (fun h' => hl (h4.1 h')),ite_eq_right hl]

end HussainQ5

namespace HussainQ5

def put {I V : Type} [DecidableEq I] (old : I → V) (i : I) (v : V) : I → V :=
  fun j => if j=i then v else old j

def readEntries {I V O : Type} [DecidableEq I]
    (finish : (I→V) → O) : List I → (I→V) → ProbeTree I V O
  | [], old => .leaf (finish old)
  | i::is, old => .probe i (fun a => readEntries finish is (put old i a))

theorem readEntries_trace {I V O : Type} [DecidableEq I] (finish : (I→V) → O)
    (is : List I) (old w : I→V) :
    (readEntries finish is old).trace w = is := by
  induction is generalizing old with
  | nil => rfl
  | cons i is ih => simp [readEntries,ProbeTree.trace,ih]

theorem readEntries_eval {I V O : Type} [DecidableEq I] (finish : (I→V) → O)
    (is : List I) (old w : I→V) :
    (readEntries finish is old).eval w = finish (fun i => if i∈is then w i else old i) := by
  induction is generalizing old with
  | nil => simp [readEntries,ProbeTree.eval]
  | cons i is ih =>
    simp only [readEntries,ProbeTree.eval,ih]
    congr 1
    funext j
    by_cases h : j∈is <;> by_cases he : j=i <;> simp [h,he,put,List.mem_cons]

noncomputable def allEntryClassifier {Q A : Type} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (start : Q) (accept : Q→Bool) : ProbeTree (Q×A) Q Class :=
  readEntries (fun db => classFinite ⟨fun s a => db (s,a),start,accept⟩)
    (Finset.univ : Finset (Q×A)).toList (fun _ => start)

theorem allEntryClassifier_correct {Q A : Type}
    [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (D : DFA Q A) (closed : D.subwordClosed) :
    let tr := allEntryClassifier D.start D.accept
    let db := fun j : Q×A => D.step j.1 j.2
    tr.eval db = classSpec D ∧ (tr.trace db).length = Fintype.card Q*Fintype.card A := by
  constructor
  · simpa [allEntryClassifier,readEntries_eval] using classFinite_correct D closed
  · simp [allEntryClassifier,readEntries_trace]

end HussainQ5

namespace HussainQ5

theorem universal_unbounded {Q A : Type} [Nonempty A] {D : DFA Q A} (h : Universal D) :
    Unbounded D := by
  intro n
  obtain ⟨a⟩ := ‹Nonempty A›
  exact ⟨List.replicate n a,h _,by simp⟩

theorem hom_unbounded {Q A : Type} {D : DFA Q A} (h : HomInfinite D) :
    Unbounded D := by
  intro n
  obtain ⟨a,b,_,hab⟩ := h n
  exact ⟨sand a b n,hab,by simp [sand]⟩

theorem het_unbounded {Q A : Type} {D : DFA Q A} (h : HetInfinite D) :
    Unbounded D := by
  intro n
  obtain ⟨a,b,_,hab⟩ := h n
  exact ⟨pairWord a b n,hab,by simp [pairWord]⟩

theorem classSpec_nonfinite {Q A : Type} [Nonempty A] (D : DFA Q A) :
    classSpec D ≠ .c5 ↔ Unbounded D := by
  classical
  unfold classSpec
  by_cases h : Universal D
  · simp [h,universal_unbounded h]
  · by_cases hh : HomInfinite D
    · simp [h,hh,hom_unbounded hh]
    · by_cases hk : HetInfinite D
      · simp [h,hh,hk,het_unbounded hk]
      · by_cases hu : Unbounded D <;> simp [h,hh,hk,hu]

def ProbeTree.map {I V O P : Type} (f : O → P) : ProbeTree I V O → ProbeTree I V P
  | .leaf o => .leaf (f o)
  | .probe i k => .probe i (fun v => (k v).map f)

theorem map_trace {I V O P : Type} (f : O → P) (t : ProbeTree I V O) (w : I→V) :
    (t.map f).trace w = t.trace w := by
  induction t with
  | leaf o => rfl
  | probe i k ih => simpa [ProbeTree.map,ProbeTree.trace] using ih (w i)

theorem map_eval {I V O P : Type} (f : O → P) (t : ProbeTree I V O) (w : I→V) :
    (t.map f).eval w = f (t.eval w) := by
  induction t with
  | leaf o => rfl
  | probe i k ih => exact ih (w i)

/-- No exact classifier can inspect fewer than every accepting chain entry
on the baseline, even though each input is promised subword closed. -/
theorem classifier_transition_lower {N : Nat} {A : Type}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (t : ProbeTree (Fin (N+2) × A) (Fin (N+2)) Class)
    (correct : ∀ x : ChainTable N A, (chainDFA x).subwordClosed →
      t.eval x = classSpec (chainDFA x)) :
    (N+1)*Fintype.card A ≤ (t.trace baseTable).toFinset.card := by
  let f : Class → Bool := fun c => decide (c ≠ .c5)
  have hh := lower_probes (t.map f) (by
    intro x hx
    rw [map_eval,correct x hx]
    exact (decide_eq_true_iff (p:=classSpec (chainDFA x) ≠ .c5)).trans (classSpec_nonfinite _))
  simpa only [map_trace] using hh

end HussainQ5

namespace HussainQ5
open Function

def letterStep {Q A : Type} (D : DFA Q A) (a : A) : Q → Q := fun q => D.step q a

def Safe {Q A : Type} (D : DFA Q A) (a : A) (q : Q) : Prop :=
  ∀ n : Nat, D.accept ((letterStep D a)^[n] q)=true

theorem safe_iff_test {Q A : Type} [Fintype Q] (D : DFA Q A)
    (closed : D.subwordClosed) (a : A) (q : Q)
    (reach : ∃ x : List A, D.run D.start x=q) :
    Safe D a q ↔ D.accept ((letterStep D a)^[Fintype.card Q] q)=true := by
  constructor
  · intro h
    exact h (Fintype.card Q)
  · intro h n
    obtain ⟨x,hx⟩ := reach
    obtain ⟨p,hp,hfix⟩ := orbit_period_after_card (letterStep D a) q
    let N := Fintype.card Q
    let E := N+n*p
    have hn : n ≤ E := by
      have hmul : n*1≤n*p := Nat.mul_le_mul_left n hp
      dsimp [E]
      omega
    have hc : D.accepts (x++List.replicate E a) := by
      unfold DFA.accepts
      rw [run_append,hx,run_power]
      change D.accept ((letterStep D a)^[E] q)=true
      rw [hfix]
      exact h
    have hd := closed ((List.Sublist.refl x).append (replicate_sublist a hn)) hc
    unfold DFA.accepts at hd
    rw [run_append,hx,run_power] at hd
    exact hd

theorem pure_unbounded_of_safe {Q A : Type} (D : DFA Q A) (a : A)
    (h : Safe D a D.start) : Unbounded D := by
  intro n
  refine ⟨List.replicate n a, ?_, by simp⟩
  unfold DFA.accepts
  rw [run_power]
  exact h n

end HussainQ5


namespace HussainQ5
open Function

theorem count_sum {A : Type} [Fintype A] [DecidableEq A] (w : List A) :
    (∑ a : A, w.count a)=w.length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp [List.count_cons,Finset.sum_add_distrib,beq_iff_eq,ih]

theorem safe_start_iff_unbounded {Q A : Type} [Fintype Q] [Fintype A] [DecidableEq A]
    (D : DFA Q A) (closed : D.subwordClosed) :
    Unbounded D ↔ ∃ a : A, Safe D a D.start := by
  constructor
  · intro h
    let N := Fintype.card Q
    let k := Fintype.card A
    obtain ⟨w,hw,hlen⟩ := h (k*N+1)
    have hex : ∃ a : A, N ≤ w.count a := by
      by_contra! hh
      have hs : (∑ a : A, w.count a) ≤ k*N := by
        calc
          _ ≤ ∑ _a : A, N := Finset.sum_le_sum (fun a _ => (hh a).le)
          _ = _ := by simp [k]
      rw [count_sum] at hs
      omega
    obtain ⟨a,ha⟩ := hex
    have hpow := closed ((List.replicate_sublist_iff).2 ha) hw
    unfold DFA.accepts at hpow
    rw [run_power] at hpow
    exact ⟨a,(safe_iff_test D closed a D.start ⟨[],rfl⟩).2 hpow⟩
  · rintro ⟨a,ha⟩
    exact pure_unbounded_of_safe D a ha

def endpoint {Q A : Type} [Fintype Q] (D : DFA Q A) (a : A) : Q :=
  (letterStep D a)^[Fintype.card Q] D.start

theorem endpoint_reached {Q A : Type} [Fintype Q] (D : DFA Q A) (a : A) :
    D.run D.start (List.replicate (Fintype.card Q) a)=endpoint D a := by
  exact run_power .. 

def bucket {I Q : Type} [Fintype I] [DecidableEq Q] (f : I→Q) (q : Q) :=
  (Finset.univ : Finset I).filter (fun i => f i=q)

theorem bucket_except {I Q : Type} [Fintype I] [DecidableEq I] [DecidableEq Q]
    (f : I→Q) (q : Q) (a : I) :
    ((if f a=q then 1 else 0) < (bucket f q).card) ↔
      ∃ b, b≠a ∧ f b=q := by
  have he : ((bucket f q).erase a).Nonempty ↔ ∃ b, b≠a ∧ f b=q := by
    simp [Finset.Nonempty,bucket]
  rw [← he,← Finset.card_pos]
  by_cases h : f a=q
  · have ha : a ∈ bucket f q := by simp [bucket,h]
    rw [ite_eq_left h,Finset.card_erase_of_mem ha]
    omega
  · have ha : a ∉ bucket f q := by simp [bucket,h]
    rw [ite_eq_right h,Finset.erase_eq_of_notMem ha]

theorem hom_grouped {Q A : Type} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (D : DFA Q A) (closed : D.subwordClosed) :
    HomInfinite D ↔ ∃ a : A, ∃ q : Q, Safe D a q ∧
      (if D.step (endpoint D a) a=q then 1 else 0) <
        (bucket (D.step (endpoint D a)) q).card := by
  rw [hom_test D closed]
  constructor
  · rintro ⟨a,b,hab,h⟩
    let q := D.step (endpoint D a) b
    have hr : D.run D.start (List.replicate (Fintype.card Q) a++[b])=q := by
      rw [run_append,endpoint_reached]
      rfl
    refine ⟨a,q,?_,(bucket_except _ _ _).2 ⟨b,hab.symm,rfl⟩⟩
    apply (safe_iff_test D closed a q ⟨_,hr⟩).2
    unfold DFA.accepts sand at h
    rwa [run_append,hr,run_power] at h
  · rintro ⟨a,q,hs,h⟩
    obtain ⟨b,hba,hq⟩ := (bucket_except _ _ _).1 h
    have hr : D.run D.start (List.replicate (Fintype.card Q) a++[b])=q := by
      rw [run_append,endpoint_reached]
      exact hq
    refine ⟨a,b,hba.symm,?_⟩
    unfold DFA.accepts sand
    rw [run_append,hr,run_power]
    exact hs _

theorem het_grouped {Q A : Type} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (D : DFA Q A) (closed : D.subwordClosed) :
    HetInfinite D ↔ ∃ b : A, ∃ q : Q, Safe D b q ∧
      (if endpoint D b=q then 1 else 0) < (bucket (endpoint D) q).card := by
  rw [het_test D closed]
  constructor
  · rintro ⟨a,b,hab,h⟩
    let q := endpoint D a
    refine ⟨b,q,?_,(bucket_except _ _ _).2 ⟨a,hab,rfl⟩⟩
    apply (safe_iff_test D closed b q ⟨_,endpoint_reached D a⟩).2
    unfold DFA.accepts pairWord at h
    rwa [run_append,endpoint_reached,run_power] at h
  · rintro ⟨b,q,hs,h⟩
    obtain ⟨a,hab,hq⟩ := (bucket_except _ _ _).1 h
    refine ⟨a,b,hab,?_⟩
    unfold DFA.accepts pairWord
    rw [run_append,endpoint_reached,hq,run_power]
    exact hs _

end HussainQ5

namespace HussainQ5

inductive Reach {Q : Type} (adj : Q→List Q) (roots : List Q) : Q → Prop
  | root (q) : q∈roots → Reach adj roots q
  | step {q v} : Reach adj roots q → v∈adj q → Reach adj roots v

structure WalkResult (Q : Type) where
  found : Finset Q
  work : Nat

/-- Standard stack-based graph search. Only fresh vertices expand their adjacency.
The work counter charges a pop once and a neighbor-list entry once when expanded.
The implementation model uses a Boolean mark array for finite indexed vertices. -/
def walk {Q : Type} [Fintype Q] [DecidableEq Q] (adj : Q→List Q)
    (pending : List Q) (seen : Finset Q) : WalkResult Q :=
  match pending with
  | [] => ⟨seen,0⟩
  | q::tail =>
    if h : q∈seen then
      let r := walk adj tail seen
      ⟨r.found,r.work+1⟩
    else
      let r := walk adj (adj q++tail) (insert q seen)
      ⟨r.found,r.work+1+(adj q).length⟩
termination_by (Fintype.card Q-seen.card,pending.length)
decreasing_by
  · simp_wf
    exact Prod.Lex.right _ (by simp)
  · apply Prod.Lex.left
    have h₁ : (insert q seen).card = seen.card+1 := Finset.card_insert_of_notMem h
    have h₂ : (insert q seen).card ≤ Fintype.card Q := Finset.card_le_univ _
    omega

def pendingClosed {Q : Type} [DecidableEq Q] (adj : Q→List Q)
    (pending : List Q) (seen : Finset Q) : Prop :=
  ∀ q∈seen, ∀ v∈adj q, v∈seen ∨ v∈pending

theorem walk_sound_complete {Q : Type} [Fintype Q] [DecidableEq Q]
    (adj : Q→List Q) (roots pending : List Q) (seen : Finset Q)
    (inv : pendingClosed adj pending seen)
    (hseen : ∀ q∈seen, Reach adj roots q)
    (hpend : ∀ q∈pending, Reach adj roots q) :
    let R := (walk adj pending seen).found
    seen ⊆ R ∧ (∀ q∈pending, q∈R) ∧
      (∀ q∈R, Reach adj roots q) ∧
      (∀ q∈R, ∀ v∈adj q, v∈R) := by
  cases hp : pending with
  | nil =>
    rw [walk]
    exact ⟨fun _ h => h,by simp,hseen,fun q h v hv => (inv q h v hv).resolve_right (by simp [hp])⟩
  | cons q tail =>
    have hin : q∈pending := by simp [hp]
    have subTail (v : Q) (hv : v∈tail) : v∈pending := by simp [hp,hv]
    rw [walk]
    by_cases h : q∈seen
    · simp only [dite_eq_left h]
      have inv' : pendingClosed adj tail seen := by
        intro x hx y hy
        rcases inv x hx y hy with hs | ht
        · exact Or.inl hs
        rw [hp] at ht
        rcases List.mem_cons.mp ht with he | htail
        · exact Or.inl (he ▸ h)
        · exact Or.inr htail
      obtain ⟨hs,ht,hsound,hclose⟩ :=
        walk_sound_complete adj roots tail seen inv' hseen (fun v hv => hpend v (subTail v hv))
      refine ⟨hs,?_,hsound,hclose⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hh
      · exact hs h
      · exact ht x hh
    · simp only [dite_eq_right h]
      have inv' : pendingClosed adj (adj q++tail) (insert q seen) := by
        intro x hx y hy
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact Or.inr (List.mem_append.mpr (Or.inl hy))
        · rcases inv x hx' y hy with hs | ht
          · exact Or.inl (Finset.mem_insert_of_mem hs)
          · rw [hp] at ht
            rcases List.mem_cons.mp ht with rfl | htail
            · exact Or.inl (Finset.mem_insert_self _ _)
            · exact Or.inr (List.mem_append.mpr (Or.inr htail))
      have sins : ∀ x∈insert q seen, Reach adj roots x := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hh
        · exact hpend _ hin
        · exact hseen x hh
      have pins : ∀ x∈adj q++tail, Reach adj roots x := by
        intro x hx
        rcases List.mem_append.mp hx with hn | ht
        · exact .step (hpend q hin) hn
        · exact hpend x (subTail x ht)
      obtain ⟨hs,ht,hsound,hclose⟩ :=
        walk_sound_complete adj roots (adj q++tail) (insert q seen) inv' sins pins
      refine ⟨fun x hx => hs (Finset.mem_insert_of_mem hx),?_,hsound,hclose⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hh
      · exact hs (Finset.mem_insert_self _ _)
      · exact ht x (List.mem_append.mpr (Or.inr hh))
termination_by (Fintype.card Q-seen.card,pending.length)
decreasing_by
  · apply Prod.Lex.right
    simp [hp]
  · apply Prod.Lex.left
    have h₁ : (insert q seen).card = seen.card+1 := Finset.card_insert_of_notMem h
    have h₂ : (insert q seen).card ≤ Fintype.card Q := Finset.card_le_univ _
    omega

theorem walk_reachable {Q : Type} [Fintype Q] [DecidableEq Q]
    (adj : Q→List Q) (roots : List Q) (q : Q) :
    q∈(walk adj roots ∅).found ↔ Reach adj roots q := by
  obtain ⟨_,hroot,hsound,hclosed⟩ :=
    walk_sound_complete adj roots roots ∅ (by simp [pendingClosed]) (by simp)
      (fun q h => Reach.root q h)
  refine ⟨hsound q,?_⟩
  intro h
  induction h with
  | root q hq => exact hroot q hq
  | step _ hv ih => exact hclosed _ ih _ hv

end HussainQ5

namespace HussainQ5

def edgeWeight {Q : Type} [Fintype Q] [DecidableEq Q]
    (adj : Q→List Q) (seen : Finset Q) : Nat :=
  ∑ q ∈ (Finset.univ : Finset Q) \ seen, (adj q).length

theorem walk_work {Q : Type} [Fintype Q] [DecidableEq Q] (adj : Q→List Q)
    (pending : List Q) (seen : Finset Q) :
    (walk adj pending seen).work ≤ pending.length + 2*edgeWeight adj seen := by
  cases hp : pending with
  | nil => simp [walk]
  | cons q tail =>
    rw [walk]
    by_cases h : q∈seen
    · simp only [dite_eq_left h,List.length_cons]
      have hr := walk_work adj tail seen
      omega
    · simp only [dite_eq_right h,List.length_cons]
      have hr := walk_work adj (adj q++tail) (insert q seen)
      have he : (Finset.univ : Finset Q) \ insert q seen =
          ((Finset.univ : Finset Q) \ seen).erase q := by
        ext x
        simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_erase]
        tauto
      have hq : q ∈ (Finset.univ : Finset Q) \ seen :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h⟩
      have hs : edgeWeight adj (insert q seen)+(adj q).length=edgeWeight adj seen := by
        unfold edgeWeight
        rw [he]
        exact Finset.sum_erase_add _ _ hq
      simp only [List.length_append] at hr
      omega
termination_by (Fintype.card Q-seen.card,pending.length)
decreasing_by
  · apply Prod.Lex.right
    simp
  · apply Prod.Lex.left
    have h₁ : (insert q seen).card = seen.card+1 := Finset.card_insert_of_notMem h
    have h₂ : (insert q seen).card ≤ Fintype.card Q := Finset.card_le_univ _
    omega

theorem walk_linear {Q : Type} [Fintype Q] [DecidableEq Q] (adj : Q→List Q)
    (roots : List Q) :
    (walk adj roots ∅).work ≤ roots.length+2*(∑ q : Q,(adj q).length) := by
  simpa [edgeWeight] using walk_work adj roots ∅

end HussainQ5

namespace HussainQ5
open Function

/-- Build reverse lists by one traversal of the finite state index.
The functional table is implemented by indexed RAM cells in the cost model. -/
def reverseIndex {Q : Type} [DecidableEq Q] (f : Q→Q) (xs : List Q) : Q→List Q :=
  xs.foldr (fun q tab => put tab (f q) (q::tab (f q))) (fun _ => [])

theorem reverseIndex_eq {Q : Type} [DecidableEq Q] (f : Q→Q) (xs : List Q) (q : Q) :
    reverseIndex f xs q = xs.filter (fun v => decide (f v=q)) := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
    change put (reverseIndex f xs) (f v) (v::reverseIndex f xs (f v)) q = _
    by_cases h : f v=q
    · subst q
      simp [put,ih]
    · have hs : q≠f v := (Ne.symm h)
      simp [put,h,hs,ih]

theorem reverseIndex_mem {Q : Type} [DecidableEq Q] (f : Q→Q)
    (xs : List Q) (q v : Q) :
    v ∈ reverseIndex f xs q ↔ v∈xs ∧ f v=q := by
  rw [reverseIndex_eq]
  simp

theorem reverseIndex_edges {Q : Type} [Fintype Q] [DecidableEq Q]
    (f : Q→Q) (xs : List Q) :
    (∑ q : Q, (reverseIndex f xs q).length)=xs.length := by
  induction xs with
  | nil => simp [reverseIndex]
  | cons v xs ih =>
    have hl (q : Q) : (reverseIndex f (v::xs) q).length =
        (reverseIndex f xs q).length+if q=f v then 1 else 0 := by
      by_cases h : q = f v
      · subst q
        simp [reverseIndex_eq]
      · simp [reverseIndex_eq,h,Ne.symm h]
    simp [hl,Finset.sum_add_distrib,ih]

def forwardAdj {Q A : Type} (D : DFA Q A) (letters : List A) (q : Q) : List Q :=
  letters.map (D.step q)

theorem forward_word {Q A : Type} (D : DFA Q A) (letters : List A)
    (all : ∀ a, a ∈ letters) (q : Q) :
    Reach (forwardAdj D letters) [D.start] q ↔ ∃ w, D.run D.start w=q := by
  constructor
  · intro hh
    induction hh with
    | root q h =>
      have he : q = D.start := by simpa using h
      exact ⟨[],he.symm⟩
    | @step r q hr hq ih =>
      obtain ⟨w,hw⟩ := ih
      obtain ⟨a,ha,he⟩ := List.mem_map.mp hq
      exact ⟨w++[a],by rw [run_append,hw]; exact he⟩
  · rintro ⟨w,rfl⟩
    induction w using List.reverseRecOn with
    | nil => exact .root _ (by simp [run_nil])
    | append_singleton w a ih =>
      rw [run_append]
      exact .step ih (List.mem_map.mpr ⟨a,all a,rfl⟩)

def rejectRoots {Q A : Type} (D : DFA Q A) (states : List Q) :=
  states.filter (fun q => ! D.accept q)

theorem reverse_reject {Q A : Type} [DecidableEq Q] (D : DFA Q A) (a : A)
    (states : List Q) (all : ∀ q, q∈states) (s : Q) :
    Reach (reverseIndex (letterStep D a) states) (rejectRoots D states) s ↔
      ∃ n : Nat, D.accept ((letterStep D a)^[n] s)=false := by
  let f := letterStep D a
  constructor
  · intro hr
    induction hr with
    | root q h =>
      have he : D.accept q=false := by simpa [rejectRoots,all] using h
      exact ⟨0,he⟩
    | @step q v hq he ih =>
      obtain ⟨n,hn⟩ := ih
      have hf : f v=q := (reverseIndex_mem _ _ _ _).1 he |>.2
      refine ⟨n+1,?_⟩
      change D.accept (f^[n+1] v)=false
      rw [Function.iterate_succ_apply,hf]
      exact hn
  · rintro ⟨n,hn⟩
    induction n generalizing s with
    | zero =>
      exact Reach.root _ (by simpa [rejectRoots,all] using hn)
    | succ n ih =>
      have hk : D.accept (f^[n] (f s))=false := by simpa only [Function.iterate_succ_apply] using hn
      exact .step (ih (f s) hk) ((reverseIndex_mem _ _ _ _).2 ⟨all s,rfl⟩)

def computeSafe {Q A : Type} [Fintype Q] [DecidableEq Q]
    (D : DFA Q A) (a : A) (states : List Q) : WalkResult Q :=
  walk (reverseIndex (letterStep D a) states) (rejectRoots D states) ∅

theorem computeSafe_correct {Q A : Type} [Fintype Q] [DecidableEq Q] (D : DFA Q A)
    (a : A) (states : List Q) (all : ∀ q, q∈states) (q : Q) :
    q ∉ (computeSafe D a states).found ↔ Safe D a q := by
  rw [computeSafe,walk_reachable,reverse_reject D a states all q]
  simp [Safe]

theorem computeSafe_work {Q A : Type} [Fintype Q] [DecidableEq Q] (D : DFA Q A)
    (a : A) (states : List Q) :
    (computeSafe D a states).work ≤ 3*states.length := by
  have hw := walk_linear (reverseIndex (letterStep D a) states) (rejectRoots D states)
  rw [reverseIndex_edges] at hw
  have hr : (rejectRoots D states).length ≤ states.length := List.length_filter_le ..
  exact hw.trans (by omega)

theorem forward_work {Q A : Type} [Fintype Q] [DecidableEq Q] (D : DFA Q A)
    (letters : List A) :
    (walk (forwardAdj D letters) [D.start] ∅).work ≤
      1+2*(Fintype.card Q*letters.length) := by
  simpa [forwardAdj,Nat.mul_comm] using walk_linear (forwardAdj D letters) [D.start]

end HussainQ5

namespace HussainQ5

/-- Populate an explicit indexed table. `put` is the semantic view of an
array update; the algorithm's cost model charges one update per key. -/
def tabulate {I V : Type} [DecidableEq I] (keys : List I) (f : I→V) (init : V) : I→V :=
  keys.foldr (fun i a => put a i (f i)) (fun _ => init)

theorem tabulate_get {I V : Type} [DecidableEq I] (keys : List I) (f : I→V)
    (init : V) (i : I) (hi : i∈keys) : tabulate keys f init i=f i := by
  induction keys with
  | nil => simp at hi
  | cons x xs ih =>
    change put (tabulate xs f init) x (f x) i = _
    by_cases hh : i=x
    · subst i; simp [put]
    · have hp := (List.mem_cons.mp hi).resolve_left hh
      simp [put,hh,ih hp]

def histogram {I Q : Type} [DecidableEq Q] (keys : List I) (f : I→Q) : Q→Nat :=
  keys.foldr (fun i tab => put tab (f i) (tab (f i)+1)) (fun _ => 0)

theorem histogram_eq {I Q : Type} [DecidableEq Q] (keys : List I) (f : I→Q) (q : Q) :
    histogram keys f q = (keys.filter (fun i => decide (f i=q))).length := by
  induction keys with
  | nil => rfl
  | cons x xs ih =>
    change put (histogram xs f) (f x) (histogram xs f (f x)+1) q = _
    by_cases he : q=f x
    · subst q; simp [put,ih]
    · simp [put,he,Ne.symm he,ih]

theorem histogram_card {I Q : Type} [Fintype I] [DecidableEq I] [DecidableEq Q]
    (keys : List I) (complete : ∀ i, i∈keys) (unique : keys.Nodup) (f : I→Q) (q : Q) :
    histogram keys f q = (bucket f q).card := by
  rw [histogram_eq]
  let xs := keys.filter (fun i => decide (f i=q))
  have hx : xs.toFinset = bucket f q := by ext i; simp [xs,bucket,complete]
  have hn : xs.Nodup := unique.filter _
  rw [← hx,List.toFinset_card_of_nodup hn]

def activeRows {Q A : Type} [DecidableEq Q] (states : List Q) (letters : List A)
    (p : A→Q) : List Q := states.filter (fun q => decide (0 < histogram letters p q))

theorem activeRows_mem {Q A : Type} [DecidableEq Q] (states : List Q) (letters : List A)
    (p : A→Q) (q : Q) :
    q∈activeRows states letters p ↔ q∈states ∧ ∃ a∈letters, p a=q := by
  simp [activeRows,histogram_eq,List.length_pos_iff_exists_mem]

theorem activeRows_cost_bound {Q A : Type} [DecidableEq Q] (states : List Q) (letters : List A)
    (p : A→Q) (nodup : states.Nodup) :
    (activeRows states letters p).length * (states.length+letters.length) ≤
      2*(states.length*letters.length) := by
  classical
  let rows := activeRows states letters p
  have hS : rows.length ≤ states.length := List.length_filter_le ..
  have hR : rows.Nodup := nodup.filter _
  have hL : rows.length ≤ letters.length := by
    have hs : rows.toFinset ⊆ letters.toFinset.image p := by
      intro q hq
      obtain ⟨_,a,ha,hp⟩ := (activeRows_mem states letters p q).1 (List.mem_toFinset.mp hq)
      exact Finset.mem_image.mpr ⟨a,List.mem_toFinset.mpr ha,hp⟩
    have hc := (Finset.card_le_card hs).trans (Finset.card_image_le.trans (List.toFinset_card_le letters))
    simpa only [List.toFinset_card_of_nodup hR] using hc
  change rows.length * _ ≤ _
  rw [Nat.mul_add]
  have hx := Nat.mul_le_mul_right states.length hL
  have hy := Nat.mul_le_mul_right letters.length hS
  rw [Nat.mul_comm letters.length states.length] at hx
  omega

end HussainQ5

namespace HussainQ5

structure LinearOutput where
  label : Class
  estimatedSteps : Nat

/-- Fixed-table RAM model. The operations represented by put, tabulate
and histogram are array writes. Membership in a visited set is a mark-array
read, and adding a graph edge is a bounded number of linked-list cell writes.
The estimatedSteps field charges the complete phases, without relying on
short circuiting. The pure functions in this file specify their contents,
not the wall-clock runtime of their Lean implementations. -/
def classLinear {Q A : Type} [Fintype Q] [DecidableEq Q] [DecidableEq A]
    (D : DFA Q A) (states : List Q) (letters : List A) : LinearOutput :=
  let n := states.length
  let k := letters.length
  let forward := walk (forwardAdj D letters) [D.start] ∅
  let p := tabulate letters (endpoint D) D.start
  let safe := tabulate letters (fun a => computeSafe D a states) ⟨∅,0⟩
  let counts := histogram letters p
  let rows := activeRows states letters p
  let targets := tabulate rows (fun q => histogram letters (D.step q)) (fun _ => 0)
  let u := states.all (fun q => decide (q ∉ forward.found ∨ D.accept q=true))
  let h := letters.any (fun a => states.any (fun q =>
    decide (q ∉ (safe a).found ∧
      (if D.step (p a) a=q then 1 else 0) < targets (p a) q)))
  let e := letters.any (fun a => states.any (fun q =>
    decide (q ∉ (safe a).found ∧ (if p a=q then 1 else 0) < counts q)))
  let v := letters.any (fun a => decide (D.start ∉ (safe a).found))
  let out := if u then Class.c2 else if h then .c1 else
    if e then .c3 else if v then .c4 else .c5
  -- Phase budgets: fixed setup/state scans, input and per-letter scans,
  -- dense active count rows, forward traversal, and each reverse traversal.
  let nVisits := (letters.map (fun a => (safe a).work)).sum
  ⟨out,20+10*(n+k)+20*(n*k)+4*rows.length*(n+k)+4*forward.work+4*nVisits⟩

theorem classLinear_correct {Q A : Type}
    [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (D : DFA Q A) (closed : D.subwordClosed) (states : List Q) (letters : List A)
    (sall : ∀ q, q∈states) (lall : ∀ a, a∈letters) (lnd : letters.Nodup) :
    (classLinear D states letters).label = classSpec D := by
  classical
  let forward := walk (forwardAdj D letters) [D.start] ∅
  let p := tabulate letters (endpoint D) D.start
  let safe := tabulate letters (fun a => computeSafe D a states) ⟨∅,0⟩
  let counts := histogram letters p
  let rows := activeRows states letters p
  let targets := tabulate rows (fun q => histogram letters (D.step q)) (fun _ => 0)
  have hp (a : A) : p a=endpoint D a := tabulate_get _ _ _ _ (lall a)
  have hsafe (a : A) (q : Q) : q∉(safe a).found ↔ Safe D a q := by
    have ht : safe a=computeSafe D a states := tabulate_get _ _ _ _ (lall a)
    rw [ht]
    exact computeSafe_correct D a states sall q
  have hc (q : Q) : counts q=(bucket (endpoint D) q).card := by
    have h : p=endpoint D := funext hp
    dsimp [counts]
    rw [h]
    exact histogram_card letters lall lnd _ _
  have htarget (a : A) (q : Q) : targets (p a) q=(bucket (D.step (endpoint D a)) q).card := by
    have hr : p a ∈ rows := (activeRows_mem ..).2 ⟨sall _,a,lall a,rfl⟩
    have ht : targets (p a) = histogram letters (D.step (p a)) := tabulate_get _ _ _ _ hr
    rw [ht,hp]
    exact histogram_card _ lall lnd _ _
  have htarget' (a : A) (q : Q) : targets (endpoint D a) q =
      (bucket (D.step (endpoint D a)) q).card := by simpa only [hp] using htarget a q
  have hU :
      (states.all (fun q => decide (q ∉ forward.found ∨ D.accept q=true))=true) ↔ Universal D := by
    simp only [List.all_eq_true,decide_eq_true_eq]
    constructor
    · intro hh w
      have hmem : D.run D.start w ∈ forward.found :=
        (walk_reachable ..).2 ((forward_word D letters lall _).2 ⟨w,rfl⟩)
      exact (hh _ (sall _)).resolve_left (not_not_intro hmem)
    · intro hh q _
      by_cases hq : q∈forward.found
      · obtain ⟨w,hw⟩ := (forward_word D letters lall _).1 ((walk_reachable ..).1 hq)
        exact Or.inr (hw ▸ hh w)
      · exact Or.inl hq
  have hH :
      (letters.any (fun a => states.any (fun q =>
        decide (q∉(safe a).found ∧
          (if D.step (p a) a=q then 1 else 0) < targets (p a) q)))=true) ↔ HomInfinite D := by
    simp only [List.any_eq_true,decide_eq_true_eq,lall,sall,true_and,hsafe,hp,htarget']
    exact (hom_grouped D closed).symm
  have hE :
      (letters.any (fun a => states.any (fun q =>
        decide (q∉(safe a).found ∧ (if p a=q then 1 else 0) < counts q)))=true)
        ↔ HetInfinite D := by
    simp only [List.any_eq_true,decide_eq_true_eq,lall,sall,true_and,hsafe,hp,hc]
    exact (het_grouped D closed).symm
  have hV :
      (letters.any (fun a => decide (D.start∉(safe a).found))=true) ↔ Unbounded D := by
    simp only [List.any_eq_true,decide_eq_true_eq,lall,true_and,hsafe]
    exact (safe_start_iff_unbounded D closed).symm
  unfold classLinear classSpec
  dsimp only
  by_cases h : Universal D
  · rw [ite_eq_left (hU.2 h),ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hU.1 h')),ite_eq_right h]
    by_cases hh : HomInfinite D
    · rw [ite_eq_left (hH.2 hh),ite_eq_left hh]
    · rw [ite_eq_right (fun h' => hh (hH.1 h')),ite_eq_right hh]
      by_cases hk : HetInfinite D
      · rw [ite_eq_left (hE.2 hk),ite_eq_left hk]
      · rw [ite_eq_right (fun h' => hk (hE.1 h')),ite_eq_right hk]
        by_cases hl : Unbounded D
        · rw [ite_eq_left (hV.2 hl),ite_eq_left hl]
        · rw [ite_eq_right (fun h' => hl (hV.1 h')),ite_eq_right hl]

end HussainQ5

namespace HussainQ5

theorem sum_map_bound {A : Type} (f : A→Nat) (xs : List A) (m : Nat)
    (h : ∀ a∈xs, f a ≤ m) : (xs.map f).sum ≤ xs.length*m := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha : f a ≤ m := h a (by simp)
    have hr := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    omega

theorem complete_length {A : Type} [Fintype A] [DecidableEq A] (xs : List A)
    (all : ∀ a, a∈xs) (nd : xs.Nodup) : xs.length=Fintype.card A := by
  have ht : xs.toFinset = Finset.univ := by ext a; simp [all]
  have hh := congrArg Finset.card ht
  simpa only [List.toFinset_card_of_nodup nd,Finset.card_univ] using hh

/-- The full grouped classifier has a linear indexed-RAM work bound. -/
theorem classLinear_work {Q A : Type}
    [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A] [Nonempty A]
    (D : DFA Q A) (states : List Q) (letters : List A)
    (sall : ∀ q, q∈states) (lall : ∀ a, a∈letters) (snd : states.Nodup) (lnd : letters.Nodup) :
    (classLinear D states letters).estimatedSteps ≤
      100*(Fintype.card Q*Fintype.card A) := by
  let n := states.length
  let k := letters.length
  let p := tabulate letters (endpoint D) D.start
  let safe := tabulate letters (fun a => computeSafe D a states) ⟨∅,0⟩
  let forward := walk (forwardAdj D letters) [D.start] ∅
  let rows := activeRows states letters p
  have hn : n=Fintype.card Q := complete_length states sall snd
  have hk : k=Fintype.card A := complete_length letters lall lnd
  have hp : 0<n := List.length_pos_of_mem (sall D.start)
  obtain ⟨a⟩ := ‹Nonempty A›
  have hkp : 0<k := List.length_pos_of_mem (lall a)
  have ha : n ≤ n*k := by simpa using Nat.mul_le_mul_left n (show 1≤k by omega)
  have hb : k ≤ n*k := by simpa using Nat.mul_le_mul_right k (show 1≤n by omega)
  have hc : 1 ≤ n*k := Nat.mul_pos hp hkp
  have hF : forward.work ≤ 1+2*(n*k) := by simpa only [hn] using forward_work D letters
  have hS : (letters.map (fun a => (safe a).work)).sum ≤ 3*(n*k) := by
    have hs := sum_map_bound (fun a => (safe a).work) letters (3*n) (by
      intro a ha
      have h : safe a = computeSafe D a states := tabulate_get _ _ _ _ ha
      rw [h]
      exact computeSafe_work D a states)
    convert hs using 1
    change 3*(n*k) = k*(3*n)
    ring
  have ht := activeRows_cost_bound states letters p snd
  change rows.length*(n+k) ≤ 2*(n*k) at ht
  change 20+10*(n+k)+20*(n*k)+4*rows.length*(n+k)+4*forward.work+
      4*(letters.map (fun a => (safe a).work)).sum ≤ _
  rw [← hn,← hk, Nat.mul_assoc 4 rows.length (n+k)]
  omega

end HussainQ5

namespace HussainQ5

/-- The promise classifier for the standard explicit transition table,
with one bounded-width state label per transition cell. -/
def indexedClassifier {N k : Nat} (D : DFA (Fin N) (Fin k)) : LinearOutput :=
  classLinear D (List.finRange N) (List.finRange k)

theorem question5_linear_upper {N k : Nat} (D : DFA (Fin N) (Fin k))
    (closed : D.subwordClosed) (hk : 2 ≤ k) :
    (indexedClassifier D).label = classSpec D ∧
    (indexedClassifier D).estimatedSteps ≤ 100*(N*k) := by
  have hki : 0<k := by omega
  let _ : Nonempty (Fin k) := ⟨⟨0,hki⟩⟩
  constructor
  · exact classLinear_correct D closed _ _ (by simp) (by simp) (List.nodup_finRange _)
  · simpa [indexedClassifier] using classLinear_work D (List.finRange N) (List.finRange k)
      (by simp) (by simp) (List.nodup_finRange _) (List.nodup_finRange _)

/-- Conversely, any deterministic exact classifier on N+2 states needs
(N+1)k distinct transition reads on some promised input. -/
theorem question5_matching_lower {N k : Nat} (hk : 2≤k)
    (t : ProbeTree (Fin (N+2)×Fin k) (Fin (N+2)) Class)
    (correct : ∀ x : ChainTable N (Fin k), (chainDFA x).subwordClosed →
      t.eval x = classSpec (chainDFA x)) :
    (N+1)*k ≤ (t.trace baseTable).length := by
  let _ : Nonempty (Fin k) := ⟨⟨0,by omega⟩⟩
  have h := classifier_transition_lower t correct
  simpa using h.trans (List.toFinset_card_le _)

end HussainQ5

#print axioms HussainQ5.question5_linear_upper
#print axioms HussainQ5.question5_matching_lower
