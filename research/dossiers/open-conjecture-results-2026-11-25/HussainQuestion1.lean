import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Order.Monotone.Basic
import Lean
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic
/-!
A Lean verification of Question 1 in Shahid Hussain,
"Decision trees for subword-closed languages over arbitrary finite alphabets",
arXiv:2611.27454v1, Section 6: https://arxiv.org/html/2611.27454v1#S6.

For an alphabet with k letters and finite homogeneity m, the coefficient
of log base two in deterministic recognition depth can be k*(k+2),
independent of m. We prove this for all subword-closed languages with
finite homogeneity, not just C3. The additive bound depends only on k,m.

Sketch: recover a long constant run using overlapping binary search
on a grid. At most k+1 grid positions can falsely match the run's
letter after it ends. Disjoint letter cores bound both the number of
long runs and the total cost of scanning the short runs. The final
statement explicitly checks complete paths, promise coverage and
correctness, depth on all paths, and legal leaf outputs.
-/
open Function
namespace SortedQueries

inductive Tree (I A O : Type) where
  | leaf (output : O)
  | query (i : I) (next : A → Tree I A O)

def Tree.eval {I A O} (t : Tree I A O) (w : I → A) : O :=
  match t with
  | .leaf y => y
  | .query i g => (g (w i)).eval w

inductive Budget {I A O} : Tree I A O → Nat → Prop
  | leaf (y : O) (d : Nat) : Budget (.leaf y) d
  | query {i : I} {g : A → Tree I A O} {d : Nat} :
      (∀ a, Budget (g a) d) → Budget (.query i g) (d+1)

/- A partial tree models complete paths beneath the unique unlabeled root edge. -/
inductive Partial (I A O : Type) where
  | absent
  | leaf (o : O)
  | query (i : I) (next : A → Partial I A O)

inductive PPath {I A O : Type} : Partial I A O → List (I × A) → O → Prop
  | leaf (o) : PPath (.leaf o) [] o
  | query {i : I} {g : A → Partial I A O} {a : A} {qs o} :
      PPath (g a) qs o → PPath (.query i g) ((i,a)::qs) o

def Consistent {I A : Type} (w : I → A) (p : List (I × A)) :=
  ∀ z ∈ p, w z.1=z.2

def refineLeaves {I A O : Type} (f : O → O) : Tree I A O → Partial I A O
  | .leaf o => .leaf (f o)
  | .query i g => .query i (fun a => refineLeaves f (g a))

theorem refined_path {I A O : Type} (f : O → O) (t : Tree I A O) (w : I → A) :
    ∃ qs, PPath (refineLeaves f t) qs (f (t.eval w)) ∧ Consistent w qs := by
  induction t with
  | leaf o => exact ⟨[],.leaf _,by simp [Consistent]⟩
  | query i g ih =>
    obtain ⟨qs,p,h⟩ := ih (w i)
    refine ⟨(i,w i)::qs,.query p,?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hh
    · rfl
    · exact h z hh

theorem refined_sound {I A O : Type} (f : O → O) (t : Tree I A O)
    {qs : List (I×A)} {o : O} {w : I → A}
    (p : PPath (refineLeaves f t) qs o) (hh : Consistent w qs) :
    o=f (t.eval w) := by
  induction t generalizing qs o with
  | leaf c =>
    cases p
    rfl
  | query i g ih =>
    cases p with
    | @query _ _ a rs v p =>
      have he : w i=a := hh (i,a) (by simp)
      simp only [Tree.eval,he]
      exact ih _ p (fun z hz => hh z (List.mem_cons_of_mem _ hz))

theorem refined_bound {I A O : Type} (f : O → O) {t : Tree I A O} {h : Nat}
    (hb : Budget t h) {qs : List (I×A)} {o : O} (p : PPath (refineLeaves f t) qs o) :
    qs.length≤h := by
  induction hb generalizing qs o with
  | leaf y h =>
    cases p
    exact Nat.zero_le _
  | @query i g h cs ih =>
    cases p with
    | @query _ _ a rs z p =>
      simpa using Nat.succ_le_succ (ih a p)

theorem refined_labels {I A O : Type} (f : O → O) (P : O→Prop) (hf : ∀ o,P (f o))
    (t : Tree I A O) {qs : List (I×A)} {o : O} (p : PPath (refineLeaves f t) qs o) : P o := by
  induction t generalizing qs o with
  | leaf y =>
    cases p
    exact hf _
  | query i g ih =>
    cases p with
    | @query _ _ a rs z p => exact ih a p


end SortedQueries

namespace HussainQ1
open SortedQueries

/-- Follow at most `q` consecutive positive replies, stopping at the first negative. -/
def allYes (i : Nat) : Nat → Tree Nat Bool Bool
  | 0 => .leaf true
  | q+1 => .query i (fun b => if b then allYes (i+1) q else .leaf false)

def Tree.bindQ {I A O P : Type} (t : Tree I A O) (f : O → Tree I A P) : Tree I A P :=
  match t with
  | .leaf o => f o
  | .query i g => .query i (fun a => Tree.bindQ (g a) f)

theorem bind_eval {I A O P : Type} (t : Tree I A O) (f : O → Tree I A P) (w : I → A) :
    (Tree.bindQ t f).eval w = (f (t.eval w)).eval w := by
  induction t with
  | leaf o => rfl
  | query i g ih => exact ih (w i)

theorem budget_mono {I A O : Type} {t : Tree I A O} {a b : Nat}
    (h : Budget t a) (hab : a ≤ b) : Budget t b := by
  induction h generalizing b with
  | leaf o d => exact .leaf o b
  | @query i g d h ih =>
    cases b with
    | zero => omega
    | succ b => exact .query (fun x => ih x (by omega))

theorem bind_budget {I A O P : Type} {t : Tree I A O} {f : O → Tree I A P}
    {d e : Nat} (ht : Budget t d) (hf : ∀ a, Budget (f a) e) :
    Budget (Tree.bindQ t f) (d+e) := by
  induction ht with
  | leaf o d => exact budget_mono (hf o) (by omega)
  | @query i g d h ih =>
    have h' : Budget (.query i (fun a => Tree.bindQ (g a) f)) (d+e+1) := .query ih
    simpa only [Tree.bindQ,show d+1+e = d+e+1 by omega] using h'

theorem allYes_budget (q i : Nat) : Budget (allYes i q) q := by
  induction q generalizing i with
  | zero => exact .leaf true 0
  | succ q ih =>
    apply Budget.query
    intro b
    cases b
    · exact .leaf false q
    · exact ih (i+1)

theorem allYes_correct (w : Nat → Bool) (q i : Nat) :
    (allYes i q).eval w = true ↔ ∀ j, i ≤ j → j < i+q → w j = true := by
  induction q generalizing i with
  | zero =>
    simp only [allYes, Tree.eval, Nat.add_zero, true_iff]
    intro j hj hj'
    omega
  | succ q ih =>
    change (if w i then allYes (i+1) q else Tree.leaf false).eval w = true ↔ _
    cases h : w i with
    | false =>
      simp only [Bool.false_eq_true, ite_false, Tree.eval, false_iff]
      exact fun k => by simpa [h] using k i (by omega) (by omega)
    | true =>
      simp only [ite_true, ih]
      constructor
      · intro hn j hj hj'
        by_cases he : j=i
        · simpa [he] using h
        · exact hn j (by omega) (by omega)
      · intro hn j hj hj'
        exact hn j (by omega) (by omega)

/-- Adjacent-grid probes permit a bounded overlap in each binary-search step. -/
def bracket (G : Nat) : Nat → Nat → Nat → Tree Nat Bool (Nat × Nat)
  | 0, lo, hi => .leaf (lo,hi)
  | f+1, lo, hi =>
    let j := lo+(hi-lo)/2
    Tree.bindQ (allYes j (G+1)) (fun b =>
      if b then bracket G f j hi else bracket G f lo (j+G))

theorem bracket_budget (G f lo hi : Nat) : Budget (bracket G f lo hi) (f*(G+1)) := by
  induction f generalizing lo hi with
  | zero => simpa [bracket] using (Budget.leaf (I := Nat) (A := Bool) (lo,hi) 0)
  | succ f ih =>
    rw [Nat.succ_mul, Nat.add_comm (f*(G+1))]
    apply bind_budget (allYes_budget ..)
    intro b
    cases b <;> exact ih _ _

theorem bracket_correct (w : Nat → Bool) (G B : Nat)
    (before : ∀ j, j ≤ B → w j = true)
    (after : ∀ i, B < i → ∃ j, i ≤ j ∧ j ≤ i+G ∧ w j = false)
    (f lo hi : Nat) (hl : lo ≤ B) (hh : B ≤ hi)
    (hw : hi-lo ≤ 2*G+2+2^f) :
    let p := (bracket G f lo hi).eval w
    p.1 ≤ B ∧ B ≤ p.2 ∧ p.2-p.1 ≤ 2*G+3 := by
  induction f generalizing lo hi with
  | zero => simpa [bracket,Tree.eval] using (show lo ≤ B ∧ B ≤ hi ∧ hi-lo ≤ 2*G+3 from ⟨hl,hh,by simpa only [pow_zero, show 2*G+2+1=2*G+3 by omega] using hw⟩)
  | succ f ih =>
    let j := lo+(hi-lo)/2
    rw [pow_succ] at hw
    cases he : (allYes j (G+1)).eval w with
    | false =>
      have hb : B ≤ j+G := by
        by_contra h
        have h' := (allYes_correct w (G+1) j).2 (fun i hi hi' => before i (by omega))
        simp [he] at h'
      simpa [bracket,bind_eval,← show j = lo+(hi-lo)/2 from rfl,he] using ih lo (j+G) hl hb (by dsimp [j]; omega)
    | true =>
      have hj : j ≤ B := by
        by_contra h
        obtain ⟨i,hi,hi',hn⟩ := after j (by omega)
        have ht := (allYes_correct w (G+1) j).1 he i hi (by omega)
        rw [hn] at ht
        contradiction
      simpa [bracket,bind_eval,← show j = lo+(hi-lo)/2 from rfl,he] using ih j hi hj hh (by dsimp [j]; omega)

end HussainQ1

namespace HussainQ1
open SortedQueries

/-- Scan from a position certified to precede the first negative. -/
def firstBad (i : Nat) : Nat → Tree Nat Bool Nat
  | 0 => .leaf i
  | d+1 => .query i (fun b => if b then firstBad (i+1) d else .leaf i)

theorem firstBad_budget (i d : Nat) : Budget (firstBad i d) d := by
  induction d generalizing i with
  | zero => exact .leaf i 0
  | succ d ih =>
    apply Budget.query
    intro b
    cases b
    · exact .leaf i d
    · exact ih (i+1)

theorem firstBad_correct (w : Nat → Bool) (i d e : Nat) (hl : i ≤ e)
    (hu : e ≤ i+d) (pos : ∀ j, i ≤ j → j < e → w j = true)
    (neg : w e = false) : (firstBad i d).eval w = e := by
  induction d generalizing i with
  | zero => simpa [firstBad,Tree.eval] using (show i=e by omega)
  | succ d ih =>
    by_cases he : i = e
    · subst i
      simp [firstBad,Tree.eval,neg]
    · have ha : w i = true := pos i (by omega) (by omega)
      simp only [firstBad,Tree.eval,ha,ite_true]
      exact ih (i+1) (by omega) (by omega) (fun j hj => pos j (by omega))

theorem window_of_card (w : Nat → Bool) (G B : Nat)
    (bad : Finset Nat) (badcard : bad.card ≤ G)
    (covers : ∀ i, B < i → w i = true → i ∈ bad) :
    ∀ i, B < i → ∃ j, i ≤ j ∧ j ≤ i+G ∧ w j = false := by
  intro i hi
  by_contra! h
  have hsub : Finset.Icc i (i+G) ⊆ bad := by
    intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hl,hu⟩
    exact covers j (by omega) (by simpa using h j hl hu)
  have hc := Finset.card_le_card hsub
  simp only [Nat.card_Icc] at hc
  omega

end HussainQ1


namespace HussainQ1
open SortedQueries

/-- Reindex arbitrary natural-coordinate decision trees; coordinates may repeat. -/
def reindex {A O : Type} (f : Nat → Nat) : Tree Nat A O → Tree Nat A O
  | .leaf p => .leaf p
  | .query j g => .query (f j) (fun b => reindex f (g b))

theorem reindex_eval {A O : Type} (f : Nat → Nat) (t : Tree Nat A O) (w : Nat → A) :
    (reindex f t).eval w = t.eval (w ∘ f) := by
  induction t with
  | leaf y => rfl
  | query i g ih => exact ih (w (f i))

theorem reindex_budget {A O : Type} (f : Nat → Nat) {t : Tree Nat A O} {d : Nat}
    (h : Budget t d) : Budget (reindex f t) d := by
  induction h with
  | leaf y d => exact .leaf y d
  | query h ih => exact .query ih

def locateRun (a D G n : Nat) : Tree Nat Bool Nat :=
  Tree.bindQ (reindex (fun j => a+j*D) (bracket G (n.log2+1) 0 n))
    (fun p => firstBad (a+p.1*D) ((2*G+4)*D))

theorem locateRun_budget (a D G n : Nat) :
    Budget (locateRun a D G n) ((n.log2+1)*(G+1)+(2*G+4)*D) := by
  change Budget (Tree.bindQ (reindex (fun j => a+j*D) (bracket G (n.log2+1) 0 n))
    (fun p => firstBad (a+p.1*D) ((2*G+4)*D))) _
  exact bind_budget (reindex_budget _ (bracket_budget ..)) (fun p => firstBad_budget ..)

theorem locateRun_correct (w : Nat → Bool) (a D G n e : Nat)
    (hD : 0 < D) (he : a < e) (hen : e ≤ n)
    (pos : ∀ j, a ≤ j → j < e → w j = true) (neg : w e = false)
    (bad : Finset Nat) (badcard : bad.card ≤ G)
    (covers : ∀ j, e ≤ a+j*D → w (a+j*D) = true → j ∈ bad) :
    (locateRun a D G n).eval w = e := by
  let B := (e-1-a)/D
  have small (j : Nat) : j ≤ B ↔ a+j*D < e := by
    change j ≤ (e-1-a)/D ↔ _
    rw [Nat.le_div_iff_mul_le hD]
    omega
  have large (j : Nat) : B < j ↔ e ≤ a+j*D := by
    rw [← not_le, small, not_lt]
  have hB : B ≤ n := by
    have hq : B ≤ e-1-a := Nat.div_le_self _ _
    omega
  let v := w ∘ (fun j => a+j*D)
  have hpre : ∀ j, j ≤ B → v j = true := fun j h => pos (a+j*D) (Nat.le_add_right a (j*D)) ((small j).1 h)
  have hpost := window_of_card v G B bad badcard (fun j h => covers j ((large j).1 h))
  let t := bracket G (n.log2+1) 0 n
  have hbr := bracket_correct v G B hpre hpost (n.log2+1) 0 n (Nat.zero_le B) hB
    (by have hn : n < 2^(n.log2+1) := Nat.lt_log2_self; omega)
  let p := t.eval v
  change p.1 ≤ B ∧ B ≤ p.2 ∧ p.2-p.1 ≤ 2*G+3 at hbr
  obtain ⟨hl,hu,hw⟩ := hbr
  have helo := (small p.1).1 hl
  have hehi := (large (p.2+1)).1 (by omega)
  have hwidth : (p.2+1)*D ≤ (p.1+(2*G+4))*D :=
    Nat.mul_le_mul_right D (by omega)
  rw [Nat.add_mul p.1 (2*G+4) D] at hwidth
  change (Tree.bindQ (reindex (fun j => a+j*D) t)
    (fun p => firstBad (a+p.1*D) ((2*G+4)*D))).eval w = e
  rw [bind_eval,reindex_eval]
  change (firstBad (a+p.1*D) ((2*G+4)*D)).eval w = e
  exact firstBad_correct w _ _ _ (by omega) (by omega) (fun j hj => pos j (by omega)) neg

end HussainQ1


namespace HussainQ1
open SortedQueries

/-- One disjoint designated interval per letter, and a bounded exceptional set.
The actual runs may extend past the designated intervals. -/
structure CoreCover {A : Type} (w : Nat → Option A) (n T : Nat) where
  lo : A → Nat
  hi : A → Nat
  exc : Finset Nat
  exc_card : exc.card ≤ T
  constant : ∀ c i, lo c ≤ i → i < hi c → w i = some c
  covers : ∀ i, i < n → i ∉ exc → ∃ c, lo c ≤ i ∧ i < hi c
  precise : ∀ c i, i ∈ exc → ¬ (lo c ≤ i ∧ i < hi c)

theorem grid_rank_inj {A : Type} [Fintype A] [DecidableEq A]
    {n T : Nat} {w : Nat → Option A} (C : CoreCover w n T)
    (a D : Nat) (hD : T < D) (bad : Finset Nat)
    (hbad : ∀ i ∈ bad, a+i*D < n ∧ a+i*D ∈ C.exc) :
    bad.card ≤ Fintype.card A + 1 := by
  let passed (x : Nat) := (Finset.univ : Finset A).filter
    (fun c => C.lo c < C.hi c ∧ C.hi c ≤ x)
  let r (i : Nat) := (passed (a+i*D)).card
  have rbound (i : Nat) : r i ≤ Fintype.card A := by
    exact (Finset.card_filter_le _ _)
  have strict (i j : Nat) (hi : i ∈ bad) (hj : j ∈ bad) (hij : i < j) : r i < r j := by
    let x := a+i*D
    let y := a+j*D
    have hdist : x+D ≤ y := by
      have hmul := Nat.mul_le_mul_right D (show i+1 ≤ j by omega)
      rw [Nat.add_mul, Nat.one_mul] at hmul
      dsimp [x,y]
      omega
    obtain ⟨hxn,hxe⟩ := hbad i hi
    obtain ⟨hyn,hye⟩ := hbad j hj
    change x < n at hxn
    change x ∈ C.exc at hxe
    change y < n at hyn
    change y ∈ C.exc at hye
    have hex : ∃ z, x ≤ z ∧ z < y ∧ z ∉ C.exc := by
      by_contra! h
      have hsub : Finset.Ico x y ⊆ C.exc := by
        intro z hz
        have hz' := Finset.mem_Ico.mp hz
        exact h z hz'.1 hz'.2
      have hc := Finset.card_le_card hsub
      rw [Nat.card_Ico] at hc
      have hz := C.exc_card
      omega
    obtain ⟨z,hxz,hzy,hze⟩ := hex
    obtain ⟨c,hl,hh⟩ := C.covers z (by omega) hze
    have hxc := C.precise c x hxe
    have hyc := C.precise c y hye
    have hleft : x < C.lo c := by omega
    have hright : C.hi c ≤ y := by omega
    have hsub : passed x ⊆ passed y := by
      intro b hb
      have hb' := (Finset.mem_filter.mp hb).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb'.1,by omega⟩
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub,?_⟩
    intro h
    have hcy : c ∈ passed y := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega,hright⟩
    rw [← h] at hcy
    have hc := (Finset.mem_filter.mp hcy).2.2
    omega
  have hcard := Finset.card_le_card_of_injOn r
    (s:=bad) (t:=Finset.range (Fintype.card A+1))
    (by intro i hi; exact Finset.mem_range.mpr (by have h := rbound i; omega))
    (by
      intro i hi j hj h
      rcases lt_trichotomy i j with hlt | he | hgt
      · exact False.elim ((Nat.ne_of_lt (strict i j hi hj hlt)) h)
      · exact he
      · exact False.elim ((Nat.ne_of_lt (strict j i hj hi hgt)) h.symm))
  simpa using hcard

theorem long_hit {A : Type} {n T : Nat} {w : Nat → Option A} (C : CoreCover w n T)
    (a e : Nat) (c : A) (hen : e ≤ n) (hlen : T < e-a)
    (pos : ∀ i, a ≤ i → i < e → w i = some c) :
    ∃ z, a ≤ z ∧ z < e ∧ C.lo c ≤ z ∧ z < C.hi c := by
  have hex : ∃ z, a ≤ z ∧ z < e ∧ z ∉ C.exc := by
    by_contra! h
    have hsub : Finset.Ico a e ⊆ C.exc := by
      intro z hz
      have hz' := Finset.mem_Ico.mp hz
      exact h z hz'.1 hz'.2
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hc
    have hz := C.exc_card
    omega
  obtain ⟨z,hl,hu,hz⟩ := hex
  obtain ⟨b,hbl,hbu⟩ := C.covers z (by omega) hz
  have he : b = c := Option.some.inj ((C.constant b z hbl hbu).symm.trans (pos z hl hu))
  subst b
  exact ⟨z,hl,hu,hbl,hbu⟩

theorem grid_false_positive {A : Type} [Fintype A] [DecidableEq A]
    {n T : Nat} {w : Nat → Option A} (C : CoreCover w n T)
    (a e : Nat) (c : A) (hen : e ≤ n) (hlen : T < e-a)
    (pos : ∀ i, a ≤ i → i < e → w i = some c) (neg : w e ≠ some c)
    (out : ∀ i, n ≤ i → w i = none) :
    ∃ bad : Finset Nat, bad.card ≤ Fintype.card A+1 ∧
      ∀ j, e ≤ a+j*(T+1) → w (a+j*(T+1)) = some c → j ∈ bad := by
  obtain ⟨z,_,hze,hzl,hzu⟩ := long_hit C a e c hen hlen pos
  let bad := (Finset.range n).filter (fun j => e ≤ a+j*(T+1) ∧ w (a+j*(T+1)) = some c)
  have badin (j : Nat) (hj₁ : e ≤ a+j*(T+1)) (hj₂ : w (a+j*(T+1)) = some c) :
      a+j*(T+1) < n ∧ a+j*(T+1) ∈ C.exc := by
    have ht : a+j*(T+1) < n := by
      by_contra! hh
      rw [out _ hh] at hj₂
      contradiction
    refine ⟨ht,?_⟩
    by_contra hz
    obtain ⟨b,hl,hu⟩ := C.covers _ ht hz
    have he : b = c := Option.some.inj ((C.constant b _ hl hu).symm.trans hj₂)
    subst b
    exact neg (C.constant c e (by omega) (by omega))
  refine ⟨bad,grid_rank_inj C a (T+1) (by omega) bad ?_,?_⟩
  · intro j hj
    have hh := (Finset.mem_filter.mp hj).2
    exact badin j hh.1 hh.2
  · intro j hj₁ hj₂
    have ht := (badin j hj₁ hj₂).1
    have hjle : j ≤ j*(T+1) := by
      simpa using Nat.mul_le_mul_left j (show 1 ≤ T+1 by omega)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hj₁,hj₂⟩

end HussainQ1


namespace HussainQ1
open SortedQueries

def occ {A : Type} [DecidableEq A] (w : Nat → Option A) (n : Nat) (c : A) :=
  (Finset.range n).filter (fun i => w i = some c)

def NoSandwich {A : Type} [DecidableEq A] (w : Nat → Option A) (n m : Nat) : Prop :=
  ∀ c i, i < n → w i ≠ some c →
    ((occ w n c).filter (· < i)).card ≤ m ∨
    ((occ w n c).filter (i < ·)).card ≤ m

theorem core_of_noSandwich {A : Type} [Fintype A] [DecidableEq A]
    {w : Nat → Option A} {n m : Nat}
    (total : ∀ i, i < n → ∃ c, w i = some c) (h : NoSandwich w n m) :
    Nonempty (CoreCover w n (Fintype.card A*(2*m+1))) := by
  classical
  let S (c : A) := occ w n c
  let N (c : A) := (S c).card
  let p (c : A) : Fin (N c) ≃o ↥(S c) := (S c).orderIsoOfFin rfl
  let l (c : A) := if hn : 2*m+2 ≤ N c then ((p c) ⟨m,by omega⟩).val else 0
  let u (c : A) := if hn : 2*m+2 ≤ N c then ((p c) ⟨N c-1-m,by omega⟩).val+1 else 0
  have memp (c : A) (j : Fin (N c)) : (p c j).val < n ∧ w (p c j).val = some c := by
    have hj := (p c j).property
    exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hj).1,(Finset.mem_filter.mp hj).2⟩
  have strict (c : A) {i j : Fin (N c)} (hij : i < j) :
      (p c i).val < (p c j).val := (p c).strictMono hij
  have const (c : A) (i : Nat) (hl : l c ≤ i) (hu : i < u c) : w i = some c := by
    by_cases hn : 2*m+2 ≤ N c
    · let left : Fin (N c) := ⟨m,by omega⟩
      let right : Fin (N c) := ⟨N c-1-m,by omega⟩
      have h₁ : (p c left).val ≤ i := by simpa [l,hn,left] using hl
      have h₂ : i ≤ (p c right).val := by simpa [u,hn,right] using hu
      have hin : i < n := h₂.trans_lt (memp c right).1
      by_contra he
      have h₁' : (p c left).val < i := by
        by_contra! hh
        have hx : (p c left).val = i := by omega
        exact he (hx ▸ (memp c left).2)
      have h₂' : i < (p c right).val := by
        by_contra! hh
        have hx : (p c right).val = i := by omega
        exact he (hx ▸ (memp c right).2)
      let f (j : Fin (m+1)) := (p c ⟨j.val,by have hj := j.isLt; omega⟩).val
      let g (j : Fin (m+1)) := (p c ⟨N c-1-m+j.val,by have hj := j.isLt; omega⟩).val
      have lf (j : Fin (m+1)) : f j < i := by
        have hp : (⟨j.val,by have hj := j.isLt; omega⟩ : Fin (N c)) ≤ left := by
          change j.val ≤ m
          have hj := j.isLt
          omega
        exact (show (f j) ≤ (p c left).val from (p c).monotone hp).trans_lt h₁'
      have rg (j : Fin (m+1)) : i < g j := by
        have hp : right ≤ (⟨N c-1-m+j.val,by have hj := j.isLt; omega⟩ : Fin (N c)) := by
          change N c-1-m ≤ N c-1-m+j.val
          omega
        exact h₂'.trans_le (show (p c right).val ≤ g j from (p c).monotone hp)
      have hleft := Finset.card_le_card_of_injOn f
        (s:=Finset.univ) (t:=(S c).filter (· < i))
        (by intro j _; exact Finset.mem_filter.mpr ⟨(p c _).property,lf j⟩)
        (by
          intro j _ j' _ hj
          apply Fin.ext
          exact congrArg (fun k : Fin (N c) => k.val) ((p c).injective (Subtype.ext hj)))
      have hright := Finset.card_le_card_of_injOn g
        (s:=Finset.univ) (t:=(S c).filter (i < ·))
        (by intro j _; exact Finset.mem_filter.mpr ⟨(p c _).property,rg j⟩)
        (by
          intro j _ j' _ hj
          have hx := congrArg Fin.val ((p c).injective (Subtype.ext hj))
          apply Fin.ext
          change N c-1-m+j.val = N c-1-m+j'.val at hx
          omega)
      simp only [Finset.card_univ,Fintype.card_fin] at hleft hright
      rcases h c i hin he with hL | hR
      · change ((S c).filter (· < i)).card ≤ m at hL
        omega
      · change ((S c).filter (i < ·)).card ≤ m at hR
        omega
    · simp [u,hn] at hu
  let E := (Finset.range n).filter (fun i => ¬ ∃ c, l c ≤ i ∧ i < u c)
  let B (c : A) := (S c).filter (fun i => ¬ (l c ≤ i ∧ i < u c))
  have hfb (c : A) : (B c).card ≤ 2*m+1 := by
    by_cases hn : 2*m+2 ≤ N c
    · let left : Fin (N c) := ⟨m,by omega⟩
      let right : Fin (N c) := ⟨N c-1-m,by omega⟩
      let j (i : Nat) (hi : i ∈ S c) := (p c).symm ⟨i,hi⟩
      let f (i : Nat) := if hi : i ∈ S c then
        let k := (j i hi).val
        if k < m then k else m+(k-(N c-m))
        else 0
      have fdata (i : Nat) (hi : i ∈ B c) : ∃ hs : i ∈ S c,
          ((j i hs).val < m ∨ N c-m ≤ (j i hs).val) ∧
          f i = (if (j i hs).val < m then (j i hs).val else m+((j i hs).val-(N c-m))) := by
        have hh := Finset.mem_filter.mp hi
        refine ⟨hh.1,?_,by simp [f,hh.1]⟩
        have hx : (p c (j i hh.1)).val = i := by simp [j]
        by_contra! hn'
        have ha : left ≤ j i hh.1 := by exact hn'.1
        have hb : j i hh.1 ≤ right := by change (j i hh.1).val ≤ N c-1-m; omega
        have ha' : (p c left).val ≤ (p c (j i hh.1)).val := (p c).monotone ha
        have hb' : (p c (j i hh.1)).val ≤ (p c right).val := (p c).monotone hb
        apply hh.2
        rw [hx] at ha' hb'
        constructor
        · simpa [l,hn,left] using ha'
        · simpa [u,hn,right] using hb'
      have hc := Finset.card_le_card_of_injOn f (s:=B c) (t:=Finset.range (2*m))
        (by
          intro i hi
          obtain ⟨hs,hr,he⟩ := fdata i hi
          have hb : (j i hs).val < N c := (j i hs).isLt
          apply Finset.mem_range.mpr
          rw [he]
          split <;> omega)
        (by
          intro i hi i' hi' he
          obtain ⟨hs,hr,hf⟩ := fdata i hi
          obtain ⟨hs',hr',hf'⟩ := fdata i' hi'
          rw [hf,hf'] at he
          have hj : j i hs = j i' hs' := by
            apply Fin.ext
            split at he <;> split at he <;> omega
          have h' := congrArg (fun q : Fin (N c) => (p c q).val) hj
          simpa [j] using h')
      rw [Finset.card_range] at hc
      omega
    · have hc := Finset.card_filter_le (s:=S c) (fun i => ¬ (l c ≤ i ∧ i < u c))
      change (B c).card ≤ N c at hc
      omega
  refine ⟨⟨l,u,E,?_,const,?_,?_⟩⟩
  · have hsub : E ⊆ (Finset.univ : Finset A).biUnion B := by
      intro i hi
      obtain ⟨hin,hnot⟩ := Finset.mem_filter.mp hi
      obtain ⟨c,he⟩ := total i (Finset.mem_range.mp hin)
      exact Finset.mem_biUnion.mpr
        ⟨c,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hin,he⟩,
          fun hh => hnot ⟨c,hh⟩⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    calc
      _ ≤ ∑ _c ∈ (Finset.univ : Finset A), (2*m+1) :=
        Finset.sum_le_sum (fun c _ => hfb c)
      _ = _ := by simp
  · intro i hi he
    by_contra hh
    exact he (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hh⟩)
  · intro c i hi hh
    exact (Finset.mem_filter.mp hi).2 ⟨c,hh⟩

end HussainQ1


namespace HussainQ1
open SortedQueries

def inputMap {I A B O : Type} (f : A → B) : Tree I B O → Tree I A O
  | .leaf o => .leaf o
  | .query i g => .query i (fun a => inputMap f (g (f a)))

theorem inputMap_eval {I A B O : Type} (f : A → B) (t : Tree I B O) (w : I → A) :
    (inputMap f t).eval w = t.eval (f ∘ w) := by
  induction t with
  | leaf o => rfl
  | query i g ih => exact ih (f (w i))

theorem inputMap_budget {I A B O : Type} (f : A → B) {t : Tree I B O} {d : Nat}
    (ht : Budget t d) : Budget (inputMap f t) d := by
  induction ht with
  | leaf o d => exact .leaf o d
  | query h ih => exact .query (fun a => ih (f a))

def outputMap {I A O P : Type} (f : O → P) (t : Tree I A O) : Tree I A P :=
  Tree.bindQ t (fun o => .leaf (f o))

theorem outputMap_eval {I A O P : Type} (f : O → P) (t : Tree I A O) (w : I → A) :
    (outputMap f t).eval w = f (t.eval w) := by simp [outputMap,bind_eval,Tree.eval]

theorem outputMap_budget {I A O P : Type} (f : O → P) {t : Tree I A O} {d : Nat}
    (ht : Budget t d) : Budget (outputMap f t) d := by
  simpa [outputMap] using bind_budget ht (fun o => Budget.leaf (f o) 0)

def toFin {n : Nat} {A O : Type} (t : Tree Nat (Option A) O) : Tree (Fin n) A O :=
  match t with
  | .leaf o => .leaf o
  | .query i g =>
    if h : i < n then .query ⟨i,h⟩ (fun a => toFin (g (some a)))
    else toFin (g none)

def extend {n : Nat} {A : Type} (w : Fin n → A) (i : Nat) : Option A :=
  if h : i < n then some (w ⟨i,h⟩) else none

theorem toFin_eval {n : Nat} {A O : Type} (t : Tree Nat (Option A) O) (w : Fin n → A) :
    (toFin t).eval w = t.eval (extend w) := by
  induction t with
  | leaf o => rfl
  | query i g ih =>
    by_cases hi : i<n
    · simpa only [toFin,dite_eq_left hi,Tree.eval,extend] using ih (some (w ⟨i,hi⟩))
    · simpa only [toFin,dite_eq_right hi,Tree.eval,extend] using ih none

theorem toFin_budget {n : Nat} {A O : Type} {t : Tree Nat (Option A) O} {d : Nat}
    (ht : Budget t d) : Budget (toFin (n:=n) t) d := by
  induction ht with
  | leaf o d => exact .leaf o d
  | @query i g d h ih =>
    by_cases hi : i<n
    · simp only [toFin,dite_eq_left hi]
      exact .query (fun a => ih (some a))
    · simp only [toFin,dite_eq_right hi]
      exact budget_mono (ih none) (by omega)

def rawPool {A : Type} [Fintype A] {w : Nat → Option A} {n T : Nat}
    (C : CoreCover w n T) : Finset Nat :=
  C.exc ∪ (Finset.univ : Finset A).biUnion
    (fun c => if C.hi c-C.lo c ≤ T then Finset.Ico (C.lo c) (C.hi c) else ∅)

theorem rawPool_card {A : Type} [Fintype A] {w : Nat → Option A} {n T : Nat}
    (C : CoreCover w n T) : (rawPool C).card ≤ (Fintype.card A+1)*T := by
  let b (c : A) : Finset Nat := if C.hi c-C.lo c ≤ T then Finset.Ico (C.lo c) (C.hi c) else ∅
  change (C.exc ∪ (Finset.univ : Finset A).biUnion b).card ≤ _
  have hsum : ∑ c ∈ (Finset.univ : Finset A), (b c).card ≤ Fintype.card A*T := by
    calc
      _ ≤ ∑ _c ∈ (Finset.univ : Finset A), T := by
        apply Finset.sum_le_sum
        intro c _
        by_cases h : C.hi c-C.lo c ≤ T
        · simpa only [b,ite_eq_left h,Nat.card_Ico] using h
        · simp only [b,ite_eq_right h,Finset.card_empty,Nat.zero_le]
      _ = _ := by simp
  calc
    _ ≤ C.exc.card + ((Finset.univ : Finset A).biUnion b).card := Finset.card_union_le _ _
    _ ≤ T + Fintype.card A*T := Nat.add_le_add C.exc_card (Finset.card_biUnion_le.trans hsum)
    _ = _ := by rw [Nat.add_mul,Nat.one_mul,Nat.add_comm]

def longPool {A : Type} [Fintype A] {w : Nat → Option A} {n T : Nat}
    (C : CoreCover w n T) (s : Nat) : Finset A :=
  Finset.univ.filter (fun c => s < C.hi c)

def rawSuffix {A : Type} [Fintype A] {w : Nat → Option A} {n T : Nat}
    (C : CoreCover w n T) (s : Nat) : Finset Nat :=
  (rawPool C).filter (s ≤ ·)

theorem pool_decrease {A : Type} [Fintype A] {w : Nat → Option A} {n T : Nat}
    (C : CoreCover w n T) (s e : Nat) (c : A) (hs : s < e) (he : e ≤ n)
    (pos : ∀ i, s ≤ i → i < e → w i = some c) (neg : w e ≠ some c)
    (left : s = 0 ∨ w (s-1) ≠ some c) :
    ((rawSuffix C e).card ≤ (rawSuffix C s).card) ∧
    ((longPool C e).card ≤ (longPool C s).card) ∧
    (e-s ≤ T → (rawSuffix C e).card < (rawSuffix C s).card) ∧
    (T < e-s → (longPool C e).card < (longPool C s).card) := by
  have all (i : Nat) (hi : s ≤ i ∧ i < e)
      (hl : C.lo c ≤ i) (hu : i < C.hi c) : s ≤ C.lo c ∧ C.hi c ≤ e := by
    refine ⟨?_,?_⟩
    · by_contra! hh
      rcases left with hz | hn
      · omega
      · exact hn (C.constant c (s-1) (by omega) (by omega))
    · by_contra! hh
      exact neg (C.constant c e (by omega) hh)
  have subR : rawSuffix C e ⊆ rawSuffix C s := by
    intro i hi
    obtain ⟨h₁,h₂⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨h₁,by omega⟩
  have subB : longPool C e ⊆ longPool C s := by
    intro i hi
    obtain ⟨h₁,h₂⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨h₁,by omega⟩
  refine ⟨Finset.card_le_card subR,Finset.card_le_card subB,?_,?_⟩
  · intro short
    have hmem : s ∈ rawPool C := by
      by_cases hx : s ∈ C.exc
      · exact Finset.mem_union_left _ hx
      · obtain ⟨b,hbl,hbu⟩ := C.covers s (by omega) hx
        have hbc : b=c := Option.some.inj ((C.constant b s hbl hbu).symm.trans (pos s (by omega) hs))
        subst b
        have h := all s ⟨by omega,hs⟩ hbl hbu
        have hlen : C.hi c-C.lo c ≤ T := by omega
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        exact ⟨c,Finset.mem_univ _,by simpa [hlen,Finset.mem_Ico] using (show C.lo c ≤ s ∧ s < C.hi c from ⟨hbl,hbu⟩)⟩
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subR,by
      intro h
      have h' : s ∈ rawSuffix C s := Finset.mem_filter.mpr ⟨hmem,by omega⟩
      rw [← h] at h'
      have ho := (Finset.mem_filter.mp h').2
      omega⟩)
  · intro long
    obtain ⟨z,h₁,h₂,hl,hu⟩ := long_hit C s e c he long pos
    have hh := all z ⟨h₁,h₂⟩ hl hu
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subB,by
      intro h
      have h' : c ∈ longPool C s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
      rw [← h] at h'
      have ho := (Finset.mem_filter.mp h').2
      omega⟩)

theorem exists_end {A : Type} [DecidableEq A] {w : Nat → Option A} {n : Nat}
    (s : Nat) (c : A) (hs : s < n) (hcur : w s = some c)
    (hout : ∀ i, n ≤ i → w i = none) :
    ∃ e, s < e ∧ e ≤ n ∧ (∀ i, s ≤ i → i < e → w i = some c) ∧ w e ≠ some c := by
  have hex : ∃ i, s ≤ i ∧ w i ≠ some c := ⟨n,hs.le,by simp [hout n le_rfl]⟩
  let e := Nat.find hex
  obtain ⟨h₁,h₂⟩ := Nat.find_spec hex
  have he : e ≤ n := Nat.find_min' hex ⟨hs.le,by simp [hout n le_rfl]⟩
  refine ⟨e,?_,he,?_,h₂⟩
  · by_contra! h
    have h' : e=s := by omega
    apply h₂
    change w e = some c
    simpa only [h'] using hcur
  · intro i hi hlt
    by_contra hn
    exact (Nat.find_min hex hlt) ⟨hi,hn⟩

end HussainQ1


namespace HussainQ1
open SortedQueries

theorem firstBad_cap (w : Nat → Bool) (s d e : Nat) (hs : s ≤ e)
    (pos : ∀ i, s ≤ i → i < e → w i = true) (neg : w e = false) :
    (firstBad s d).eval w = min e (s+d) := by
  by_cases he : e ≤ s+d
  · rw [min_eq_left he]
    exact firstBad_correct w s d e hs he pos neg
  · rw [min_eq_right (by omega)]
    clear neg
    induction d generalizing s with
    | zero => simp [firstBad,Tree.eval]
    | succ d ih =>
      have hp : w s = true := pos s (by omega) (by omega)
      simp only [firstBad,Tree.eval,hp,ite_true]
      rw [ih (s+1) (by omega) (fun j hj => pos j (by omega)) (by omega)]
      omega

def fill {A : Type} (s e : Nat) (c : A) (tail : Nat → Option A) (i : Nat) : Option A :=
  if s ≤ i ∧ i < e then some c else tail i

def overhead (T : Nat) := T+2
def runCost (n T G : Nat) := (n.log2+1)*(G+1)+(2*G+4)*(T+1)

def recover {A : Type} [DecidableEq A] (n T G : Nat) (r b s : Nat) :
    Tree Nat (Option A) (Nat → Option A) :=
  if r+b=0 then .leaf (fun _ => none)
  else if s < n then
    .query s (fun x => match x with
      | none => .leaf (fun _ => none)
      | some c =>
        Tree.bindQ (inputMap (fun x => decide (x = some c)) (firstBad s (T+1))) (fun e =>
          if e < s+(T+1) then
            if _ : 0 < r then outputMap (fill s e c) (recover n T G (r-1) b e)
            else .leaf (fun _ => none)
          else
            if _ : 0 < b then
              Tree.bindQ (inputMap (fun x => decide (x = some c)) (locateRun s (T+1) G n))
                (fun f => outputMap (fill s f c) (recover n T G r (b-1) f))
            else .leaf (fun _ => none)))
  else .leaf (fun _ => none)
termination_by r+b
decreasing_by all_goals omega

def totalCost (n T G r b : Nat) :=
  r*overhead T + b*(overhead T + runCost n T G)

theorem totalCost_raw (n T G r b : Nat) (hr : 0 < r) :
    totalCost n T G (r-1) b + overhead T = totalCost n T G r b := by
  unfold totalCost
  have hh : (r-1+1)*overhead T = (r-1)*overhead T+overhead T := Nat.succ_mul _ _
  rw [show r-1+1=r by omega] at hh
  omega

theorem totalCost_long (n T G r b : Nat) (hb : 0 < b) :
    totalCost n T G r (b-1) + (overhead T + runCost n T G) = totalCost n T G r b := by
  unfold totalCost
  have hh : (b-1+1)*(overhead T+runCost n T G) =
      (b-1)*(overhead T+runCost n T G)+(overhead T+runCost n T G) := Nat.succ_mul _ _
  rw [show b-1+1=b by omega] at hh
  omega

theorem recover_budget {A : Type} [DecidableEq A] (n T G r b s : Nat) :
    Budget (recover (A:=A) n T G r b s) (totalCost n T G r b) := by
  by_cases h0 : r+b=0
  · rw [recover]
    simp only [ite_eq_left h0]
    exact .leaf _ _
  · have ht : overhead T ≤ totalCost n T G r b := by
      by_cases hr : 0 < r
      · rw [← totalCost_raw n T G r b hr]; omega
      · have hb : 0 < b := by omega
        rw [← totalCost_long n T G r b hb]; omega
    let rest := totalCost n T G r b-overhead T
    have hsum : T+1+rest+1 = totalCost n T G r b := by
      unfold overhead at ht
      dsimp [rest,overhead]
      omega
    rw [recover, ite_eq_right h0, ← hsum]
    split
    · apply Budget.query
      intro x
      cases x with
      | none => exact .leaf _ _
      | some c =>
        apply bind_budget (inputMap_budget _ (firstBad_budget ..))
        intro e
        by_cases he : e < s+(T+1)
        · simp only [ite_eq_left he]
          by_cases hr : 0 < r
          · simp only [dite_eq_left hr]
            have h' : totalCost n T G (r-1) b = rest := by
              have hh := totalCost_raw n T G r b hr
              dsimp [rest]
              omega
            rw [← h']
            exact outputMap_budget _ (recover_budget n T G (r-1) b e)
          · simp only [dite_eq_right hr]
            exact .leaf _ _
        · simp only [ite_eq_right he]
          by_cases hb : 0 < b
          · simp only [dite_eq_left hb]
            have h' : runCost n T G + totalCost n T G r (b-1) = rest := by
              have hh := totalCost_long n T G r b hb
              dsimp [rest]
              omega
            rw [← h']
            apply bind_budget (inputMap_budget _ (locateRun_budget ..))
            intro f
            exact outputMap_budget _ (recover_budget n T G r (b-1) f)
          · simp only [dite_eq_right hb]
            exact .leaf _ _
    · exact .leaf _ _
termination_by r+b
decreasing_by all_goals omega

end HussainQ1

namespace HussainQ1
open SortedQueries

theorem recover_correct {A : Type} [Fintype A] [DecidableEq A]
    {w : Nat → Option A} {n T : Nat} (C : CoreCover w n T)
    (total : ∀ i, i < n → ∃ c, w i = some c)
    (out : ∀ i, n ≤ i → w i = none)
    (r b s : Nat)
    (hr : (rawSuffix C s).card ≤ r) (hb : (longPool C s).card ≤ b)
    (beginRun : ∀ c, w s = some c → s = 0 ∨ w (s-1) ≠ some c) :
    ∀ i, s ≤ i → (recover n T (Fintype.card A+1) r b s).eval w i = w i := by
  intro i hi
  by_cases hs : s < n
  · obtain ⟨c,hc⟩ := total s hs
    obtain ⟨e,hse,hen,pos,neg⟩ := exists_end s c hs hc out
    obtain ⟨hraw,hlong,shortDec,longDec⟩ :=
      pool_decrease C s e c hse hen pos neg (beginRun c hc)
    have nz : r+b ≠ 0 := by
      by_cases hshort : e-s ≤ T
      · have := shortDec hshort
        omega
      · have := longDec (by omega)
        omega
    let test : Option A → Bool := fun x => decide (x = some c)
    have hit : ∀ j, s ≤ j → j < e → (test ∘ w) j = true := by
      intro j h₁ h₂
      simp [test,pos j h₁ h₂]
    have miss : (test ∘ w) e = false := by simp [test,neg]
    have cap := firstBad_cap (test ∘ w) s (T+1) e (by omega) hit miss
    have bnext : ∀ a, w e = some a → e = 0 ∨ w (e-1) ≠ some a := by
      intro a ha
      right
      intro hp
      have hd : c=a := Option.some.inj ((pos (e-1) (by omega) (by omega)).symm.trans hp)
      exact neg (hd ▸ ha)
    have single (tail : Nat → Option A) (tail_ok : ∀ j, e ≤ j → tail j = w j) :
        fill s e c tail i = w i := by
      by_cases he : i < e
      · simp [fill,hi,he,pos i hi he]
      · simp [fill,he,tail_ok i (by omega)]
    rw [recover, ite_eq_right nz, ite_eq_left hs]
    simp only [Tree.eval,hc]
    rw [bind_eval,inputMap_eval,cap]
    change ((if min e (s+(T+1)) < s+(T+1) then
      if _ : 0 < r then outputMap (fill s (min e (s+(T+1))) c)
        (recover n T (Fintype.card A+1) (r-1) b (min e (s+(T+1))))
      else .leaf (fun _ => none)
      else if _ : 0 < b then
        Tree.bindQ (inputMap test (locateRun s (T+1) (Fintype.card A+1) n))
          (fun f => outputMap (fill s f c) (recover n T (Fintype.card A+1) r (b-1) f))
        else .leaf (fun _ => none)).eval w) i = w i
    · by_cases hshort : e-s ≤ T
      · have hlim : e < s+(T+1) := by omega
        have hraw' := shortDec hshort
        have hr' : 0 < r := by omega
        simp only [min_eq_left hlim.le,ite_eq_left hlim,dite_eq_left hr',outputMap_eval]
        apply single
        exact recover_correct C total out (r-1) b e (by omega) (by omega) bnext
      · have hlim : s+(T+1) ≤ e := by omega
        have hlong' := longDec (by omega)
        have hb' : 0 < b := by omega
        simp only [min_eq_right hlim,Nat.lt_irrefl,ite_false,dite_eq_left hb',bind_eval,inputMap_eval]
        obtain ⟨bad,hbd,hcv⟩ := grid_false_positive C s e c hen (by omega) pos neg out
        have hfind := locateRun_correct (test ∘ w) s (T+1) (Fintype.card A+1) n e
          (by omega) hse hen hit miss bad hbd
          (by intro j hj ht; exact hcv j hj (by simpa [test] using ht))
        rw [hfind,outputMap_eval]
        apply single
        exact recover_correct C total out r (b-1) e (by omega) (by omega) bnext
  · rw [recover]
    split
    · exact (out i (by omega)).symm
    · exact (out i (by omega)).symm
termination_by r+b
decreasing_by all_goals omega

end HussainQ1

namespace HussainQ1
open SortedQueries

def SourceFeasibleOn {A : Type} {n : Nat} (P : (Fin n → A) → Prop) (d : Nat) : Prop :=
  ∃ t : Partial (Fin n) A (Fin n → A),
    (∀ qs v, PPath t qs v → P v) ∧
    (∀ w, P w → ∃ qs v, PPath t qs v ∧ Consistent w qs) ∧
    (∀ w, P w → ∀ qs v, PPath t qs v → Consistent w qs → v = w) ∧
    (∀ qs v, PPath t qs v → qs.length ≤ d)

theorem feasible_of_total {A : Type} {n : Nat} (P : (Fin n → A) → Prop)
    {t : Tree (Fin n) A (Fin n → A)} {d : Nat} (ht : Budget t d)
    (hc : ∀ w, P w → t.eval w = w) : SourceFeasibleOn P d := by
  classical
  by_cases he : ∃ w, P w
  · obtain ⟨v,hv⟩ := he
    let f := fun w => if P w then w else v
    have f_good (w : Fin n → A) : P (f w) := by
      dsimp [f]
      split <;> assumption
    refine ⟨refineLeaves f t,?_,?_,?_,?_⟩
    · intro qs w hp
      exact refined_labels f P f_good t hp
    · intro w _
      obtain ⟨qs,hp,hq⟩ := refined_path f t w
      exact ⟨qs,_,hp,hq⟩
    · intro w hw qs v hp hq
      rw [refined_sound f t hp hq, hc w hw]
      simp [f,hw]
    · intro qs v hp
      exact refined_bound f ht hp
  · refine ⟨.absent,?_,?_,?_,?_⟩
    · intro qs v hp
      cases hp
    · intro w hw
      exact False.elim (he ⟨w,hw⟩)
    · intro w hw
      exact False.elim (he ⟨w,hw⟩)
    · intro qs v hp
      cases hp

theorem recognition_of_noSandwich {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
    {n m : Nat} (P : (Fin n → A) → Prop)
    (h : ∀ w, P w → NoSandwich (extend w) n m) :
    let k := Fintype.card A
    let T := k*(2*m+1)
    SourceFeasibleOn P (totalCost n T (k+1) ((k+1)*T) k) := by
  let k := Fintype.card A
  let T := k*(2*m+1)
  let R := (k+1)*T
  let t : Tree Nat (Option A) (Nat → Option A) := recover n T (k+1) R k 0
  let outWord : (Nat → Option A) → (Fin n → A) := fun o i => (o i.val).getD default
  have hb := outputMap_budget outWord (toFin_budget (n:=n) (recover_budget (A:=A) n T (k+1) R k 0))
  apply feasible_of_total P hb
  intro w hw
  rw [outputMap_eval,toFin_eval]
  have tot (i : Nat) (hi : i<n) : ∃ c, extend w i = some c := ⟨w ⟨i,hi⟩,by simp [extend,hi]⟩
  have out (i : Nat) (hi : n ≤ i) : extend w i = none := by simp [extend,show ¬ i < n from by omega]
  obtain ⟨C⟩ := core_of_noSandwich tot (h w hw)
  have hr : (rawSuffix C 0).card ≤ R := (Finset.card_filter_le _ _).trans (rawPool_card C)
  have hl : (longPool C 0).card ≤ k := Finset.card_filter_le _ _
  have hc := recover_correct C tot out R k 0 hr hl (by intro c _; exact Or.inl rfl)
  funext i
  change ((t.eval (extend w)) i.val).getD default = w i
  rw [hc i.val (Nat.zero_le _)]
  have hi := i.isLt
  simp [extend,hi]

end HussainQ1


namespace HussainQ1
open SortedQueries

abbrev Language (A : Type) := ∀ n : Nat, (Fin n → A) → Prop

def SubwordClosed {A : Type} (L : Language A) : Prop :=
  ∀ {n j : Nat} {w : Fin n → A} (f : Fin j → Fin n),
    StrictMono f → L n w → L j (w ∘ f)

def sandwich {A : Type} (c b : A) (q : Nat) : Fin (2*q+1) → A :=
  fun i => if i.val=q then b else c

/-- The finite homogeneity assumption excludes these sandwiches by the definition
of the source's homogeneity dimension and downward closure. -/
def HomAtMost {A : Type} (L : Language A) (m : Nat) : Prop :=
  ∀ c b : A, c ≠ b → ¬ L (2*(m+1)+1) (sandwich c b (m+1))

theorem noSandwich_of_languages {A : Type} [DecidableEq A] {L : Language A}
    (hc : SubwordClosed L) {m n : Nat} (hm : HomAtMost L m)
    {w : Fin n → A} (hw : L n w) :
    NoSandwich (extend w) n m := by
  intro c i hi hne
  by_contra! h
  let b := w ⟨i,hi⟩
  have hcb : c ≠ b := by
    intro hh
    apply hne
    simp [extend,hi,hh,b]
  let Q := m+1
  let SL := (occ (extend w) n c).filter (· < i)
  let SR := (occ (extend w) n c).filter (i < ·)
  have hL : Q ≤ SL.card := by dsimp [Q,SL]; omega
  have hR : Q ≤ SR.card := by dsimp [Q,SR]; omega
  let pL := SL.orderIsoOfFin rfl
  let pR := SR.orderIsoOfFin rfl
  let left (j : Nat) (hj : j<Q) := (pL ⟨j,by omega⟩).val
  let right (j : Nat) (hj : j<Q) := (pR ⟨j,by omega⟩).val
  have factL (j : Nat) (hj : j<Q) : left j hj < i ∧ extend w (left j hj) = some c := by
    have hx := Finset.mem_filter.mp ((pL ⟨j,by omega⟩).property)
    exact ⟨hx.2,(Finset.mem_filter.mp hx.1).2⟩
  have factR (j : Nat) (hj : j<Q) :
      i < right j hj ∧ right j hj < n ∧ extend w (right j hj) = some c := by
    have hx := Finset.mem_filter.mp ((pR ⟨j,by omega⟩).property)
    have hy := Finset.mem_filter.mp hx.1
    exact ⟨hx.2,Finset.mem_range.mp hy.1,hy.2⟩
  let f : Fin (2*Q+1) → Fin n := fun j =>
    if h₁ : j.val < Q then ⟨left j.val h₁,(factL _ h₁).1.trans hi⟩
    else if j.val = Q then ⟨i,hi⟩
    else ⟨right (j.val-(Q+1)) (by have hj := j.isLt; omega), (factR _ (by
      have hj := j.isLt; omega)).2.1⟩
  have hf : StrictMono f := by
    intro j k hjk
    have hjk' : j.val < k.val := hjk
    change (f j).val < (f k).val
    by_cases hj : j.val<Q <;> by_cases hk : k.val<Q <;>
      by_cases hj' : j.val=Q <;> by_cases hk' : k.val=Q
    all_goals try omega
    all_goals simp only [f,hj,hk,hj',hk',Nat.lt_irrefl,dite_true,dite_false,ite_true,ite_false]
    · exact (pL.strictMono (show (⟨j.val,by omega⟩ : Fin SL.card) < ⟨k.val,by omega⟩ from hjk'))
    · exact (factL _ hj).1
    · exact (factL _ hj).1.trans (factR (k.val-(Q+1)) (by have hk := k.isLt; omega)).1
    · exact (factR (k.val-(Q+1)) (by have hk := k.isLt; omega)).1
    · exact pR.strictMono (show (⟨j.val-(Q+1),by have h := j.isLt; omega⟩ : Fin SR.card) <
        ⟨k.val-(Q+1),by have h := k.isLt; omega⟩ from by
          change j.val-(Q+1) < k.val-(Q+1)
          omega)
  have he : w ∘ f = sandwich c b Q := by
    funext j
    change w (f j) = sandwich c b Q j
    by_cases hj : j.val<Q
    · have hh := factL _ hj
      have h₁ := hh.1.trans hi
      have hn : j.val ≠ Q := by omega
      simpa [extend,h₁,f,hj,sandwich,hn] using hh.2
    · by_cases he : j.val=Q
      · simp [f,he,sandwich,b]
      · have hr : j.val-(Q+1) < Q := by have h' := j.isLt; omega
        have hh := factR _ hr
        simpa [extend,hh.2.1,f,hj,he,sandwich] using hh.2.2
  exact hm c b hcb (he ▸ hc f hf hw)

def coefficient (k : Nat) := k*(k+2)
def additive (k m : Nat) :=
  let T := k*(2*m+1)
  totalCost 0 T (k+1) ((k+1)*T) k

theorem cost_eq (n k m : Nat) :
    let T := k*(2*m+1)
    totalCost n T (k+1) ((k+1)*T) k = coefficient k*n.log2+additive k m := by
  dsimp [totalCost,runCost,additive,coefficient]
  rw [show Nat.log2 0 = 0 from rfl]
  ring

/-- Hussain's Question 1, with explicit coefficient k(k+2).
Neither the coefficient nor the search depends on the heterogeneity dimension. -/
theorem hussain_question1 {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
    {L : Language A} (hc : SubwordClosed L) {m : Nat} (hm : HomAtMost L m) (n : Nat) :
    let k := Fintype.card A
    SourceFeasibleOn (L n) (coefficient k*n.log2+additive k m) := by
  dsimp
  rw [← cost_eq n (Fintype.card A) m]
  exact recognition_of_noSandwich _ (fun _ hw => noSandwich_of_languages hc hm hw)

end HussainQ1
#print axioms HussainQ1.hussain_question1

namespace HussainQ1

/-- The exact natural bound implies the requested real-valued logarithmic bound. -/
theorem hussain_question1_real {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
    {L : Language A} (hc : SubwordClosed L) {m n : Nat} (hm : HomAtMost L m)
    (hn : 0 < n) :
    ∃ d : Nat, SourceFeasibleOn (L n) d ∧
      (d : ℝ) ≤ (coefficient (Fintype.card A) : ℝ) * Real.logb 2 (n : ℝ)
        + (additive (Fintype.card A) m : ℝ) := by
  refine ⟨_,hussain_question1 hc hm n,?_⟩
  push_cast
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpow : (2 : ℝ) ^ n.log2 ≤ (n : ℝ) := by
    exact_mod_cast Nat.log2_self_le (Nat.ne_of_gt hn)
  have hl := (Real.log_le_log (by positivity) hpow)
  rw [Real.log_pow] at hl
  have hp : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hw : (n.log2 : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    rw [Real.logb]
    exact (le_div_iff₀ hp).2 hl
  exact add_le_add (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)) le_rfl

end HussainQ1

#print axioms HussainQ1.hussain_question1_real
