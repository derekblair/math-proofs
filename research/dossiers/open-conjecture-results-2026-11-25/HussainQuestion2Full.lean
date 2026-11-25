import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Order.Monotone.Basic
import Lean
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic
/-!
A Lean verification of the full Question 2 in Shahid Hussain,
"Decision trees for subword-closed languages over arbitrary finite alphabets",
arXiv:2611.27454v1, Section 6: https://arxiv.org/html/2611.27454v1#S6.

For every C3 language the limiting deterministic recognition depth divided
by log base two of the word length equals r-1. Here r is the largest number
of distinct letters that can occur in that order as contiguous blocks of
arbitrarily large (common) length within a word of the language. The lower
bound uses r-1 independent binary switches. The upper bound searches the
first r-1 long-run boundaries with a bracket robust to finitely many false
positive probes; the final run ends within a bounded terminal window.
The supporting Q1 development is included so the file is standalone.
Check with Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
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

namespace SortedQueries
open Function
/-- On any family with at most two answers per query, at most 2^h inputs
can be distinguished if the output map is injective. -/
theorem card_le_pow {Ω I A O : Type} [DecidableEq A]
    {t : Tree I A O} {d : Nat} (ht : Budget t d)
    {w : Ω → I → A} {out : Ω → O} (inj : Injective out)
    (two : ∀ i, ∃ a b, ∀ z, w z i = a ∨ w z i = b)
    (xs : Finset Ω) (good : ∀ z ∈ xs, t.eval (w z) = out z) :
    xs.card ≤ 2^d := by
  classical
  induction ht generalizing xs with
  | leaf y d =>
    have h : xs.card ≤ 1 := Finset.card_le_one.mpr (by
      intro x hx z hz
      apply inj
      exact (good x hx).symm.trans (good z hz))
    exact h.trans (Nat.one_le_pow _ _ (by decide))
  | @query i g d hsub ih =>
    obtain ⟨a,b,hab⟩ := two i
    let l := xs.filter (fun z => w z i = a)
    let r := xs.filter (fun z => w z i ≠ a)
    have hll : l.card ≤ 2^d := by
      apply ih a l
      intro z hz
      have ⟨hm,he⟩ := Finset.mem_filter.mp hz
      simpa [Tree.eval,he] using good z hm
    have hrr : r.card ≤ 2^d := by
      apply ih b r
      intro z hz
      have ⟨hm,hne⟩ := Finset.mem_filter.mp hz
      have he := (hab z).resolve_left hne
      simpa [Tree.eval,he] using good z hm
    have hsum : l.card+r.card=xs.card := Finset.card_filter_add_card_filter_not _
    rw [pow_succ]
    omega

abbrev Word (n k : Nat) := Fin n → Fin k

private theorem block_index {i m d : Nat} (h : i < d*m) :
    i/m < d := by
  have hp : 0 < m := by
    by_cases hm : m=0
    · simp [hm] at h
    · omega
  exact (Nat.div_lt_iff_lt_mul hp).mpr h

def encode {d m n : Nat} (cuts : Fin d → Fin (m+1)) (i : Fin n) : Fin (d+1) :=
  if h : i.val < d*m then
    let j : Fin d := ⟨i.val/m, block_index h⟩
    if i.val%m < (cuts j).val then ⟨j.val, by omega⟩ else ⟨j.val+1, by omega⟩
  else ⟨d, by omega⟩

theorem encode_val {d m n : Nat} (cuts : Fin d → Fin (m+1)) (i : Fin n)
    (h : i.val<d*m) :
    (encode cuts i).val = (if i.val%m < (cuts ⟨i.val/m,block_index h⟩).val then i.val/m else i.val/m+1) := by
  simp only [encode,dite_eq_left h]
  split <;> rfl

theorem encode_tail {d m n : Nat} (cuts : Fin d → Fin (m+1)) (i : Fin n)
    (h : ¬ i.val<d*m) : (encode cuts i).val=d := by simp [encode,h]

theorem encode_two (d m n : Nat) (i : Fin n) :
    ∃ a b : Fin (d+1), ∀ cuts : Fin d → Fin (m+1), encode cuts i = a ∨ encode cuts i = b := by
  by_cases h : i.val < d*m
  · have hb := block_index h
    refine ⟨⟨i.val/m, by omega⟩,⟨i.val/m+1, by omega⟩,?_⟩
    intro cuts
    simp only [encode,dite_eq_left h]
    split <;> simp
  · exact ⟨⟨d,by omega⟩,⟨d,by omega⟩,fun c => by simp [encode,h]⟩

theorem encode_monotone {d m n : Nat} (cuts : Fin d → Fin (m+1)) : Monotone (@encode d m n cuts) := by
  intro i j hij
  have hn : i.val ≤ j.val := hij
  change (encode cuts i).val ≤ (encode cuts j).val
  by_cases hi : i.val < d*m
  · by_cases hj : j.val < d*m
    · have hbi := block_index hi
      have hbj := block_index hj
      have hd : i.val/m ≤ j.val/m := Nat.div_le_div_right hn
      by_cases he : i.val/m = j.val/m
      · have hf : (⟨i.val/m,hbi⟩ : Fin d) = ⟨j.val/m,hbj⟩ := Fin.ext he
        have hrem : i.val % m ≤ j.val % m := by
          have y := Nat.mod_add_div i.val m
          have z := Nat.mod_add_div j.val m
          rw [he] at y
          omega
        rw [encode_val cuts i hi,encode_val cuts j hj,hf]
        split <;> split <;> omega
      · rw [encode_val cuts i hi,encode_val cuts j hj]
        split <;> split <;> omega
    · have hbi := block_index hi
      rw [encode_val cuts i hi,encode_tail cuts j hj]
      split <;> omega
  · have hj : ¬ j.val < d*m := by omega
    rw [encode_tail cuts i hi,encode_tail cuts j hj]

theorem encode_at {d m n : Nat} (cuts : Fin d → Fin (m+1))
    (b : Fin d) {x : Nat} (hx : x < m) (hsize : d*m ≤ n) :
    ∃ z : Fin n, z.val = x + m*b.val ∧
       (encode cuts z).val = if x < (cuts b).val then b.val else b.val+1 := by
  have hmul : m*(b.val+1) ≤ d*m := by
    rw [Nat.mul_comm d m]
    exact Nat.mul_le_mul_left _ (by omega)
  have hz0 : x+m*b.val < d*m := by
    rw [Nat.mul_succ] at hmul
    omega
  let z : Fin n := ⟨x + m*b.val, by omega⟩
  have hd : z.val/m = b.val := by
    dsimp [z]
    rw [Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt hx,zero_add]
  have hr : z.val%m=x := by
    dsimp [z]
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hx]
  have hzi : z.val < d*m := hz0
  have hf : (⟨z.val/m,block_index hzi⟩ : Fin d)=b := Fin.ext hd
  refine ⟨z,rfl,?_⟩
  rw [encode_val cuts z hzi,hf,hd,hr]

theorem encode_injective {d m n : Nat} (hsize : d*m ≤ n) :
    Injective (@encode d m n) := by
  intro f g he
  funext b
  apply Fin.ext
  by_cases h₁ : (f b).val=(g b).val
  · exact h₁
  · have hf : (f b).val≤m := by omega
    have hg : (g b).val≤m := by omega
    let j := min (f b).val (g b).val
    have hj : j<m := by dsimp [j]; omega
    obtain ⟨z,hz,hfa⟩ := encode_at f b hj hsize
    obtain ⟨v,hv,hga⟩ := encode_at g b hj hsize
    have eqz : z=v := Fin.ext (hz.trans hv.symm)
    have hvv := congrArg Fin.val (congrFun he z)
    rw [hfa,eqz,hga] at hvv
    dsimp [j] at hvv
    split at hvv <;> split at hvv <;> omega


noncomputable def totalize {I A O : Type} (default : O) : Partial I A O → Tree I A O
  | .absent => .leaf default
  | .leaf o => .leaf o
  | .query i g => by
    classical
    exact if ∃ qs o, PPath (.query i g) qs o then
      .query i (fun a => totalize default (g a)) else .leaf default

theorem total_eval {I A O : Type} (default : O)
    {t : Partial I A O} {qs : List (I×A)} {o : O} {w : I → A}
    (p : PPath t qs o) (h : Consistent w qs) :
    (totalize default t).eval w=o := by
  induction p with
  | leaf => rfl
  | @query i g a qs o p ih =>
    have ex : ∃ qs o, PPath (.query i g) qs o := ⟨_,_,.query p⟩
    have e : w i = a := h (i,a) (by simp)
    have tail : Consistent w qs := fun v hv => h v (List.mem_cons_of_mem _ hv)
    simpa [totalize,ex,Tree.eval,e] using ih tail

theorem total_budget {I A O : Type} (default : O) (t : Partial I A O) (h : Nat)
    (hb : ∀ qs o, PPath t qs o → qs.length≤h) :
    Budget (totalize default t) h := by
  classical
  induction t generalizing h with
  | absent => exact .leaf _ _
  | leaf o => exact .leaf _ _
  | query i g ih =>
    by_cases ex : ∃ qs o, PPath (.query i g) qs o
    · cases h with
      | zero =>
        obtain ⟨qs,o,p⟩ := ex
        have hq := hb qs o p
        cases p with
        | query p => simp at hq
      | succ d =>
        rw [totalize,ite_eq_left ex]
        apply Budget.query
        intro a
        apply ih a d
        intro qs o p
        have hq := hb _ _ (PPath.query p)
        simpa using hq
    · rw [totalize,ite_eq_right ex]
      exact .leaf _ _


end SortedQueries

namespace HussainQ2
open SortedQueries HussainQ1

/-- Standard upper-midpoint binary search for a fixed number of probes.
Replies blacklisted after earlier verification failures are skipped. -/
def chunk (S : Finset Nat) : Nat → Nat → Nat → Tree Nat Bool (Nat × Nat)
  | 0, l,h => .leaf (l,h)
  | q+1, l,h =>
    if h ≤ l then .leaf (l,h) else
      let j := l+(h-l+1)/2
      if j ∈ S then chunk S q l (j-1)
      else .query j (fun answer =>
        if answer then chunk S q j h else chunk S q l (j-1))

theorem chunk_budget (S : Finset Nat) (q l h : Nat) : Budget (chunk S q l h) q := by
  induction q generalizing l h with
  | zero => exact .leaf _ _
  | succ q ih =>
    rw [chunk]
    split
    · exact .leaf _ _
    · dsimp only
      split
      · exact budget_mono (ih ..) (Nat.le_succ q)
      · apply Budget.query
        intro x
        cases x <;> exact ih .. 

/-- The tentative lower endpoint can overshoot, but only at a true, fresh bad point.
The upper endpoint always remains sound. -/
theorem chunk_invariant (w : Nat → Bool) (S : Finset Nat) (B : Nat)
    (before : ∀ j≤B, w j = true) (forbidden : ∀ j∈S, B<j)
    (q l h : Nat) (h₁ : l≤h) (h₂ : B≤h)
    (h₃ : B<l → w l = true ∧ l∉S) :
    let p := (chunk S q l h).eval w
    l ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ h ∧ B ≤ p.2 ∧
      (B < p.1 → w p.1 = true ∧ p.1 ∉ S) ∧
      p.2-p.1 ≤ (h-l)/2^q := by
  induction q generalizing l h with
  | zero => simpa [chunk,Tree.eval] using (show l ≤ l ∧ l ≤ h ∧ h ≤ h ∧ B ≤ h ∧
        (B < l → w l = true ∧ l ∉ S) ∧ h-l ≤ h-l from
        ⟨le_rfl,h₁,le_rfl,h₂,h₃,le_rfl⟩)
  | succ q ih =>
    let j := l+(h-l+1)/2
    by_cases he : h≤l
    · have he' : h=l := by omega
      subst h
      simpa [chunk,Tree.eval,h₂] using h₃
    · have hlj : l<j := by dsimp [j]; omega
      have hjh : j≤h := by dsimp [j]; omega
      have widthL : j-1-l ≤ (h-l)/2 := by dsimp [j]; omega
      have widthR : h-j ≤ (h-l)/2 := by dsimp [j]; omega
      have reduced (x : Nat) (hx : x ≤ (h-l)/2) : x/2^q ≤ (h-l)/2^(q+1) := by
        rw [pow_succ, Nat.mul_comm (2^q) 2, ← Nat.div_div_eq_div_mul]
        exact Nat.div_le_div_right hx
      have upperNeg (hle : B<j) :
          let p := (chunk S q l (j-1)).eval w
          l ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ h ∧ B ≤ p.2 ∧
            (B < p.1 → w p.1 = true ∧ p.1 ∉ S) ∧ p.2-p.1 ≤ (h-l)/2^(q+1) := by
        have hh := ih l (j-1) (by omega) (by omega) h₃
        exact ⟨hh.1,hh.2.1,hh.2.2.1.trans (by omega),hh.2.2.2.1,hh.2.2.2.2.1,
          hh.2.2.2.2.2.trans (reduced _ widthL)⟩
      by_cases hs : j ∈ S
      · simpa [chunk,he,← show j=l+(h-l+1)/2 from rfl,hs] using upperNeg (forbidden j hs)
      · cases hw : w j with
        | false =>
          have hjB : B<j := by
            by_contra! hh
            rw [before j hh] at hw
            contradiction
          simpa only [chunk,ite_eq_right he,← show j=l+(h-l+1)/2 from rfl,
            ite_eq_right hs,Tree.eval,hw,Bool.false_eq_true,ite_false] using upperNeg hjB
        | true =>
          have hh := ih j h hjh h₂ (fun _ => ⟨hw,hs⟩)
          have hfinish :
              let p := (chunk S q j h).eval w
              l ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ h ∧ B ≤ p.2 ∧
                (B < p.1 → w p.1 = true ∧ p.1 ∉ S) ∧ p.2-p.1 ≤ (h-l)/2^(q+1) :=
            ⟨hlj.le.trans hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1,
              hh.2.2.2.2.2.trans (reduced _ widthR)⟩
          simpa only [chunk,ite_eq_right he,← show j=l+(h-l+1)/2 from rfl,
            ite_eq_right hs,Tree.eval,hw,ite_true] using hfinish

end HussainQ2


namespace HussainQ2
open SortedQueries HussainQ1

def verify (G i : Nat) : Tree Nat Bool Bool := allYes (i-G) (min i G+1)

theorem verify_budget (G i : Nat) : Budget (verify G i) (G+1) :=
  budget_mono (allYes_budget ..) (by have h : min i G ≤ G := min_le_right ..; omega)

theorem verify_good (w : Nat → Bool) (G B i : Nat) (bad : Finset Nat)
    (bc : bad.card ≤ G) (covers : ∀ j, B<j → w j=true → j∈bad)
    (h : (verify G i).eval w = true) : i-G ≤ B := by
  by_contra! hB
  have hi : G ≤ i := by omega
  obtain ⟨j,h₁,h₂,h₃⟩ := window_of_card w G B bad bc covers (i-G) hB
  have hh : (allYes (i-G) (G+1)).eval w = true := by
    simpa only [verify,min_eq_right hi] using h
  have hf := (allYes_correct w (G+1) (i-G)).1 hh j h₁ (by omega)
  rw [h₃] at hf
  contradiction

theorem verify_bad (w : Nat → Bool) (G B i : Nat)
    (before : ∀ j≤B, w j=true) (h : (verify G i).eval w = false) : B < i := by
  by_contra! hi
  have ht : (verify G i).eval w = true := by
    apply (allYes_correct w (min i G+1) (i-G)).2
    intro j hj hj'
    apply before
    have he : i-G+min i G=i := by omega
    omega
  rw [h] at ht
  contradiction

def chunkCost (G : Nat) (qs : List Nat) (b f : Nat) :=
  qs.sum + qs.length*(G+1) + f*(b+G+1)

def sharpBracket (G : Nat) (qs : List Nat) (f : Nat) (S : Finset Nat) (l h : Nat) :
    Tree Nat Bool (Nat × Nat) :=
  match qs with
  | [] => .leaf (l,h)
  | q::tail =>
    Tree.bindQ (chunk S q l h) (fun p =>
      Tree.bindQ (verify G p.1) (fun ok =>
        if ok then sharpBracket G tail f S (max l (p.1-G)) p.2
        else if _ : 0 < f then sharpBracket G (q::tail) (f-1) (insert p.1 S) l p.2
        else .leaf (l,p.2)))
termination_by qs.length + f
decreasing_by all_goals simp_wf; all_goals omega

theorem sharp_budget (G : Nat) (qs : List Nat) (b f : Nat)
    (S : Finset Nat) (l h : Nat) (hq : ∀ q∈qs, q ≤ b) :
    Budget (sharpBracket G qs f S l h) (chunkCost G qs b f) := by
  cases hqs : qs with
  | nil =>
    rw [sharpBracket]
    exact .leaf _ _
  | cons q tail =>
    have hqt : ∀ j ∈ q::tail, j ≤ b := by simpa only [hqs] using hq
    rw [sharpBracket]
    have hc : q+(G+1)+chunkCost G tail b f = chunkCost G (q::tail) b f := by
      simp only [chunkCost,List.sum_cons,List.length_cons,Nat.succ_mul]
      omega
    rw [← hc, Nat.add_assoc]
    apply bind_budget (chunk_budget ..)
    intro p
    apply bind_budget (verify_budget ..)
    intro ok
    cases ok with
    | true =>
      simp only [ite_true]
      exact sharp_budget G tail b f S _ _ (fun j hj => hqt j (List.mem_cons_of_mem _ hj))
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      by_cases hf : 0<f
      · simp only [dite_eq_left hf]
        have hmul : f*(b+G+1)=(f-1)*(b+G+1)+(b+G+1) := by
          rw [← Nat.succ_mul]
          congr 1
          omega
        have hc' : chunkCost G (q::tail) b (f-1) ≤ chunkCost G tail b f := by
          have hqb : q ≤ b := hqt q (by simp)
          simp only [chunkCost,List.sum_cons,List.length_cons,Nat.succ_mul]
          rw [hmul]
          omega
        exact budget_mono (sharp_budget G (q::tail) b (f-1) _ _ _ hqt) hc'
      · simp only [dite_eq_right hf]
        exact .leaf _ _
termination_by qs.length + f
decreasing_by
  all_goals simp_wf
  all_goals rw [hqs]
  all_goals simp only [List.length_cons]
  all_goals omega

end HussainQ2

namespace HussainQ2
open SortedQueries HussainQ1

theorem sharp_correct (w : Nat → Bool) (G B : Nat)
    (before : ∀ j≤B, w j=true)
    (bad : Finset Nat) (bc : bad.card ≤ G)
    (covers : ∀ j, B<j → w j=true → j∈bad)
    (badAbove : ∀ j∈bad, B<j)
    (qs : List Nat) (f : Nat) (S : Finset Nat) (l h : Nat)
    (posq : ∀ q∈qs, 0 < q) (sub : S ⊆ bad)
    (hfuel : bad.card ≤ S.card+f) (hl : l≤B) (hh : B≤h)
    (hwidth : h-l ≤ 2*G+2+2^qs.sum) :
    let p := (sharpBracket G qs f S l h).eval w
    p.1 ≤ B ∧ B ≤ p.2 ∧ p.2-p.1 ≤ 2*G+3 := by
  cases hqs : qs with
  | nil =>
    rw [sharpBracket]
    have hw : h-l ≤ 2*G+3 := by
      simpa only [hqs,List.sum_nil,pow_zero,show 2*G+2+1=2*G+3 by omega] using hwidth
    exact ⟨hl,hh,hw⟩
  | cons q tail =>
    have hqt : ∀ j ∈ q::tail, 0<j := by simpa only [hqs] using posq
    have hq : 0<q := hqt q (by simp)
    let p := (chunk S q l h).eval w
    have inv : l ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ h ∧ B ≤ p.2 ∧
        (B < p.1 → w p.1 = true ∧ p.1 ∉ S) ∧ p.2-p.1 ≤ (h-l)/2^q :=
      chunk_invariant w S B before (fun j hj => badAbove j (sub hj))
        q l h (hl.trans hh) hh (fun h => False.elim (by omega))
    obtain ⟨hpl,hpm,hph,hpB,hbad,hw⟩ := inv
    rw [sharpBracket,bind_eval,bind_eval]
    change (let z := (if (verify G p.1).eval w then
      sharpBracket G tail f S (max l (p.1-G)) p.2
      else if _ : 0 < f then sharpBracket G (q::tail) (f-1) (insert p.1 S) l p.2
      else .leaf (l,p.2)).eval w; z.1 ≤ B ∧ B ≤ z.2 ∧ z.2-z.1 ≤ 2*G+3)
    cases hv : (verify G p.1).eval w with
    | true =>
      simp only [ite_true]
      have hok := verify_good w G B p.1 bad bc covers hv
      have hlow : max l (p.1-G) ≤ B := max_le hl hok
      have hd : (h-l)/2^q ≤ G+1+2^tail.sum := by
        have hp : 0 < 2^q := by positivity
        have hp2 : 2 ≤ 2^q := Nat.pow_le_pow_right (n:=2) (by decide) hq
        have hd : (h-l)/2^q ≤ (2*G+2+2^qs.sum)/2^q := Nat.div_le_div_right hwidth
        rw [hqs,List.sum_cons,Nat.pow_add,Nat.add_mul_div_left _ _ hp] at hd
        have hcut := Nat.div_le_div_left (a:=2*G+2) hp2 (by decide)
        omega
      have hm : p.1-G ≤ max l (p.1-G) := le_max_right .. 
      have hnew : p.2-max l (p.1-G) ≤ 2*G+2+2^tail.sum := by
        have h := hw.trans hd
        omega
      exact sharp_correct w G B before bad bc covers badAbove tail f S _ _
        (fun j hj => hqt j (List.mem_cons_of_mem _ hj)) sub hfuel hlow hpB hnew
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      have hpb := verify_bad w G B p.1 before hv
      obtain ⟨ht,hfresh⟩ := hbad hpb
      have hbel := covers p.1 hpb ht
      have sub' : insert p.1 S ⊆ bad := Finset.insert_subset_iff.mpr ⟨hbel,sub⟩
      have hc : (insert p.1 S).card = S.card+1 := Finset.card_insert_of_notMem hfresh
      have hsc := Finset.card_le_card sub'
      have hf : 0 < f := by omega
      simp only [dite_eq_left hf]
      have hnew : p.2-l ≤ 2*G+2+2^(q::tail).sum := by
        rw [hqs] at hwidth
        omega
      exact sharp_correct w G B before bad bc covers badAbove (q::tail) (f-1) _ _ _
        hqt sub' (by omega) hl hpB hnew
termination_by qs.length+f
decreasing_by
  all_goals simp_wf
  all_goals rw [hqs]
  all_goals simp only [List.length_cons]
  all_goals omega

end HussainQ2


namespace HussainQ2
open SortedQueries HussainQ1

/-- Partition the exponent budget into b-step chunks, with a single remainder. -/
def plan (p b : Nat) : List Nat :=
  if p%b=0 then List.replicate (p/b) b else (p%b)::List.replicate (p/b) b

theorem plan_sum (p b : Nat) : (plan p b).sum = p := by
  have h : p % b + b*(p/b)=p := Nat.mod_add_div p b
  by_cases he : p%b=0
  · simpa [plan,he,List.sum_replicate,Nat.mul_comm] using h
  · simpa [plan,he,List.sum_replicate,Nat.mul_comm] using h

theorem plan_len (p b : Nat) : (plan p b).length ≤ p/b+1 := by
  by_cases h : p%b=0 <;> simp [plan,h]

theorem plan_mem (p b q : Nat) (hb : 0 < b) (hq : q ∈ plan p b) :
    0<q ∧ q≤b := by
  by_cases h : p%b=0
  · have hm : q ∈ List.replicate (p/b) b := by simpa [plan,h] using hq
    have he : q=b := List.eq_of_mem_replicate hm
    simpa [he] using hb
  · have hm : q ∈ (p%b)::List.replicate (p/b) b := by simpa [plan,h] using hq
    rcases List.mem_cons.mp hm with he | he
    · subst q
      have h' := Nat.mod_lt p hb
      omega
    · have he' : q=b := List.eq_of_mem_replicate he
      simpa [he'] using hb

def sharpRunCost (n T G b : Nat) :=
  let p := n.log2+1
  p + (p/b+1)*(G+1) + G*(b+G+1) + (2*G+4)*(T+1)

def locateRunSharp (a T G n b : Nat) : Tree Nat Bool Nat :=
  Tree.bindQ
    (reindex (fun j => a+j*(T+1)) (sharpBracket G (plan (n.log2+1) b) G ∅ 0 n))
    (fun p => firstBad (a+p.1*(T+1)) ((2*G+4)*(T+1)))

theorem locateRunSharp_budget (a T G n b : Nat) (hb : 0 < b) :
    Budget (locateRunSharp a T G n b) (sharpRunCost n T G b) := by
  apply budget_mono (bind_budget (reindex_budget _ (sharp_budget G _ b G ∅ 0 n
    (fun q hq => (plan_mem _ _ _ hb hq).2))) (fun p => firstBad_budget ..))
  dsimp [sharpRunCost,chunkCost]
  rw [plan_sum]
  have hh := Nat.mul_le_mul_right (G+1) (plan_len (n.log2+1) b)
  omega

theorem locateRunSharp_correct (w : Nat → Bool) (a T G n b e : Nat)
    (hb : 0 < b) (he : a < e) (hen : e ≤ n)
    (pos : ∀ j, a ≤ j → j < e → w j = true) (neg : w e = false)
    (bad : Finset Nat) (badcard : bad.card ≤ G)
    (covers : ∀ j, e ≤ a+j*(T+1) → w (a+j*(T+1)) = true → j ∈ bad) :
    (locateRunSharp a T G n b).eval w = e := by
  let D := T+1
  let B := (e-1-a)/D
  have small (j : Nat) : j ≤ B ↔ a+j*D < e := by
    change j ≤ (e-1-a)/D ↔ _
    rw [Nat.le_div_iff_mul_le (by dsimp [D]; omega)]
    omega
  have large (j : Nat) : B < j ↔ e ≤ a+j*D := by rw [← not_le, small, not_lt]
  have hB : B ≤ n := by
    have hq : B ≤ e-1-a := Nat.div_le_self _ _
    omega
  let v := w ∘ (fun j => a+j*D)
  have hpre : ∀ j, j ≤ B → v j = true := fun j h =>
    pos (a+j*D) (Nat.le_add_right a (j*D)) ((small j).1 h)
  let bad' := bad.filter (B < ·)
  have hpost : ∀ j, B < j → v j = true → j ∈ bad' :=
    fun j hj h => Finset.mem_filter.mpr ⟨covers j ((large j).1 hj) h,hj⟩
  have hbc : bad'.card ≤ G := (Finset.card_filter_le _ _).trans badcard
  let t := sharpBracket G (plan (n.log2+1) b) G ∅ 0 n
  have hbr := sharp_correct v G B hpre bad' hbc hpost (fun j hj => (Finset.mem_filter.mp hj).2)
    (plan (n.log2+1) b) G ∅ 0 n (fun q hq => (plan_mem _ _ _ hb hq).1)
    (Finset.empty_subset _) (by simpa using hbc) (Nat.zero_le B) hB (by
      rw [plan_sum]
      have hn : n < 2^(n.log2+1) := Nat.lt_log2_self
      omega)
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

end HussainQ2


namespace HussainQ2
open SortedQueries HussainQ1

theorem tail_covered_by_exc {A : Type} [Fintype A] {w : Nat → Option A} {n T : Nat}
    (C : CoreCover w n T) (e : Nat) (h : (longPool C e).card = 0) :
    n-T ≤ e := by
  have hsub : Finset.Ico e n ⊆ C.exc := by
    intro i hi
    by_contra hx
    obtain ⟨hel,hen⟩ := Finset.mem_Ico.mp hi
    obtain ⟨c,hlo,hhi⟩ := C.covers i hen hx
    have hc : c ∈ longPool C e := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
    rw [Finset.card_eq_zero.mp h] at hc
    exact Finset.notMem_empty c hc
  have hle := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hle
  have hex := C.exc_card
  omega

theorem tail_search_correct (w : Nat → Bool) (s e n T : Nat)
    (hs : s ≤ e) (he : e ≤ n) (hpos : n-T ≤ e)
    (pos : ∀ j, s ≤ j → j < e → w j=true) (neg : w e=false) :
    (firstBad (max s (n-T)) T).eval w = e := by
  apply firstBad_correct w _ _ _
  · exact max_le hs hpos
  · have h := le_max_right s (n-T)
    omega
  · intro j hj je
    exact pos j ((le_max_left s (n-T)).trans hj) je
  · exact neg

end HussainQ2

namespace HussainQ2
open SortedQueries HussainQ1

def longFinder (n T G step b s : Nat) : Tree Nat Bool Nat :=
  if b=1 then firstBad (max s (n-T)) T else locateRunSharp s T G n step

def recoverSharp {A : Type} [DecidableEq A] (n T G step : Nat) (r b s : Nat) :
    Tree Nat (Option A) (Nat → Option A) :=
  if r+b=0 then .leaf (fun _ => none)
  else if s < n then
    .query s (fun x => match x with
      | none => .leaf (fun _ => none)
      | some c =>
        Tree.bindQ (inputMap (fun x => decide (x = some c)) (firstBad s (T+1))) (fun e =>
          if e < s+(T+1) then
            if _ : 0 < r then outputMap (fill s e c) (recoverSharp n T G step (r-1) b e)
            else .leaf (fun _ => none)
          else
            if _ : 0 < b then
              Tree.bindQ (inputMap (fun x => decide (x = some c)) (longFinder n T G step b s))
                (fun f => outputMap (fill s f c) (recoverSharp n T G step r (b-1) f))
            else .leaf (fun _ => none)))
  else .leaf (fun _ => none)
termination_by r+b
decreasing_by all_goals omega


def findCost (n T G step b : Nat) :=
  T + (if b=1 then 0 else sharpRunCost n T G step)

def totalSharpCost (n T G step r b : Nat) :=
  r*overhead T + b*(overhead T+T) + (b-1)*sharpRunCost n T G step

theorem totalSharpCost_raw (n T G step r b : Nat) (hr : 0 < r) :
    totalSharpCost n T G step (r-1) b + overhead T = totalSharpCost n T G step r b := by
  unfold totalSharpCost
  have hh : (r-1+1)*overhead T = (r-1)*overhead T+overhead T := Nat.succ_mul _ _
  rw [show r-1+1=r by omega] at hh
  omega

theorem totalSharpCost_long (n T G step r b : Nat) (hb : 0 < b) :
    totalSharpCost n T G step r (b-1) + (overhead T + findCost n T G step b) =
      totalSharpCost n T G step r b := by
  unfold totalSharpCost findCost
  have hh : (b-1+1)*(overhead T+T) = (b-1)*(overhead T+T)+(overhead T+T) := Nat.succ_mul _ _
  rw [show b-1+1=b by omega] at hh
  by_cases he : b=1
  · simp only [he,ite_true,Nat.sub_self,Nat.zero_sub,Nat.zero_mul]
    simp
  · rw [ite_eq_right he]
    have hh' : (b-1-1+1)*sharpRunCost n T G step =
        (b-1-1)*sharpRunCost n T G step+sharpRunCost n T G step := Nat.succ_mul _ _
    rw [show b-1-1+1=b-1 by omega] at hh'
    omega

theorem longFinder_budget (n T G step b s : Nat) (hp : 0 < step) :
    Budget (longFinder n T G step b s) (findCost n T G step b) := by
  by_cases he : b=1
  · simpa [longFinder,findCost,he] using firstBad_budget (max s (n-T)) T
  · simp only [longFinder,findCost,ite_eq_right he]
    exact budget_mono (locateRunSharp_budget s T G n step hp) (Nat.le_add_left ..)

theorem recoverSharp_budget {A : Type} [DecidableEq A] (n T G step r b s : Nat) (hstep : 0 < step) :
    Budget (recoverSharp (A:=A) n T G step r b s) (totalSharpCost n T G step r b) := by
  by_cases h0 : r+b=0
  · rw [recoverSharp]
    simp only [ite_eq_left h0]
    exact .leaf _ _
  · have ht : overhead T ≤ totalSharpCost n T G step r b := by
      by_cases hr : 0 < r
      · rw [← totalSharpCost_raw n T G step r b hr]; omega
      · have hb : 0 < b := by omega
        rw [← totalSharpCost_long n T G step r b hb]; omega
    let rest := totalSharpCost n T G step r b-overhead T
    have hsum : T+1+rest+1 = totalSharpCost n T G step r b := by
      unfold overhead at ht
      dsimp [rest,overhead]
      omega
    rw [recoverSharp, ite_eq_right h0, ← hsum]
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
            have h' : totalSharpCost n T G step (r-1) b = rest := by
              have hh := totalSharpCost_raw n T G step r b hr
              dsimp [rest]
              omega
            rw [← h']
            exact outputMap_budget _ (recoverSharp_budget n T G step (r-1) b e hstep)
          · simp only [dite_eq_right hr]
            exact .leaf _ _
        · simp only [ite_eq_right he]
          by_cases hb : 0 < b
          · simp only [dite_eq_left hb]
            have h' : findCost n T G step b + totalSharpCost n T G step r (b-1) = rest := by
              have hh := totalSharpCost_long n T G step r b hb
              dsimp [rest]
              omega
            rw [← h']
            apply bind_budget (inputMap_budget _ (longFinder_budget n T G step b s hstep))
            intro f
            exact outputMap_budget _ (recoverSharp_budget n T G step r (b-1) f hstep)
          · simp only [dite_eq_right hb]
            exact .leaf _ _
    · exact .leaf _ _
termination_by r+b
decreasing_by all_goals omega

end HussainQ2

namespace HussainQ2
open SortedQueries HussainQ1

theorem recoverSharp_correct {A : Type} [Fintype A] [DecidableEq A]
    {w : Nat → Option A} {n T : Nat} (C : CoreCover w n T)
    (total : ∀ i, i < n → ∃ c, w i = some c)
    (out : ∀ i, n ≤ i → w i = none)
    (step r b s : Nat) (hstep : 0<step)
    (hr : (rawSuffix C s).card ≤ r) (hb : (longPool C s).card ≤ b)
    (beginRun : ∀ c, w s = some c → s = 0 ∨ w (s-1) ≠ some c) :
    ∀ i, s ≤ i → (recoverSharp n T (Fintype.card A+1) step r b s).eval w i = w i := by
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
    rw [recoverSharp, ite_eq_right nz, ite_eq_left hs]
    simp only [Tree.eval,hc]
    rw [bind_eval,inputMap_eval,cap]
    change ((if min e (s+(T+1)) < s+(T+1) then
      if _ : 0 < r then outputMap (fill s (min e (s+(T+1))) c)
        (recoverSharp n T (Fintype.card A+1) step (r-1) b (min e (s+(T+1))))
      else .leaf (fun _ => none)
      else if _ : 0 < b then
        Tree.bindQ (inputMap test (longFinder n T (Fintype.card A+1) step b s))
          (fun f => outputMap (fill s f c) (recoverSharp n T (Fintype.card A+1) step r (b-1) f))
        else .leaf (fun _ => none)).eval w) i = w i
    · by_cases hshort : e-s ≤ T
      · have hlim : e < s+(T+1) := by omega
        have hraw' := shortDec hshort
        have hr' : 0 < r := by omega
        simp only [min_eq_left hlim.le,ite_eq_left hlim,dite_eq_left hr',outputMap_eval]
        apply single
        exact recoverSharp_correct C total out step (r-1) b e hstep (by omega) (by omega) bnext
      · have hlim : s+(T+1) ≤ e := by omega
        have hlong' := longDec (by omega)
        have hb' : 0 < b := by omega
        simp only [min_eq_right hlim,Nat.lt_irrefl,ite_false,dite_eq_left hb',bind_eval,inputMap_eval]
        have hfind : (longFinder n T (Fintype.card A+1) step b s).eval (test ∘ w) = e := by
          by_cases hb1 : b=1
          · simp only [longFinder,ite_eq_left hb1]
            have hp : (longPool C e).card = 0 := by omega
            exact tail_search_correct _ s e n T hse.le hen (tail_covered_by_exc C e hp) hit miss
          · simp only [longFinder,ite_eq_right hb1]
            obtain ⟨bad,hbd,hcv⟩ := grid_false_positive C s e c hen (by omega) pos neg out
            exact locateRunSharp_correct (test ∘ w) s T (Fintype.card A+1) n step e
              hstep hse hen hit miss bad hbd
              (by intro j hj ht; exact hcv j hj (by simpa [test] using ht))
        rw [hfind,outputMap_eval]
        apply single
        exact recoverSharp_correct C total out step r (b-1) e hstep (by omega) (by omega) bnext
  · rw [recoverSharp]
    split
    · exact (out i (by omega)).symm
    · exact (out i (by omega)).symm
termination_by r+b
decreasing_by all_goals omega

end HussainQ2


namespace HussainQ2
open SortedQueries HussainQ1

def largeCores {A : Type} [Fintype A] {w : Nat → Option A} {n T : Nat}
    (C : CoreCover w n T) (K : Nat) : Finset A :=
  Finset.univ.filter (fun c => K ≤ C.hi c-C.lo c)

def prune {A : Type} [Fintype A] {w : Nat → Option A} {n T : Nat}
    (C : CoreCover w n T) (K : Nat) :
    CoreCover w n (T+Fintype.card A*(K-1)) := by
  let keep (c : A) := K ≤ C.hi c-C.lo c
  let l (c : A) := if keep c then C.lo c else 0
  let u (c : A) := if keep c then C.hi c else 0
  let discarded (c : A) := if keep c then ∅ else Finset.Ico (C.lo c) (C.hi c)
  let lost := (Finset.univ : Finset A).biUnion discarded
  refine ⟨l,u,C.exc ∪ lost,?_,?_,?_,?_⟩
  · have hsum : ∑ c ∈ (Finset.univ : Finset A), (discarded c).card ≤ Fintype.card A*(K-1) := by
      calc
        _ ≤ ∑ _c ∈ (Finset.univ : Finset A), (K-1) := by
          apply Finset.sum_le_sum
          intro c _
          by_cases h : keep c
          · simp only [discarded,ite_eq_left h,Finset.card_empty,Nat.zero_le]
          · simp only [discarded,ite_eq_right h,Nat.card_Ico]
            dsimp [keep] at h
            omega
        _ = _ := by simp
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add C.exc_card (Finset.card_biUnion_le.trans hsum))
  · intro c i h₁ h₂
    by_cases h : keep c
    · exact C.constant c i (by simpa only [l,ite_eq_left h] using h₁)
        (by simpa only [u,ite_eq_left h] using h₂)
    · simp only [u,ite_eq_right h,Nat.not_lt_zero] at h₂
  · intro i hi hx
    obtain ⟨c,h₁,h₂⟩ := C.covers i hi (fun h => hx (Finset.mem_union_left _ h))
    by_cases h : keep c
    · exact ⟨c,by simpa only [l,ite_eq_left h] using h₁,by simpa only [u,ite_eq_left h] using h₂⟩
    · exact False.elim (hx (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨c,Finset.mem_univ _,by simpa only [discarded,ite_eq_right h] using Finset.mem_Ico.mpr ⟨h₁,h₂⟩⟩)))
  · intro c i hi ⟨h₁,h₂⟩
    by_cases h : keep c
    · have hl : C.lo c ≤ i := by simpa only [l,ite_eq_left h] using h₁
      have hu : i < C.hi c := by simpa only [u,ite_eq_left h] using h₂
      rcases Finset.mem_union.mp hi with hex | hd
      · exact C.precise c i hex ⟨hl,hu⟩
      · obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp hd
        by_cases hh : keep b
        · simp only [discarded,ite_eq_left hh,Finset.notMem_empty] at hb
        · have hb' := Finset.mem_Ico.mp (by simpa only [discarded,ite_eq_right hh] using hb)
          have he : b=c := Option.some.inj ((C.constant b i hb'.1 hb'.2).symm.trans (C.constant c i hl hu))
          exact hh (he ▸ h)
    · simp only [u,ite_eq_right h,Nat.not_lt_zero] at h₂

theorem pruned_count {A : Type} [Fintype A] {w : Nat → Option A} {n T : Nat}
    (C : CoreCover w n T) (K : Nat) :
    (longPool (prune C K) 0).card ≤ (largeCores C K).card := by
  apply Finset.card_le_card
  intro c hc
  have hp := (Finset.mem_filter.mp hc).2
  by_cases h : K ≤ C.hi c-C.lo c
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
  · simp only [prune,ite_eq_right h,Nat.lt_irrefl] at hp

end HussainQ2

namespace HussainQ2
open SortedQueries HussainQ1

def blockIndex {r K : Nat} (i : Fin (r*K)) : Fin r :=
  ⟨i.val/K,by
    have hi := i.isLt
    have hp : 0<K := by
      by_contra! h
      have he : K=0 := by omega
      simp [he] at hi
    exact (Nat.div_lt_iff_lt_mul hp).2 hi⟩

def blockWord {A : Type} {r : Nat} (a : Fin r → A) (K : Nat) (i : Fin (r*K)) : A :=
  a (blockIndex i)

theorem many_cores_accept_block {A : Type} [Fintype A] [DecidableEq A]
    {n T : Nat} {w : Fin n → A} (C : CoreCover (extend w) n T)
    (L : Language A) (closed : SubwordClosed L) (hw : L n w)
    (r K : Nat) (hK : 0 < K) (hlarge : r ≤ (largeCores C K).card) :
    ∃ f : Fin r ↪ A, L (r*K) (blockWord f K) := by
  classical
  let F := largeCores C K
  change r ≤ F.card at hlarge
  have largeLength (c : A) (hc : c ∈ F) : C.lo c+K ≤ C.hi c := by
    have ht := (Finset.mem_filter.mp hc).2
    omega
  have ends (c : A) (hc : c ∈ F) : C.hi c ≤ n := by
    by_contra! h
    let i := max (C.lo c) n
    have hh := largeLength c hc
    have ht := C.constant c i (le_max_left ..) (max_lt (by omega) h)
    have out : extend w i = none := by
      have hin : n ≤ i := le_max_right ..
      simp only [HussainQ1.extend,dite_eq_right (show ¬ i<n from by omega)]
    rw [out] at ht
    contradiction
  let S := F.image C.lo
  have hinj : Set.InjOn C.lo ↑F := by
    intro c hc b hb he
    have hh := largeLength c hc
    have hj := largeLength b hb
    have ht₁ := C.constant c (C.lo c) le_rfl (by omega)
    have ht₂ := C.constant b (C.lo c) (by omega) (by omega)
    exact Option.some.inj (ht₁.symm.trans ht₂)
  have hcard : S.card = F.card := Finset.card_image_of_injOn hinj
  let order := S.orderIsoOfFin rfl
  let start (j : Fin r) := (order ⟨j.val,by have hj := j.isLt; omega⟩).val
  have start_lt : StrictMono start := by
    intro i j hi
    exact order.strictMono (show (⟨i.val,by have h := i.isLt; omega⟩ : Fin S.card) <
      ⟨j.val,by have h := j.isLt; omega⟩ from hi)
  have hex (j : Fin r) : ∃ c ∈ F, C.lo c = start j :=
    Finset.mem_image.mp (order _).property
  let a (j : Fin r) := Classical.choose (hex j)
  have ha (j : Fin r) : a j ∈ F ∧ C.lo (a j) = start j := Classical.choose_spec (hex j)
  have hainj : Function.Injective a := by
    intro i j he
    apply start_lt.injective
    rw [← (ha i).2,← (ha j).2,he]
  let f : Fin r ↪ A := ⟨a,hainj⟩
  have room (i : Fin (r*K)) : start (blockIndex i)+i.val%K < C.hi (a (blockIndex i)) := by
    have ht := largeLength _ (ha (blockIndex i)).1
    have hh := (ha (blockIndex i)).2
    have hm := Nat.mod_lt i.val hK
    omega
  let emb (i : Fin (r*K)) : Fin n := ⟨start (blockIndex i)+i.val%K,
    (room i).trans_le (ends _ (ha (blockIndex i)).1)⟩
  have emb_inc : StrictMono emb := by
    intro i j hij
    have hii : i.val < j.val := hij
    have hv : (blockIndex i).val ≤ (blockIndex j).val := Nat.div_le_div_right hii.le
    rcases lt_or_eq_of_le hv with hl | he
    · have har : a (blockIndex i) ≠ a (blockIndex j) := by
        intro hc
        have hh := congrArg Fin.val (hainj hc)
        omega
      have hstart : start (blockIndex i) < start (blockIndex j) := start_lt hl
      have sep : C.hi (a (blockIndex i)) ≤ start (blockIndex j) := by
        by_contra! hh
        have h₁ := (ha (blockIndex i)).2
        have h₂ := (ha (blockIndex j)).2
        have hj := largeLength _ (ha (blockIndex j)).1
        have hc := C.constant (a (blockIndex i)) (start (blockIndex j)) (by omega) hh
        have hd := C.constant (a (blockIndex j)) (start (blockIndex j)) (by omega) (by omega)
        exact har (Option.some.inj (hc.symm.trans hd))
      change start (blockIndex i)+i.val%K < start (blockIndex j)+j.val%K
      exact (room i).trans_le (sep.trans (Nat.le_add_right ..))
    · have heB : blockIndex i = blockIndex j := Fin.ext he
      have heN : i.val/K = j.val/K := he
      have hmod : i.val%K < j.val%K := by
        have hii' := Nat.div_add_mod i.val K
        have hjj' := Nat.div_add_mod j.val K
        rw [heN] at hii'
        omega
      change start (blockIndex i)+i.val%K < start (blockIndex j)+j.val%K
      rw [heB]
      omega
  refine ⟨f,?_⟩
  have he : w ∘ emb = blockWord f K := by
    funext i
    have ha' := (ha (blockIndex i)).2
    have hconst := C.constant (a (blockIndex i)) (emb i).val
      (show C.lo (a (blockIndex i)) ≤ start (blockIndex i)+i.val%K by omega) (room i)
    have hn := (emb i).isLt
    rw [HussainQ1.extend,dite_eq_left hn] at hconst
    change w (emb i) = a (blockIndex i)
    exact Option.some.inj hconst
  exact he ▸ closed emb emb_inc hw

end HussainQ2


namespace HussainQ2
open SortedQueries HussainQ1

theorem blockIndex_mono {r K : Nat} : Monotone (@blockIndex r K) :=
  fun _ _ h => Nat.div_le_div_right h

/-- A sufficiently large uniform block word contains every shorter sorted word
over the same ordered tuple. Give the ith letter offset i inside its block. -/
theorem accept_monotone_of_big {A : Type} {r n K : Nat}
    {L : Language A} (hc : SubwordClosed L) (a : Fin r → A)
    (hbig : L (r*K) (blockWord a K)) (hn : n ≤ K)
    (v : Fin n → Fin r) (hv : Monotone v) : L n (a ∘ v) := by
  let e (i : Fin n) : Fin (r*K) := ⟨(v i).val*K+i.val,by
    have hi : i.val < K := i.isLt.trans_le hn
    have hm := Nat.mul_le_mul_right K (show (v i).val+1 ≤ r from (v i).isLt)
    rw [Nat.add_mul,Nat.one_mul] at hm
    omega⟩
  have he : StrictMono e := by
    intro i j hij
    have hm := Nat.mul_le_mul_right K (show (v i).val ≤ (v j).val from hv hij.le)
    change (v i).val*K+i.val < (v j).val*K+j.val
    have hh : i.val < j.val := hij
    omega
  have hh : blockWord a K ∘ e = a ∘ v := by
    funext i
    change a (blockIndex (e i)) = a (v i)
    congr 1
    apply Fin.ext
    change ((v i).val*K+i.val)/K = (v i).val
    have hp : 0<K := Nat.zero_lt_of_lt (i.isLt.trans_le hn)
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt (i.isLt.trans_le hn)]
    omega
  exact hh ▸ hc e he hbig

def Admitted {A : Type} (L : Language A) (r : Nat) : Prop :=
  ∃ a : Fin r ↪ A, ∀ K : Nat, L (r*K) (blockWord a K)

theorem sharp_upper_of_forbidden {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
    {L : Language A} (hc : SubwordClosed L) {m : Nat} (hm : HomAtMost L m)
    (r K n step : Nat) (hK : 0<K) (hstep : 0<step)
    (hforbid : ∀ a : Fin (r+1) ↪ A, ¬ L ((r+1)*K) (blockWord a K)) :
    let k := Fintype.card A
    let T := k*(2*m+1)+k*(K-1)
    SourceFeasibleOn (L n) (totalSharpCost n T (k+1) step ((k+1)*T) r) := by
  let k := Fintype.card A
  let T := k*(2*m+1)+k*(K-1)
  let R := (k+1)*T
  let t : Tree Nat (Option A) (Nat → Option A) := recoverSharp n T (k+1) step R r 0
  let outWord : (Nat → Option A) → (Fin n → A) := fun o i => (o i.val).getD default
  have hb := outputMap_budget outWord (toFin_budget (n:=n)
    (recoverSharp_budget (A:=A) n T (k+1) step R r 0 hstep))
  apply feasible_of_total (L n) hb
  intro w hw
  rw [outputMap_eval,toFin_eval]
  have tot (i : Nat) (hi : i<n) : ∃ c, HussainQ1.extend w i = some c :=
    ⟨w ⟨i,hi⟩,by simp [HussainQ1.extend,hi]⟩
  have out (i : Nat) (hi : n ≤ i) : HussainQ1.extend w i = none :=
    by simp [HussainQ1.extend,show ¬i<n from by omega]
  obtain ⟨C₀⟩ := core_of_noSandwich tot (noSandwich_of_languages hc hm hw)
  let C := prune C₀ K
  have hcount : (largeCores C₀ K).card ≤ r := by
    by_contra! h
    obtain ⟨a,ha⟩ := many_cores_accept_block C₀ L hc hw (r+1) K hK (by omega)
    exact hforbid a ha
  have hr : (rawSuffix C 0).card ≤ R := (Finset.card_filter_le _ _).trans (rawPool_card C)
  have hl : (longPool C 0).card ≤ r := (pruned_count C₀ K).trans hcount
  have hc' := recoverSharp_correct C tot out step R r 0 hstep hr hl (by intro c _; exact Or.inl rfl)
  funext i
  change ((t.eval (HussainQ1.extend w)) i.val).getD default = w i
  rw [hc' i.val (Nat.zero_le _)]
  have hi := i.isLt
  simp [HussainQ1.extend,hi]

end HussainQ2


namespace HussainQ2
open SortedQueries HussainQ1

theorem forbidden_of_not_admitted {A : Type} [Fintype A] [DecidableEq A]
    {L : Language A} (hc : SubwordClosed L) (r : Nat)
    (hn : ¬ Admitted L r) :
    ∃ K, 0 < K ∧ ∀ a : Fin r ↪ A, ¬ L (r*K) (blockWord a K) := by
  classical
  have fail (a : Fin r ↪ A) : ∃ q, ¬ L (r*q) (blockWord a q) := by
    by_contra! h
    exact hn ⟨a,h⟩
  let Q (a : Fin r ↪ A) := r*Classical.choose (fail a)
  let K := (Finset.univ : Finset (Fin r ↪ A)).sup Q + 1
  refine ⟨K,by dsimp [K]; omega,?_⟩
  intro a ha
  have hq : Q a ≤ K := (Finset.le_sup (Finset.mem_univ a)).trans (Nat.le_succ _)
  let q := Classical.choose (fail a)
  exact (Classical.choose_spec (fail a)) (accept_monotone_of_big hc a ha hq
    (fun i => blockIndex (K:=q) i) blockIndex_mono)

def InfiniteHet {A : Type} (L : Language A) : Prop :=
  ∀ K : Nat, ∃ a : Fin 2 ↪ A, L (2*K) (blockWord a K)

theorem admitted_two {A : Type} [Fintype A] [DecidableEq A]
    {L : Language A} (hc : SubwordClosed L) (hh : InfiniteHet L) : Admitted L 2 := by
  by_contra hn
  obtain ⟨K,_,not⟩ := forbidden_of_not_admitted hc 2 hn
  obtain ⟨a,ha⟩ := hh K
  exact not a ha

theorem admitted_max {A : Type} [Fintype A] {L : Language A} (ha : Admitted L 2) :
    ∃ d, 0<d ∧ Admitted L (d+1) ∧ (∀ j, Admitted L j → j ≤ d+1) ∧
      ¬ Admitted L (d+2) := by
  classical
  have leA (j : Nat) (h : Admitted L j) : j ≤ Fintype.card A := by
    obtain ⟨a,_⟩ := h
    simpa using Fintype.card_le_of_injective a a.injective
  let E := (Finset.Icc 2 (Fintype.card A)).filter (Admitted L)
  have hm : 2 ∈ E :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,leA 2 ha⟩,ha⟩
  let r := E.max' ⟨2,hm⟩
  have hr : r ∈ E := Finset.max'_mem _ _
  have hmin : 2 ≤ r := Finset.le_max' _ _ hm
  have had : Admitted L r := (Finset.mem_filter.mp hr).2
  have hmax : ∀ j, Admitted L j → j ≤ r := by
    intro j hj
    by_cases hj' : 2 ≤ j
    · exact Finset.le_max' _ _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hj',leA _ hj⟩,hj⟩)
    · omega
  have hn : ¬ Admitted L (r+1) := by
    intro hh
    have hp : r+1 ∈ E :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,leA _ hh⟩,hh⟩
    have hh' : r+1 ≤ r := Finset.le_max' _ _ hp
    omega
  refine ⟨r-1,by omega,?_⟩
  rw [show r-1+1=r by omega,show r-1+2=r+1 by omega]
  exact ⟨had,hmax,hn⟩

end HussainQ2


namespace HussainQ2
open SortedQueries HussainQ1

noncomputable def recognitionDepth {A : Type} (L : Language A) (n : Nat) : Nat := by
  classical
  exact if h : ∃ j, SourceFeasibleOn (L n) j then Nat.find h else 0

theorem recognitionDepth_le {A : Type} {L : Language A} {n j : Nat}
    (h : SourceFeasibleOn (L n) j) : recognitionDepth L n ≤ j := by
  classical
  have hex : ∃ j, SourceFeasibleOn (L n) j := ⟨j,h⟩
  rw [recognitionDepth,dite_eq_left hex]
  exact Nat.find_min' hex h

theorem recognitionDepth_feasible {A : Type} {L : Language A} {n : Nat}
    (hex : ∃ j, SourceFeasibleOn (L n) j) : SourceFeasibleOn (L n) (recognitionDepth L n) := by
  classical
  rw [recognitionDepth,dite_eq_left hex]
  exact Nat.find_spec hex

theorem lower_of_admitted {A : Type} [DecidableEq A] [Inhabited A]
    {L : Language A} (hc : SubwordClosed L) (n d h : Nat)
    (ha : Admitted L (d+1)) (hs : SourceFeasibleOn (L n) h) :
    (n/d+1)^d ≤ 2^h := by
  classical
  obtain ⟨a,hA⟩ := ha
  obtain ⟨pt,labels,cover,sound,depth⟩ := hs
  let t := totalize (fun _ : Fin n => (default : A)) pt
  have ht : Budget t h := total_budget _ pt h depth
  let w (z : Fin d → Fin (n/d+1)) : Fin n → A := a ∘ (encode z)
  have good (z : Fin d → Fin (n/d+1)) : L n (w z) :=
    accept_monotone_of_big hc a (hA n) le_rfl (encode z) (encode_monotone z)
  have inj : Function.Injective w := by
    intro z z' hz
    apply encode_injective (n:=n) (m:=n/d) (Nat.mul_div_le n d)
    funext i
    exact a.injective (congrFun hz i)
  have two (i : Fin n) : ∃ b c : A, ∀ z, w z i=b ∨ w z i=c := by
    obtain ⟨b,c,h⟩ := encode_two d (n/d) n i
    exact ⟨a b,a c,fun z => (h z).imp (congrArg a) (congrArg a)⟩
  have hh := card_le_pow ht inj two Finset.univ (by
    intro z _
    obtain ⟨qs,v,path,cons⟩ := cover (w z) (good z)
    exact (total_eval _ path cons).trans (sound (w z) (good z) qs v path cons))
  simpa using hh

theorem log_lower {d n h : Nat} (hd : 0<d) (hn : 2≤n)
    (hl : (n/d+1)^d ≤ 2^h) :
    (d:ℝ)*Real.log (n:ℝ) - (d:ℝ)*Real.log (d:ℝ) ≤ (h:ℝ) * Real.log 2 := by
  have hnR : 2 ≤ (n:ℝ) := by exact_mod_cast hn
  have hnP : 0 < (n:ℝ) := by linarith
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  let a : ℕ := n/d+1
  have ha : 0 < a := by simp [a]
  have haR : 0 < (a:ℝ) := by exact_mod_cast ha
  have hbase : n ≤ d*a := by
    rw [Nat.mul_comm]
    apply Nat.le_of_lt
    apply (Nat.div_lt_iff_lt_mul hd).mp
    simp [a]
  have hlR : (a:ℝ)^d ≤ (2:ℝ)^h := by exact_mod_cast hl
  have hlog := Real.log_le_log (pow_pos haR _) hlR
  rw [Real.log_pow,Real.log_pow] at hlog
  have hnMul : (n:ℝ) ≤ (d:ℝ)*(a:ℝ) := by exact_mod_cast hbase
  have hlogN := Real.log_le_log hnP hnMul
  rw [Real.log_mul hdR.ne' haR.ne'] at hlogN
  have hL := mul_le_mul_of_nonneg_left hlogN hdR.le
  rw [mul_add] at hL
  linarith

end HussainQ2


namespace HussainQ2
open SortedQueries HussainQ1
open Filter Topology

theorem log2_floor_le (n : Nat) (hn : 0<n) :
    (n.log2:ℝ) ≤ Real.logb 2 (n:ℝ) := by
  have hpow : (2:ℝ)^n.log2 ≤ (n:ℝ) := by
    exact_mod_cast Nat.log2_self_le (Nat.ne_of_gt hn)
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlog
  rw [Real.logb]
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).2 hlog

theorem real_upper_of_sharp {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
    {L : Language A} (hc : SubwordClosed L) {m : Nat} (hm : HomAtMost L m)
    (d K b : Nat) (hK : 0<K) (hb : 0<b)
    (hforbid : ∀ a : Fin (d+2) ↪ A, ¬ L ((d+2)*K) (blockWord a K)) :
    let G := Fintype.card A+1
    ∃ C : ℝ, ∀ n : Nat, 0<n →
      (recognitionDepth L n : ℝ) ≤
        (d:ℝ)*(1+((G:ℝ)+1)/(b:ℝ))*Real.logb 2 (n:ℝ)+C := by
  let k := Fintype.card A
  let G := k+1
  let T := k*(2*m+1)+k*(K-1)
  let R := (k+1)*T
  let F : ℝ := (G:ℝ)+1
  let bR : ℝ := b
  have hbp : 0 < bR := by dsimp [bR]; exact_mod_cast hb
  let C₀ : ℝ := (G*(b+G+1)+(2*G+4)*(T+1) : Nat)
  let D : ℝ := (R*overhead T+(d+1)*(overhead T+T) : Nat)
  let C₁ : ℝ := 1+(1/bR+1)*F+C₀
  refine ⟨D+(d:ℝ)*C₁,?_⟩
  intro n hn
  let x := Real.logb 2 (n:ℝ)
  let p := n.log2+1
  have hp : (p:ℝ) ≤ x+1 := by dsimp [p,x]; push_cast; linarith [log2_floor_le n hn]
  have hmul : ((p/b:Nat):ℝ)*bR ≤ (p:ℝ) := by
    have hx := Nat.div_mul_le_self p b
    dsimp [bR]
    exact_mod_cast hx
  have hq : ((p/b:Nat):ℝ) ≤ (x+1)/bR := (le_div_iff₀ hbp).2 (hmul.trans hp)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hqF := mul_le_mul_of_nonneg_right (add_le_add hq (show (1:ℝ) ≤ 1 from le_rfl)) hF
  have hr : (sharpRunCost n T G b : ℝ) ≤ (1+F/bR)*x+C₁ := by
    have he : (sharpRunCost n T G b : ℝ) = (p:ℝ) + (((p/b:Nat):ℝ)+1)*F + C₀ := by
      dsimp [sharpRunCost,p,F,C₀]
      push_cast
      ring
    rw [he]
    calc
      _ ≤ x+1+(((x+1)/bR)+1)*F+C₀ := add_le_add (add_le_add hp hqF) le_rfl
      _ = _ := by dsimp [C₁]; ring
  have hbase : recognitionDepth L n ≤ totalSharpCost n T G b R (d+1) :=
    recognitionDepth_le (sharp_upper_of_forbidden hc hm (d+1) K n b hK hb hforbid)
  have hD : (recognitionDepth L n : ℝ) ≤ D+(d:ℝ)*(sharpRunCost n T G b : ℝ) := by
    have he : totalSharpCost n T G b R (d+1) =
      (R*overhead T+(d+1)*(overhead T+T))+d*sharpRunCost n T G b := by
      simp [totalSharpCost]
    rw [he] at hbase
    dsimp [D]
    exact_mod_cast hbase
  calc
    _ ≤ D+(d:ℝ)*((1+F/bR)*x+C₁) :=
      hD.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hr (by positivity)))
    _ = _ := by dsimp [F,bR,x,G,k]; ring

end HussainQ2


namespace HussainQ2
open SortedQueries HussainQ1
open Filter Topology

/-- Full general limit, given a maximal admitted ordered alphabet tuple. -/
theorem limit_of_max {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
    {L : Language A} (hc : SubwordClosed L) {m d : Nat} (hm : HomAtMost L m)
    (hd : 0<d) (ha : Admitted L (d+1)) (hnxt : ¬ Admitted L (d+2)) :
    Tendsto (fun n : Nat => (recognitionDepth L n:ℝ)/Real.logb 2 (n:ℝ)) atTop (𝓝 (d:ℝ)) := by
  obtain ⟨K,hK,hforbid⟩ := forbidden_of_not_admitted hc (d+2) hnxt
  let G := Fintype.card A+1
  let D : ℝ := d
  let F : ℝ := (G:ℝ)+1
  have hD : 0<D := by dsimp [D]; exact_mod_cast hd
  have hF : 0<F := by dsimp [F]; positivity
  have hpos : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have ht : Tendsto (fun n : Nat => Real.logb 2 (n:ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  apply Metric.tendsto_nhds.mpr
  intro ε he
  obtain ⟨b,hbR⟩ := exists_nat_gt (2*D*F/ε)
  have hbRpos : 0 < (b:ℝ) := (by positivity : 0 < 2*D*F/ε) |>.trans hbR
  have hb : 0<b := by exact_mod_cast hbRpos
  have hδ : D*F/(b:ℝ) < ε/2 := by
    apply (div_lt_iff₀ hbRpos).2
    have hh := (div_lt_iff₀ he).1 hbR
    nlinarith only [hh]
  obtain ⟨C,hC⟩ := real_upper_of_sharp hc hm d K b hK hb hforbid
  let M := max 1 (max (2*|C|/ε) (|D*Real.logb 2 D|/ε))
  filter_upwards [eventually_ge_atTop (2:Nat), ht.eventually (eventually_gt_atTop M)] with n hn hM
  let x := Real.logb 2 (n:ℝ)
  let y := (recognitionDepth L n:ℝ)
  have hx : 0<x := (by unfold M; positivity : 0 < M).trans hM
  have hcx : C < (ε/2)*x := by
    have hh : 2*|C|/ε < x := (le_max_left _ _).trans ((le_max_right 1 _)) |>.trans_lt hM
    have hh' := (div_lt_iff₀ he).1 hh
    nlinarith only [hh',le_abs_self C]
  have hdx : D*Real.logb 2 D < ε*x := by
    have hh : |D*Real.logb 2 D|/ε < x :=
      (le_max_right _ _).trans (le_max_right 1 _) |>.trans_lt hM
    have hh' := (div_lt_iff₀ he).1 hh
    nlinarith only [hh',le_abs_self (D*Real.logb 2 D)]
  have huv : y ≤ D*(1+F/(b:ℝ))*x+C := hC n (by omega)
  have hxy : y < (D+ε)*x := by
    have hh := mul_lt_mul_of_pos_right hδ hx
    have heq : D*(1+F/(b:ℝ))*x+C = D*x+(D*F/(b:ℝ))*x+C := by
      rw [mul_add,mul_one,mul_div_assoc,add_mul]
    rw [heq] at huv
    nlinarith only [huv,hcx,hh]
  have hfea : SourceFeasibleOn (L n) (recognitionDepth L n) :=
    recognitionDepth_feasible ⟨_,sharp_upper_of_forbidden hc hm (d+1) K n b hK hb hforbid⟩
  have hlo := log_lower hd hn (lower_of_admitted hc n d _ ha hfea)
  have hlv : D*x-D*Real.logb 2 D ≤ y := by
    have hp : (D*x-D*Real.logb 2 D)*Real.log 2 ≤ y*Real.log 2 := by
      convert hlo using 1
      dsimp [x,D,Real.logb]
      field_simp [hpos.ne']
    exact le_of_mul_le_mul_right hp hpos
  have hyl : (D-ε)*x < y := by nlinarith only [hlv,hdx]
  change dist (y/x) D < ε
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor
  · have hh := (lt_div_iff₀ hx).2 hyl
    linarith
  · have hh := (div_lt_iff₀ hx).2 hxy
    linarith

/-- Hussain's §6 Question 2 in full: the limit exists for every C3 language.
The integer result d is one less than the maximum admitted block-tuple length. -/
theorem hussain_question2_full {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
    {L : Language A} (hc : SubwordClosed L) {m : Nat} (hm : HomAtMost L m)
    (hh : InfiniteHet L) :
    ∃ d : Nat, 0<d ∧ Admitted L (d+1) ∧ (∀ j, Admitted L j → j ≤ d+1) ∧
      Tendsto (fun n : Nat => (recognitionDepth L n:ℝ)/Real.logb 2 (n:ℝ)) atTop (𝓝 (d:ℝ)) := by
  obtain ⟨d,hd,ha,hmax,hn⟩ := admitted_max (admitted_two hc hh)
  exact ⟨d,hd,ha,hmax,limit_of_max hc hm hd ha hn⟩

end HussainQ2
#print axioms HussainQ2.hussain_question2_full
