import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card

namespace BoxToken
set_option linter.unusedSectionVars false

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

/-- All tokens that can still advance remain strictly above forgotten
positions. Finished tokens are removed, but their terminals stay reserved
by the target test. -/
def Safe (rank : V → ℕ) (active : Finset I) (pos : I → V) (forgot : Finset V) : Prop :=
  ∀ v ∈ forgot, ∀ j ∈ active, rank v < rank (pos j)

def Distinct (active : Finset I) (pos : I → V) : Prop :=
  ∀ i ∈ active, ∀ j ∈ active, i ≠ j → pos i ≠ pos j

def Earliest (rank : V → ℕ) (active : Finset I) (pos : I → V) (i : I) : Prop :=
  i ∈ active ∧ ∀ j ∈ active, rank (pos i) ≤ rank (pos j)

def setPos (pos : I → V) (i : I) (v : V) : I → V :=
  fun j => if j=i then v else pos j

theorem earliest_exists (rank : V → ℕ) (active : Finset I) (pos : I → V)
    (hne : active.Nonempty) :
    ∃ i, Earliest rank active pos i := by
  obtain ⟨i, hi, h⟩ := Finset.exists_min_image active (fun j => rank (pos j)) hne
  exact ⟨i,hi,h⟩

theorem safe_initial (rank : V → ℕ) (active : Finset I) (pos : I → V) :
    Safe rank active pos ∅ := by
  intro v hv
  exact (Finset.notMem_empty v hv).elim

/-- Each newly entered vertex is fresh without querying the forgotten
roster. The local checks are only rank increase and noncollision with the
other currently occupied positions. -/
theorem advance (rank : V → ℕ) (inj : Function.Injective rank)
    (active : Finset I) (pos : I → V) (forgot : Finset V) (i : I) (v : V)
    (safe : Safe rank active pos forgot) (distinct : Distinct active pos)
    (first : Earliest rank active pos i) (rise : rank (pos i) < rank v)
    (clear : ∀ j ∈ active, i ≠ j → v ≠ pos j) :
    v ∉ forgot ∧ v ≠ pos i ∧
      Safe rank active (setPos pos i v) (insert (pos i) forgot) ∧
      Distinct active (setPos pos i v) := by
  have hi := first.1
  have fresh : v ∉ forgot := fun hv => (Nat.lt_asymm rise (safe v hv i hi))
  have hn : v ≠ pos i := fun h => (Nat.lt_irrefl _ (h ▸ rise))
  refine ⟨fresh,hn,?_,?_⟩
  · intro x hx j hj
    rcases Finset.mem_insert.mp hx with rfl|hx
    · by_cases he : j=i
      · simpa [setPos,he] using rise
      · have hlt : rank (pos i) < rank (pos j) :=
          Nat.lt_of_le_of_ne (first.2 j hj) (fun h => distinct i hi j hj (Ne.symm he) (inj h))
        simpa [setPos,he] using hlt
    · by_cases he : j=i
      · simpa [setPos,he] using (safe x hx i hi).trans rise
      · simpa [setPos,he] using safe x hx j hj
  · intro j hj l hl hne
    by_cases hj' : j=i
    · subst j
      simpa [setPos,Ne.symm hne] using clear l hl hne
    · by_cases hl' : l=i
      · subst l
        simpa [setPos,hj'] using (clear j hj (Ne.symm hj')).symm
      · simpa [setPos,hj',hl'] using distinct j hj l hl hne

theorem retire (rank : V → ℕ) (active : Finset I) (pos : I → V)
    (forgot : Finset V) (i : I) (safe : Safe rank active pos forgot)
    (distinct : Distinct active pos) :
    Safe rank (active.erase i) pos forgot ∧ Distinct (active.erase i) pos := by
  exact ⟨fun v hv j hj => safe v hv j (Finset.mem_erase.mp hj).2,
    fun j hj l hl => distinct j (Finset.mem_erase.mp hj).2 l (Finset.mem_erase.mp hl).2⟩

/-- Reserved starts and targets of other paths can be tested without
tracking any retired token. For every vertex-disjoint witness system,
such reservation and the current-token test never block a genuine step. -/
theorem witness_target_clear (active : Finset I) (pos start stop : I → V)
    (path : I → Set V) (disjoint : ∀ i j, i ≠ j → Disjoint (path i) (path j))
    (hpos : ∀ j ∈ active, pos j ∈ path j)
    (hstart : ∀ j, start j ∈ path j) (hstop : ∀ j, stop j ∈ path j)
    {i : I} {v : V} (hv : v ∈ path i) :
    (∀ j ∈ active, i ≠ j → v ≠ pos j) ∧
    (∀ j, i ≠ j → v ≠ start j ∧ v ≠ stop j) := by
  have separate (j : I) (hne : i ≠ j) (x : V) (hx : x ∈ path j) : v ≠ x := by
    rintro rfl
    exact Set.disjoint_left.mp (disjoint i j hne) hv hx
  exact ⟨fun j hj hn => separate j hn _ (hpos j hj),
    fun j hn => ⟨separate j hn _ (hstart j),separate j hn _ (hstop j)⟩⟩

#print axioms earliest_exists
#print axioms advance
#print axioms retire
#print axioms witness_target_clear

/-- Termination of witness-guided scheduling. Take the measure to be the
sum, over live path fragments, of untraversed edges plus one retirement
step. Once a legal step along a witness is available for the earliest
token, no bound on intermediate token histories is needed. -/
theorem terminating_schedule {S : Type*} (step : S → S → Prop) (size : S → ℕ)
    (find : ∀ x, 0 < size x → ∃ y, step x y ∧ size y < size x) (start : S) :
    ∃ stop, Relation.ReflTransGen step start stop ∧ size stop = 0 := by
  have main (n : ℕ) :
      ∀ x, size x = n → ∃ stop, Relation.ReflTransGen step x stop ∧ size stop = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      by_cases hn : n = 0
      · exact ⟨x,Relation.ReflTransGen.refl,hx.trans hn⟩
      · have hp : 0 < size x := by omega
        obtain ⟨y,hxy,hy⟩ := find x hp
        obtain ⟨z,hyz,hz⟩ := ih (size y) (by omega) y rfl
        exact ⟨z,Relation.ReflTransGen.head hxy hyz,hz⟩
  exact main (size start) start rfl

#print axioms terminating_schedule
end BoxToken
