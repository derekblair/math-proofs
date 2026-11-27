import UnitCodes

namespace EdgeExpansion
open WeightedWalk

variable {V I : Type*}
variable (src dst : I → V) (weight : I → ℤ)

abbrev Node (V I : Type*) := V ⊕ (I × List ℤ)
def base : V → Node V I := Sum.inl
def atList (i : I) (R : List ℤ) : Node V I :=
  match R with
  | [] => base (dst i)
  | k::L => Sum.inr (i,k::L)

def edge (x : V) (k : ℤ) (y : V) :=
  ∃ i, src i=x ∧ dst i=y ∧ weight i=k

inductive arc : Node V I → ℤ → Node V I → Prop
  | start (i : I) {k R} : UnitCodes.code (weight i)=k::R →
      arc (base (src i)) k (atList dst i R)
  | rest (i : I) (k : ℤ) (R : List ℤ) :
      arc (Sum.inr (i,k::R)) k (atList dst i R)

def point : Node V I → V
  | .inl x => x
  | .inr (i,_) => dst i

def debt : Node V I → ℤ
  | .inl _ => 0
  | .inr (_,R) => R.sum

theorem point_tail (i : I) (R : List ℤ) : point dst (atList dst i R) = dst i := by
  cases R <;> rfl

theorem debt_tail (i : I) (R : List ℤ) : debt (atList dst i R) = R.sum := by
  cases R <;> rfl

theorem compress {x y : Node V I} {L : List ℤ} (h : Walk (arc src dst weight) x y L) :
    ∃ C, Walk (edge src dst weight) (point dst x) (point dst y) C ∧
      C.sum = L.sum + debt y - debt x := by
  induction h with
  | nil x => exact ⟨[],.nil _,by simp⟩
  | @step x y z k L a p ih =>
    obtain ⟨C,hC,hEq⟩ := ih
    cases a with
    | start i hs =>
      have ht := UnitCodes.total (weight i)
      rw [hs,List.sum_cons] at ht
      rw [point_tail] at hC
      rw [debt_tail] at hEq
      refine ⟨weight i::C,.step ⟨i,rfl,rfl,rfl⟩ hC,?_⟩
      change weight i+C.sum = k+L.sum+debt z-0
      omega
    | rest i k R =>
      rw [point_tail] at hC
      rw [debt_tail] at hEq
      refine ⟨C,hC,?_⟩
      change C.sum = k+L.sum+debt z-(k+R.sum)
      omega

theorem tails (i : I) (R : List ℤ) :
    Walk (arc src dst weight) (atList dst i R) (base (dst i)) R := by
  induction R with
  | nil => exact .nil _
  | cons k R h => exact .step (.rest i k R) h

theorem expand_atom (i : I) :
    Walk (arc src dst weight) (base (src i)) (base (dst i)) (UnitCodes.code (weight i)) := by
  cases h : UnitCodes.code (weight i) with
  | nil => exact False.elim (UnitCodes.nonempty _ h)
  | cons k R => exact .step (.start i h) (tails src dst weight i R)

theorem expand {x y : V} {L : List ℤ} (h : Walk (edge src dst weight) x y L) :
    ∃ C, Walk (arc src dst weight) (base x) (base y) C ∧ C.sum=L.sum := by
  induction h with
  | nil => exact ⟨[],.nil _,rfl⟩
  | @step x y z k L a p ih =>
    obtain ⟨i, rfl, rfl, rfl⟩ := a
    obtain ⟨C,hC,hEq⟩ := ih
    exact ⟨_, append _ (expand_atom src dst weight i) hC,
      by simp [hEq,UnitCodes.total]⟩

theorem zero_iff (x y : V) :
    (∃ L, Walk (edge src dst weight) x y L ∧ L.sum=0) ↔
    (∃ L, Walk (arc src dst weight) (base x) (base y) L ∧ L.sum=0) := by
  constructor
  · rintro ⟨L,w,h⟩
    obtain ⟨C,z,hC⟩ := expand src dst weight w
    exact ⟨C,z,hC.trans h⟩
  · rintro ⟨L,w,h⟩
    obtain ⟨C,z,hC⟩ := compress src dst weight w
    exact ⟨C,z,by simpa [base,debt,h] using hC⟩

end EdgeExpansion

#print axioms EdgeExpansion.zero_iff
