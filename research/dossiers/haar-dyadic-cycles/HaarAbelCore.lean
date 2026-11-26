import HaarAllNoncommuting
namespace HaarAbelCore
open HaarAllNoncommuting HaarCycle
abbrev P := ℤ × ℤ
variable {G : Type*} [Group G]
def image (x y : G) (p : P) := y^p.2*x^p.1
def R (x y : G) (p : P) : Prop := image x y p=1

theorem image_zero (x y : G) : image x y (0:P)=1 := by simp [image]
theorem image_add (x y : G) (c : Commute x y) (p q : P) :
    image x y (p+q)=image x y p*image x y q := by
  simp only [image,Prod.fst_add,Prod.snd_add,zpow_add]
  have h := ((c.zpow_left p.1).zpow_right q.2).eq
  calc
    y ^ p.2 * y ^ q.2 * (x ^ p.1 * x ^ q.1) =
      y ^ p.2 * (y ^ q.2 * x ^ p.1) * x ^ q.1 := by simp [mul_assoc]
    _ = _ := by rw [← h]; simp [mul_assoc]

theorem diffR (x y : G) (h : Commute x y) (p q : P)
    (he : image x y p=image x y q) : R x y (p-q) := by
  have k : p-q+q=p := sub_add_cancel p q
  have n := image_add x y h (p-q) q
  rw [k,he] at n
  unfold R
  exact mul_right_cancel (show image x y (p-q)*image x y q = 1*image x y q by simpa using n.symm)

theorem negR (x y : G) (h : Commute x y) (p : P) (hp : R x y p) : R x y (-p) := by
  have k := image_add x y h (-p) p
  rw [neg_add_cancel,image_zero] at k
  unfold R at hp ⊢
  simpa [hp] using k.symm

theorem addR (x y : G) (h : Commute x y) (p q : P) (hp : R x y p) (hq : R x y q) :
    R x y (p+q) := by unfold R at *; simp [image_add x y h,hp,hq]
theorem subR (x y : G) (h : Commute x y) (p q : P) (hp : R x y p) (hq : R x y q) :
    R x y (p-q) := by
  rw [sub_eq_add_neg]
  exact addR x y h p (-q) hp (negR x y h q hq)
theorem natR (x y : G) (h : Commute x y) (p : P) (hp : R x y p) (n : ℕ) :
    R x y (n • p) := by
  induction n with
  | zero => simpa [R] using image_zero x y
  | succ n ih =>
    rw [succ_nsmul]
    exact addR x y h (n•p) p ih hp

theorem zR (x y : G) (h : Commute x y) (p : P) (hp : R x y p) (i : ℤ) :
    R x y (i • p) := by
  cases i with
  | ofNat n => exact natR x y h p hp n
  | negSucc n =>
    rw [show Int.negSucc n = -((n+1):ℕ) by simp [Int.negSucc_eq]]
    rw [neg_smul]
    exact negR x y h _ (natR x y h p hp (n+1))

def adj2 (p q : P) : Prop := q=p ∨ q=p+(1,0) ∨ q=p+(0,1)
instance (p q : P) : Decidable (adj2 p q) := by unfold adj2; infer_instance
def side (j : ℕ) : Bool := decide (j%2=1)

def edge_ok {n : ℕ} (V : Fin (n+1) → P) : Prop :=
  ∀ i : Fin n,
    if side i.val then adj2 (V ⟨i.val+1,by omega⟩) (V ⟨i.val,by omega⟩)
    else adj2 (V ⟨i.val,by omega⟩) (V ⟨i.val+1,by omega⟩)

def sep_ok {n : ℕ} (V : Fin (n+1) → P) (D : List P) : Prop :=
  ∀ i j : Fin n, i=j ∨ side i.val ≠ side j.val ∨
    (let d := V ⟨i.val,by omega⟩ - V ⟨j.val,by omega⟩
     d ∈ D ∨ -d ∈ D)

instance {n : ℕ} (V : Fin (n+1) → P) : Decidable (edge_ok V) := by unfold edge_ok; infer_instance
instance {n : ℕ} (V : Fin (n+1) → P) (D : List P) : Decidable (sep_ok V D) := by unfold sep_ok; infer_instance

theorem chain {n : ℕ} (np : 0<n) (even : n%2=0)
    (x y : G) (c : Commute x y) (V : Fin (n+1) → P) (D : List P)
    (edge : edge_ok V) (sep : sep_ok V D)
    (close : image x y (V ⟨n,by omega⟩)=image x y (V ⟨0,by omega⟩))
    (safe : ∀ d∈D, ¬R x y d) : HasCycle x y n := by
  let f (i : Fin n) := (side i.val,image x y (V ⟨i.val,by omega⟩))
  have transfer {p q : P} (e : adj2 p q) :
      image x y q=image x y p ∨ image x y q=image x y p*x ∨ image x y q=image x y p*y := by
    rcases e with rfl|rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (by rw [image_add x y c]; simp [image]))
    · exact Or.inr (Or.inr (by rw [image_add x y c]; simp [image]))
  refine ⟨f,?_,?_⟩
  · intro i j H
    rcases sep i j with z|z|z
    · exact z
    · exact False.elim (z (congrArg Prod.fst H))
    · let p := V ⟨i.val,by omega⟩
      let q := V ⟨j.val,by omega⟩
      have hh := diffR x y c p q (congrArg Prod.snd H)
      exact False.elim (z.elim (fun m => safe _ m hh) (fun m => safe _ m (negR x y c _ hh)))
  · intro i
    have hv : (f ⟨(i.val+1)%n,Nat.mod_lt _ np⟩).2 =
        image x y (V ⟨i.val+1,by omega⟩) := by
      by_cases h : i.val+1<n
      · simp [f,Nat.mod_eq_of_lt h]
      · have eq : i.val+1=n := by omega
        simp only [f,eq,Nat.mod_self]
        exact close.symm
    have hs : side ((i.val+1)%n)= !(side i.val) := by
      by_cases h : i.val+1<n
      · rw [Nat.mod_eq_of_lt h]
        unfold side
        by_cases g : i.val%2=1
        · have k : (i.val+1)%2 ≠1 := by omega
          simp [g,k]
        · have k : (i.val+1)%2=1 := by omega
          simp [g,k]
      · have eq : i.val+1=n := by omega
        have g : i.val%2=1 := by omega
        simp [eq,side,g]
    have e := edge i
    change (if side i.val then _ else _) at e
    have hsa : (f ⟨(i.val+1)%n,Nat.mod_lt _ np⟩).1= !(side i.val) := hs
    unfold haarAdj
    change (if side i.val then _ else _)
    rw [hsa,hv]
    cases h : side i.val
    · simp [h] at e ⊢
      exact transfer e
    · simp [h] at e ⊢
      exact transfer e
end HaarAbelCore
#print axioms HaarAbelCore.chain
