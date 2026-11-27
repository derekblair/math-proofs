import HaarK33Haar
import HaarAbelCore

namespace HaarK33Collapse
open HaarAllNoncommuting HaarAbelCore
variable {G Q : Type*} [Group G] [Group Q]

abbrev Grid := Bool × P
def eval (x y u : G) (p : Grid) : G :=
  image x u p.2 * if p.1 then y else 1

def edge3 (p q : Grid) : Prop :=
    q=p ∨
    (q.1=p.1 ∧ q.2=p.2+(if p.1 then (0,1) else (1,0))) ∨
    (p.1=false ∧ q.1=true ∧ q.2=p.2)
instance (p q : Grid) : Decidable (edge3 p q) := by unfold edge3; infer_instance

def edges {n : ℕ} (T : Fin (n+1) → Grid) : Prop :=
  ∀ i : Fin n, if side i.val then edge3 (T ⟨i.val+1,by omega⟩) (T ⟨i.val,by omega⟩)
    else edge3 (T ⟨i.val,by omega⟩) (T ⟨i.val+1,by omega⟩)

def separated {n : ℕ} (T : Fin (n+1) → Grid) (D : List P) : Prop :=
  ∀ i j : Fin n, i=j ∨ side i.val ≠ side j.val ∨
    (T ⟨i.val,by omega⟩).1 ≠ (T ⟨j.val,by omega⟩).1 ∨
    (let d := (T ⟨i.val,by omega⟩).2 - (T ⟨j.val,by omega⟩).2
     d ∈ D ∨ -d ∈ D)

instance {n : ℕ} (T : Fin (n+1) → Grid) : Decidable (edges T) := by unfold edges; infer_instance
instance {n : ℕ} (T : Fin (n+1) → Grid) (D : List P) : Decidable (separated T D) := by unfold separated; infer_instance

theorem transport (x y u : G) (c : Commute x u) (rel : y*x=u*y) {p q : Grid}
    (e : edge3 p q) : eval x y u q=eval x y u p ∨
      eval x y u q=eval x y u p*x ∨ eval x y u q=eval x y u p*y := by
  rcases e with rfl|⟨h,he⟩|⟨a,b,h⟩
  · exact Or.inl rfl
  · apply Or.inr; apply Or.inl
    unfold eval
    rw [h,he,image_add x u c]
    cases e : p.1
    · simp [e,image]
    · simp only [e,if_true]
      have t : image x u (0,1)=u := by simp [image]
      rw [t]
      simp only [mul_assoc,rel]
  · right; right
    simp [eval,a,b,h]

theorem opposite (f : G →* Q) (x y u : G) (hx : f x=1) (hu : f u=1) (hy : f y≠1)
    (p q : Grid) (e : eval x y u p=eval x y u q) : p.1=q.1 := by
  have ee := congrArg f e
  simp only [eval,image,map_mul,map_zpow,hx,hu,one_zpow,one_mul] at ee
  cases a : p.1 <;> cases b : q.1 <;> simp [a,b] at ee ⊢
  · exact (hy ee.symm).elim
  · exact (hy ee).elim

theorem table {n : ℕ} (np : 0<n) (even : n%2=0)
    (f : G →* Q) (x y u : G) (c : Commute x u) (rel : y*x=u*y)
    (hx : f x=1) (hu : f u=1) (hy : f y≠1)
    (T : Fin (n+1) → Grid) (D : List P)
    (edge : edges T) (sep : separated T D)
    (close : eval x y u (T ⟨n,by omega⟩)=eval x y u (T ⟨0,by omega⟩))
    (safe : ∀ d∈D, ¬R x u d) : HasCycle x y n := by
  let g (i : Fin n) := (side i.val,eval x y u (T ⟨i.val,by omega⟩))
  refine ⟨g,?_,?_⟩
  · intro i j H
    rcases sep i j with z|z|z|z
    · exact z
    · exact False.elim (z (congrArg Prod.fst H))
    · exact False.elim (z (opposite f x y u hx hu hy _ _ (congrArg Prod.snd H)))
    · let p := T ⟨i.val,by omega⟩
      let q := T ⟨j.val,by omega⟩
      have eq : eval x y u p = eval x y u q := congrArg Prod.snd H
      have a := opposite f x y u hx hu hy p q eq
      have e : image x u p.2 = image x u q.2 := by
        unfold eval at eq
        rw [a] at eq
        exact mul_right_cancel eq
      have hh := diffR x u c p.2 q.2 e
      exact False.elim (z.elim (fun m => safe _ m hh) (fun m => safe _ m (negR x u c _ hh)))
  · intro i
    have hv : (g ⟨(i.val+1)%n,Nat.mod_lt _ np⟩).2 = eval x y u (T ⟨i.val+1,by omega⟩) := by
      by_cases h : i.val+1<n
      · simp [g,Nat.mod_eq_of_lt h]
      · have eq : i.val+1=n := by omega
        simp only [g,eq,Nat.mod_self]
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
    have hsa : (g ⟨(i.val+1)%n,Nat.mod_lt _ np⟩).1= !(side i.val) := hs
    unfold HaarCycle.haarAdj
    change (if side i.val then _ else _)
    rw [hsa,hv]
    cases h : side i.val
    · simp [h] at e ⊢
      exact transport x y u c rel e
    · simp [h] at e ⊢
      exact transport x y u c rel e
end HaarK33Collapse
