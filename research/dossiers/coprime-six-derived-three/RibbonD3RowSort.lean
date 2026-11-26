import Mathlib.Order.Fin.Basic

namespace RibbonD3RowSort

structure Sorting (n : Nat) where
  ranks : Array Nat
  order : Array Nat

def Sorting.rank {n : Nat} (s : Sorting n) (i : Fin (n+1)) : Fin (n+1) :=
  ⟨s.ranks[i.val]!%(n+1),Nat.mod_lt _ (Nat.zero_lt_succ n)⟩

def Sorting.ord {n : Nat} (s : Sorting n) (i : Fin (n+1)) : Fin (n+1) :=
  ⟨s.order[i.val]!%(n+1),Nat.mod_lt _ (Nat.zero_lt_succ n)⟩

def key {n : Nat} (a b : Array Nat) (p : Fin (n+1)) : Nat := 1000000*a[p.val]!+b[p.val]!

def Valid {n : Nat} (a b : Array Nat) (owner : Fin (n+1) → Nat) (P : Sorting n) : Prop :=
  (∀ i : Fin (n+1), P.ord (P.rank i) = i) ∧
  ∀ i : Fin n,
    let p := P.ord i.castSucc
    let q := P.ord i.succ
    key a b p≤key a b q ∧
      (key a b p=key a b q → owner p=owner q)
instance {n : Nat} (a b : Array Nat) (owner : Fin (n+1) → Nat) (P : Sorting n) : Decidable (Valid a b owner P) := by
  unfold Valid; infer_instance

theorem run_same {n : Nat} {f g : Fin (n+1) → Nat}
    (mon : Monotone f) (next : ∀ j : Fin n,
      f j.castSucc=f j.succ → g j.castSucc=g j.succ)
    (i j : Fin (n+1)) (le : i≤j) (eq : f i=f j) : g i=g j := by
  let Q (v : Nat) := ∀ k : Fin (n+1), k.val=v → i≤k → f i=f k → g i=g k
  have Qn (v : Nat) : Q v := by
    induction v using Nat.strong_induction_on with
    | h v ih =>
      intro k kn ik e
      by_cases h : i=k
      · rw [h]
      · have lo : i.val<k.val := (show i<k from lt_of_le_of_ne ik h)
        have p : k.val-1<n := by have := k.isLt; omega
        let t : Fin n := ⟨k.val-1,p⟩
        have kt : t.succ=k := Fin.ext (by change k.val-1+1=k.val; omega)
        have it : i≤t.castSucc := by change i.val≤k.val-1; omega
        have tk : t.castSucc≤k := by change k.val-1≤k.val; omega
        have k0 : f i=f t.castSucc := le_antisymm (mon it) (e.symm ▸ mon tk)
        have k1 : f t.castSucc=f k := k0.symm.trans e
        exact (ih (k.val-1) (by omega) t.castSucc rfl it k0).trans
          (kt ▸ next t (kt.symm ▸ k1))
  exact Qn j.val j rfl le eq

theorem checked {n : Nat} {a b : Array Nat} {owner : Fin (n+1) → Nat} {P : Sorting n}
    (h : Valid a b owner P)
    (i j : Fin (n+1)) (ea : a[i.val]! = a[j.val]!) (eb : b[i.val]! = b[j.val]!) :
    owner i=owner j := by
  let f (p : Fin (n+1)) := key a b (P.ord p)
  let g (p : Fin (n+1)) := owner (P.ord p)
  have mon : Monotone f := Fin.monotone_iff_le_succ.mpr (fun p => (h.2 p).1)
  have adj (p : Fin n) : f p.castSucc=f p.succ → g p.castSucc=g p.succ :=
    (h.2 p).2
  have ee : f (P.rank i) = f (P.rank j) := by
    change key a b (P.ord (P.rank i)) = key a b (P.ord (P.rank j))
    rw [h.1 i,h.1 j]
    -- The two actual numeric keys have the same chart coordinates.
    simp [key,ea,eb]
  have R : g (P.rank i) = g (P.rank j) := by
    rcases le_total (P.rank i) (P.rank j) with w|w
    · exact run_same mon adj _ _ w ee
    · exact (run_same mon adj _ _ w ee.symm).symm
  change owner (P.ord (P.rank i)) = owner (P.ord (P.rank j)) at R
  rwa [h.1 i,h.1 j] at R

end RibbonD3RowSort
#print axioms RibbonD3RowSort.checked
