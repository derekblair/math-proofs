import RibbonOrderThreeAff
import Mathlib.Order.Fin.Basic

namespace RibbonOddRowSort
open RibbonStationaryWord

def owner (s : Spec) (i : Fin 64) : Nat :=
  if ((32 : Nat) ≤ i.val ∧ IsMate s (i.val - 32) i.val) then i.val - 32 else i.val

theorem owner_sound (s : Spec) (i j : Fin 64) (lt : i.val<j.val)
    (h : owner s i=owner s j) : IsMate s i.val j.val := by
  unfold owner at h
  split at h <;> split at h
  · omega
  · omega
  · rename_i _ a
    obtain ⟨_,m⟩ := a
    rwa [←h] at m
  · omega

structure Sorting where
  rank : Array (Fin 64)
  ord : Array (Fin 64)

def key (a b : Array Nat) (p : Fin 64) : Nat := 1000000*a[p.val]!+b[p.val]!

def Valid (a b : Array Nat) (s : Spec) (P : Sorting) : Prop :=
  (∀ i : Fin 64, P.ord[(P.rank[i.val]!).val]! = i) ∧
  ∀ i : Fin 63,
    let p := P.ord[i.val]!
    let q := P.ord[i.val+1]!
    key a b p≤key a b q ∧
      (key a b p=key a b q → owner s p=owner s q)
instance (a b : Array Nat) (s : Spec) (P : Sorting) : Decidable (Valid a b s P) := by
  unfold Valid; infer_instance

theorem run_same {f g : Fin 64 → Nat}
    (mon : Monotone f) (next : ∀ j : Fin 63,
      f j.castSucc=f j.succ → g j.castSucc=g j.succ)
    (i j : Fin 64) (le : i≤j) (eq : f i=f j) : g i=g j := by
  let Q (n : Nat) := ∀ k : Fin 64, k.val=n → i≤k → f i=f k → g i=g k
  have Qn (n : Nat) : Q n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k kn ik e
      by_cases h : i=k
      · rw [h]
      · have lo : i.val<k.val := (show i<k from lt_of_le_of_ne ik h)
        have p : k.val-1<63 := by have := k.isLt; omega
        let t : Fin 63 := ⟨k.val-1,p⟩
        have kt : t.succ=k := Fin.ext (by change k.val-1+1=k.val; omega)
        have it : i≤t.castSucc := by change i.val≤k.val-1; omega
        have tk : t.castSucc≤k := by change k.val-1≤k.val; omega
        have k0 : f i=f t.castSucc := le_antisymm (mon it) (e.symm ▸ mon tk)
        have k1 : f t.castSucc=f k := k0.symm.trans e
        exact (ih (k.val-1) (by omega) t.castSucc rfl it k0).trans
          (kt ▸ next t (kt.symm ▸ k1))
  exact Qn j.val j rfl le eq

theorem checked {a b : Array Nat} {s : Spec} {P : Sorting} (h : Valid a b s P)
    (i j : Fin 64) (lt : i.val<j.val) (ea : a[i.val]! = a[j.val]!) (eb : b[i.val]! = b[j.val]!) :
    IsMate s i.val j.val := by
  apply owner_sound s i j lt
  let f (p : Fin 64) := key a b (P.ord[p.val]!)
  let g (p : Fin 64) := owner s (P.ord[p.val]!)
  have mon : Monotone f := Fin.monotone_iff_le_succ.mpr (fun p => (h.2 p).1)
  have adj (p : Fin 63) : f p.castSucc=f p.succ → g p.castSucc=g p.succ :=
    (h.2 p).2
  have ee : f P.rank[i.val]! = f P.rank[j.val]! := by
    change key a b P.ord[P.rank[i.val]!.val]! = key a b P.ord[P.rank[j.val]!.val]!
    rw [h.1 i,h.1 j]
    -- The two actual numeric keys have the same chart coordinates.
    simp [key,ea,eb]
  have R : g P.rank[i.val]! = g P.rank[j.val]! := by
    rcases le_total P.rank[i.val]! P.rank[j.val]! with w|w
    · exact run_same mon adj _ _ w ee
    · exact (run_same mon adj _ _ w ee.symm).symm
  change owner s P.ord[P.rank[i.val]!.val]! = owner s P.ord[P.rank[j.val]!.val]! at R
  rwa [h.1 i,h.1 j] at R

end RibbonOddRowSort
#print axioms RibbonOddRowSort.checked
