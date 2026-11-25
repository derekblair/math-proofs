import Counts
import Mathlib.Data.Fin.Tuple.Basic

namespace CoverCutoff

def nVerts (k step j : ℕ) : ℕ := k+(j-1)*step

def window {k step j : ℕ} (t : Fin j) (i : Fin k) : Fin (nVerts k step j) :=
  ⟨t.val*step+i.val,by
    have ht : t.val≤j-1 := by omega
    have hm := Nat.mul_le_mul_right step ht
    unfold nVerts
    omega⟩

def Packs {k : ℕ} (p : Equiv.Perm (Fin k)) (step j : ℕ)
    (r : Equiv.Perm (Fin (nVerts k step j))) : Prop :=
  ∀ t : Fin j, ∀ a b : Fin k, (r (window t a)<r (window t b) ↔ p a<p b)

/-- Each edge is an immediate comparison in the inverse pattern order. -/
def edges {k : ℕ} (inv : Fin (k+1)→Fin (k+1)) (step j : ℕ)
    (a b : Fin (nVerts (k+1) step j)) : Bool :=
  (List.finRange j).any fun t =>
    (List.finRange k).any fun i =>
      a == (window t (inv i.castSucc)) && b == (window t (inv i.succ))

lemma edges_iff {k : ℕ} (inv : Fin (k+1)→Fin (k+1)) (step j : ℕ)
    (a b : Fin (nVerts (k+1) step j)) :
    edges inv step j a b = true ↔
      ∃ (t : Fin j) (i : Fin k), a=window t (inv i.castSucc) ∧ b=window t (inv i.succ) := by
  simp [edges,List.any_eq_true]

lemma edges_irreflexive {k : ℕ} (inv : Fin (k+1)→Fin (k+1))
    (hi : Function.Injective inv) (step j : ℕ) :
    ∀ a, edges inv step j a a = false := by
  intro a
  apply Bool.eq_false_iff.mpr
  intro he
  obtain ⟨t,i,h1,h2⟩ := (edges_iff inv step j _ _).mp he
  have h := congrArg Fin.val (h1.symm.trans h2)
  change t.val*step + (inv i.castSucc).val = t.val*step + (inv i.succ).val at h
  have hv : (inv i.castSucc).val = (inv i.succ).val := Nat.add_left_cancel h
  have heq : i.castSucc = i.succ := hi (Fin.ext hv)
  exact (ne_of_lt (Fin.castSucc_lt_succ (i := i))) heq

lemma packs_rankOK {k : ℕ} (p : Equiv.Perm (Fin (k+1))) (step j : ℕ)
    (r : Equiv.Perm (Fin (nVerts (k+1) step j))) :
    Packs p step j r ↔ RankOK (edges p.symm step j) r := by
  constructor
  · intro h a b he
    obtain ⟨t,i,rfl,rfl⟩ := (edges_iff p.symm step j _ _).mp he
    apply (h t _ _).mpr
    simpa only [Equiv.apply_symm_apply] using (Fin.castSucc_lt_succ (i := i))
  · intro h t a b
    let f : Fin (k+1)→Fin (nVerts (k+1) step j) := fun i => r (window t (p.symm i))
    have hf : StrictMono f := Fin.strictMono_iff_lt_succ.mpr (fun i => by
      apply h
      exact (edges_iff p.symm step j _ _).mpr ⟨t,i,rfl,rfl⟩)
    simpa only [f,Equiv.symm_apply_apply] using (hf.lt_iff_lt (a:=p a) (b:=p b))

noncomputable def packCount {k : ℕ} (p : Equiv.Perm (Fin k)) (step j : ℕ) : ℕ :=
  Nat.card {r : Equiv.Perm (Fin (nVerts k step j)) // Packs p step j r}

theorem pack_count_exec {k : ℕ} (p : Equiv.Perm (Fin (k+1))) (step j : ℕ) :
    packCount p step j =
      countSearch (edges p.symm step j) (nVerts (k+1) step j) (List.finRange _) := by
  unfold packCount
  let e := Equiv.subtypeEquivRight (fun r => packs_rankOK p step j r)
  rw [Nat.card_congr e]
  rw [rank_count _ (edges_irreflexive p.symm p.symm.injective _ _),countSearch_eq]
  rfl

#print axioms pack_count_exec
end CoverCutoff
