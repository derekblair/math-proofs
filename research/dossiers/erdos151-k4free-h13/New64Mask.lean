import New64Input
namespace Erdos151Ramsey.New64
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def adj (a b : Fin 64) : Bool := masks[a.val]!.testBit b.val

def graph (a b : Fin 64) : Prop := adj a b = true

instance graph_dec : DecidableRel graph := fun a b => inferInstanceAs (Decidable (adj a b = true))

def vv (m : Nat) : Finset (Fin 64) :=
  Finset.univ.filter fun v => m.testBit v.val

def removes (v : Fin 64) : Nat :=
  18446744073709551615 ^^^ (1 <<< v.val)

def notAdjacent (v : Fin 64) : Nat :=
  18446744073709551615 ^^^ masks[v.val]!

lemma removes_spec (x v : Fin 64) : (removes x).testBit v.val = decide (x ≠ v) := by
  have h : v.val < 64 := v.isLt
  have E : (18446744073709551615 : Nat) = 2^64-1 := rfl
  simp only [removes, Nat.testBit_xor, E, Nat.testBit_two_pow_sub_one, h, decide_true,
    Nat.testBit_shiftLeft]
  by_cases he : x=v
  · subst v; simp
  · have he' : x.val ≠ v.val := fun h => he (Fin.ext h)
    by_cases ho : x.val ≤ v.val
    · have hz : (1 : Nat).testBit (v.val-x.val) = false := by
        apply Bool.eq_false_iff.mpr
        intro tb
        have eq := Nat.testBit_one_eq_true_iff_self_eq_zero.mp tb
        omega
      simp [ho, he, hz]
    · simp [ho, he]

lemma notAdjacent_spec : ∀ x v : Fin 64, (notAdjacent x).testBit v.val = !adj x v := by
  intro x v
  have E : (18446744073709551615 : Nat) = 2^64-1 := rfl
  simp only [notAdjacent, adj, Nat.testBit_xor, E, Nat.testBit_two_pow_sub_one, v.isLt, decide_true]
  cases masks[x.val]!.testBit v.val <;> rfl

def extra : Fin 64 := 63

def checkRoot : Nat := removes extra &&& notAdjacent extra

def popN : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,m => m%2 + popN n (m/2)

lemma popN_n (n m : Nat) :
    popN n m = ((List.range n).filter (fun v=>m.testBit v)).length := by
  induction n generalizing m with
  | zero => simp [popN]
  | succ n ih =>
    rw [popN, ih, List.range_succ_eq_map, List.filter_cons, List.filter_map]
    have T : ((fun v => m.testBit v) ∘ Nat.succ) = fun v => (m/2).testBit v := by
      funext v
      exact Nat.testBit_succ m v
    simp [T, Nat.testBit_zero]
    by_cases h:m%2=0
    · simp [h]
    · have h1:m%2=1 := by omega
      simp [h1, Nat.add_comm]

lemma pop_card (m : Nat) : (vv m).card = popN 64 m := by
  rw [popN_n]
  unfold vv
  have L : (List.finRange 64).map Fin.val = List.range 64 := by decide +kernel
  rw [← L, List.filter_map, List.length_map]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 64).filter _)]
  congr 1
  ext v
  simp [Finset.mem_univ]

def leafCheck : List (Fin 64 × Fin 64) → Nat → Nat → Bool
  | [], m, k => decide (popN 64 m < k)
  | (a,b)::ls, m, k => adj a b && leafCheck ls (m &&& removes a &&& removes b) (k-1)

lemma leaf_sound (ls : List (Fin 64 × Fin 64)) (m k : Nat)
    (ok : leafCheck ls m k = true) :
    ∀ S : Finset (Fin 64), S ⊆ vv m → Independent graph S → S.card < k := by
  induction ls generalizing m k with
  | nil =>
    intro S h _
    refine (Finset.card_le_card h).trans_lt ?_
    simpa [leafCheck, pop_card] using ok
  | cons p ls ih =>
    rcases p with ⟨a,b⟩
    intro S h ind
    simp only [leafCheck, Bool.and_eq_true] at ok
    obtain ⟨edge, verified⟩ := ok
    let T := (S.erase a).erase b
    have sub : T ⊆ vv (m &&& removes a &&& removes b) := by
      intro x hx
      obtain ⟨xb,hx⟩ := Finset.mem_erase.mp hx
      obtain ⟨xa,hx⟩ := Finset.mem_erase.mp hx
      have one : m.testBit x.val = true := (Finset.mem_filter.mp (h hx)).2
      simp [vv, removes_spec, one, xa.symm, xb.symm]
    have ti : Independent graph T :=
      fun x hx y hy => ind x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
        y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
    have bound := ih _ _ verified T sub ti
    by_cases ha : a ∈ S
    · have hb : b ∉ S := fun hb=>ind a ha b hb edge
      have hb' : b ∉ S.erase a := fun hb' => hb (Finset.mem_of_mem_erase hb')
      have te : T = S.erase a := Finset.erase_eq_of_notMem hb'
      rw [te] at bound
      have hc := Finset.card_erase_add_one ha
      omega
    · have te : T = S.erase b := by simp [T, Finset.erase_eq_of_notMem ha]
      rw [te] at bound
      by_cases hb : b ∈ S
      · have hc := Finset.card_erase_add_one hb
        omega
      · rw [Finset.erase_eq_of_notMem hb] at bound
        omega

inductive Plan where
  | leaf (edges : List (Fin 64 × Fin 64))
  | step (vertex : Fin 64) (yes no : Plan)

def check : Plan → Nat → Nat → Bool
  | .leaf es, m, k => leafCheck es m k
  | .step x a b, m, k =>
    ((m.testBit x.val) &&
     check a (m &&& removes x &&& notAdjacent x) (k-1) &&
     check b (m &&& removes x) k)

lemma check_combine {v : Fin 64} {l r : Plan} {m k : Nat}
    (mv : m.testBit v.val = true)
    (hc : check l (m &&& removes v &&& notAdjacent v) (k-1) = true)
    (he : check r (m &&& removes v) k = true) :
    check (.step v l r) m k = true := by
  simp [check, mv, hc, he]

theorem check_sound (s : Plan) (m k : Nat) (ok : check s m k = true) :
    ∀ S : Finset (Fin 64), S ⊆ vv m → Independent graph S → S.card < k := by
  induction s generalizing m k with
  | leaf es => exact leaf_sound es m k ok
  | step v l r il ir =>
    intro S h ind
    simp only [check, Bool.and_eq_true] at ok
    obtain ⟨⟨_, lc⟩, rc⟩ := ok
    by_cases hv : v∈S
    · have inc : S.erase v ⊆ vv (m &&& removes v &&& notAdjacent v) := by
        intro x hx
        obtain ⟨ne,hx⟩ := Finset.mem_erase.mp hx
        have one : m.testBit x.val = true := (Finset.mem_filter.mp (h hx)).2
        have two : adj v x = false := Bool.eq_false_iff.mpr (ind v hv x hx)
        simpa [vv, removes_spec, notAdjacent_spec, one, two, ne.symm]
      have ii : Independent graph (S.erase v) :=
        fun a ha b hb => ind a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
      have hc := il _ _ lc _ inc ii
      have eq := Finset.card_erase_add_one hv
      omega
    · have exc : S ⊆ vv (m &&& removes v) := by
        intro x hx
        have one : m.testBit x.val = true := (Finset.mem_filter.mp (h hx)).2
        have ne : v ≠ x := fun e=>hv (e ▸ hx)
        simpa [vv, removes_spec, one, ne]
      exact ir _ _ rc S exc ind

end Erdos151Ramsey.New64
