import HaarDerivedGirth22

namespace HaarDerivedTrie
inductive Trie where
  | empty
  | leaf
  | node (a b : Trie)

def Trie.lookup : ℕ → Trie → ℕ → Bool
  | _, .empty, _ => false
  | _, .leaf, _ => true
  | 0, .node _ _, _ => false
  | n+1, .node a b, k => if k%2=0 then a.lookup n (k/2) else b.lookup n (k/2)

def Trie.ins : ℕ → Trie → ℕ → Trie
  | 0, _, _ => .leaf
  | _+1, .leaf, _ => .leaf
  | n+1, .empty, k =>
    if k%2=0 then .node (ins n .empty (k/2)) .empty else .node .empty (ins n .empty (k/2))
  | n+1, .node a b,k =>
    if k%2=0 then .node (a.ins n (k/2)) b else .node a (b.ins n (k/2))

theorem Trie.lookup_ins_self (n : ℕ) (a : Trie) (k : ℕ) :
    (a.ins n k).lookup n k = true := by
  induction n generalizing a k with
  | zero => rfl
  | succ n ih =>
    cases a <;> by_cases h : k%2=0 <;> simp [Trie.ins,Trie.lookup,h,ih]

theorem Trie.lookup_ins_preserve (n : ℕ) (a : Trie) (k j : ℕ)
    (h : a.lookup n j=true) : (a.ins n k).lookup n j=true := by
  induction n generalizing a k j with
  | zero => rfl
  | succ n ih =>
    cases a with
    | empty => simp [Trie.lookup] at h
    | leaf => rfl
    | node u v =>
      by_cases hk : k%2=0 <;> by_cases hj : j%2=0 <;>
      simp [Trie.ins,Trie.lookup,hk,hj] at h ⊢ <;> first | exact h | exact ih _ _ _ h

def ok (depth : ℕ) (t : Trie) : List ℕ → Bool
  | [] => true
  | k::ks => !t.lookup depth k && ok depth (t.ins depth k) ks

theorem avoids (depth : ℕ) (t : Trie) (xs : List ℕ) (h : ok depth t xs=true) :
    ∀ k ∈ xs, t.lookup depth k=false := by
  induction xs generalizing t with
  | nil => simp
  | cons x xs ih =>
    simp only [ok,Bool.and_eq_true] at h
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · cases e : t.lookup depth k <;> simp_all
    · have m := ih _ h.2 k hk
      cases e : t.lookup depth k
      · rfl
      · have q := t.lookup_ins_preserve depth x k e
        rw [q] at m; contradiction

theorem nodup (depth : ℕ) (t : Trie) (xs : List ℕ) (h : ok depth t xs=true) : xs.Nodup := by
  induction xs generalizing t with
  | nil => simp
  | cons x xs ih =>
    simp only [ok,Bool.and_eq_true] at h
    refine List.nodup_cons.mpr ⟨?_,ih _ h.2⟩
    intro e
    have g := avoids depth (t.ins depth x) xs h.2 x e
    rw [Trie.lookup_ins_self] at g
    contradiction

end HaarDerivedTrie

namespace HaarDerivedGirth22
open HaarSharpPortGeometry
open HaarSharpLamp (Row words compatible compat_members)
def trieCheck (n : ℕ) : Bool :=
  HaarDerivedTrie.ok 68 .empty (((words n none).map row).map Row.k)
theorem cert_trie {n : ℕ} (h : trieCheck n=true) {u v : List (Fin 3)}
    (hu : u ∈ words n none) (hv : v ∈ words n none)
    (he : value port true u = value port true v) :
    u.head? = v.head? ∨ u.getLast? = v.getLast? := by
  have nd := HaarDerivedTrie.nodup 68 .empty (((words n none).map row).map Row.k) h
  rw [List.Nodup,List.pairwise_map] at nd
  have comp : ((words n none).map row).Pairwise compatible := by
    refine nd.imp ?_
    intro a b e
    exact Or.inl e
  have c := compat_members comp (List.mem_map.mpr ⟨u,hu,rfl⟩) (List.mem_map.mpr ⟨v,hv,rfl⟩)
  simpa [compatible,row,he] using c
end HaarDerivedGirth22
#print axioms HaarDerivedGirth22.cert_trie
