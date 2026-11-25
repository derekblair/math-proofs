import TreeInfluenceScopes

namespace TreeInfluence
open SimpleGraph
universe u
variable {V : Type u} [DecidableEq V]

noncomputable def restrict (G : SimpleGraph V) (k : Nat) (S : Finset V) (u : V) : Finset V :=
  S.filter fun v => G.dist u v ≤ k

theorem restrict_eq_ball [Fintype V] (G : SimpleGraph V) (k : Nat) (S : Finset V) (u : V) :
    restrict G k S u = S ∩ ball G k u := by
  ext v
  simp [restrict, ball]

noncomputable def intrinsic (G : SimpleGraph V) (k : Nat) (S : Finset V) (u : V) :
    Finset V := if h : u ∈ S then
  (S.attach.filter fun v => (G.induce (S : Set V)).dist ⟨u,h⟩ ⟨v.val,v.property⟩ ≤ k).image
    Subtype.val
  else ∅

theorem intrinsic_eq_restrict [Fintype V] {G : SimpleGraph V} (ht : G.IsTree)
    (k : Nat) {S : Finset V} (hS : S ∈ scopes G k) {u : V} (hu : u ∈ S) :
    intrinsic G k S u = restrict G k S u := by
  unfold intrinsic
  rw [dif_pos hu]
  ext v
  simp only [restrict, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and]
  refine ⟨?_,?_⟩
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w.property, (scopeDist ht k hS ⟨u,hu⟩ ⟨w.val,w.property⟩) ▸ hw⟩
  · rintro ⟨hv,hw⟩
    exact ⟨⟨v,hv⟩, (scopeDist ht k hS ⟨u,hu⟩ ⟨v,hv⟩).symm ▸ hw, rfl⟩

/-- Algorithm 2's largest feasible count. Scanning from |S| instead of
    |S_sub| + |S_eql| cannot add a feasible candidate. -/
def combine (child : Finset V → V → Finset V) (threshold : V → Nat)
    (S : Finset V) (value : Finset V → Nat) : Nat :=
  (((List.range (S.card + 1)).reverse.find? fun i =>
    i ≤ (S.filter fun u =>
      if child S u ⊂ S then threshold u ≤ value (child S u) else threshold u ≤ i).card)).getD 0

theorem intrinsic_subset (G : SimpleGraph V) (k : Nat) (S : Finset V) (u : V) :
    intrinsic G k S u ⊆ S := by
  unfold intrinsic
  split
  · intro v hv
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
    exact w.property
  · simp

theorem combine_congr {c₁ c₂ : Finset V → V → Finset V} {v₁ v₂ : Finset V → Nat}
    {S : Finset V} (threshold : V → Nat)
    (he : ∀ u ∈ S, c₁ S u = c₂ S u)
    (hv : ∀ u ∈ S, c₁ S u ⊂ S → v₁ (c₁ S u) = v₂ (c₁ S u)) :
    combine c₁ threshold S v₁ = combine c₂ threshold S v₂ := by
  unfold combine
  have hh (i : Nat) : (S.filter fun u => if c₁ S u ⊂ S then threshold u ≤ v₁ (c₁ S u) else threshold u ≤ i) =
    (S.filter fun u => if c₂ S u ⊂ S then threshold u ≤ v₂ (c₂ S u) else threshold u ≤ i) := by
    ext u
    simp only [Finset.mem_filter]
    by_cases hu : u ∈ S
    · simp only [hu, true_and, ← he u hu]
      by_cases hlt : c₁ S u ⊂ S
      · simp [hlt,hv u hu hlt]
      · simp [hlt]
    · simp [hu]
  simp_rw [hh]

private theorem findReverseRangeBound (p : Nat → Bool) {m : Nat}
    (h : ∀ i, m < i → p i = false) :
    ∀ n, m ≤ n →
      ((List.range (n + 1)).reverse.find? p) =
        ((List.range (m + 1)).reverse.find? p) := by
  intro n
  induction n with
  | zero =>
    intro hm
    have he : m = 0 := by omega
    subst m
    rfl
  | succ n ih =>
    intro hm
    by_cases he : m = n + 1
    · subst m; rfl
    have hx : m < n + 1 := by omega
    simpa only [@List.range_succ (n + 1), List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.find?_cons, h _ hx, Bool.false_eq_true, ↓reduceIte] using
      ih (by omega)

/-- Exact counting phase as printed: the proper children contributing r are
    P, and the equivalent children are E. The first successful count is the
    same whether the scan begins at |P| + |E| or at |S|. -/
theorem combine_literal (child : Finset V → V → Finset V) (threshold : V → Nat)
    (S : Finset V) (val : Finset V → Nat) :
    let P := S.filter fun u => child S u ⊂ S ∧ threshold u ≤ val (child S u)
    let E := S.filter fun u => ¬ child S u ⊂ S
    combine child threshold S val =
      (((List.range (P.card + E.card + 1)).reverse.find? fun i =>
        i ≤ P.card + (E.filter fun u => threshold u ≤ i).card)).getD 0 := by
  dsimp only
  let P := S.filter fun u => child S u ⊂ S ∧ threshold u ≤ val (child S u)
  let E := S.filter fun u => ¬ child S u ⊂ S
  change combine child threshold S val =
    (((List.range (P.card + E.card + 1)).reverse.find? fun i =>
      i ≤ P.card + (E.filter fun u => threshold u ≤ i).card)).getD 0
  have hd : Disjoint P E := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    exact (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hu).2.1
  have hb : P.card + E.card ≤ S.card := by
    rw [← Finset.card_union_of_disjoint hd]
    exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hcount (i : Nat) :
      (S.filter fun u =>
        if child S u ⊂ S then threshold u ≤ val (child S u) else threshold u ≤ i).card =
      P.card + (E.filter fun u => threshold u ≤ i).card := by
    have hset : (S.filter fun u =>
        if child S u ⊂ S then threshold u ≤ val (child S u) else threshold u ≤ i) =
        P ∪ E.filter (fun u => threshold u ≤ i) := by
      ext u
      by_cases hu : u ∈ S <;> by_cases h : child S u ⊂ S <;> simp [P,E,hu,h]
    rw [hset,Finset.card_union_of_disjoint (hd.mono_right (Finset.filter_subset _ _))]
  unfold combine
  simp_rw [hcount]
  rw [findReverseRangeBound _ (m := P.card + E.card) (n := S.card) _ hb]
  intro i hi
  have h := Finset.card_filter_le (s := E) (p := fun u => threshold u ≤ i)
  exact decide_eq_false (by omega)

/-- Direct well-founded interpretation of the article's proper-subview recursion. -/
def recursive (child : Finset V → V → Finset V) (threshold : V → Nat) (S : Finset V) : Nat :=
  combine child threshold S (fun T =>
    if _h : T.card < S.card then recursive child threshold T else 0)
termination_by S.card

def lookup (S : Finset V) : List (Finset V × Nat) → Nat
  | [] => 0
  | (T,v) :: tail => if S = T then v else lookup S tail

theorem lookup_batch (S : Finset V) (B : List (Finset V)) (val : Finset V → Nat)
    (old : List (Finset V × Nat)) :
    lookup S (B.map (fun T => (T,val T)) ++ old) =
      if S ∈ B then val S else lookup S old := by
  induction B with
  | nil => simp
  | cons head tail ih =>
    by_cases h : S = head <;> simp [lookup,ih,h]

/-- Materialized bottom-up table. Pass m fills keys of cardinality strictly below m. -/
def table (K : List (Finset V)) (child : Finset V → V → Finset V)
    (threshold : V → Nat) : Nat → List (Finset V × Nat)
  | 0 => []
  | m+1 =>
    let prev := table K child threshold m
    let bucket := K.filter fun T => T.card == m
    bucket.map (fun T => (T,combine child threshold T fun U => lookup U prev)) ++ prev

theorem tableLength (K : List (Finset V)) (child : Finset V → V → Finset V)
    (threshold : V → Nat) (m : Nat) :
    (table K child threshold m).length = (K.filter fun T => T.card < m).length := by
  induction m with
  | zero => simp [table]
  | succ m ih =>
    simp only [table, List.length_append, List.length_map, ih]
    clear ih
    induction K with
    | nil => simp
    | cons hd tl step =>
      by_cases hlt : hd.card < m
      · have hne : hd.card ≠ m := by omega
        have hsucc : hd.card ≤ m := by omega
        simp [hlt,hne,hsucc] at *
        omega
      · by_cases he : hd.card = m
        · simp [he] at *
          omega
        · have hsucc : ¬ hd.card ≤ m := by omega
          simp [hlt,he,hsucc,step]

theorem tableLength_le (K : List (Finset V)) (child : Finset V → V → Finset V)
    (threshold : V → Nat) (m : Nat) : (table K child threshold m).length ≤ K.length := by
  rw [tableLength]
  exact List.length_filter_le _ _

theorem table_correct {K : List (Finset V)} {c₁ c₂ : Finset V → V → Finset V}
    (threshold : V → Nat)
    (he : ∀ S ∈ K, ∀ u ∈ S, c₁ S u = c₂ S u)
    (hK : ∀ S ∈ K, ∀ u ∈ S, c₁ S u ⊂ S → c₁ S u ∈ K)
    (m : Nat) {S : Finset V} (hS : S ∈ K) (hm : S.card < m) :
    lookup S (table K c₁ threshold m) = recursive c₂ threshold S := by
  induction m generalizing S with
  | zero => omega
  | succ m ih =>
    simp only [table,lookup_batch,List.mem_filter,beq_iff_eq,hS,true_and]
    split_ifs with h
    · rw [recursive]
      apply combine_congr threshold (he S hS)
      intro u hu hlt
      have hh := Finset.card_lt_card hlt
      rw [dif_pos hh]
      exact ih (hK S hS u hu hlt) (by omega)
    · exact ih hS (by omega)

theorem optimalTreeTable [Fintype V] {G : SimpleGraph V} (ht : G.IsTree)
    (threshold : V → Nat) (k : Nat) (r : V) :
    let K := (scopes G k).toList
    K.length ≤ (Fintype.card V)^2 ∧
    lookup (ball G k r) (table K (restrict G k) threshold (Fintype.card V + 1)) =
      recursive (intrinsic G k) threshold (ball G k r) := by
  dsimp only
  refine ⟨by simpa using scopesCard (G := G) k, ?_⟩
  apply table_correct
  · intro S hS u hu
    exact (intrinsic_eq_restrict ht k (by simpa using hS) hu).symm
  · intro S hS u _ _
    rw [restrict_eq_ball]
    simpa using restrictMemScopes ht k (by simpa using hS) u
  · simpa using ballMemScopes (G := G) k r
  · have h := Finset.card_le_univ (ball G k r)
    omega

theorem optimalLocalTreeTable [Fintype V] {G : SimpleGraph V} (ht : G.IsTree)
    (threshold : V → Nat) (k : Nat) (r : V) (hr : ∀ v, G.dist r v ≤ k) :
    let K := (scopes G k).toList
    let T := table K (restrict G k) threshold (Fintype.card V + 1)
    T.length ≤ (Fintype.card V)^2 ∧
    ((threshold r ≤ lookup Finset.univ T) ↔
    (threshold r ≤ recursive (intrinsic G k) threshold Finset.univ)) := by
  dsimp only
  have hb : ball G k r = Finset.univ := by
    ext v
    simp [ball,hr]
  obtain ⟨hs,he⟩ := optimalTreeTable ht threshold k r
  rw [hb] at he
  have hl := (tableLength_le (scopes G k).toList (restrict G k) threshold (Fintype.card V + 1)).trans hs
  simp [hl,he]

#print axioms combine_literal
#print axioms optimalLocalTreeTable
#print axioms optimalTreeTable
end TreeInfluence
