import Refute269
open SimpleGraph
namespace Refute269
abbrev Small := Vert 2 2
def code : Small → Nat
  | .inl r => r.val
  | .inr (.inl (i,r)) => 4 + 4*i.val + r.val
  | .inr (.inr (i,r)) => 12 + 2*i.val + r.val
def decode (k : Nat) : Small :=
  if k < 4 then P (Fin.ofNat 4 k)
  else if k < 12 then A (Fin.ofNat 2 ((k-4)/4)) (Fin.ofNat 4 (k-4))
  else B (Fin.ofNat 2 ((k-12)/2)) (Fin.ofNat 2 (k-12))
def distData : Array (Array Nat) := #[
  #[0, 1, 4, 3, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 2, 3],
  #[1, 0, 3, 4, 2, 3, 2, 4, 2, 3, 2, 4, 1, 2, 1, 2],
  #[4, 3, 0, 1, 3, 2, 4, 2, 3, 2, 4, 2, 2, 1, 2, 1],
  #[3, 4, 1, 0, 2, 1, 3, 1, 2, 1, 3, 1, 3, 2, 3, 2],
  #[1, 2, 3, 2, 0, 1, 1, 2, 2, 3, 2, 3, 3, 4, 3, 4],
  #[2, 3, 2, 1, 1, 0, 2, 1, 3, 2, 3, 2, 4, 3, 4, 3],
  #[1, 2, 4, 3, 1, 2, 0, 3, 2, 3, 2, 4, 3, 4, 3, 4],
  #[3, 4, 2, 1, 2, 1, 3, 0, 3, 2, 4, 2, 4, 3, 4, 3],
  #[1, 2, 3, 2, 2, 3, 2, 3, 0, 1, 1, 2, 3, 4, 3, 4],
  #[2, 3, 2, 1, 3, 2, 3, 2, 1, 0, 2, 1, 4, 3, 4, 3],
  #[1, 2, 4, 3, 2, 3, 2, 4, 1, 2, 0, 3, 3, 4, 3, 4],
  #[3, 4, 2, 1, 3, 2, 4, 2, 2, 1, 3, 0, 4, 3, 4, 3],
  #[2, 1, 2, 3, 3, 4, 3, 4, 3, 4, 3, 4, 0, 1, 2, 3],
  #[3, 2, 1, 2, 4, 3, 4, 3, 4, 3, 4, 3, 1, 0, 3, 2],
  #[2, 1, 2, 3, 3, 4, 3, 4, 3, 4, 3, 4, 2, 3, 0, 1],
  #[3, 2, 1, 2, 4, 3, 4, 3, 4, 3, 4, 3, 3, 2, 1, 0]
]
def predData : Array (Array Nat) := #[
  #[0, 0, 3, 5, 0, 4, 0, 5, 0, 8, 0, 9, 1, 12, 1, 14],
  #[1, 1, 13, 2, 0, 4, 0, 5, 0, 8, 0, 9, 1, 12, 1, 14],
  #[1, 12, 2, 2, 5, 3, 4, 3, 9, 3, 8, 3, 13, 2, 15, 2],
  #[4, 0, 3, 3, 5, 3, 4, 3, 9, 3, 8, 3, 13, 2, 15, 2],
  #[4, 0, 3, 5, 4, 4, 4, 5, 0, 8, 0, 3, 1, 2, 1, 2],
  #[4, 0, 3, 5, 5, 5, 4, 5, 0, 3, 0, 3, 1, 2, 1, 2],
  #[6, 0, 3, 5, 6, 4, 6, 5, 0, 8, 0, 9, 1, 12, 1, 14],
  #[4, 0, 3, 7, 5, 7, 4, 7, 9, 3, 0, 3, 13, 2, 15, 2],
  #[8, 0, 3, 9, 0, 3, 0, 3, 8, 8, 8, 9, 1, 2, 1, 2],
  #[8, 0, 3, 9, 0, 3, 0, 3, 9, 9, 8, 9, 1, 2, 1, 2],
  #[10, 0, 3, 9, 0, 4, 0, 3, 10, 8, 10, 9, 1, 12, 1, 14],
  #[8, 0, 3, 11, 5, 3, 0, 3, 9, 11, 8, 11, 13, 2, 15, 2],
  #[1, 12, 13, 2, 0, 3, 0, 3, 0, 8, 0, 3, 12, 12, 1, 2],
  #[1, 12, 13, 2, 0, 3, 0, 3, 0, 3, 0, 3, 13, 13, 1, 2],
  #[1, 14, 15, 2, 0, 3, 0, 3, 0, 8, 0, 3, 1, 2, 14, 14],
  #[1, 14, 15, 2, 0, 3, 0, 3, 0, 3, 0, 3, 1, 2, 15, 15]
]

def dd (s t : Small) : Nat := (distData[code s]!)[code t]!
def predecessor (s t : Small) : Small := decode ((predData[code s]!)[code t]!)
set_option maxRecDepth 16000
set_option maxHeartbeats 6000000

theorem diag : ∀ s : Small, dd s s = 0 := by decide
theorem zero : ∀ s t : Small, dd s t = 0 → s = t := by decide
theorem pred_good : ∀ s t : Small, dd s t ≠ 0 →
    adj (predecessor s t) t ∧ dd s (predecessor s t) + 1 = dd s t := by decide
theorem max4 : ∀ s t : Small, dd s t ≤ 4 := by decide
theorem has4 : ∀ s : Small, ∃ t : Small, dd s t = 4 := by decide
theorem lips : ∀ s t u : Small, adj t u → dd s u ≤ dd s t + 1 := by decide

theorem walks (s t : Small) : ∃ w : (graph 2 2).Walk s t, w.length = dd s t := by
  by_cases h : dd s t = 0
  · have he := zero s t h
    subst t
    exact ⟨.nil, (diag _).symm⟩
  · obtain ⟨he,hd⟩ := pred_good s t h
    change (graph 2 2).Adj (predecessor s t) t at he
    obtain ⟨w, hw⟩ := walks s (predecessor s t)
    refine ⟨w.concat he, ?_⟩
    rw [Walk.length_concat, hw, hd]
termination_by dd s t
decreasing_by omega

lemma smallconn : (graph 2 2).Connected := by
  refine { preconnected := ?_, nonempty := ⟨P 0⟩ }
  intro v w
  obtain ⟨t, _⟩ := walks v w
  exact ⟨t⟩

lemma along (s : Small) {t u : Small} (w : (graph 2 2).Walk t u) :
    dd s u ≤ dd s t + w.length := by
  induction w with
  | nil => simp
  | @cons x y z he p ih =>
    have hh := lips s x y he
    simp only [Walk.length_cons]
    omega

theorem exact_dist (s t : Small) : (graph 2 2).dist s t = dd s t := by
  apply le_antisymm
  · obtain ⟨w, hw⟩ := walks s t
    exact hw ▸ dist_le w
  · obtain ⟨w, hw⟩ := smallconn.exists_walk_length_eq_dist s t
    simpa [diag, hw] using along s w

#print axioms exact_dist
end Refute269
