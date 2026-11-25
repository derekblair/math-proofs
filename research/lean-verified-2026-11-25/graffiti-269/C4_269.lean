import Big269
open SimpleGraph
namespace Refute269

def color4 {k} (a b c i : Fin k) : Fin 4 := if i = a then 0 else if i = b then 1 else if i = c then 2 else 3
def pick4 {k} (a b c d : Fin k) (i : Fin 4) : Fin k :=
  if i = 0 then a else if i = 1 then b else if i = 2 then c else d

lemma rec4 {k} (a b c d i : Fin k) (h : i = a ∨ i = b ∨ i = c ∨ i = d) :
    pick4 a b c d (color4 a b c i) = i := by
  by_cases ha : i = a
  · simp [color4,pick4,ha]
  by_cases hb : i = b
  · simp only [color4,ite_eq_right ha,ite_eq_left hb]
    simpa [pick4] using hb.symm
  by_cases hc : i = c
  · simp only [color4,ite_eq_right ha,ite_eq_right hb,ite_eq_left hc]
    simpa [pick4] using hc.symm
  have hd : i = d := by tauto
  simp only [color4,ite_eq_right ha,ite_eq_right hb,ite_eq_right hc]
  simpa [pick4] using hd.symm

set_option maxRecDepth 16000
set_option maxHeartbeats 9000000
theorem common_bound : ∀ s t : Vert 4 4, s ≠ t →
  (Finset.univ.filter (fun w : Vert 4 4 => adj s w ∧ adj t w)).card ≤ 1 := by decide

theorem no4Small (s t u v : Vert 4 4) (hst : s ≠ t) (huv : u ≠ v)
    (hsu : (graph 4 4).Adj s u) (hsv : (graph 4 4).Adj s v)
    (htu : (graph 4 4).Adj t u) (htv : (graph 4 4).Adj t v) : False := by
  have he := Finset.card_le_one.mp (common_bound s t hst)
  exact huv (he u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsu, htu⟩)
               v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsv, htv⟩))

def C4Free {V : Type*} (G' : SimpleGraph V) : Prop :=
  ∀ s t u v, s ≠ t → u ≠ v → G'.Adj s u → G'.Adj s v → G'.Adj t u → G'.Adj t v → False

theorem no4 : C4Free G := by
  intro s t u v hst huv hsu hsv htu htv
  let f : G →g graph 4 4 := reindex (color4 (ia s) (ia t) (ia u)) (color4 (ib s) (ib t) (ib u))
  let g : graph 4 4 →g G := reindex (pick4 (ia s) (ia t) (ia u) (ia v)) (pick4 (ib s) (ib t) (ib u) (ib v))
  have hgf (w : Big) (hw : w = s ∨ w = t ∨ w = u ∨ w = v) : g (f w) = w := by
    rcases w with p | (⟨i,r⟩ | ⟨i,r⟩)
    · rfl
    · have hw' : i = ia s ∨ i = ia t ∨ i = ia u ∨ i = ia v := by
        rcases hw with h | h | h | h <;> first
         | exact Or.inl (congrArg ia h)
         | exact Or.inr (.inl (congrArg ia h))
         | exact Or.inr (.inr (.inl (congrArg ia h)))
         | exact Or.inr (.inr (.inr (congrArg ia h)))
      change A (pick4 (ia s) (ia t) (ia u) (ia v) (color4 (ia s) (ia t) (ia u) i)) r = A i r
      rw [rec4 _ _ _ _ _ hw']
    · have hw' : i = ib s ∨ i = ib t ∨ i = ib u ∨ i = ib v := by
        rcases hw with h | h | h | h
        · exact Or.inl (congrArg ib h)
        · exact Or.inr (.inl (congrArg ib h))
        · exact Or.inr (.inr (.inl (congrArg ib h)))
        · exact Or.inr (.inr (.inr (congrArg ib h)))
      change B (pick4 (ib s) (ib t) (ib u) (ib v) (color4 (ib s) (ib t) (ib u) i)) r = B i r
      rw [rec4 _ _ _ _ _ hw']
  have hs := hgf s (.inl rfl)
  have ht := hgf t (.inr (.inl rfl))
  have hu := hgf u (.inr (.inr (.inl rfl)))
  have hv := hgf v (.inr (.inr (.inr rfl)))
  have fst : f s ≠ f t := fun h => hst (hs ▸ ht ▸ congrArg g h)
  have fuv : f u ≠ f v := fun h => huv (hu ▸ hv ▸ congrArg g h)
  exact no4Small (f s) (f t) (f u) (f v) fst fuv (f.map_rel hsu) (f.map_rel hsv) (f.map_rel htu) (f.map_rel htv)

#print axioms no4
end Refute269
