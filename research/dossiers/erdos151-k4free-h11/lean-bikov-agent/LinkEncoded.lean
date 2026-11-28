import LinkSound

namespace BikovLocal

def pack (g : E→Bool) : List E→Nat
| [] => 0
| e::es => 2*pack g es+(g e).toNat

lemma pack_small (g : E→Bool) (L : List E) :
    pack g L < 2^L.length := by
  induction L with
  | nil => simp [pack]
  | cons e L ih =>
    simp only [pack,List.length_cons,Nat.pow_succ]
    cases h:g e <;> simp [h, Bool.toNat] <;> omega

lemma pack_bit (g : E→Bool) (L : List E) (i : Nat) (e : E)
    (h : L[i]?=some e) : (pack g L).testBit i=g e := by
  induction L generalizing i with
  | nil => simp at h
  | cons a L ih =>
    cases i with
    | zero =>
      have ea : a=e := by simpa using h
      subst e
      rw [pack,Nat.testBit_zero]
      cases z:g a <;> simp [z,Bool.toNat] <;> omega
    | succ i =>
      have ih' := ih i (by simpa using h)
      rw [pack,Nat.testBit_succ,←ih']
      congr 1
      cases z:g a <;> simp [z,Bool.toNat] <;> omega

theorem edge_pack (g : E→Bool) (e : E) :
    e∈edges (pack g extra) ↔ e∈c5 ∨ (e∈extra ∧ g e=true) := by
  simp only [edges,List.mem_append,List.mem_map,List.mem_filter]
  rw [or_congr_right]
  constructor
  · rintro ⟨⟨a,i⟩,⟨h,b⟩,eq⟩
    dsimp at eq b
    subst a
    have ei := List.mk_mem_zipIdx_iff_getElem?.mp h
    exact ⟨List.mem_iff_getElem?.mpr ⟨i,ei⟩,(pack_bit g extra i e ei).symm.trans b⟩
  · rintro ⟨h,gtrue⟩
    obtain ⟨i,ei⟩ := List.mem_iff_getElem?.mp h
    exact ⟨(e,i),⟨List.mk_mem_zipIdx_iff_getElem?.mpr ei,(pack_bit g extra i e ei).trans gtrue⟩,rfl⟩

theorem c5_arbitrary (g : E→Bool) (c : E→Bool)
    (tf : ∀ i j k : Nat, i<j → j<k → k<7 →
      ¬ (g (i,j)=true ∧ g (i,k)=true ∧ g (j,k)=true))
    (fixed : ∀ e∈c5, g e=true) :
    ∃ f : Nat→Bool, ∀ e, (e∈c5 ∨ e∈extra) → g e=true →
      ¬ (f e.1=c e ∧ f e.2=c e) := by
  let m := pack g extra
  have sh : m<2048 := pack_small g extra
  have good (e : E) (he : e∈edges m) : g e=true := by
    rcases (edge_pack g e).mp he with ff|⟨_,h⟩
    · exact fixed _ ff
    · exact h
  have T : triFree (edges m)=true := by
    apply List.all_eq_true.mpr
    rintro ⟨i,j,k⟩ h
    have I : i<7 ∧ j<7 ∧ k<7 ∧ i<j ∧ j<k := by
      unfold tris at h
      simp only [List.mem_flatMap,List.mem_range,List.mem_filterMap] at h
      obtain ⟨a,ha,b,hb,d,hd,eq⟩ := h
      split at eq
      next hy =>
        injection eq with eq'
        cases eq'
        exact ⟨ha,hb,hd,hy.1,hy.2⟩
      next _ => contradiction
    by_cases x : (i,j)∈edges m <;>
      by_cases y : (i,k)∈edges m <;>
      by_cases z : (j,k)∈edges m <;> simp [x,y,z]
    exact False.elim (tf i j k I.2.2.2.1 I.2.2.2.2 I.2.2.1
      ⟨good _ x,good _ y,
        good _ z⟩)
  obtain ⟨f,h⟩ := c5_bank_extends m sh T c
  refine ⟨f,fun e e' eg=>h e ((edge_pack g e).mpr ?_)⟩
  exact e'.imp id (fun ee=>⟨ee,eg⟩)

#print axioms c5_arbitrary
end BikovLocal
