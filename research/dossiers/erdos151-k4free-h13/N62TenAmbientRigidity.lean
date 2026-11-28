import N62AmbientSaturated

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V→V→Prop) [DecidableRel G] [DecidableRel C]

/-- In the tight core-degree-ten, link-size-sixteen row, the ambient
link contains no extra edge (including edges involving the two ghosts). -/
theorem sixteen_link_exact
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (csym : ∀ {a b}, C a b → C b a)
    (sub : ∀ {a b}, C a b → G a b) (two : TwoTriangles C)
    (deg : ∀ v, (neighbors G v).card≤12)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (hn : 62≤Fintype.card V) (w : V) (s12 : (neighbors G w).card=12)
    (t10 : (neighbors C w).card=10)
    (hmin : ∀ u∈neighbors C w, 8≤(neighbors C u).card)
    (h16 : ∑ u∈neighbors C w,row C (neighbors C w) u = 32) :
    ∀ a∈neighbors G w, ∀ b∈neighbors G w, G a b →
      a∈neighbors C w ∧ b∈neighbors C w ∧ C a b := by
  classical
  let S := neighbors G w
  let T := neighbors C w
  let X := ext S w
  have ts : T⊆S := fun _ hu => (mem_neighbors G).mpr (sub ((mem_neighbors C).mp hu))
  intro a ha b hb e
  by_contra bad
  have ne : a≠b := fun h => irr b (h ▸ e)
  let core (u : V) : Nat := if u∈T then row C T u else 0
  let extra (u : V) : Nat := if u∈({a,b} : Finset V) then 1 else 0
  have erow (u : V) (hu : u∈S) : core u+extra u≤row G S u := by
    let Q := if u∈T then T.filter (C u) else ∅
    let E := ({a,b} : Finset V).filter (fun v => v≠u ∧ u∈({a,b} : Finset V))
    have qc : Q.card=core u := by by_cases h : u∈T <;> simp [Q,core,h,row]
    have ec : E.card=extra u := by
      by_cases h : u∈({a,b} : Finset V)
      · simp only [Finset.mem_insert,Finset.mem_singleton] at h
        rcases h with rfl|rfl
        · have ex : E={b} := by ext t; simp [E,ne,ne.symm]; aesop
          simp [ex,extra]
        · have ex : E={a} := by ext t; simp [E,ne,ne.symm]; aesop
          simp [ex,extra]
      · have ex : E=∅ := by ext t; simp [E,h]
        rw [ex]; simp only [Finset.card_empty,extra,if_neg h]
    have dj : Disjoint Q E := Finset.disjoint_left.mpr (fun v hq he => by
      obtain ⟨hev,vne,heu⟩ := Finset.mem_filter.mp he
      have uq : u∈T ∧ v∈T ∧ C u v := by
        by_cases ut : u∈T
        · obtain ⟨vt,uc⟩ := Finset.mem_filter.mp (show v∈T.filter (C u) by simpa [Q,ut] using hq)
          exact ⟨ut,vt,uc⟩
        · simp [Q,ut] at hq
      simp only [Finset.mem_insert,Finset.mem_singleton] at heu hev
      rcases heu with rfl|rfl <;> rcases hev with rfl|rfl
      · exact vne rfl
      · exact bad uq
      · exact bad ⟨uq.2.1,uq.1,csym uq.2.2⟩
      · exact vne rfl)
    have se : Q∪E⊆S.filter (G u) := by
      intro v hv
      rcases Finset.mem_union.mp hv with hq|he
      · by_cases h : u∈T
        · obtain ⟨vu,ce⟩ := Finset.mem_filter.mp (show v∈T.filter (C u) by simpa [Q,h] using hq)
          exact Finset.mem_filter.mpr ⟨ts vu,sub ce⟩
        · simp [Q,h] at hq
      · obtain ⟨hev,vne,heu⟩ := Finset.mem_filter.mp he
        simp only [Finset.mem_insert,Finset.mem_singleton] at hev heu
        rcases heu with rfl|rfl <;> rcases hev with rfl|rfl
        · exact False.elim (vne rfl)
        · exact Finset.mem_filter.mpr ⟨hb,e⟩
        · exact Finset.mem_filter.mpr ⟨ha,sym e⟩
        · exact False.elim (vne rfl)
    have hs := Finset.card_le_card se
    rw [Finset.card_union_of_disjoint dj,qc,ec] at hs
    exact hs
  have hcore : (∑ u∈S,core u)=32 := by
    unfold core
    rw [←Finset.sum_filter]
    have f : S.filter (fun u => u∈T)=T := by ext u; simp [Finset.mem_filter, and_iff_right_of_imp (fun h => ts h)]
    rwa [f]
  have hex : (∑ u∈S,extra u)=2 := by
    unfold extra
    rw [←Finset.sum_filter]
    have f : S.filter (fun u => u∈({a,b} : Finset V))={a,b} := by
      ext u
      rw [Finset.mem_filter]
      refine ⟨fun h => h.2, ?_⟩
      intro hu
      simp only [Finset.mem_insert,Finset.mem_singleton] at hu
      exact ⟨hu.elim (fun h => h ▸ ha) (fun h => h ▸ hb), by simpa using hu⟩
    rw [f]; simp [ne]
  have hsum := Finset.sum_le_sum erow
  rw [Finset.sum_add_distrib,hcore,hex] at hsum
  have hF := frame_of_ambient_saturated G C w sym irr tf sub two deg upper hn s12 t10 hmin 16
    (by simpa only using h16) hsum
  have hsf : Free (Forbidden G) (S : Set V) := by
    convert neighborhood_free G sym tf w using 1
    ext x
    exact mem_neighbors G
  have hd : Disjoint X S := Finset.disjoint_left.mpr (fun x hx hs =>
    (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_of_mem hs))
  exact frame_impossible G hF sym irr hd s12 hsf upper deg

#print axioms sixteen_link_exact
end Erdos151N62
