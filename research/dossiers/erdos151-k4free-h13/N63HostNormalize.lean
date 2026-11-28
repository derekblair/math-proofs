import N63HostDegree
import N63TableCore

namespace Erdos151N63
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V→V→Prop) [DecidableRel G]

/-- Complete host coverage: every sufficiently dense triangle-free
9-link admits an actual adjacency-preserving chart reindexing and the
chart's certified pivot or an explicit exception-chart relabeling. -/
theorem nine_host_of_code_binding
    (bind : ∀ d h : Nat, 4≤d → d≤8 → h < 2^((8-d)*(7-d)/2) →
      ∀ r : Array Nat, r ∈ enumFast 9 14 d h → ∃ e : Entry, r=e.rows ∧ e.Check 9)
    (hn : Fintype.card V=9)
    (sym : ∀ a b, G a b ↔ G b a) (irr : ∀ v, ¬G v v)
    (tf : ∀ v x y, G v x → G v y → ¬G x y)
    (hmin : ∀ v, 2 ≤ fullDeg G v)
    (dense : 28 ≤ ∑ v : V, fullDeg G v) :
    ∃ (e : Entry) (relabel : Fin 9 ≃ V), e.Check 9 ∧
      ∀ i j : Fin 9, adj e.rows i.val j.val = true ↔ G (relabel i) (relabel j) := by
  obtain ⟨w,hd,hds,hmax,L,R,M,hmono,hwid,hbits,hL,_⟩ :=
    max_normalization_sorted G 9 hn (by omega) irr tf
  let d := fullDeg G w
  let q := 8-d
  have hql : q = 9-1-d := rfl
  have hd8 : d≤8 := by omega
  let RR (i j : Nat) : Bool := if hi : i<q then if hj : j<q then
    decide (G (R ⟨i,hi⟩).val (R ⟨j,hj⟩).val) else false else false
  obtain ⟨h,hh,hdec⟩ := right_code_nine d hd hd8 RR
    (by intro i j; by_cases hi : i<q <;> by_cases hj : j<q <;> simp [RR,hi,hj,sym])
    (by intro i; by_cases hi : i<q <;> simp [RR,hi,irr])
  let H := graphOfCode q h
  let f (i : Fin d) : Fin (2^q) := ⟨M i,hwid i⟩
  have hsymR (i j : Fin q) : adj H i.val j.val = decide (G (R i).val (R j).val) := by
    exact (hdec i.val i.isLt j.val j.isLt).trans (by simp [RR,i.isLt,j.isLt])
  have hML (i : Fin d) (j : Fin q) :
      (f i).val.testBit j.val = decide (G (L i).val (R j).val) := by
    apply Bool.eq_iff_iff.mpr
    simpa [f] using hbits i j
  have ht : tfRight q H = true := by
    apply tfRight_of_bits
    · exact fun i hi => rightBits_width _ _ _ hi
    · intro a b j ha hb hj hab haj
      have hab' := hsymR ⟨a,ha⟩ ⟨b,hb⟩
      have haj' := hsymR ⟨a,ha⟩ ⟨j,hj⟩
      rw [hab] at hab'
      rw [haj] at haj'
      have n := tf _ _ _ (of_decide_eq_true hab'.symm) (of_decide_eq_true haj'.symm)
      exact (hsymR ⟨b,hb⟩ ⟨j,hj⟩).trans (by simp [n])
  have ha (i : Fin d) : allowed q H (f i) = true := by
    apply allowed_of_bits
    · exact fun j hj => rightBits_width _ _ _ hj
    · intro a b ha hb hLa hAB
      have hLa' := hML i ⟨a,ha⟩
      have hAB' := hsymR ⟨a,ha⟩ ⟨b,hb⟩
      rw [hLa] at hLa'
      rw [hAB] at hAB'
      have n := tf _ _ _ ((sym _ _).mp (of_decide_eq_true hLa'.symm)) (of_decide_eq_true hAB'.symm)
      exact (hML i ⟨b,hb⟩).trans (by simp [sym _ _,n])
  have qn : d+q+1=9 := by omega
  have hdeg := hostDegree_filter G w (m:=14) H f L R sym (irr w) hL hsymR hML qn rfl hmin hmax dense
  have hm := code_mem_enumFast 9 14 d h f (fun i j hij => hmono hij) ha ht hdeg
  obtain ⟨e,he,hcheck⟩ := bind d h hd hd8 hh _ hm
  let index := indexEquiv d q 9 qn
  let slot := slotEquiv G w (irr w) L R
  refine ⟨e,index.symm.trans slot,hcheck,?_⟩
  intro i j
  have hi : indexVal (index.symm i)=i.val := congrArg Fin.val (index.apply_symm_apply i)
  have hj : indexVal (index.symm j)=j.val := congrArg Fin.val (index.apply_symm_apply j)
  have z := hostAdj_slots G w H f L R sym (irr w) hL hsymR hML (index.symm i) (index.symm j)
  rw [hi,hj,he] at z
  rw [z]
  simp [index,slot,slotEquiv]

#print axioms nine_host_of_code_binding
end Erdos151N63
