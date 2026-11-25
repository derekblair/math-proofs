import IrrCount

namespace FibPopularity
open Emerging

abbrev Marked (a b : Nat) := {s : Mask (a+4+b) // bit s a=true ∧ bit s (a+2)=true}

def doubleDimer : Mask 4 := splice mDimer mDimer
lemma DD0 : bit doubleDimer 0 = true := by decide
lemma DD1 : bit doubleDimer 1 = false := by decide
lemma DD2 : bit doubleDimer 2 = true := by decide
lemma DD3 : bit doubleDimer 3 = false := by decide

lemma DD_unique (s : Mask 4) (h0 : bit s 0=true) (h2 : bit s 2=true) : s=doubleDimer := by
  apply mask_ext
  intro i hi
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases h with rfl|rfl|rfl|rfl
  · rw [DD0]; exact h0
  · rw [DD1]; exact bits_disjoint s h0
  · rw [DD2]; exact h2
  · rw [DD3]; exact bits_disjoint s h2

lemma markedCutR {a b : Nat} (s : Marked a b) : cutOK (a:=a+4) (b:=b) s.val := by
  exact Or.inr (bits_disjoint s.val s.property.2)

def middleAndPrefix {a b : Nat} (s : Marked a b) : Mask (a+4) :=
  restrictFirst s.val (markedCutR s)

lemma markedCutL {a b : Nat} (s : Marked a b) : cutOK (a:=a) (b:=4) (middleAndPrefix s) := by
  by_cases ha : a=0
  · exact Or.inl ha
  · right
    unfold middleAndPrefix
    rw [bit_first _ _ _ (by omega)]
    apply Bool.eq_false_iff.mpr
    intro h
    have hd := bits_disjoint s.val h
    rw [show a-1+1=a by omega,s.property.1] at hd
    cases hd

lemma middle_eq {a b : Nat} (s : Marked a b) : restrictLast (a:=a) (b:=4) (middleAndPrefix s)=doubleDimer := by
  apply DD_unique
  · rw [bit_last (a:=a) (b:=4) _ _ (by decide)]
    unfold middleAndPrefix
    rw [bit_first _ _ _ (by omega)]
    exact s.property.1
  · rw [bit_last (a:=a) (b:=4) _ _ (by decide)]
    unfold middleAndPrefix
    rw [bit_first _ _ _ (by omega)]
    exact s.property.2

lemma splice_marked {a b : Nat} (s : Mask a) (u : Mask b) :
    bit (splice (splice s doubleDimer) u) a=true ∧
    bit (splice (splice s doubleDimer) u) (a+2)=true := by
  constructor
  · rw [bit_splice _ _ _ (by omega)]
    rw [show spliceBit (splice s doubleDimer) u a=bit (splice s doubleDimer) a by simp [spliceBit]]
    rw [bit_splice _ _ _ (by omega)]
    simpa [spliceBit] using DD0
  · rw [bit_splice _ _ _ (by omega)]
    rw [show spliceBit (splice s doubleDimer) u (a+2)=bit (splice s doubleDimer) (a+2) by
      simp [spliceBit,show a+2<a+4 by omega]]
    rw [bit_splice _ _ _ (by omega)]
    simpa [spliceBit,show ¬a+2<a by omega,show a+2-a=2 by omega] using DD2

def markedEquiv (a b : Nat) : Marked a b ≃ Mask a × Mask b where
  toFun s := (restrictFirst (middleAndPrefix s) (markedCutL s),restrictLast (a:=a+4) (b:=b) s.val)
  invFun p := ⟨splice (splice p.1 doubleDimer) p.2,splice_marked p.1 p.2⟩
  left_inv s := by
    apply Subtype.ext
    have he := congrArg Subtype.val ((cutting a 4).left_inv ⟨middleAndPrefix s,markedCutL s⟩)
    change splice (restrictFirst (middleAndPrefix s) (markedCutL s)) (restrictLast (a:=a) (b:=4) (middleAndPrefix s)) = middleAndPrefix s at he
    rw [middle_eq s] at he
    change splice (splice (restrictFirst (middleAndPrefix s) (markedCutL s)) doubleDimer) (restrictLast (a:=a+4) (b:=b) s.val)=s.val
    rw [he]
    exact congrArg Subtype.val ((cutting (a+4) b).left_inv ⟨s.val,markedCutR s⟩)
  right_inv p := by
    have he := (cutting (a+4) b).right_inv (splice p.1 doubleDimer,p.2)
    apply Prod.ext
    · let s : Marked a b := ⟨splice (splice p.1 doubleDimer) p.2,splice_marked p.1 p.2⟩
      have hM : middleAndPrefix s = splice p.1 doubleDimer := congrArg Prod.fst he
      have ei : restrictFirst (middleAndPrefix s) (markedCutL s) = restrictFirst (a:=a) (b:=4) (splice p.1 doubleDimer) (splice_cut p.1 doubleDimer) := by
        generalize_proofs h1 h2
        congr
      exact ei.trans (congrArg Prod.fst ((cutting a 4).right_inv (p.1,doubleDimer)))
    · have hh := congrArg Prod.snd he
      exact hh

theorem card_marked (a b : Nat) [Fintype (Marked a b)] : Fintype.card (Marked a b) = Nat.fib (a+1)*Nat.fib (b+1) := by
  rw [Fintype.card_congr (markedEquiv a b),Fintype.card_prod,card_mask,card_mask]

def q2143 : Perm 4 := swPerm doubleDimer

lemma q2143_values (i : Fin 4) : (q2143 i).val = ([1,0,3,2][i.val]!) := by decide +revert

lemma sw_asc {n i : Nat} (s : Mask n) (hi : i+1<n) (h : bit s i=false) :
    sw s i < sw s (i+1) := by
  have hh := sw_desc s hi
  have he : sw s i ≠ sw s (i+1) := fun h' => by
    have h0 := congrArg (sw s) h'
    rw [sw_invol,sw_invol] at h0
    omega
  simp [h] at hh
  omega

lemma occurs_marked {n : Nat} (s : Mask n) (i : Nat) (hi : i+4≤n) :
    occurs (swPerm s) i q2143 ↔ bit s i=true ∧ bit s (i+2)=true := by
  constructor
  · intro h
    constructor
    · have hl : q2143 1 < q2143 0 := by decide
      have hd := (h 1 0).mpr hl
      change ext (swPerm s) (i+1) < ext (swPerm s) i at hd
      rw [swPerm_ext _ _ (by omega),swPerm_ext _ _ (by omega)] at hd
      exact (sw_desc s (by omega)).mp hd
    · have hl : q2143 3 < q2143 2 := by decide
      have hd := (h 3 2).mpr hl
      change ext (swPerm s) (i+3) < ext (swPerm s) (i+2) at hd
      rw [swPerm_ext _ _ (by omega),swPerm_ext _ _ (by omega)] at hd
      exact (sw_desc (i:=i+2) s (by omega)).mp hd
  · rintro ⟨l,m⟩ r v
    have hr := r.isLt
    have hv := v.isLt
    rw [swPerm_ext _ _ (by omega),swPerm_ext _ _ (by omega)]
    have d0 := (sw_desc (i:=i) s (by omega)).mpr l
    have d2 := (sw_desc (i:=i+2) s (by omega)).mpr m
    have d1 := sw_asc (i:=i+1) s (by omega) (bits_disjoint s l)
    rw [show i+2+1=i+3 by omega] at d2
    rw [show i+1+1=i+2 by omega] at d1
    have c02 := sw_far (i:=i) (j:=i+2) s (by omega) (by omega)
    have c03 := sw_far (i:=i) (j:=i+3) s (by omega) (by omega)
    have c13 := sw_far (i:=i+1) (j:=i+3) s (by omega) (by omega)
    rw [Fin.lt_def,q2143_values,q2143_values]
    fin_cases r <;> fin_cases v <;> simp <;> omega

end FibPopularity
