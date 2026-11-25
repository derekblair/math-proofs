import WindowRules

namespace FussCover

lemma block_succ {D t s a b : ℕ} (hD : 0<D) (ha : a<D) (hb : b<D)
    (E : t*D+a+1=s*D+b) :
    (t=s ∧ a+1=b) ∨ (t+1=s ∧ b=0) := by
  have le : t≤s := by
    by_contra! h
    have q := Nat.mul_le_mul_right D (show s+1≤t by omega)
    rw [Nat.add_mul,one_mul] at q
    omega
  have le' : s≤t+1 := by
    by_contra! h
    have q := Nat.mul_le_mul_right D (show t+2≤s by omega)
    rw [show t+2=(t+1)+1 by omega,Nat.add_mul,one_mul,Nat.add_mul,one_mul] at q
    omega
  by_cases H : t=s
  · left
    exact ⟨H,by rw [H] at E; omega⟩
  · right
    have H' : t+1=s := by omega
    refine ⟨H',?_⟩
    rw [←H',Nat.add_mul,one_mul] at E
    omega

variable {z h j : ℕ} (hj : 0<j) (hz : 0<z)
variable (r : Equiv.Perm (Fin (n z h j))) (P : packed r)
include P

lemma low_lt_same (t : Fin (j+1)) {a b : Fin z} (hab : a<b) :
    r (headS hj t a) < r (headS hj t b) := by
  by_cases E : t.val<j
  · let t' : Fin j := ⟨t.val,E⟩
    have e : t'.castSucc=t := Fin.ext rfl
    simpa only [e] using local_low_lt hj r P t' hab
  · let t' : Fin j := ⟨j-1,by omega⟩
    have e : t'.succ=t := Fin.ext (by change j-1+1=t.val; have := t.isLt; omega)
    simpa only [e] using local_suffix_low_lt hj r P t' hab

lemma head_adj (i : Fin (hN z h j)) (tlt : i.val+1<hN z h j) :
    r (hAt hj hz i) < r (hAt hj hz ⟨i.val+1,tlt⟩) := by
  let q : Fin (hN z h j) := ⟨i.val+1,tlt⟩
  have Q : q.val = i.val+1 := rfl
  have D : 0<z+h := by omega
  rcases hAt_range hj hz i with ⟨t,a,I,G⟩|⟨t,a,I,G⟩ <;>
      rcases hAt_range hj hz q with ⟨s,b,J,H⟩|⟨s,b,J,H⟩
  · change r (hAt hj hz i) < r (hAt hj hz q)
    rw [G,H]
    have E : t.val*(z+h)+a.val+1=s.val*(z+h)+b.val := by rw [I,J] at Q; exact Q.symm
    rcases block_succ D (by have := a.isLt; omega) (by have := b.isLt; omega) E with ⟨eqt,eqab⟩|⟨eqt,_⟩
    · have e : t=s := Fin.ext eqt
      subst s
      exact low_lt_same hj r P t (by change a.val<b.val; omega)
    · let t' : Fin j := ⟨t.val,by have := s.isLt; omega⟩
      have x : t'.castSucc=t := Fin.ext rfl
      have y : t'.succ=s := Fin.ext eqt
      simpa only [x,y] using local_low_next hj r P t' a b
  · change r (hAt hj hz i) < r (hAt hj hz q)
    rw [G,H]
    have E : t.val*(z+h)+a.val+1=s.val*(z+h)+(z+b.val) := by rw [I,J] at Q; exact Q.symm
    rcases block_succ D (by have := a.isLt; omega) (by have := b.isLt; omega) E with ⟨eqt,_⟩|⟨_,eqb⟩
    · have e : s.castSucc=t := Fin.ext eqt.symm
      simpa only [e] using local_low_pvt hj r P s a b
    · omega
  · change r (hAt hj hz i) < r (hAt hj hz q)
    rw [G,H]
    have E : t.val*(z+h)+(z+a.val)+1=s.val*(z+h)+b.val := by rw [I,J] at Q; exact Q.symm
    rcases block_succ D (by have := a.isLt; omega) (by have := b.isLt; omega) E with ⟨_,eqab⟩|⟨eqt,_⟩
    · have := b.isLt; omega
    · have e : t.succ=s := Fin.ext eqt
      simpa only [e] using local_pvt_next hj r P t a b
  · change r (hAt hj hz i) < r (hAt hj hz q)
    rw [G,H]
    have E : t.val*(z+h)+(z+a.val)+1=s.val*(z+h)+(z+b.val) := by rw [I,J] at Q; exact Q.symm
    rcases block_succ D (by have := a.isLt; omega) (by have := b.isLt; omega) E with ⟨eqt,eqab⟩|⟨_,eqb⟩
    · have e : t=s := Fin.ext eqt
      subst s
      exact local_pvt_lt hj r P t (by change a.val<b.val; omega)
    · omega

lemma packed_head_mono :
    StrictMono (fun i : Fin (hN z h j) => r (hAt hj hz i)) := by
  intro a b hab
  have key (v : ℕ) (hv : a.val+v<hN z h j) :
      r (hAt hj hz a) ≤ r (hAt hj hz ⟨a.val+v,hv⟩) := by
    induction v with
    | zero => exact le_rfl
    | succ v ih =>
      have ep : a.val+v<hN z h j := by omega
      exact (ih ep).trans (head_adj hj hz r P ⟨a.val+v,ep⟩ hv).le
  let v := b.val-a.val-1
  have e : (a.val+v)+1=b.val := by change a.val+(b.val-a.val-1)+1=b.val; change a.val<b.val at hab; omega
  have lt : a.val+v<hN z h j := by have := b.isLt; omega
  have hlt : (a.val+v)+1<hN z h j := by rw [e]; exact b.isLt
  have bEq : (⟨a.val+v+1,hlt⟩ : Fin (hN z h j))=b := Fin.ext e
  exact (key v lt).trans_lt (bEq ▸ head_adj hj hz r P ⟨a.val+v,lt⟩ hlt)

end FussCover
