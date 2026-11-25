import SourceBridge
import Mathlib.Tactic

namespace PackingSeparator

def nPos (K J : ℕ) : ℕ := J*(K-2)+2

variable {K J : ℕ} (hk : 4≤K)

def atPos (t : Fin J) (i : Fin K) : Fin (nPos K J) := by
  refine ⟨t.val*(K-2)+i.val,?_⟩
  have e := Nat.mul_le_mul_right (K-2) (show t.val+1≤J by have := t.isLt; omega)
  rw [Nat.add_mul,one_mul] at e
  have := i.isLt
  unfold nPos
  omega

def atBlock (t : Fin (J+1)) (a : Fin 2) : Fin (nPos K J) := by
  refine ⟨t.val*(K-2)+a.val,?_⟩
  have e := Nat.mul_le_mul_right (K-2) (show t.val≤J by have := t.isLt; omega)
  have := a.isLt
  unfold nPos
  omega

lemma prefix_pos (t : Fin J) (a : Fin 2) :
    atPos hk t ⟨a.val,by have := a.isLt; omega⟩=atBlock (K:=K) t.castSucc a := rfl

lemma suffix_pos (t : Fin J) (a : Fin 2) :
    atPos hk t ⟨K-2+a.val,by have := a.isLt; omega⟩=atBlock (K:=K) t.succ a := by
  apply Fin.ext
  change t.val*(K-2)+(K-2+a.val)=(t.val+1)*(K-2)+a.val
  rw [Nat.add_mul,one_mul,Nat.add_assoc]

def stepEdges (p : Equiv.Perm (Fin K)) (x y : Fin (nPos K J)) : Prop :=
  ∃ (t : Fin J) (i l : Fin K), x=atPos hk t i ∧ y=atPos hk t l ∧ p i<p l

lemma within (p : Equiv.Perm (Fin K)) (t : Fin J) {i l : Fin K} (h : p i<p l) :
    Relation.TransGen (stepEdges hk p) (atPos hk t i) (atPos hk t l) :=
  Relation.TransGen.single ⟨t,i,l,rfl,rfl,h⟩

lemma cover_pos (hJ : 0<J) (x : Fin (nPos K J)) :
    ∃ (t : Fin J) (i : Fin K), x=atPos hk t i := by
  let d := K-2
  have hd : 0<d := by dsimp [d]; omega
  let t := x.val/d
  let r := x.val%d
  have hr : r<d := Nat.mod_lt _ hd
  have E : t*d+r=x.val := by simpa only [Nat.add_comm,Nat.mul_comm] using Nat.mod_add_div x.val d
  have xl : x.val<J*d+2 := x.isLt
  by_cases ht : t<J
  · exact ⟨⟨t,ht⟩,⟨r,by dsimp [d] at hr; omega⟩,Fin.ext E.symm⟩
  · have tj : t=J := by
      by_contra h
      have F := Nat.mul_le_mul_right d (show J+1≤t by omega)
      rw [Nat.add_mul,one_mul] at F
      dsimp [d] at *
      omega
    have r2 : r<2 := by rw [tj] at E; omega
    have dd : d+r<K := by dsimp [d]; omega
    refine ⟨⟨J-1,by omega⟩,⟨d+r,dd⟩,Fin.ext ?_⟩
    change x.val=(J-1)*d+(d+r)
    calc x.val=J*d+r := by rw [tj] at E; exact E.symm
      _=((J-1)+1)*d+r := by rw [show J-1+1=J by omega]
      _=_ := by rw [Nat.add_mul,one_mul,Nat.add_assoc]

lemma block_parts {K J : ℕ} (hk : 4≤K) (t : Fin (J+1)) (a : Fin 2) :
    (atBlock (K:=K) t a).val/(K-2)=t.val ∧
    (atBlock (K:=K) t a).val%(K-2)=a.val := by
  have dpos : 0<K-2 := by omega
  have ar : a.val<K-2 := by have := a.isLt; omega
  change (t.val*(K-2)+a.val)/(K-2)=t.val ∧ (t.val*(K-2)+a.val)%(K-2)=a.val
  constructor
  · rw [Nat.add_comm,Nat.add_mul_div_right _ _ dpos,Nat.div_eq_of_lt ar,zero_add]
  · rw [Nat.mul_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt ar]

lemma window_private_parts (t : Fin J) {i : Fin K} (hi : i.val<K-2) :
    (atPos hk t i).val/(K-2)=t.val ∧ (atPos hk t i).val%(K-2)=i.val := by
  have dpos : 0<K-2 := by omega
  change (t.val*(K-2)+i.val)/(K-2)=t.val ∧ (t.val*(K-2)+i.val)%(K-2)=i.val
  constructor
  · rw [Nat.add_comm,Nat.add_mul_div_right _ _ dpos,Nat.div_eq_of_lt hi,zero_add]
  · rw [Nat.mul_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt hi]

end PackingSeparator
