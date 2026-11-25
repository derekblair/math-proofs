import WindowGeometry
namespace FussCover

def hN (z h j : ℕ) : ℕ := j*(z+h)+z
lemma n_eq_head_core {z h j : ℕ} (hj : 0<j) :
    n z h j = hN z h j + 2*(j+1) := by
  rw [n_def hj,st_def,hN,Nat.mul_add]
  omega

def hLowID {z h j : ℕ} (t : Fin (j+1)) (i : Fin z) : Fin (hN z h j) := by
  refine ⟨t.val*(z+h)+i.val,?_⟩
  have e := Nat.mul_le_mul_right (z+h) (show t.val≤j by omega)
  have := i.isLt
  unfold hN
  omega
def hPrvID {z h j : ℕ} (t : Fin j) (i : Fin h) : Fin (hN z h j) := by
  refine ⟨t.val*(z+h)+(z+i.val),?_⟩
  have e := Nat.mul_le_mul_right (z+h) (show t.val+1≤j by omega)
  rw [Nat.add_mul,one_mul] at e
  have := i.isLt
  unfold hN
  omega

def hAt {z h j : ℕ} (hj : 0<j) (hz : 0<z) (u : Fin (hN z h j)) : Fin (n z h j) := by
  let D := z+h
  let t := u.val/D
  let r := u.val%D
  have hD : 0<D := by omega
  have R : r<D := Nat.mod_lt _ hD
  have T : t*D+r=u.val := by simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div u.val D
  have U : u.val<j*D+z := u.isLt
  have th : t≤j := by
    by_contra! e
    have e' := Nat.mul_le_mul_right D (show j+1≤t by omega)
    rw [Nat.add_mul,one_mul] at e'
    dsimp only [D] at *
    omega
  by_cases L : r<z
  · exact headS hj ⟨t,by omega⟩ ⟨r,L⟩
  · have j' : t<j := by
      by_contra! ne
      have eq : t=j := by omega
      rw [eq] at T
      omega
    exact posP hj ⟨t,j'⟩ ⟨r-z,by dsimp only [D] at R; omega⟩

lemma hAt_low {z h j : ℕ} (hj : 0<j) (hz : 0<z) (t : Fin (j+1)) (i : Fin z) :
    hAt hj hz (hLowID (h:=h) t i) = headS hj t i := by
  have hzH : 0<z+h := by omega
  have lit : i.val<z+h := by have := i.isLt; omega
  have hmod : (hLowID (h:=h) t i).val%(z+h)=i.val := by
    change (t.val*(z+h)+i.val)%(z+h)=i.val
    rw [Nat.mul_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt lit]
  have hquot : (hLowID (h:=h) t i).val/(z+h)=t.val := by
    change (t.val*(z+h)+i.val)/(z+h)=t.val
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hzH,Nat.div_eq_of_lt lit,zero_add]
  unfold hAt
  dsimp only
  split_ifs with E
  · apply Fin.ext
    change (hLowID (h:=h) t i).val/(z+h)*st z h+(hLowID (h:=h) t i).val%(z+h)=t.val*st z h+i.val
    rw [hmod,hquot]
  · exact (E (by omega)).elim

lemma hAt_private {z h j : ℕ} (hj : 0<j) (hz : 0<z) (t : Fin j) (i : Fin h) :
    hAt hj hz (hPrvID (z:=z) t i) = posP hj t i := by
  have hzH : 0<z+h := by omega
  have lit : z+i.val<z+h := by have := i.isLt; omega
  have hmod : (hPrvID (z:=z) t i).val%(z+h)=z+i.val := by
    change (t.val*(z+h)+(z+i.val))%(z+h)=z+i.val
    rw [Nat.mul_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt lit]
  have hquot : (hPrvID (z:=z) t i).val/(z+h)=t.val := by
    change (t.val*(z+h)+(z+i.val))/(z+h)=t.val
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hzH,Nat.div_eq_of_lt lit,zero_add]
  unfold hAt
  dsimp only
  split_ifs with E
  · exfalso; rw [hmod] at E; omega
  · apply Fin.ext
    change (hPrvID (z:=z) t i).val/(z+h)*st z h+(z+2+((hPrvID (z:=z) t i).val%(z+h)-z)) =
        t.val*st z h+(z+2+i.val)
    rw [hmod,hquot,Nat.add_sub_cancel_left]

lemma hAt_range {z h j : ℕ} (hj : 0<j) (hz : 0<z) (u : Fin (hN z h j)) :
    (∃ (t : Fin (j+1)) (i : Fin z), u = hLowID t i ∧ hAt hj hz u = headS hj t i) ∨
    (∃ (t : Fin j) (i : Fin h), u = hPrvID t i ∧ hAt hj hz u = posP hj t i) := by
  let D := z+h
  let t := u.val/D
  let r := u.val%D
  have hD : 0<D := by omega
  have R : r<D := Nat.mod_lt _ hD
  have T : t*D+r=u.val := by simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div u.val D
  have U : u.val<j*D+z := u.isLt
  have th : t≤j := by
    by_contra! e
    have e' := Nat.mul_le_mul_right D (show j+1≤t by omega)
    rw [Nat.add_mul,one_mul] at e'
    dsimp only [D] at *
    omega
  by_cases L : r<z
  · let t' : Fin (j+1) := ⟨t,by omega⟩
    let i' : Fin z := ⟨r,L⟩
    have E : u = hLowID (h:=h) t' i' := Fin.ext T.symm
    exact Or.inl ⟨t',i',E,E ▸ hAt_low hj hz t' i'⟩
  · have jt : t<j := by
      by_contra! ne
      have eq : t=j := by omega
      rw [eq] at T
      omega
    let t' : Fin j := ⟨t,jt⟩
    let i' : Fin h := ⟨r-z,by dsimp only [D] at R; omega⟩
    have E : u = hPrvID (z:=z) t' i' := Fin.ext (by change u.val=t*D+(z+(r-z)); omega)
    exact Or.inr ⟨t',i',E,E ▸ hAt_private hj hz t' i'⟩

end FussCover
