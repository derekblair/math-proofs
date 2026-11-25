import FussPattern

namespace FussCover

def st (z h : ℕ) : ℕ := step z 1 h
def wi (z h : ℕ) : ℕ := width z 1 h
def n (z h j : ℕ) : ℕ := CoverCutoff.nVerts (wi z h) (st z h) j

lemma st_def (z h : ℕ) : st z h = z+h+2 := by unfold st step; omega
lemma wi_def (z h : ℕ) : wi z h = st z h + (z+2) := by unfold wi width; rw [st_def]; omega
lemma pos_st (z h : ℕ) : 0 < st z h := by rw [st_def]; omega
lemma n_def {z h j : ℕ} (hj : 0<j) : n z h j = j * st z h + (z+2) := by
  unfold n CoverCutoff.nVerts
  rw [wi_def, show j = (j-1)+1 by omega] at ⊢
  have q : j-1+1-1 = j-1 := by omega
  rw [q, Nat.add_mul, one_mul]
  omega

def pos {z h j : ℕ} (hj : 0<j) (t : Fin (j+1)) (i : ℕ) (hi : i<z+2) :
    Fin (n z h j) :=
  ⟨t.val * st z h + i, by
    rw [n_def hj]
    have le : t.val ≤ j := by omega
    have p := Nat.mul_le_mul_right (st z h) le
    omega⟩

def posP {z h j : ℕ} (hj : 0<j) (t : Fin j) (i : Fin h) :
    Fin (n z h j) :=
  ⟨t.val * st z h + (z+2+i.val), by
    rw [n_def hj]
    have le : t.val+1 ≤ j := by omega
    have p := Nat.mul_le_mul_right (st z h) le
    rw [Nat.add_mul,one_mul] at p
    have hi := i.isLt
    rw [st_def] at p ⊢
    omega⟩

def A {z h j : ℕ} (hj : 0<j) (t : Fin (j+1)) : Fin (n z h j) := pos hj t z (by omega)
def B {z h j : ℕ} (hj : 0<j) (t : Fin (j+1)) : Fin (n z h j) := pos hj t (z+1) (by omega)
def headS {z h j : ℕ} (hj : 0<j) (t : Fin (j+1)) (a : Fin z) : Fin (n z h j) :=
  pos hj t a.val (by have := a.isLt; omega)

lemma pos_mod {z h j : ℕ} (hj : 0<j) (t : Fin (j+1)) (i : ℕ) (hi : i<z+2) :
    (pos (z:=z) (h:=h) hj t i hi).val % st z h=i := by
  have q : i<st z h := by rw [st_def]; omega
  change (t.val*st z h+i)%st z h=i
  rw [Nat.mul_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt q]

lemma pos_div {z h j : ℕ} (hj : 0<j) (t : Fin (j+1)) (i : ℕ) (hi : i<z+2) :
    (pos (z:=z) (h:=h) hj t i hi).val / st z h=t.val := by
  have q : i<st z h := by rw [st_def]; omega
  change (t.val*st z h+i)/st z h=t.val
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (pos_st _ _),Nat.div_eq_of_lt q,zero_add]

lemma posP_mod {z h j : ℕ} (hj : 0<j) (t : Fin j) (i : Fin h) :
    (posP (z:=z) hj t i).val % st z h=z+2+i.val := by
  have q : z+2+i.val<st z h := by rw [st_def]; have := i.isLt; omega
  change (t.val*st z h+(z+2+i.val))%st z h=z+2+i.val
  rw [Nat.mul_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt q]

lemma posP_div {z h j : ℕ} (hj : 0<j) (t : Fin j) (i : Fin h) :
    (posP (z:=z) hj t i).val / st z h=t.val := by
  have q : z+2+i.val<st z h := by rw [st_def]; have := i.isLt; omega
  change (t.val*st z h+(z+2+i.val))/st z h=t.val
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (pos_st _ _),Nat.div_eq_of_lt q,zero_add]

lemma vertex_cover {z h j : ℕ} (hj : 0<j) (v : Fin (n z h j)) :
    (∃ (t : Fin (j+1)) (i : Fin z), v = headS hj t i) ∨
    (∃ (t : Fin j) (i : Fin h), v = posP hj t i) ∨
    (∃ t : Fin (j+1), v = A hj t) ∨ (∃ t : Fin (j+1), v = B hj t) := by
  let s := st z h
  let q := v.val/s
  let r := v.val%s
  have hdiv : q*s+r=v.val := by simpa only [Nat.add_comm,Nat.mul_comm] using Nat.mod_add_div v.val s
  have vr : r<s := Nat.mod_lt _ (pos_st z h)
  have vv : v.val < j * st z h + (z+2) := by have vlt := v.isLt; have e := n_def (z:=z) (h:=h) hj; omega
  have hq : q≤j := by
    by_contra! he
    have hb := Nat.mul_le_mul_right s (show j+1 ≤ q by omega)
    rw [Nat.add_mul,one_mul] at hb
    have hs : z+2≤s := by dsimp [s]; rw [st_def]; omega
    change v.val < j*s+(z+2) at vv
    omega
  have e : q=j → r<z+2 := by
    intro E
    rw [E] at hdiv
    change v.val < j*s+(z+2) at vv
    omega
  let t : Fin (j+1) := ⟨q,by omega⟩
  by_cases a : r<z
  · exact Or.inl ⟨t,⟨r,a⟩,Fin.ext hdiv.symm⟩
  by_cases a2 : r=z
  · apply Or.inr; apply Or.inr; apply Or.inl
    exact ⟨t,Fin.ext (by change v.val=q*s+z; omega)⟩
  by_cases a3 : r=z+1
  · apply Or.inr; apply Or.inr; apply Or.inr
    exact ⟨t,Fin.ext (by change v.val=q*s+(z+1); omega)⟩
  have hlt : q<j := by by_contra! he; have := e (by omega); omega
  have hr : r-(z+2)<h := by change r < st z h at vr; rw [st_def] at vr; omega
  apply Or.inr; apply Or.inl
  refine ⟨⟨q,hlt⟩,⟨r-(z+2),hr⟩,Fin.ext ?_⟩
  change v.val=q*s+(z+2+(r-(z+2)))
  omega

end FussCover
