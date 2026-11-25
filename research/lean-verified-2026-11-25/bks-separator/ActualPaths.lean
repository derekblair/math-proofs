import Physical

namespace PackingSeparator
variable {K J : ℕ} (hk : 4≤K) (p : Equiv.Perm (Fin K))
variable {a b c : ℕ}

abbrev RT (E : α → α → Prop) := Relation.ReflTransGen E
abbrev TG (E : α → α → Prop) := Relation.TransGen E

def L {K J : ℕ} (t : Fin (J+1)) : Fin (nPos K J) := atBlock t 0
def H {K J : ℕ} (t : Fin (J+1)) : Fin (nPos K J) := atBlock t 1

lemma H_L (r1 : (p ⟨1,by omega⟩).val=a)
    (r2 : (p ⟨K-2,by omega⟩).val=b) (hab : a<b) (t : Fin J) :
    TG (stepEdges hk p) (H t.castSucc) (L t.succ) := by
  have q := within hk p t (i:=⟨1,by omega⟩) (l:=⟨K-2,by omega⟩)
    (by change (p ⟨1,by omega⟩).val < (p ⟨K-2,by omega⟩).val; rwa [r1,r2])
  rw [show atPos hk t ⟨1,by omega⟩ = H t.castSucc from prefix_pos hk t (1 : Fin 2),
      show atPos hk t ⟨K-2,by omega⟩ = L t.succ from suffix_pos hk t (0 : Fin 2)] at q
  exact q

lemma last_in_window (t : Fin J) :
    atPos hk t ⟨K-1,by omega⟩ = H t.succ := by
  have F := suffix_pos hk t (1 : Fin 2)
  have I : (⟨K-2+(1:Fin 2).val,by omega⟩ : Fin K)=⟨K-1,by omega⟩ :=
    Fin.ext (by change K-2+1=K-1;omega)
  rwa [I] at F

lemma L_H (r2 : (p ⟨K-2,by omega⟩).val=b)
    (r3 : (p ⟨K-1,by omega⟩).val=c) (hbc : b<c) (t : Fin J) :
    TG (stepEdges hk p) (L t.succ) (H t.succ) := by
  have q := within hk p t (i:=⟨K-2,by omega⟩) (l:=⟨K-1,by omega⟩)
    (by change (p ⟨K-2,by omega⟩).val < (p ⟨K-1,by omega⟩).val; rwa [r2,r3])
  rw [show atPos hk t ⟨K-2,by omega⟩ = L t.succ from suffix_pos hk t (0 : Fin 2),
      last_in_window] at q
  exact q

lemma H_mono (r1 : (p ⟨1,by omega⟩).val=a)
    (r2 : (p ⟨K-2,by omega⟩).val=b)
    (r3 : (p ⟨K-1,by omega⟩).val=c) (hab : a<b) (hbc : b<c)
    {s t : Fin (J+1)} (h : s≤t) :
    RT (stepEdges hk p) (H s) (H t) := by
  have aux (i : ℕ) (hi : s.val+i<J+1) :
      RT (stepEdges hk p) (H s) (H (⟨s.val+i,hi⟩ : Fin (J+1))) := by
    induction i with
    | zero => exact Relation.ReflTransGen.refl
    | succ i ih =>
      let u : Fin J := ⟨s.val+i,by omega⟩
      have A : RT (stepEdges hk p) (H s) (H u.castSucc) := ih (by omega)
      have E := (H_L hk p r1 r2 hab u).trans (L_H hk p r2 r3 hbc u)
      exact A.trans E.to_reflTransGen
  have hle : s.val≤t.val := h
  have e : s.val+(t.val-s.val)=t.val := by omega
  have out := aux (t.val-s.val) (by rw [e]; exact t.isLt)
  have e' : (⟨s.val+(t.val-s.val),by rw [e];exact t.isLt⟩ : Fin (J+1))=t := Fin.ext e
  rwa [e'] at out

lemma first_le (r0 : (p ⟨0,by omega⟩).val=0) (t : Fin J) (i : Fin K) :
    RT (stepEdges hk p) (L t.castSucc) (atPos hk t i) := by
  have L' : L (K:=K) t.castSucc = atPos hk t ⟨0,by omega⟩ := (prefix_pos hk t (0 : Fin 2)).symm
  rw [L']
  by_cases e : i.val=0
  · have E : i=(⟨0,by omega⟩ : Fin K) := Fin.ext e
    rw [E]
  · apply (within hk p t ?_).to_reflTransGen
    change (p ⟨0,by omega⟩).val < (p i).val
    rw [r0]
    by_contra! he
    have eq : p i = p ⟨0,by omega⟩ := Fin.ext (by omega)
    exact e (congrArg Fin.val (p.injective eq))

lemma pivot_all (J3 : 3≤J) (r0 : (p ⟨0,by omega⟩).val=0)
    (r1 : (p ⟨1,by omega⟩).val=a)
    (r2 : (p ⟨K-2,by omega⟩).val=b)
    (r3 : (p ⟨K-1,by omega⟩).val=c) (hab : a<b) (hbc : b<c)
    (x : Fin (nPos K J)) :
    RT (stepEdges hk p) x (H (⟨1,by omega⟩ : Fin (J+1))) ∨
      RT (stepEdges hk p) (H (⟨1,by omega⟩ : Fin (J+1))) x := by
  let one : Fin (J+1) := ⟨1,by omega⟩
  obtain ⟨t,i,rfl⟩ := cover_pos hk (by omega) x
  have in_same (j' : Fin K) (hh : H (K:=K) one = atPos hk t j') :
      RT (stepEdges hk p) (atPos hk t i) (H one) ∨
        RT (stepEdges hk p) (H one) (atPos hk t i) := by
    rw [hh]
    rcases lt_trichotomy (p i) (p j') with h|h|h
    · exact Or.inl (within hk p t h).to_reflTransGen
    · rw [p.injective h]; exact Or.inl .refl
    · exact Or.inr (within hk p t h).to_reflTransGen
  by_cases h0 : t.val=0
  · have e : t.succ=one := Fin.ext (by change t.val+1=1; omega)
    exact in_same ⟨K-1,by omega⟩ (e ▸ (last_in_window hk t).symm)
  by_cases h1 : t.val=1
  · have e : t.castSucc=one := Fin.ext h1
    exact in_same ⟨1,by omega⟩ (e ▸ (prefix_pos hk t (1 : Fin 2)).symm)
  right
  let prev : Fin J := ⟨t.val-1,by have := t.isLt; omega⟩
  have e : prev.succ=t.castSucc := Fin.ext (by change t.val-1+1=t.val;omega)
  have hh : one≤prev.castSucc := by change 1≤t.val-1; omega
  have start := H_mono hk p r1 r2 r3 hab hbc hh
  have mid := H_L hk p r1 r2 hab prev
  rw [e] at mid
  exact start.trans (mid.to_reflTransGen.trans (first_le hk p r0 t i))

end PackingSeparator
