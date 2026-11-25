import Stamps
import ActualPaths

namespace PackingSeparator

variable {K J : ℕ} (hk : 4≤K) (p : Equiv.Perm (Fin K))
variable {a b c : ℕ}

lemma stamp_pair {t s : Fin J} (e : s.val=t.val+1)
    (ha : 1<a) (hab : a<b) (hbc : b+1<c) (ck : c<K)
    (r0 : (p ⟨0,by omega⟩).val=0) (r1 : (p ⟨1,by omega⟩).val=a)
    (r2 : (p ⟨K-2,by omega⟩).val=b) (r3 : (p ⟨K-1,by omega⟩).val=c) :
    ReachInc (stepEdges hk p)
      (atPos hk s (p.symm ⟨1,by omega⟩)) (atPos hk t (p.symm ⟨b+1,by omega⟩)) := by
  let u := atPos hk s (p.symm ⟨1,by omega⟩)
  let v := atPos hk t (p.symm ⟨b+1,by omega⟩)
  have stampU (flip : Bool) :
      stamp K J hk p a b c flip u = toLex (2*s.val+1,tag1 K flip+1) := by
    dsimp only [u]
    rw [on_window hk p (by omega : 0<a) hab (by omega : b<c) r0 r1 r2 r3,p.apply_symm_apply]
    simp [localStamp,ha]
  have stampV (flip : Bool) :
      stamp K J hk p a b c flip v = toLex (2*t.val+3,tag3 K flip+(b+1)) := by
    dsimp only [v]
    rw [on_window hk p (by omega : 0<a) hab (by omega : b<c) r0 r1 r2 r3,p.apply_symm_apply]
    simp [localStamp,show ¬b+1<a by omega,
      show b+1≠a by omega,show ¬b+1<b by omega,hbc]
  have before : stamp K J hk p a b c false u < stamp K J hk p a b c false v := by
    rw [stampU,stampV,Prod.Lex.toLex_lt_toLex']
    simp [tag1,tag3]
    omega
  have after : stamp K J hk p a b c true v < stamp K J hk p a b c true u := by
    rw [stampU,stampV,Prod.Lex.toLex_lt_toLex']
    simp [tag1,tag3]
    omega
  have E (flip : Bool) (x y : Fin (nPos K J)) (h : stepEdges hk p x y) :
      stamp K J hk p a b c flip x ≤ stamp K J hk p a b c flip y :=
    (stamp_edges hk p (by omega) hab (by omega) r0 r1 r2 r3 flip x y h).le
  exact ⟨fun walk => (not_le_of_gt after) (edge_to_path _ (E true) walk),
    fun walk => (not_le_of_gt before) (edge_to_path _ (E false) walk)⟩

/-- For overlap two and the disjoint pattern ranks in Part I, §7 item 5,
the last position of the first occurrence is a separator. Ranks and positions
are zero-based. The conclusion uses actual prescribed pattern windows. -/
theorem last_first_window_separates (J3 : 3≤J)
    (ha : 1<a) (hab : a<b) (hbc : b+1<c) (ck : c<K)
    (r0 : (p ⟨0,by omega⟩).val=0) (r1 : (p ⟨1,by omega⟩).val=a)
    (r2 : (p ⟨K-2,by omega⟩).val=b) (r3 : (p ⟨K-1,by omega⟩).val=c) :
    ReachSeparator (stepEdges (J:=J) hk p) ⟨K-1,by
      have e := Nat.mul_le_mul_right (K-2) (show 1≤J by omega)
      rw [one_mul] at e
      unfold nPos
      omega⟩ := by
  let t₀ : Fin J := ⟨0,by omega⟩
  let t₁ : Fin J := ⟨1,by omega⟩
  let t₂ : Fin J := ⟨2,by omega⟩
  let z : Fin (nPos K J) := H (⟨1,by omega⟩ : Fin (J+1))
  let I : Fin K := p.symm ⟨1,by omega⟩
  let B : Fin K := p.symm ⟨b+1,by omega⟩
  have u : (p I).val=1 := by simp [I]
  have v : (p B).val=b+1 := by simp [B]
  have eqZ : (⟨K-1,by
      have e := Nat.mul_le_mul_right (K-2) (show 1≤J by omega)
      rw [one_mul] at e
      unfold nPos
      omega⟩ : Fin (nPos K J))=z := by
    apply Fin.ext
    change K-1=1*(K-2)+1
    omega
  have sZ : atPos hk t₀ ⟨K-1,by omega⟩ = z := last_in_window hk t₀
  have fZ : atPos hk t₁ ⟨1,by omega⟩ = z := prefix_pos hk t₁ (1 : Fin 2)
  have aL : TG (stepEdges hk p) (atPos hk t₁ I) z := by
    rw [←fZ]
    apply within
    change (p I).val < (p ⟨1,by omega⟩).val
    rw [u,r1]; exact ha
  have bL : TG (stepEdges hk p) (atPos hk t₀ B) z := by
    rw [←sZ]
    apply within
    change (p B).val < (p ⟨K-1,by omega⟩).val
    rw [v,r3]; exact hbc
  have bR : TG (stepEdges hk p) z (atPos hk t₁ B) := by
    rw [←fZ]
    apply within
    change (p ⟨1,by omega⟩).val < (p B).val
    rw [v,r1]; omega
  have aR : TG (stepEdges hk p) z (atPos hk t₂ I) := by
    have mid := H_L hk p r1 r2 hab t₁
    have s : L (K:=K) t₁.succ = atPos hk t₂ ⟨0,by omega⟩ := (prefix_pos hk t₂ (0 : Fin 2)).symm
    change TG (stepEdges hk p) z (L t₁.succ) at mid
    rw [s] at mid
    apply mid.trans
    apply within
    change (p ⟨0,by omega⟩).val < (p I).val
    rw [u,r0]; decide
  rw [eqZ]
  exact ⟨pivot_all hk p J3 r0 r1 r2 r3 hab (by omega),
    ⟨atPos hk t₁ I,atPos hk t₀ B,aL,bL,stamp_pair hk p (t:=t₀) (s:=t₁) rfl ha hab hbc ck r0 r1 r2 r3⟩,
    ⟨atPos hk t₂ I,atPos hk t₁ B,aR,bR,stamp_pair hk p (t:=t₁) (s:=t₂) rfl ha hab hbc ck r0 r1 r2 r3⟩⟩

#print axioms last_first_window_separates
end PackingSeparator
