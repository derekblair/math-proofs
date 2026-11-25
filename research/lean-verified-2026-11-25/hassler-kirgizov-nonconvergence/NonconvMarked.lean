import NonconvWalk
namespace Nonconv
open scoped BigOperators

abbrev Focus (m : Nat) (i : Fin (m+1)) := {f : Route false m // f.val i=q}
abbrev Halves (m : Nat) (i : Fin (m+1)) := Starts true i.val q × Starts false (m-i.val) q

noncomputable instance focusFintype (m : Nat) (i : Fin (m+1)) : Fintype (Focus m i) := Fintype.ofFinite _

def splitL {m : Nat} {i : Fin (m+1)} (f : Focus m i) : Starts true i.val q :=
  ⟨⟨fun j => f.val.val ⟨i.val-j.val,by have := i.isLt; omega⟩, by
      intro j
      have hJ := j.isLt
      have hI := i.isLt
      have h := f.val.property ⟨i.val-j.val-1,by omega⟩
      have e : i.val-j.val-1+1=i.val-j.val := by omega
      change edge (f.val.val ⟨i.val-(j.val+1),by omega⟩) (f.val.val ⟨i.val-j.val,by omega⟩) = true
      have er : i.val-(j.val+1)=i.val-j.val-1 := by omega
      simp only [er]
      simpa [adj,e] using h⟩, by
    exact f.property⟩

def splitR {m : Nat} {i : Fin (m+1)} (f : Focus m i) : Starts false (m-i.val) q :=
  ⟨⟨fun j => f.val.val ⟨i.val+j.val,by have := i.isLt; have := j.isLt; omega⟩, by
      intro j
      have hJ := j.isLt
      have hI := i.isLt
      have h := f.val.property ⟨i.val+j.val,by omega⟩
      change edge (f.val.val ⟨i.val+j.val,by omega⟩) (f.val.val ⟨i.val+(j.val+1),by omega⟩) = true
      simpa [adj,Nat.add_assoc] using h⟩, by
    exact f.property⟩

def joined {m : Nat} {i : Fin (m+1)} (p : Halves m i) (j : Fin (m+1)) : State :=
  if h : j.val  ≤  i.val then p.1.val.val ⟨i.val-j.val,by omega⟩
  else p.2.val.val ⟨j.val-i.val,by have := j.isLt; omega⟩

lemma joined_left {m : Nat} {i : Fin (m+1)} (p : Halves m i) (j : Fin (m+1)) (h : j.val ≤ i.val) :
    joined p j = p.1.val.val ⟨i.val-j.val,by omega⟩ := by simp [joined,h]
lemma joined_right {m : Nat} {i : Fin (m+1)} (p : Halves m i) (j : Fin (m+1)) (h : i.val ≤ j.val) :
    joined p j = p.2.val.val ⟨j.val-i.val,by have := j.isLt; omega⟩ := by
  have hJ := j.isLt
  have hI := i.isLt
  by_cases he : i.val=j.val
  · have eL : i.val-j.val=0 := by omega
    have eR : j.val-i.val=0 := by omega
    rw [joined_left p j (by omega)]
    have e₁ : (⟨i.val-j.val,by omega⟩ : Fin (i.val+1)) = 0 := Fin.ext eL
    have e₂ : (⟨j.val-i.val,by have := j.isLt; omega⟩ : Fin (m-i.val+1)) = 0 := Fin.ext eR
    rw [e₁,e₂,p.1.property,p.2.property]
  · have hh : ¬ (j.val ≤ i.val) := by omega
    simp [joined,hh]

lemma joined_route {m : Nat} {i : Fin (m+1)} (p : Halves m i) : ValidRoute false m (joined p) := by
  intro j
  have hJ := j.isLt
  have hI := i.isLt
  by_cases he : j.val+1 ≤ i.val
  · rw [joined_left p _ (by simp; omega),joined_left p _ (by simpa using he)]
    have hv := p.1.val.property ⟨i.val-(j.val+1),by omega⟩
    change edge (p.1.val.val ⟨(i.val-(j.val+1))+1,by omega⟩) (p.1.val.val ⟨i.val-(j.val+1),by omega⟩)=true at hv
    have eq : (i.val-(j.val+1))+1=i.val-j.val := by omega
    simpa [adj,eq] using hv
  · rw [joined_right p _ (by simp; omega),joined_right p _ (by simp; omega)]
    have hv := p.2.val.property ⟨j.val-i.val,by omega⟩
    change edge (p.2.val.val ⟨j.val-i.val,by omega⟩) (p.2.val.val ⟨(j.val-i.val)+1,by omega⟩)=true at hv
    simp only [Fin.val_castSucc,Fin.val_succ]
    have heq : (⟨j.val+1-i.val,by omega⟩ : Fin (m-i.val+1)) = ⟨(j.val-i.val)+1,by omega⟩ := Fin.ext (by dsimp; omega)
    rw [heq]
    exact hv

def markedSplit (m : Nat) (i : Fin (m+1)) : Focus m i ≃ Halves m i where
  toFun f := (splitL f,splitR f)
  invFun p := ⟨⟨joined p,joined_route p⟩,by
    change joined p i=q
    rw [joined_left p i le_rfl]
    have h : (⟨i.val-i.val,by omega⟩ : Fin (i.val+1)) = 0 := Fin.ext (by simp)
    rw [h]
    exact p.1.property⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    change joined (splitL f,splitR f) j = f.val.val j
    by_cases hf : j.val ≤ i.val
    · rw [joined_left _ _ hf]
      change f.val.val ⟨i.val-(i.val-j.val),by have := i.isLt; omega⟩ = _
      apply congrArg f.val.val
      apply Fin.ext
      dsimp only
      omega
    · rw [joined_right _ _ (by omega)]
      change f.val.val ⟨i.val+(j.val-i.val),by have := j.isLt; omega⟩ = _
      apply congrArg f.val.val
      apply Fin.ext
      dsimp only
      omega
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      funext j
      have hJ := j.isLt
      have hI := i.isLt
      change joined p ⟨i.val-j.val,by omega⟩=p.1.val.val j
      rw [joined_left _ _ (by dsimp; omega)]
      apply congrArg p.1.val.val
      apply Fin.ext
      dsimp
      omega
    · apply Subtype.ext
      apply Subtype.ext
      funext j
      have hJ := j.isLt
      have hI := i.isLt
      change joined p ⟨i.val+j.val,by omega⟩=p.2.val.val j
      rw [joined_right _ _ (by dsimp; omega)]
      apply congrArg p.2.val.val
      apply Fin.ext
      dsimp
      omega

theorem focus_count (m : Nat) (i : Fin (m+1)) :
    Fintype.card (Focus m i) = ways true i.val q * ways false (m-i.val) q := by
  rw [Fintype.card_congr (markedSplit m i),Fintype.card_prod,starts_count,starts_count]

theorem marked_count (m : Nat) : Fintype.card (Σ i : Fin (m+1), Focus m i) = marks m := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [focus_count]
  exact Fin.sum_univ_eq_sum_range (fun i => ways true i q * ways false (m-i) q) (m+1)

end Nonconv
