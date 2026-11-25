import NonconvCounts
namespace Nonconv

def ValidRoute (rev : Bool) (m : Nat) (f : Fin (m+1) → State) : Prop :=
  ∀ i : Fin m, adj rev (f i.castSucc) (f i.succ) = true
abbrev Route (rev : Bool) (m : Nat) := {f : Fin (m+1) → State // ValidRoute rev m f}
abbrev Starts (rev : Bool) (m : Nat) (u : State) := {f : Route rev m // f.val 0=u}
abbrev Next (rev : Bool) (u : State) := {v : State // adj rev u v=true}

noncomputable instance routeFintype (rev : Bool) (m : Nat) : Fintype (Route rev m) := Fintype.ofFinite _
noncomputable instance startsFintype (rev : Bool) (m : Nat) (u : State) : Fintype (Starts rev m u) := Fintype.ofFinite _
noncomputable instance nextFintype (rev : Bool) (u : State) : Fintype (Next rev u) := Fintype.ofFinite _

def routeTail {rev : Bool} {m : Nat} (f : Route rev (m+1)) : Route rev m :=
  ⟨fun i => f.val i.succ, by
    intro i
    exact f.property i.succ⟩

def routeCons {rev : Bool} {m : Nat} (u : State) (f : Route rev m)
    (h : adj rev u (f.val 0)=true) : Route rev (m+1) :=
  ⟨Fin.cons u f.val, by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h
    · exact f.property j⟩

def startsCons (rev : Bool) (m : Nat) (u : State) :
    Starts rev (m+1) u ≃ Σ v : Next rev u, Starts rev m v.val where
  toFun f := ⟨⟨(routeTail f.val).val 0, by
    have hh := f.val.property 0
    have h0 : f.val.val 0 = u := f.property
    change adj rev (f.val.val 0) ((routeTail f.val).val 0) = true at hh
    rwa [h0] at hh⟩,⟨routeTail f.val,rfl⟩⟩
  invFun v := ⟨routeCons u v.2.val (by rw [v.2.property]; exact v.1.property),rfl⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact f.property.symm
    · rfl
  right_inv v := by
    obtain ⟨⟨v,hv⟩,f,hf⟩ := v
    change f.val 0=v at hf
    subst v
    apply Sigma.ext
    · rfl
    · rfl

theorem starts_count (rev : Bool) (m : Nat) (u : State) : Fintype.card (Starts rev m u) = ways rev m u := by
  classical
  induction m generalizing u with
  | zero =>
    letI : Unique (Starts rev 0 u) := {
      default := ⟨⟨fun _ => u, fun i => Fin.elim0 i⟩,rfl⟩
      uniq := fun f => by
        apply Subtype.ext
        apply Subtype.ext
        funext i
        rw [show i=0 by apply Fin.ext; have := i.isLt; omega]
        exact f.property }
    simp [ways]
  | succ m ih =>
    rw [Fintype.card_congr (startsCons rev m u),Fintype.card_sigma]
    change (∑ v : Next rev u, Fintype.card (Starts rev m v.val)) = _
    simp only [ih,ways]
    rw [←Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (fun v : State => adj rev u v=true))
      (by simp) (fun v => ways rev m v)).symm

def routeFirst (rev : Bool) (m : Nat) : Route rev m ≃ Σ u : State, Starts rev m u where
  toFun f := ⟨f.val 0,⟨f,rfl⟩⟩
  invFun f := f.2.val
  left_inv _ := rfl
  right_inv f := by obtain ⟨u,p,h⟩ := f; subst u; rfl

theorem count_routes (m : Nat) : Fintype.card (Route false m) = totalRoutes m := by
  classical
  rw [Fintype.card_congr (routeFirst false m),Fintype.card_sigma]
  simp only [starts_count,totalRoutes]

end Nonconv
