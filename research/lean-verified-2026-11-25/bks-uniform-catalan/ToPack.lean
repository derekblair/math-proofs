import GlobalFromPack

namespace FussCover
open CoverCutoff

variable {z h j : ℕ}
variable (hj : 0<j) (hz : 0<z)
variable (r : Equiv.Perm (Fin (n z h j)))

def winIndex (z h u : ℕ) : ℕ :=
  let F := 2*z+h
  if u<z then u
  else if u<z+h then u+2
  else if u<F then st z h+(u-(z+h))
  else if u=F then st z h+z
  else if u=F+1 then z
  else if u=F+2 then st z h+(z+1)
  else z+1

lemma i_lt {u : ℕ} (hu : u<wi z h) : winIndex z h u<wi z h := by
  unfold winIndex; dsimp only
  rw [wi_def,st_def] at *
  split_ifs <;> omega

lemma rank_winIndex {u : ℕ} (hu : u<wi z h) : rank z 1 h (winIndex z h u)=u := by
  unfold winIndex
  dsimp only
  rw [wi_def,st_def] at hu
  split_ifs with H₁ H₂ H₃ H₄ H₅ H₆
  · exact rank_prefix_low H₁
  · let i : Fin h := ⟨u-z, by omega⟩
    have e : u+2=z+2+i.val := by dsimp [i]; omega
    rw [e,rank_private]; dsimp [i]; omega
  · let i : Fin z := ⟨u-(z+h),by omega⟩
    rw [show u-(z+h)=i.val from rfl,rank_suffix_low]
    dsimp [i]; omega
  · rw [rank_suffix_A,H₄]
  · rw [rank_prefix_A,H₅]
  · have e : st z h+(z+1)=st z h+z+1 := by omega
    rw [e,rank_suffix_B,H₆]
  · rw [rank_prefix_B]; omega

def wh {t : Fin j} {u : ℕ} (hu : u<2*z+h) : Fin (hN z h j) := by
  refine ⟨t.val*(z+h)+u,?_⟩
  have e := Nat.mul_le_mul_right (z+h) (show t.val+1≤j by omega)
  rw [Nat.add_mul,one_mul] at e
  unfold hN
  omega

lemma wi_head (t : Fin j) {u : ℕ} (hu : u<2*z+h) :
    win t (winIndex z h u) (i_lt (by rw [wi_def,st_def]; omega)) =
      hAt hj hz (wh (t:=t) hu) := by
  unfold winIndex; dsimp only
  split_ifs with H H₂
  · let i : Fin z := ⟨u,H⟩
    have E : wh (t:=t) hu=hLowID (h:=h) t.castSucc i := Fin.ext rfl
    rw [E,hAt_low]
    exact win_prefix hj t u (by omega)
  · let i : Fin h := ⟨u-z,by omega⟩
    have E : wh (t:=t) hu=hPrvID (z:=z) t i := Fin.ext (by
      change t.val*(z+h)+u=t.val*(z+h)+(z+(u-z)); omega)
    have e : u+2=z+2+i.val := by dsimp [i]; omega
    rw [E,hAt_private]
    apply Fin.ext
    change t.val*st z h+(u+2)=t.val*st z h+(z+2+i.val)
    rw [e]
  · let i : Fin z := ⟨u-(z+h),by omega⟩
    have E : wh (t:=t) hu=hLowID (h:=h) t.succ i := Fin.ext (by
      change t.val*(z+h)+u=(t.val+1)*(z+h)+(u-(z+h))
      rw [Nat.add_mul,one_mul]; omega)
    rw [E,hAt_low]
    exact win_suffix hj t i.val (by have := i.isLt; omega)

def CoreOrder : Prop :=
  StrictMono (fun u : Fin (hN z h j) => r (hAt hj hz u)) ∧
  (∀ u t, r (hAt hj hz u)<r (A hj t)) ∧
  (∀ t : Fin j, r (A hj t.succ)<r (A hj t.castSucc)) ∧
  (∀ t : Fin j, r (A hj t.castSucc)<r (B hj t.succ)) ∧
  (∀ t : Fin j, r (B hj t.succ)<r (B hj t.castSucc))

lemma packed_to_order (P : packed r) : CoreOrder hj hz r :=
  ⟨packed_head_mono hj hz r P,packed_H_before_A hj hz r P,
   local_A_desc hj r P,local_cross hj r P,local_B_desc hj r P⟩

lemma wi_aNext (t : Fin j) :
    win t (winIndex z h (2*z+h)) (i_lt (by rw [wi_def,st_def]; omega)) =
      A hj t.succ := by
  have e : winIndex z h (2*z+h)=st z h+z := by unfold winIndex; dsimp only; split_ifs <;> omega
  apply Fin.ext
  change t.val*st z h+winIndex z h (2*z+h)=(t.val+1)*st z h+z
  rw [e,Nat.add_mul,one_mul]; omega
lemma wi_aNow (t : Fin j) :
    win t (winIndex z h (2*z+h+1)) (i_lt (by rw [wi_def,st_def]; omega)) =
      A hj t.castSucc := by
  have e : winIndex z h (2*z+h+1)=z := by unfold winIndex; dsimp only; split_ifs <;> omega
  exact Fin.ext (by change t.val*st z h+winIndex z h (2*z+h+1)=t.val*st z h+z; rw [e])
lemma wi_bNext (t : Fin j) :
    win t (winIndex z h (2*z+h+2)) (i_lt (by rw [wi_def,st_def]; omega)) =
      B hj t.succ := by
  have e : winIndex z h (2*z+h+2)=st z h+(z+1) := by unfold winIndex;dsimp only;split_ifs <;> omega
  apply Fin.ext
  change t.val*st z h+winIndex z h (2*z+h+2)=(t.val+1)*st z h+(z+1)
  rw [e,Nat.add_mul,one_mul]; omega
lemma wi_bNow (t : Fin j) :
    win t (winIndex z h (2*z+h+3)) (i_lt (by rw [wi_def,st_def]; omega)) =
      B hj t.castSucc := by
  have e : winIndex z h (2*z+h+3)=z+1 := by unfold winIndex;dsimp only;split_ifs <;> omega
  exact Fin.ext (by change t.val*st z h+winIndex z h (2*z+h+3)=t.val*st z h+(z+1); rw [e])

def windowRanks (t : Fin j) (u : Fin (wi z h)) : Fin (n z h j) :=
    r (win t (winIndex z h u.val) (i_lt u.isLt))

lemma strictMono_fin_of_nat_succ {m : ℕ} {α : Type} [Preorder α] (f : Fin m → α)
    (H : ∀ (a : Fin m) (ha : a.val+1<m), f a < f ⟨a.val+1,ha⟩) :
    StrictMono f := by
  intro a b hab
  have key (v : ℕ) (hv : a.val+v<m) : f a ≤ f ⟨a.val+v,hv⟩ := by
    induction v with
    | zero => exact le_rfl
    | succ v ih =>
      have ep : a.val+v<m := by omega
      exact (ih ep).trans (H ⟨a.val+v,ep⟩ hv).le
  let v := b.val-a.val-1
  have e : (a.val+v)+1=b.val := by change a.val+(b.val-a.val-1)+1=b.val; change a.val<b.val at hab; omega
  have lt : a.val+v<m := by have := b.isLt; omega
  have hlt : (a.val+v)+1<m := by rw [e]; exact b.isLt
  have bEq : (⟨a.val+v+1,hlt⟩ : Fin m)=b := Fin.ext e
  exact (key v lt).trans_lt (bEq ▸ H ⟨a.val+v,lt⟩ hlt)

lemma windowRanks_mono (t : Fin j) (H : CoreOrder hj hz r) :
    StrictMono (windowRanks r t) := by
  apply strictMono_fin_of_nat_succ
  intro a ha
  unfold windowRanks
  have W : wi z h=2*z+h+4 := by rw [wi_def,st_def]; omega
  have hau : a.val<wi z h := a.isLt
  by_cases E1 : a.val+1<2*z+h
  · rw [wi_head hj hz t (by omega),wi_head hj hz t E1]
    apply H.1
    change t.val*(z+h)+a.val < t.val*(z+h)+(a.val+1)
    omega
  by_cases E2 : a.val<2*z+h
  · have e : a.val+1=2*z+h := by omega
    rw [wi_head hj hz t E2]
    have R : win t (winIndex z h (a.val+1)) (i_lt ha)=A hj t.succ := by
      apply Fin.ext
      change t.val*st z h+winIndex z h (a.val+1) = (t.val+1)*st z h+z
      rw [e]
      exact congrArg Fin.val (wi_aNext hj t)
    rw [R]
    exact H.2.1 _ _
  · have E : a.val=2*z+h ∨ a.val=2*z+h+1 ∨ a.val=2*z+h+2 := by omega
    obtain e|e|e := E
    · have k0 : a = ⟨2*z+h,by omega⟩ := Fin.ext e
      have k1 : (⟨a.val+1,ha⟩: Fin (wi z h)) = ⟨2*z+h+1,by omega⟩ := Fin.ext (by change a.val+1=2*z+h+1; omega)
      calc
        _ = r (A hj t.succ) := (congrArg (windowRanks r t) k0).trans (congrArg r (wi_aNext hj t))
        _ < r (A hj t.castSucc) := H.2.2.1 t
        _ = _ := (congrArg r (wi_aNow hj t)).symm.trans (congrArg (windowRanks r t) k1).symm
    · have k0 : a = ⟨2*z+h+1,by omega⟩ := Fin.ext e
      have k1 : (⟨a.val+1,ha⟩: Fin (wi z h)) = ⟨2*z+h+2,by omega⟩ := Fin.ext (by change a.val+1=2*z+h+2; omega)
      calc
        _ = r (A hj t.castSucc) := (congrArg (windowRanks r t) k0).trans (congrArg r (wi_aNow hj t))
        _ < r (B hj t.succ) := H.2.2.2.1 t
        _ = _ := (congrArg r (wi_bNext hj t)).symm.trans (congrArg (windowRanks r t) k1).symm
    · have k0 : a = ⟨2*z+h+2,by omega⟩ := Fin.ext e
      have k1 : (⟨a.val+1,ha⟩: Fin (wi z h)) = ⟨2*z+h+3,by omega⟩ := Fin.ext (by change a.val+1=2*z+h+3; omega)
      calc
        _ = r (B hj t.succ) := (congrArg (windowRanks r t) k0).trans (congrArg r (wi_bNext hj t))
        _ < r (B hj t.castSucc) := H.2.2.2.2 t
        _ = _ := (congrArg r (wi_bNow hj t)).symm.trans (congrArg (windowRanks r t) k1).symm

lemma order_to_packed (H : CoreOrder hj hz r) : packed r := by
  intro t a b
  let p := pattern z 1 h (by decide)
  have X (x : Fin (wi z h)) :
      winIndex z h (p x).val = x.val := by
    apply rank_inj (show 0<1 by decide) (i_lt (p x).isLt) x.isLt
    exact rank_winIndex (p x).isLt
  have Y (x : Fin (wi z h)) : windowRanks r t (p x) = r (window t x) := by
    apply congrArg r
    apply Fin.ext
    change t.val*st z h+winIndex z h (p x).val = t.val*st z h+x.val
    rw [X]
  change r (window t a) < r (window t b) ↔ p a < p b
  rw [←Y a,←Y b]
  exact (windowRanks_mono hj hz r t H).lt_iff_lt

end FussCover
