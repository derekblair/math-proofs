import Ribbon5PackedSound
import Ribbon5Run

namespace Ribbon5Packed
open HaarMatrixCycle (UT)
open Ribbon5UT (V a b)

theorem back_actualStep (u : V) (j : P) : actualStep (actualStep u j) (back j)=u := by
  obtain ⟨s,g⟩ := u
  cases s <;> fin_cases j <;> simp [actualStep,back,mul_assoc]

theorem adj_port {u v : V} (e : Ribbon.Adj a b u v) : ∃ j, actualStep u j=v := by
  rcases e with ⟨hu,hv,(h|h)⟩ | ⟨hu,hv,(h|h)⟩ | ⟨s,g⟩
  · exact ⟨0,Prod.ext (hu.trans hv.symm) (by simpa [actualStep,hu] using h)⟩
  · refine ⟨1,Prod.ext (hu.trans hv.symm) ?_⟩
    simpa [actualStep,hu,mul_assoc] using congrArg (·*a⁻¹) h.symm
  · exact ⟨0,Prod.ext (hu.trans hv.symm) (by simpa [actualStep,hu] using h)⟩
  · refine ⟨1,Prod.ext (hu.trans hv.symm) ?_⟩
    simpa [actualStep,hu,mul_assoc] using congrArg (·*b⁻¹) h.symm
  · have E : (!u.1)=v.1 := by cases hu : u.1 <;> cases hv : v.1 <;> simp_all
    exact ⟨2,Prod.ext E g⟩

theorem symm {u v : V} (E : Ribbon.Adj a b u v) : Ribbon.Adj a b v u := by
  rcases E with ⟨p,q,h⟩ | ⟨p,q,h⟩ | ⟨p,q⟩
  · exact Or.inl ⟨q,p,h.symm⟩
  · exact Or.inr (Or.inl ⟨q,p,h.symm⟩)
  · exact Or.inr (Or.inr ⟨Ne.symm p,q.symm⟩)

def left (g : UT) (v : V) : V := (v.1,g*v.2)

theorem left_inj (g : UT) : Function.Injective (left g) := by
  intro u v e
  have h := congrArg Prod.fst e
  have h' := congrArg Prod.snd e
  exact Prod.ext h (mul_left_cancel h')

theorem left_actualStep (g : UT) (v : V) (j : P) : left g (actualStep v j)=actualStep (left g v) j := by
  unfold actualStep left
  split <;> simp [mul_assoc]


def Checked16 : Prop :=
  ∀ (s : Bool) (q r : P), q≠r →
    List.Disjoint (ends 15 (step (zero s) q) q) (ends 15 (step (zero s) r) r)

theorem runs_of_actual (v : Nat → V) (i m : Nat) (p : P)
    (edge : ∀ j, i ≤ j → j < i+m → ∃ q, actualStep (v j) q=v (j+1))
    (nobounce : ∀ j, i ≤ j → j+1 < i+m → v j≠v (j+2))
    (prior : m≠0 → actualStep (v i) (back p) ≠ v (i+1)) :
    ∃ q, Runs m (projection (v i)) p (projection (v (i+m))) q := by
  induction m generalizing i p with
  | zero => exact ⟨p,by simpa using Runs.nil (projection (v i)) p⟩
  | succ m ih =>
    obtain ⟨q,hq⟩ := edge i le_rfl (by omega)
    have allowed : q≠back p := by
      intro eq
      exact prior (by omega) (eq ▸ hq)
    have nofirst (hm : m≠0) : actualStep (v (i+1)) (back q) ≠ v (i+1+1) := by
      rw [←hq,back_actualStep]
      exact nobounce i le_rfl (by omega)
    obtain ⟨r,e⟩ := ih (i+1) q
      (fun j hi hj => edge j (by omega) (by omega))
      (fun j hi hj => nobounce j (by omega) (by omega)) nofirst
    have a : i+1+m=i+(m+1) := by omega
    have b : projection (v (i+1)) = step (projection (v i)) q := by
      rw [←hq,step_sound]
    rw [a,b] at e
    exact ⟨r,.cons allowed e⟩

private theorem endpoint (v : Nat → V) (h : Nat) (hh : 2≤h) (q : P)
    (first : actualStep (v 0) q=v 1)
    (edge : ∀ j<h, ∃ p, actualStep (v j) p=v (j+1))
    (inj : ∀ i j, i≤h → j≤h → v i=v j → i=j) :
    ∃ r, Runs (h-1) (step (projection (v 0)) q) q (projection (v h)) r := by
  have s : 1+(h-1)=h := by omega
  obtain ⟨r,e⟩ := runs_of_actual v 1 (h-1) q
    (fun j _ hj => edge j (by omega))
    (by
      intro j _ hj eq
      have x := inj j (j+2) (by omega) (by omega) eq
      omega)
    (by
      intro _ eq
      have z : v 0=v 2 := by rw [←eq,←first,back_actualStep]
      have x := inj 0 2 (by omega) (by omega) z
      omega)
  have E : projection (v 1) = step (projection (v 0)) q := by rw [←first,step_sound]
  exact ⟨r,by simpa only [s,E] using e⟩

/-- A simple cycle splits into two reduced half-walks with the same endpoint,
but with different first ports. A disjoint endpoint spectrum precludes this. -/
theorem excluded (h : Nat) (hh : 2≤h) (hle : h≤16) (check : Checked16) :
    ¬ Ribbon.Cycle a b (2*h) := by
  rintro ⟨v,vi,ve⟩
  have pos : 0<2*h := by omega
  let idx (i : Nat) : Fin (2*h) := ⟨i%(2*h), Nat.mod_lt _ pos⟩
  let xt := (v (idx 0)).2⁻¹
  let F (i : Nat) := left xt (v (idx i))
  let R (i : Nat) := left xt (v (idx (2*h-i)))
  have F0 : F 0 = ((v (idx 0)).1,1) := by simp [F,xt,left]
  have R0 : R 0 = F 0 := by
    dsimp [R,F,idx]
    simp
  have finish : F h=R h := by
    have E : 2*h-h=h := by omega
    simp [F,R,E]
  have eF (j : Nat) (hj : j<h) : ∃ p, actualStep (F j) p=F (j+1) := by
    have er := ve (idx j)
    have ej : (idx j).val=j := Nat.mod_eq_of_lt (by omega)
    have eq : (⟨((idx j).val+1)%(2*h),Nat.mod_lt _ pos⟩ : Fin (2*h)) = idx (j+1) :=
      Fin.ext (by simp [ej,idx])
    rw [eq] at er
    obtain ⟨p,hp⟩ := adj_port er
    exact ⟨p,(left_actualStep xt _ p).symm.trans (congrArg (left xt) hp)⟩
  have eR (j : Nat) (hj : j<h) : ∃ p, actualStep (R j) p=R (j+1) := by
    let k := 2*h-(j+1)
    have klt : k<2*h := by dsimp [k]; omega
    have knext : k+1=2*h-j := by dsimp [k]; omega
    have er := ve (idx k)
    have ek : (idx k).val=k := Nat.mod_eq_of_lt klt
    have eq : (⟨((idx k).val+1)%(2*h),Nat.mod_lt _ pos⟩ : Fin (2*h)) = idx (2*h-j) :=
      Fin.ext (by simp [ek,idx,knext])
    rw [eq] at er
    obtain ⟨p,hp⟩ := adj_port (symm er)
    exact ⟨p,(left_actualStep xt _ p).symm.trans (congrArg (left xt) hp)⟩
  have iF (i j : Nat) (hi : i≤h) (hj : j≤h) (eq : F i=F j) : i=j := by
    have H := congrArg Fin.val (vi ((left_inj xt) eq))
    change i%(2*h)=j%(2*h) at H
    rw [Nat.mod_eq_of_lt (by omega : i<2*h), Nat.mod_eq_of_lt (by omega : j<2*h)] at H
    exact H
  have iR (i j : Nat) (hi : i≤h) (hj : j≤h) (eq : R i=R j) : i=j := by
    have H := congrArg Fin.val (vi ((left_inj xt) eq))
    change (2*h-i)%(2*h)=(2*h-j)%(2*h) at H
    by_cases e : i=0
    · by_cases f : j=0
      · omega
      · rw [e,Nat.sub_zero,Nat.mod_self,Nat.mod_eq_of_lt (by omega : 2*h-j<2*h)] at H
        omega
    · by_cases f : j=0
      · rw [f,Nat.sub_zero,Nat.mod_self,Nat.mod_eq_of_lt (by omega : 2*h-i<2*h)] at H
        omega
      · rw [Nat.mod_eq_of_lt (by omega : 2*h-i<2*h),Nat.mod_eq_of_lt (by omega : 2*h-j<2*h)] at H
        omega
  obtain ⟨q,hq⟩ := eF 0 (by omega)
  obtain ⟨r,hr⟩ := eR 0 (by omega)
  have qr : q≠r := by
    intro E
    rw [E,←R0,hr] at hq
    have H := congrArg Fin.val (vi ((left_inj xt) hq))
    change (2*h-1)%(2*h)=1%(2*h) at H
    rw [Nat.mod_eq_of_lt (by omega : 2*h-1<2*h),Nat.mod_eq_of_lt (by omega : 1<2*h)] at H
    omega
  obtain ⟨u,P⟩ := endpoint F h hh q hq eF iF
  obtain ⟨u',Q⟩ := endpoint R h hh r hr eR iR
  rw [F0,proj_zero] at P
  rw [←finish,R0,F0,proj_zero] at Q
  obtain ⟨t,l,k,A,B⟩ := compatible (16-h) (projection (F h)) u u'
  have P' := (P.concat A).member
  have Q' := (Q.concat B).member
  have he : h-1+(16-h)=15 := by omega
  rw [he] at P' Q'
  exact check _ q r qr P' Q'

end Ribbon5Packed
#print axioms Ribbon5Packed.excluded
