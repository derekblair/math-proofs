import RibbonClass3SharpCert
import Ribbon5Walk

namespace RibbonClass3SharpGraph
open Ribbon5Bridge

variable {G : Type*} [Group G]

private theorem generic_port {x y : G} {u v : Bool × G}
    (e : Ribbon.Adj x y u v) : ∃ j, action x y u j=v := by
  rcases e with ⟨hu,hv,(h|h)⟩ | ⟨hu,hv,(h|h)⟩ | ⟨s,g⟩
  · exact ⟨0,Prod.ext (hu.trans hv.symm) (by simpa [action,hu] using h)⟩
  · refine ⟨1,Prod.ext (hu.trans hv.symm) ?_⟩
    simpa [action,hu,mul_assoc] using congrArg (·*x⁻¹) h.symm
  · exact ⟨0,Prod.ext (hu.trans hv.symm) (by simpa [action,hu] using h)⟩
  · refine ⟨1,Prod.ext (hu.trans hv.symm) ?_⟩
    simpa [action,hu,mul_assoc] using congrArg (·*y⁻¹) h.symm
  · have E : (!u.1)=v.1 := by cases hu : u.1 <;> cases hv : v.1 <;> simp_all
    exact ⟨2,Prod.ext E g⟩

private theorem generic_symm {x y : G} {u v : Bool × G} (E : Ribbon.Adj x y u v) :
    Ribbon.Adj x y v u := by
  rcases E with ⟨p,q,h⟩ | ⟨p,q,h⟩ | ⟨p,q⟩
  · exact Or.inl ⟨q,p,h.symm⟩
  · exact Or.inr (Or.inl ⟨q,p,h.symm⟩)
  · exact Or.inr (Or.inr ⟨Ne.symm p,q.symm⟩)

def pr (f : G →* H) (v : Bool × G) : V := (v.1,f v.2)

private theorem pr_action (f : G →* H) (x y : G) (hx : f x=a) (hy : f y=b)
    (u : Bool × G) (p : P) : pr f (action x y u p) = step (pr f u) p := by
  obtain ⟨s,g⟩ := u
  cases s <;> fin_cases p <;> simp [pr,step,action,hx,hy]

private theorem step_base_inj : ∀ s : Bool, Function.Injective (step (s,1)) := by
  unfold Function.Injective
  decide +kernel

private theorem step_inj (v : V) : Function.Injective (step v) := by
  obtain ⟨s,g⟩ := v
  intro p q e
  apply step_base_inj s
  apply left_inj g
  rw [left_step,left_step]
  simpa [left] using e

private theorem neighbor_pr_inj (f : G →* H) (x y : G) (hx : f x=a) (hy : f y=b)
    {u v w : Bool × G} (uv : Ribbon.Adj x y u v) (uw : Ribbon.Adj x y u w)
    (E : pr f v=pr f w) : v=w := by
  obtain ⟨p,hp⟩ := generic_port uv
  obtain ⟨q,hq⟩ := generic_port uw
  have en : step (pr f u) p=step (pr f u) q := by
    rw [←pr_action f x y hx hy,←pr_action f x y hx hy,hp,hq,E]
  rw [←hp,←hq,step_inj _ en]

private theorem pr_edge (f : G →* H) (x y : G) (hx : f x=a) (hy : f y=b)
    {u v : Bool × G} (uv : Ribbon.Adj x y u v) :
    ∃ p, step (pr f u) p=pr f v := by
  obtain ⟨p,ep⟩ := generic_port uv
  exact ⟨p,(pr_action f x y hx hy u p).symm.trans (congrArg (pr f) ep)⟩

private theorem half_endpoint (v : Nat → V) (h : Nat) (hh : 2≤h) (q : P)
    (first : step (v 0) q=v 1)
    (edge : ∀ j<h, ∃ p, step (v j) p=v (j+1))
    (nobounce : ∀ j, j+2≤h → v j≠v (j+2)) :
    v h ∈ ends (h-1) (step (v 0) q) q := by
  have E : 1+(h-1)=h := by omega
  rw [first,←E]
  have B : v (1+(h-1)) ∈ ends (h-1) (v 1) q := by
    apply ends_mem v 1 (h-1) q
    · intro j _ hj
      exact edge j (by omega)
    · intro j _ hj
      exact nobounce j (by omega)
    · intro _ eq
      have G : v 0 = v (1+1) := by rw [←eq,←first,back_step]
      exact nobounce 0 (by omega) G
  simpa [E] using B

/-- An arbitrary port-preserving lift cannot have any of the certified short
simple cycles. The projection need not be globally injective. -/
theorem excluded_lift (f : G →* H) (x y : G) (hx : f x=a) (hy : f y=b)
    (h : Nat) (hh : 2≤h) (check : Checked h) : ¬ Ribbon.Cycle x y (2*h) := by
  rintro ⟨v,vi,ve⟩
  have pos : 0<2*h := by omega
  let idx (i : Nat) : Fin (2*h) := ⟨i%(2*h), Nat.mod_lt _ pos⟩
  let F0 (i : Nat) := v (idx i)
  let R0 (i : Nat) := v (idx (2*h-i))
  have uf (j : Nat) (hj : j<h) : Ribbon.Adj x y (F0 j) (F0 (j+1)) := by
    have w := ve (idx j)
    have jv : (idx j).val=j := Nat.mod_eq_of_lt (by omega)
    have eq : (⟨((idx j).val+1)%(2*h),Nat.mod_lt _ pos⟩ : Fin (2*h)) = idx (j+1) :=
      Fin.ext (by simp [jv,idx])
    rw [eq] at w
    exact w
  have ur (j : Nat) (hj : j<h) : Ribbon.Adj x y (R0 j) (R0 (j+1)) := by
    let k := 2*h-(j+1)
    have klt : k<2*h := by dsimp [k]; omega
    have knext : k+1=2*h-j := by dsimp [k]; omega
    have er := ve (idx k)
    have ek : (idx k).val=k := Nat.mod_eq_of_lt klt
    have eq : (⟨((idx k).val+1)%(2*h),Nat.mod_lt _ pos⟩ : Fin (2*h)) = idx (2*h-j) :=
      Fin.ext (by simp [ek,idx,knext])
    rw [eq] at er
    exact generic_symm er
  have startEq : R0 0=F0 0 := by simp [R0,F0,idx]
  let g := (pr f (F0 0)).2⁻¹
  let F (i : Nat) := left g (pr f (F0 i))
  let R (i : Nat) := left g (pr f (R0 i))
  have Fstart : F 0 = ((F0 0).1,1) := by simp [F,g,left,pr]
  have Rstart : R 0 = F 0 := by simp [R,F,startEq]
  have finish : F h=R h := by
    have eq : 2*h-h=h := by omega
    simp [F,R,F0,R0,eq]
  have ef (j : Nat) (hj : j<h) : ∃ p, step (F j) p=F (j+1) := by
    obtain ⟨p,hp⟩ := pr_edge f x y hx hy (uf j hj)
    exact ⟨p,(left_step g _ p).symm.trans (congrArg (left g) hp)⟩
  have er (j : Nat) (hj : j<h) : ∃ p, step (R j) p=R (j+1) := by
    obtain ⟨p,hp⟩ := pr_edge f x y hx hy (ur j hj)
    exact ⟨p,(left_step g _ p).symm.trans (congrArg (left g) hp)⟩
  have nf (j : Nat) (hj : j+2≤h) : F j ≠ F (j+2) := by
    intro e
    have a := neighbor_pr_inj f x y hx hy (generic_symm (uf j (by omega)))
      (uf (j+1) (by omega)) (left_inj g e)
    have A := congrArg Fin.val (vi a)
    change j%(2*h)=(j+2)%(2*h) at A
    rw [Nat.mod_eq_of_lt (by omega : j<2*h),Nat.mod_eq_of_lt (by omega : j+2<2*h)] at A
    omega
  have nr (j : Nat) (hj : j+2≤h) : R j ≠ R (j+2) := by
    intro e
    have a := neighbor_pr_inj f x y hx hy (generic_symm (ur j (by omega)))
      (ur (j+1) (by omega)) (left_inj g e)
    have A := congrArg Fin.val (vi a)
    change (2*h-j)%(2*h)=(2*h-(j+2))%(2*h) at A
    by_cases z : j=0
    · rw [z,Nat.sub_zero,Nat.mod_self,Nat.mod_eq_of_lt (by omega : 2*h-(0+2)<2*h)] at A
      omega
    · rw [Nat.mod_eq_of_lt (by omega : 2*h-j<2*h),Nat.mod_eq_of_lt (by omega : 2*h-(j+2)<2*h)] at A
      omega
  obtain ⟨q,hq⟩ := ef 0 (by omega)
  obtain ⟨r,hr⟩ := er 0 (by omega)
  have qr : q≠r := by
    intro eq
    rw [eq,←Rstart,hr] at hq
    have A := ur 0 (by omega)
    rw [startEq] at A
    have a := neighbor_pr_inj f x y hx hy A (uf 0 (by omega)) (left_inj g hq)
    have E := congrArg Fin.val (vi a)
    change (2*h-1)%(2*h)=1%(2*h) at E
    rw [Nat.mod_eq_of_lt (by omega : 2*h-1<2*h),Nat.mod_eq_of_lt (by omega : 1<2*h)] at E
    omega
  have p := half_endpoint F h hh q hq ef nf
  have q' := half_endpoint R h hh r hr er nr
  rw [Fstart] at p
  rw [←finish,Rstart,Fstart] at q'
  exact check _ q r qr p q'

end RibbonClass3SharpGraph
#print axioms RibbonClass3SharpGraph.excluded_lift
