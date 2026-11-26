import RibbonClass3SharpGraph

namespace RibbonClass3SharpGraph

private theorem endpoint (v : Nat → V) (h : Nat) (hh : 2≤h) (q : P)
    (first : step (v 0) q=v 1)
    (edge : ∀ j<h, ∃ p, step (v j) p=v (j+1))
    (inj : ∀ i j, i≤h → j≤h → v i=v j → i=j) :
    v h ∈ ends (h-1) (step (v 0) q) q := by
  have E : 1+(h-1)=h := by omega
  rw [first,←E]
  have B : v (1+(h-1)) ∈ ends (h-1) (v 1) q := by
    apply ends_mem v 1 (h-1) q
    · intro j _ hj
      exact edge j (by omega)
    · intro j _ hj eq
      have e := inj j (j+2) (by omega) (by omega) eq
      omega
    · intro _ eq
      have G : v 0 = v (1+1) := by rw [←eq,←first,back_step]
      have impossible := inj 0 2 (by omega) (by omega) G
      omega
  simpa [E] using B

/-- A simple cycle splits into two reduced half-walks with the same endpoint,
but with different first ports. A disjoint endpoint spectrum precludes this. -/
theorem excluded (h : Nat) (hh : 2≤h) (check : Checked h) :
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
  have eF (j : Nat) (hj : j<h) : ∃ p, step (F j) p=F (j+1) := by
    have er := ve (idx j)
    have ej : (idx j).val=j := Nat.mod_eq_of_lt (by omega)
    have eq : (⟨((idx j).val+1)%(2*h),Nat.mod_lt _ pos⟩ : Fin (2*h)) = idx (j+1) :=
      Fin.ext (by simp [ej,idx])
    rw [eq] at er
    obtain ⟨p,hp⟩ := adj_port er
    exact ⟨p,(left_step xt _ p).symm.trans (congrArg (left xt) hp)⟩
  have eR (j : Nat) (hj : j<h) : ∃ p, step (R j) p=R (j+1) := by
    let k := 2*h-(j+1)
    have klt : k<2*h := by dsimp [k]; omega
    have knext : k+1=2*h-j := by dsimp [k]; omega
    have er := ve (idx k)
    have ek : (idx k).val=k := Nat.mod_eq_of_lt klt
    have eq : (⟨((idx k).val+1)%(2*h),Nat.mod_lt _ pos⟩ : Fin (2*h)) = idx (2*h-j) :=
      Fin.ext (by simp [ek,idx,knext])
    rw [eq] at er
    obtain ⟨p,hp⟩ := adj_port (symm er)
    exact ⟨p,(left_step xt _ p).symm.trans (congrArg (left xt) hp)⟩
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
  have p := endpoint F h hh q hq eF iF
  have p' := endpoint R h hh r hr eR iR
  rw [F0] at p
  rw [←finish,R0,F0] at p'
  exact check _ q r qr p p'

end RibbonClass3SharpGraph
#print axioms RibbonClass3SharpGraph.excluded
