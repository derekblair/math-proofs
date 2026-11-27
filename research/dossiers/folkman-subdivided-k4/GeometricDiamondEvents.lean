import GeometricTriangleLabels

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Finset
variable {V : Type*} [DecidableEq V] [Fintype V]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def diamondLabel (x y u v : V) : Four→V :=
  Sum.elim (fun i => if i=0 then x else y) (fun i => if i=0 then u else v)

theorem diamondLabel_injective {x y u v : V} (xy : x≠y) (xu : x≠u) (xv : x≠v)
    (yu : y≠u) (yv : y≠v) (uv : u≠v) :
    Function.Injective (diamondLabel x y u v) := by
  intro i j h
  rcases i with i|i <;> rcases j with j|j
  all_goals fin_cases i <;> fin_cases j <;> first | rfl | (simp [diamondLabel] at h; grind)

theorem diamond_moment_explicit (t : ℝ) (x y u v : V) (xy : x≠y) (xu : x≠u) (xv : x≠v)
    (yu : y≠u) (yv : y≠v) (uv : u≠v) :
    Moment.mean (sphericalHostWeight (E:=E) t)
      (fun g => triangleIndicator g {x,y,u} * triangleIndicator g {x,y,v}) =
      (patternMass (E:=E) diamondEdges t).toReal := by
  classical
  let l : Four↪V := ⟨diamondLabel x y u v, diamondLabel_injective xy xu xv yu yv uv⟩
  have iff (g : EdgeGraph V) : labeledPattern diamondEdges l g ↔
      ({x,y,u}:Finset V).powersetCard 2 ⊆ g ∧ ({x,y,v}:Finset V).powersetCard 2 ⊆ g := by
    rw [diamond_labeled_iff, powerset_two_triple xy xu yu,powerset_two_triple xy xv yv]
    simp [l,diamondLabel,hasEdge,triangleEdges,Finset.insert_subset_iff,
      xy,xu,xv,yu,yv,and_assoc,and_left_comm,and_comm]
  have per (g : EdgeGraph V) :
      triangleIndicator (K:=ℝ) g {x,y,u} * triangleIndicator g {x,y,v} =
        labeledIndicator diamondEdges l g := by
    simp only [triangleIndicator,labeledIndicator,iff]
    split <;> split <;> simp_all
  simp_rw [per]
  exact labeled_moment_probability diamondEdges diamond_noloop l t

theorem diamond_moment_overlap_two (t : ℝ) (s r : Finset V)
    (sc : s.card=3) (rc : r.card=3) (inter : (r∩s).card=2) :
    Moment.mean (sphericalHostWeight (E:=E) t)
      (fun g => triangleIndicator g s * triangleIndicator g r) =
      (patternMass (E:=E) diamondEdges t).toReal := by
  obtain ⟨x,y,xy,xyi⟩ := Finset.card_eq_two.mp inter
  have sub (a : V) (ha : a∈({x,y}:Finset V)) : a∈r∧a∈s := Finset.mem_inter.mp (xyi.symm ▸ ha)
  have xs := (sub x (by simp)).2
  have ys := (sub y (by simp)).2
  have xr := (sub x (by simp)).1
  have yr := (sub y (by simp)).1
  have split (A : Finset V) (ac : A.card=3) (xA : x∈A) (yA : y∈A) :
      ∃ u : V, x≠u ∧ y≠u ∧ A={x,y,u} := by
    have p : ({x,y}:Finset V) ⊆ A := by
      intro w hw
      simp only [Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl|rfl <;> assumption
    have q := Finset.card_sdiff_add_card_eq_card p
    have q2 : ({x,y}:Finset V).card=2 := Finset.card_eq_two.mpr ⟨x,y,xy,rfl⟩
    rw [ac,q2] at q
    have s1 : (A\{x,y}).card=1 := by omega
    obtain ⟨u,ue⟩ := Finset.card_eq_one.mp s1
    have um : u∈A\{x,y} := ue.symm ▸ (by simp : u∈({u}:Finset V))
    refine ⟨u,fun h => (Finset.mem_sdiff.mp um).2 (by simp [h]),
      fun h => (Finset.mem_sdiff.mp um).2 (by simp [h]),?_⟩
    have rel := Finset.sdiff_union_of_subset p
    rw [ue] at rel
    ext a
    rw [← rel]
    simp [or_assoc,or_left_comm,or_comm]
  obtain ⟨u,xu,yu,su⟩ := split s sc xs ys
  obtain ⟨v,xv,yv,rv⟩ := split r rc xr yr
  have uv : u≠v := by
    intro e
    have us : u∈s := su.symm ▸ (by simp : u∈({x,y,u}:Finset V))
    have ur : u∈r := rv.symm ▸ (by simp [e] : u∈({x,y,v}:Finset V))
    have he : u∈({x,y}:Finset V) := xyi ▸ Finset.mem_inter.mpr ⟨ur,us⟩
    simp [Ne.symm xu,Ne.symm yu] at he
  rw [su,rv]
  exact diamond_moment_explicit t x y u v xy xu xv yu yv uv

#print axioms diamond_moment_overlap_two
end RobustFolkman.GeometricGap
