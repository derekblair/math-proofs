import HaarClass3Collect

namespace HaarClass3Cycle
open HaarClass3Table HaarClass3Collect
variable {G C : Type*} [Group G] [Group C]

theorem x_range (i : Fin 32) : (table i).1=0 ∨ (table i).1= -1 ∨ (table i).1= -2 := by
  revert i
  decide

def vertex (x y c u v : G) (i : Fin 32) : Bool × G :=
  (HaarCycle.side i,norm x y c u v (table i))

theorem adj (x y c u v : G)
    (hu : ∀ z : G, Commute u z) (hv : ∀ z : G, Commute v z)
    (r : x*y=y*x*c) (rx : c*x=x*c*u) (ry : c*y=y*c*v) (i : Fin 32) :
    HaarCycle.haarAdj x y (vertex x y c u v i) (vertex x y c u v (i+1)) := by
  have transfer (a b : Fin 32) (h : edge (table a) (table b)) :
      norm x y c u v (table b)=norm x y c u v (table a) ∨
      norm x y c u v (table b)=norm x y c u v (table a)*x ∨
      norm x y c u v (table b)=norm x y c u v (table a)*y := by
    rcases h with h | h | h
    · exact Or.inl (congrArg _ h)
    · exact Or.inr (Or.inl ((congrArg _ h).trans (norm_x x y c u v hu hv rx (table a))))
    · exact Or.inr (Or.inr ((congrArg _ h).trans (norm_y x y c u v hu hv r rx ry (table a) (x_range a))))
  have hCert := step i
  have hs := HaarCycle.differentSide i
  cases h1 : HaarCycle.side i <;> cases h2 : HaarCycle.side (i+1) <;>
    simp [h1,h2] at hs hCert
  · exact (by simpa [HaarCycle.haarAdj,vertex,h1,h2] using transfer _ _ hCert)
  · exact (by simpa [HaarCycle.haarAdj,vertex,h1,h2] using transfer _ _ hCert)

theorem pow_ne {g : C} (ng : g ≠ 1) (ng2 : g^2≠1) {i j : ℤ} (h : modest (i-j)) :
    g^i ≠ g^j := by
  have h' : i-j=1 ∨ i-j=2 ∨ j-i=1 ∨ j-i=2 := by
    unfold modest at h
    rcases abs_choice (i-j) with a | a <;> omega
  exact HaarCycle.centralNE g ng ng2 i j h'

theorem projected_normal (x y c u v : G) (cz : G →* C)
    (hcu : cz u=1) (hcv : cz v=1) (p : Coord) :
    cz (HaarClass3Collect.norm x y c u v p) =
      HaarCycle.norm (cz x) (cz y) (cz c) (p.1,p.2.1,p.2.2.1) := by
  simp [HaarClass3Collect.norm,HaarCycle.norm,hcu,hcv]

theorem injective_map (x y c u v : G)
    (r : x*y=y*x*c) (rx : c*x=x*c*u) (ry : c*y=y*c*v)
    (cz : G →* C)
    (hc : cz c ≠ 1) (hc' : (cz c)^2 ≠ 1) (hcu : cz u=1) (hcv : cz v=1)
    (hv : v ≠ 1) (hv' : v^2 ≠ 1) :
    Function.Injective (vertex x y c u v) := by
  have rel : cz x * cz y = cz y * cz x * cz c := by simpa using congrArg cz r
  have cx : Commute (cz c) (cz x) := by
    change cz c * cz x = cz x * cz c
    simpa [hcu] using congrArg cz rx
  have cy : Commute (cz c) (cz y) := by
    change cz c * cz y = cz y * cz c
    simpa [hcv] using congrArg cz ry
  intro i j heq
  have H := congrArg Prod.snd heq
  change HaarClass3Collect.norm x y c u v (table i)=HaarClass3Collect.norm x y c u v (table j) at H
  let p : HaarCycle.Coord := ((table i).1,(table i).2.1,(table i).2.2.1)
  let q : HaarCycle.Coord := ((table j).1,(table j).2.1,(table j).2.2.1)
  have hpq : HaarCycle.norm (cz x) (cz y) (cz c) p = HaarCycle.norm (cz x) (cz y) (cz c) q :=
    (projected_normal x y c u v cz hcu hcv (table i)).symm.trans
      ((congrArg cz H).trans (projected_normal x y c u v cz hcu hcv (table j)))
  rcases split i j with E | E | E | E | ⟨a,b,k⟩ | ⟨a,b,k,l,m⟩
  · exact E
  · exact (E (congrArg Prod.fst heq)).elim
  · exfalso
    apply pow_ne hc hc' (show modest (p.1-q.1) from E)
    apply mul_left_cancel (a := cz y * HaarCycle.norm (cz x) (cz y) (cz c) p)
    rw [← HaarCycle.normShiftY (cz x) (cz y) (cz c) cx cy rel p,hpq,
      HaarCycle.normShiftY (cz x) (cz y) (cz c) cx cy rel q,← hpq]
  · exfalso
    have hm : modest ((-p.2.1)-(-q.2.1)) := by
      unfold modest
      rw [show (-p.2.1)-(-q.2.1)= -(p.2.1-q.2.1) by ring,abs_neg]
      exact E
    apply pow_ne hc hc' hm
    apply mul_left_cancel (a := cz x * HaarCycle.norm (cz x) (cz y) (cz c) p)
    rw [← HaarCycle.normShiftX (cz x) (cz y) (cz c) cx cy rel p,hpq,
      HaarCycle.normShiftX (cz x) (cz y) (cz c) cx cy rel q,← hpq]
  · dsimp [p,q,HaarCycle.norm] at hpq
    rw [a,b] at hpq
    exact (pow_ne hc hc' k (mul_left_cancel hpq)).elim
  · unfold HaarClass3Collect.norm at H
    rw [a,b,k,l] at H
    exact (pow_ne hv hv' (Or.inl m) (mul_left_cancel H)).elim

theorem certified (x y c u v : G)
    (hu : ∀ z : G, Commute u z) (hv : ∀ z : G, Commute v z)
    (r : x*y=y*x*c) (rx : c*x=x*c*u) (ry : c*y=y*c*v)
    (cz : G →* C)
    (hc : cz c ≠ 1) (hc' : (cz c)^2 ≠ 1) (hcu : cz u=1) (hcv : cz v=1)
    (hv₁ : v ≠ 1) (hv₂ : v^2 ≠ 1) :
    ∃ w : Fin 32 → Bool × G, Function.Injective w ∧
      ∀ i, HaarCycle.haarAdj x y (w i) (w (i+1)) :=
  ⟨vertex x y c u v, injective_map x y c u v r rx ry cz hc hc' hcu hcv hv₁ hv₂,
    adj x y c u v hu hv r rx ry⟩

end HaarClass3Cycle

#print axioms HaarClass3Cycle.certified
