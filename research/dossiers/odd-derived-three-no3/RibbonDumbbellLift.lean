import RibbonDumbbellNumeric

namespace RibbonDumbbell
open Ribbon5Bridge
variable {G Q : Type*} [Group G] [Group Q]

def rho (r s : G) (z : Z) : G := r^z.1 * s^z.2

@[simp] theorem rho_zero (r s : G) : rho r s 0 = 1 := by
  simp [rho,zpow_zero]

theorem rho_add {r s : G} (h : Commute r s) (a b : Z) :
    rho r s (a+b) = rho r s a * rho r s b := by
  change r^(a.1+b.1) * s^(a.2+b.2) = _
  simp only [rho,zpow_add,mul_assoc]
  rw [←mul_assoc (r^b.1), (h.zpow_zpow b.1 a.2).eq,mul_assoc]

theorem rho_neg {r s : G} (h : Commute r s) (a : Z) :
    rho r s (-a) = (rho r s a)⁻¹ := by
  have H := rho_add h a (-a)
  rw [add_neg_cancel,rho_zero] at H
  exact (eq_inv_of_mul_eq_one_right H.symm)

def project (f : G →* Q) (v : Bool × G) : Bool × Q := (v.1,f v.2)

theorem project_shift (f : G →* Q) {r s : G} (fr : f r = 1) (fs : f s = 1)
    (a : Z) (v : Bool × G) :
    project f (shift (rho r s a) v) = project f v := by
  simp [project,shift,rho,map_zpow,fr,fs]

theorem shift_mul (g h : G) (v : Bool × G) :
    shift g (shift h v) = shift (g*h) v := by simp [shift,mul_assoc]

theorem adj_translate (x y g : G) {u v : Bool × G} (H : Ribbon.Adj x y u v) :
    Ribbon.Adj x y (shift g u) (shift g v) := by
  simpa [Ribbon.Adj,shift,mul_assoc] using H

theorem adj_symm (x y : G) {u v : Bool × G} (H : Ribbon.Adj x y u v) :
    Ribbon.Adj x y v u := by
  rcases H with ⟨h,k,L⟩|⟨h,k,L⟩|⟨h,k⟩
  · exact Or.inl ⟨k,h,L.elim Or.inr Or.inl⟩
  · exact Or.inr (Or.inl ⟨k,h,L.elim Or.inr Or.inl⟩)
  · exact Or.inr (Or.inr ⟨Ne.symm h,k.symm⟩)

theorem adj_inverse (x y a : G) {u v : Bool × G}
    (E : Ribbon.Adj x y u (shift a v)) :
    Ribbon.Adj x y v (shift a⁻¹ u) := by
  have h := adj_translate x y a⁻¹ (adj_symm x y E)
  simpa [shift_mul,shift] using h

/-- Forward arcs only: A and B each have 32 edges, and P joins them with 32
edges; only the last edge on A/B may have nontrivial shift. -/
structure Forward (x y r s : G) (v : Tag → Bool × G) : Prop where
  a (i : Dot) : Ribbon.Adj x y (v (src 0 i))
      (shift (if i.val == 31 then r else 1) (v (dst 0 i)))
  b (i : Dot) : Ribbon.Adj x y (v (src 2 i))
      (shift (if i.val == 31 then s else 1) (v (dst 2 i)))
  p (i : Dot) : Ribbon.Adj x y (v (src 4 i)) (v (dst 4 i))


theorem all_arcs (x y r s : G) (h : Commute r s) (v : Tag → Bool × G)
    (F : Forward x y r s v) (a b : Z) (A : rho r s a = r) (B : rho r s b = s)
    (d : Dir) (i : Dot) :
    Ribbon.Adj x y (v (src d i)) (shift (rho r s (gain a b d i)) (v (dst d i))) := by
  have same (d : Dir) (i : Dot) (H : ¬revDir d) :
      Ribbon.Adj x y (v (src d i)) (shift (rho r s (gain a b d i)) (v (dst d i))) := by
    fin_cases d <;> try simp [revDir] at H
    · have q := F.a i
      change Ribbon.Adj x y (v (src 0 i))
        (shift (rho r s (if i.val == 31 then a else 0)) (v (dst 0 i)))
      by_cases k : (i.val == 31)=true <;> simpa [k,A] using q
    · have q := F.b i
      change Ribbon.Adj x y (v (src 2 i))
        (shift (rho r s (if i.val == 31 then b else 0)) (v (dst 2 i)))
      by_cases k : (i.val == 31)=true <;> simpa [k,B] using q
    · simpa [gain,shift] using F.p i
  by_cases H : revDir d
  · have Hd : ¬revDir (alter d) := by
      fin_cases d <;> simp_all [alter,revDir]
    have t := adj_inverse x y _ (same (alter d) (reverseDot i) Hd)
    rw [←reverse_site d i,←reverse_end d i,←rho_neg h,←reverse_gain a b d i] at t
    exact t
  · exact same d i H

/-- Finite lift of a validated closed symbolic walk, provided the allowed
gain levels are distinct in the actual group. This part needs no nilpotence. -/
theorem lift_mode_project {X : Type*} (x y r s : G) (h : Commute r s) (π : Bool × G → X)
    (inv : ∀ (a : Z) (q : Bool × G), π (shift (rho r s a) q) = π q)
    (v : Tag → Bool × G) (vinj : Function.Injective (π ∘ v)) (m : Mode)
    (injLevel : ∀ a ∈ allowed m, ∀ b ∈ allowed m, rho r s a = rho r s b → a=b)
    (arc : ∀ d i, Ribbon.Adj x y (v (src d i))
      (shift (rho r s (gain (shiftA m) (shiftB m) d i)) (v (dst d i)))) :
    Ribbon.Cycle x y (len m) := by
  let W (i : Fin (len m)) := shift (rho r s (levels m i.val)) (v (site m i.val))
  refine ⟨W,?_,?_⟩
  · intro i j E
    have Esite : site m i.val = site m j.val := by
      apply vinj
      have C := congrArg π E
      simpa only [W,inv,Function.comp_apply] using C
    have Elevel : levels m i.val = levels m j.val := by
      apply injLevel _ (level_checked m i) _ (level_checked m j)
      have C := congrArg Prod.snd E
      change rho r s (levels m i.val) * (v (site m i.val)).2 =
        rho r s (levels m j.val) * (v (site m j.val)).2 at C
      rw [Esite] at C
      exact mul_right_cancel C
    apply Fin.ext
    rw [←code_checked m i,←code_checked m j]
    simp only [indexCode,Esite,Elevel]
  · intro i
    have E := step_checked m i
    have H := adj_translate x y (rho r s (levels m i.val))
      (arc (stepDir m i.val) (dot i.val))
    rw [shift_mul,←rho_add h,←E.2,E.1] at H
    exact H

theorem lift_mode (x y r s : G) (h : Commute r s) (f : G →* Q)
    (fr : f r=1) (fs : f s=1) (v : Tag → Bool × G)
    (vinj : Function.Injective (project f ∘ v)) (m : Mode)
    (injLevel : ∀ a ∈ allowed m, ∀ b ∈ allowed m, rho r s a = rho r s b → a=b)
    (arc : ∀ d i, Ribbon.Adj x y (v (src d i))
      (shift (rho r s (gain (shiftA m) (shiftB m) d i)) (v (dst d i)))) :
    Ribbon.Cycle x y (len m) :=
  lift_mode_project x y r s h (project f) (project_shift f fr fs) v vinj m injLevel arc

#print axioms lift_mode_project
#print axioms lift_mode
end RibbonDumbbell
