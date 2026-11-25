import IntegerBasis
import Mathlib.Data.Int.GCD
import Mathlib.Topology.Algebra.Order.Field

namespace PermHex
open Filter
open scoped Topology

lemma floorCast_bound (x : ℝ) : |((⌊x⌋:ℤ):ℝ)-x|≤1 := by
  apply abs_le.mpr
  constructor
  · linarith [Int.lt_floor_add_one x]
  · linarith [Int.floor_le x]

lemma rough_row_approx {x y ε : ℝ} (hxy : ¬(x=0 ∧ y=0)) (hε : 0<ε) :
    ∃ a b : ℤ, ∃ L : ℕ, 0<L ∧ ¬(a=0 ∧ b=0) ∧
      |(a:ℝ)/(L:ℝ)-x|<ε ∧ |(b:ℝ)/(L:ℝ)-y|<ε := by
  let M := max |x| |y|
  have hM : 0<M := by
    by_contra! hM'
    have h1 : |x|≤M := le_max_left _ _
    have h2 : |y|≤M := le_max_right _ _
    exact hxy ⟨abs_eq_zero.mp (by linarith [abs_nonneg x]),abs_eq_zero.mp (by linarith [abs_nonneg y])⟩
  let e := min ε (M/2)
  have he : 0<e := lt_min hε (by positivity)
  obtain ⟨L,hL⟩ := exists_nat_gt (1/e)
  have h1 : 0<(L:ℝ) := (by positivity : 0<1/e).trans hL
  have hLp : 0<L := by exact_mod_cast h1
  have hs : 1/(L:ℝ)<e := by
    apply (div_lt_iff₀ h1).2
    have hh := (div_lt_iff₀ he).1 hL
    rwa [mul_comm]
  let a := ⌊(L:ℝ)*x⌋
  let b := ⌊(L:ℝ)*y⌋
  have hx : |(a:ℝ)/(L:ℝ)-x|<e := by
    have hh : (a:ℝ)/(L:ℝ)-x = ((a:ℝ)-(L:ℝ)*x)/(L:ℝ) := by
      field_simp [h1.ne'] <;> ring
    rw [hh,abs_div,abs_of_pos h1]
    exact (div_le_div_of_nonneg_right (floorCast_bound _) h1.le).trans_lt hs
  have hy : |(b:ℝ)/(L:ℝ)-y|<e := by
    have hh : (b:ℝ)/(L:ℝ)-y = ((b:ℝ)-(L:ℝ)*y)/(L:ℝ) := by
      field_simp [h1.ne'] <;> ring
    rw [hh,abs_div,abs_of_pos h1]
    exact (div_le_div_of_nonneg_right (floorCast_bound _) h1.le).trans_lt hs
  refine ⟨a,b,L,hLp,?_,hx.trans_le (min_le_left _ _),hy.trans_le (min_le_left _ _)⟩
  rintro ⟨ha,hb⟩
  simp only [ha,hb,Int.cast_zero,zero_div,zero_sub,abs_neg] at hx hy
  have hme : e≤M/2 := min_le_right _ _
  have hm : M<e := max_lt hx hy
  linarith

lemma primitive_direction {x y ε : ℝ} (hxy : ¬(x=0 ∧ y=0)) (hε : 0<ε) :
    ∃ p q : ℤ, ∃ scale : ℝ, 0<scale ∧ PrimitiveRow p q ∧
      |scale*(p:ℝ)-x|<ε ∧ |scale*(q:ℝ)-y|<ε := by
  obtain ⟨a,b,L,hLp,hab,ha,hb⟩ := rough_row_approx hxy hε
  let g := Int.gcd a b
  obtain ⟨p,hp⟩ := Int.gcd_dvd_left a b
  obtain ⟨q,hq⟩ := Int.gcd_dvd_right a b
  change a=(g:ℤ)*p at hp
  change b=(g:ℤ)*q at hq
  have hg : g≠0 := by
    intro hg0
    exact hab ⟨by simpa [hg0] using hp,by simpa [hg0] using hq⟩
  have hgZ : (g:ℤ)≠0 := by exact_mod_cast hg
  let scale : ℝ := (g:ℝ)/(L:ℝ)
  have hscale : 0<scale := by
    dsimp [scale]
    exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hg) (by exact_mod_cast hLp)
  obtain ⟨u,v,huv⟩ : PrimitiveRow p q := by
    let u := Int.gcdA a b
    let v := Int.gcdB a b
    have he := Int.gcd_eq_gcd_ab a b
    change (g:ℤ)=a*u+b*v at he
    rw [hp,hq] at he
    refine ⟨u,v,?_⟩
    apply mul_left_cancel₀ hgZ
    linear_combination -he
  have hpR : (a:ℝ)=(g:ℝ)*(p:ℝ) := by exact_mod_cast hp
  have hqR : (b:ℝ)=(g:ℝ)*(q:ℝ) := by exact_mod_cast hq
  refine ⟨p,q,scale,hscale,⟨u,v,huv⟩,?_,?_⟩
  · have h : scale*(p:ℝ)=(a:ℝ)/(L:ℝ) := by dsimp [scale]; rw [hpR]; ring
    rwa [h]
  · have h : scale*(q:ℝ)=(b:ℝ)/(L:ℝ) := by dsimp [scale]; rw [hqR]; ring
    rwa [h]

lemma eventually_primitive_row {x y ε : ℝ} (hxy : ¬(x=0 ∧ y=0)) (hε : 0<ε) :
    ∀ᶠ R in atTop, ∃ a b : ℤ, PrimitiveRow a b ∧
      |(a:ℝ)-R*x|≤ε*R ∧ |(b:ℝ)-R*y|≤ε*R := by
  obtain ⟨p,q,scale,hscale,⟨u,v,huv⟩,hp,hq⟩ := primitive_direction hxy (show 0<ε/2 by positivity)
  let C := |(p:ℝ)|+|(q:ℝ)|+|(u:ℝ)|+|(v:ℝ)|
  filter_upwards [eventually_ge_atTop (max 1 (2*C/ε))] with R hR
  have hR1 : 1≤R := (le_max_left _ _).trans hR
  have hR0 : 0≤R := by linarith
  have hbnd : C≤ε*R/2 := by
    have hr := (le_max_right (1:ℝ) _).trans hR
    have hh := (div_le_iff₀ hε).1 hr
    nlinarith
  let m := ⌊scale*R⌋
  let a := m*p-v
  let b := m*q+u
  have hfm : |(m:ℝ)-scale*R|≤1 := floorCast_bound _
  have hab : PrimitiveRow a b := by
    refine ⟨-q,p,?_⟩
    dsimp [a,b]
    linear_combination huv
  have ha : (a:ℝ)-R*x = ((m:ℝ)-scale*R)*(p:ℝ) -(v:ℝ) + R*(scale*(p:ℝ)-x) := by
    dsimp [a]
    push_cast
    ring
  have hb : (b:ℝ)-R*y = ((m:ℝ)-scale*R)*(q:ℝ) +(u:ℝ) + R*(scale*(q:ℝ)-y) := by
    dsimp [b]
    push_cast
    ring
  refine ⟨a,b,hab,?_,?_⟩
  · rw [ha]
    have hone := mul_le_mul_of_nonneg_right hfm (abs_nonneg (p:ℝ))
    have htwo := mul_le_mul_of_nonneg_left hp.le hR0
    have hsum := abs_add_le (((m:ℝ)-scale*R)*(p:ℝ)-(v:ℝ)) (R*(scale*(p:ℝ)-x))
    have hsm : |((m:ℝ)-scale*R)*(p:ℝ)-(v:ℝ)| ≤
        |((m:ℝ)-scale*R)*(p:ℝ)|+|(v:ℝ)| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (((m:ℝ)-scale*R)*(p:ℝ)) (-(v:ℝ))
    simp only [sub_zero,abs_mul,abs_of_nonneg hR0] at hsum hsm
    dsimp [C] at hbnd
    linarith [abs_nonneg (q:ℝ),abs_nonneg (u:ℝ)]
  · rw [hb]
    have hone := mul_le_mul_of_nonneg_right hfm (abs_nonneg (q:ℝ))
    have htwo := mul_le_mul_of_nonneg_left hq.le hR0
    have hsum := abs_add_le (((m:ℝ)-scale*R)*(q:ℝ)+(u:ℝ)) (R*(scale*(q:ℝ)-y))
    have hsm := abs_add_le (((m:ℝ)-scale*R)*(q:ℝ)) (u:ℝ)
    simp only [abs_mul,abs_of_nonneg hR0] at hsum hsm
    dsimp [C] at hbnd
    linarith [abs_nonneg (p:ℝ),abs_nonneg (v:ℝ)]

#print axioms eventually_primitive_row
end PermHex
