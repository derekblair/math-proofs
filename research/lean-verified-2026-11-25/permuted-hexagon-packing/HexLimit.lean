import HexDensity
import Limit

namespace PermHex
open Filter
open scoped Topology

def HexMin (c s r : ℝ) {n : ℕ} (p : Equiv.Perm (Fin n)) : Prop :=
  2≤n ∧ (∀ i j, i≠j → 2*r≤gaugeR c s (center p i-center p j)) ∧
    ∀ m, HexFits c s r m → n≤m

lemma rescaled_upper {c s ε : ℝ} (hU : c^2+s^2=1)
    (hε : 0<ε) (hε' : ε<1/24) :
    ∀ᶠ r in atTop, ∃ m, HexFits c s r m ∧
          (m:ℝ)≤((areaUnit+14*ε)/(1-12*ε)^2)*r^2 := by
  obtain ⟨R,hR⟩ := eventually_atTop.1 (eventual_oriented_packing hU hε hε')
  let c0 := 1-12*ε
  have hc0 : 0<c0 := by dsimp [c0]; linarith
  filter_upwards [eventually_ge_atTop (R*c0)] with r hr
  have hb : R≤r/c0 := by rwa [le_div_iff₀ hc0]
  obtain ⟨m,hm,hd⟩ := hR (r/c0) hb
  have he : r/c0*(1-12*ε)=r := by change r/c0*c0=r; exact div_mul_cancel₀ _ hc0.ne'
  rw [he] at hm
  refine ⟨m,hm,hd.trans_eq ?_⟩
  change (areaUnit+14*ε)*(r/c0)^2=((areaUnit+14*ε)/c0^2)*r^2
  rw [div_pow]
  ring

theorem eventually_min_exists {c s : ℝ} (hU : c^2+s^2=1) :
    ∀ᶠ r in atTop, ∃ (n : ℕ) (p : Equiv.Perm (Fin n)), HexMin c s r p := by
  classical
  filter_upwards [rescaled_upper hU (by norm_num : (0:ℝ)<1/48) (by norm_num)] with r hi
  obtain ⟨m,hm,_⟩ := hi
  have he : ∃ n, HexFits c s r n := ⟨m,hm⟩
  obtain ⟨hn,p,hp⟩ := Nat.find_spec he
  exact ⟨Nat.find he,p,hn,hp,fun j hj => Nat.find_min' he hj⟩

lemma coefficient_choice {δ : ℝ} (hδ : 0<δ) :
    ∃ ε : ℝ, 0<ε ∧ ε<1/24 ∧ (areaUnit+14*ε)/(1-12*ε)^2<areaUnit+δ := by
  have hA := areaUnit_pos
  let B := 24*(areaUnit+δ)+14
  have hB : 0<B := by dsimp [B]; positivity
  let ε := min (1/48) (δ/(2*B))
  have hε : 0<ε := lt_min (by norm_num) (div_pos hδ (by positivity))
  have hε' : ε<1/24 := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨ε,hε,hε',?_⟩
  have hP : 0<1-12*ε := by linarith
  have hSmall : ε*B≤δ/2 := by
    have he : ε≤δ/(2*B) := min_le_right _ _
    have hh := (le_div_iff₀ (show 0<2*B by positivity)).mp he
    nlinarith only [hh]
  have hx := mul_nonneg (show 0≤areaUnit+δ by positivity) (sq_nonneg ε)
  apply (div_lt_iff₀ (pow_pos hP 2)).mpr
  dsimp [B] at hSmall
  nlinarith only [hSmall,hx,hδ]

lemma order_limit {c s : ℝ} (hU : c^2+s^2=1)
    {n : ℝ→ℕ} (p : ∀ t, Equiv.Perm (Fin (n t)))
    (hM : ∀ᶠ t in atTop, HexMin c s t (p t)) :
    Tendsto (fun t => (n t:ℝ)/t^2) atTop (𝓝 areaUnit) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have hp := (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
    have hl : Tendsto (fun t : ℝ => areaUnit-272*t⁻¹) atTop (𝓝 areaUnit) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hp)
    filter_upwards [hl.eventually_const_lt ha,hM,eventually_ge_atTop (1:ℝ)] with t ht hm h1
    have hlow := lower_size hU (by linarith : 0<t) ⟨hm.1,p t,hm.2.1⟩
    have ht0 : 0<t := by linarith
    have hb : areaUnit-272*t⁻¹≤(n t:ℝ)/t^2 := by
      apply (le_div_iff₀ (pow_pos ht0 2)).2
      convert hlow using 1
      field_simp [ht0.ne']
    exact ht.trans_le hb
  · intro b hb
    obtain ⟨ε,hε,hε',hc⟩ := coefficient_choice (show 0<b-areaUnit by linarith)
    filter_upwards [rescaled_upper hU hε hε',hM,eventually_ge_atTop (1:ℝ)] with t hU' hm h1
    obtain ⟨m,hfit,hm'⟩ := hU'
    have hle : (n t:ℝ)≤m := by exact_mod_cast hm.2.2 m hfit
    have hU'' := hle.trans hm'
    have ht0 : 0<t := by linarith
    have he := (div_le_iff₀ (pow_pos ht0 2)).mpr hU''
    exact he.trans_lt (by linarith : (areaUnit+14*ε)/(1-12*ε)^2<b)

/-- The positive-area regular-hexagon analogue of BHT Q5.5, all fixed
    orientations, and every minimizing selection of permutations. -/
theorem oriented_hex_limit {c s : ℝ} (hU : c^2+s^2=1)
    {n : ℝ→ℕ} (p : ∀ t, Equiv.Perm (Fin (n t)))
    (h : ∀ᶠ t in atTop, HexMin c s t (p t)) :
    Tendsto (fun t => clippedDensity c s t (p t)) atTop (𝓝 1) := by
  let A := areaUnit
  let K := Real.pi/A
  have hA0 : 0<A := areaUnit_pos
  have hK0 : 0<K := div_pos Real.pi_pos hA0
  have hN := order_limit hU p h
  have hLo : ∀ᶠ t in atTop,
      Real.pi*t^2*((n t:ℝ)-16*t-4)/((n t:ℝ)-1)^2≤K*clippedDensity c s t (p t) := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have hh := mul_le_mul_of_nonneg_left (density_bounds hU ht (p t)).1 hK0.le
    convert hh using 1
    change Real.pi*t^2*((n t:ℝ)-16*t-4)/((n t:ℝ)-1)^2 =
      Real.pi/A*(A*t^2*((n t:ℝ)-16*t-4)/((n t:ℝ)-1)^2)
    field_simp [hA0.ne'] 
  have hHi : ∀ᶠ t in atTop,
      K*clippedDensity c s t (p t)≤Real.pi*t^2*(n t:ℝ)/((n t:ℝ)-1)^2 := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have hh := mul_le_mul_of_nonneg_left (density_bounds hU ht (p t)).2 hK0.le
    convert hh using 1
    change Real.pi*t^2*(n t:ℝ)/((n t:ℝ)-1)^2 =
      Real.pi/A*(A*t^2*(n t:ℝ)/((n t:ℝ)-1)^2)
    field_simp [hA0.ne'] 
  have hS := PermCircles.clipped_density_limit hA0.ne' hN hLo hHi
  have hInv : Tendsto (fun _ : ℝ => K⁻¹) atTop (𝓝 K⁻¹) := tendsto_const_nhds
  have hh := hInv.mul hS
  have he : K⁻¹*(Real.pi/A)=1 := by change K⁻¹*K=1; exact inv_mul_cancel₀ hK0.ne'
  rw [he] at hh
  convert hh using 1
  funext t
  rw [←mul_assoc,inv_mul_cancel₀ hK0.ne',one_mul]

#print axioms eventually_min_exists
#print axioms oriented_hex_limit
end PermHex
