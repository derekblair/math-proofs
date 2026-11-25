import DetBound

namespace PermHex
open Filter
open scoped Topology

def center {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) : Point :=
  ((i.val:ℝ),((p i).val:ℝ))

def HexFits (c s t : ℝ) (n : ℕ) : Prop :=
  2≤n ∧ ∃ p : Equiv.Perm (Fin n), ∀ i j, i≠j →
    2*t≤gaugeR c s (center p i-center p j)

lemma ideal_first_nonzero {c s : ℝ} (h : c^2+s^2=1) :
    ¬((ideal c s).a=0 ∧ (ideal c s).b=0) := by
  intro hc
  have hz := ideal_det h
  unfold detR at hz
  rw [hc.1,hc.2,zero_mul,zero_mul,sub_self] at hz
  exact areaUnit_pos.ne' hz.symm

lemma ideal_second_nonzero {c s : ℝ} (h : c^2+s^2=1) :
    ¬((ideal c s).c=0 ∧ (ideal c s).d=0) := by
  intro hc
  have hz := ideal_det h
  unfold detR at hz
  rw [hc.1,hc.2,mul_zero,mul_zero,sub_self] at hz
  exact areaUnit_pos.ne' hz.symm

lemma scaled_n_lb {r ε : ℝ} (hr : 2≤r) (hε : ε<1/24) :
    2≤(areaUnit-14*ε)*r^2 := by
  have hA : 3/2≤areaUnit := by unfold areaUnit; linarith [one_le_root3]
  have hC : 1/2≤areaUnit-14*ε := by linarith
  have hRp : 0≤r := by linarith
  have hq : (4:ℝ)≤r^2 := by
    have he := mul_nonneg (show 0≤r-2 by linarith) (show 0≤r+2 by linarith)
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hC (sq_nonneg r)
  linarith

/-- A primitive approximation of the rotated triangular lattice gives
    a permutation packing at the reduced radius r(1−12ε). -/
theorem eventual_oriented_packing {c s ε : ℝ} (hU : c^2+s^2=1)
    (hε : 0<ε) (hε' : ε<1/24) :
    ∀ᶠ r in atTop, ∃ n, HexFits c s (r*(1-12*ε)) n ∧
      (n:ℝ)≤(areaUnit+14*ε)*r^2 := by
  let I := ideal c s
  filter_upwards [eventually_primitive_row (ideal_first_nonzero hU) hε,
    eventually_primitive_row (ideal_second_nonzero hU) hε,
    eventually_ge_atTop (2:ℝ)] with r hA hB hr
  obtain ⟨a,b,ha,hac,hbc⟩ := hA
  obtain ⟨c',d,hb,hcc,hdc⟩ := hB
  let M : Mat := ⟨(a:ℝ),(b:ℝ),(c':ℝ),(d:ℝ)⟩
  have hNear : Close r ε M I := ⟨hac,hbc,hcc,hdc⟩
  have hr0 : 0≤r := by linarith
  have hD := det_close hU hr0 hε.le (by linarith) hNear
  have hDL := (abs_le.mp hD).1
  have hDH := (abs_le.mp hD).2
  let N := det a b c' d
  have hNe : (N:ℝ)=detR M := by dsimp [N,det,detR,M]; push_cast; rfl
  have hnReal : (2:ℝ)≤(N:ℝ) := by
    rw [hNe]
    nlinarith [scaled_n_lb hr hε']
  have hn : 2≤N := by exact_mod_cast hnReal
  have hn0 : 0<N := by omega
  have hnNat : 2≤N.toNat := by omega
  have hnCast : (N.toNat:ℝ)=(N:ℝ) := by exact_mod_cast positive_natCast hn0
  obtain ⟨p,hp⟩ := primitive_lattice_permutation hn0 ha hb
  refine ⟨N.toNat,⟨hnNat,p,?_⟩,?_⟩
  · intro i j hij
    obtain ⟨x,y,hx,hy⟩ := hp i j
    have hne : x≠0 ∨ y≠0 := by
      by_contra! hh
      rw [hh.1,hh.2,mul_zero,mul_zero,add_zero] at hx
      exact hij (Fin.ext (by omega))
    have hE : center p i-center p j=act M (x:ℝ) (y:ℝ) := by
      apply Prod.ext
      · change (i.val:ℝ)-j.val=(a:ℝ)*x+(b:ℝ)*y
        exact_mod_cast hx
      · change ((p i).val:ℝ)-(p j).val=(c':ℝ)*x+(d:ℝ)*y
        exact_mod_cast hy
    rw [hE]
    have he := close_basis_separation hU hr0 hε.le (by linarith) hNear hne
    nlinarith
  · rw [hnCast,hNe]
    nlinarith

#print axioms eventual_oriented_packing
end PermHex
