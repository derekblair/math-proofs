import PackingGeometry
import Upper
import CellArrangement

namespace PermHex
open Set MeasureTheory Function
open scoped ENNReal BigOperators
open PermCircles (box volume_box rotate)

lemma center_in_square {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    center p i∈box 0 ((n:ℝ)-1) := by
  have h1 : (i.val:ℝ)+1≤(n:ℝ) := by exact_mod_cast (show i.val+1≤n from i.isLt)
  have h2 : ((p i).val:ℝ)+1≤(n:ℝ) := by exact_mod_cast (show (p i).val+1≤n from (p i).isLt)
  change ((0:ℝ)≤(i.val:ℝ) ∧ (i.val:ℝ)≤(n:ℝ)-1) ∧
    ((0:ℝ)≤((p i).val:ℝ) ∧ ((p i).val:ℝ)≤(n:ℝ)-1)
  exact ⟨⟨by positivity,by linarith⟩,⟨by positivity,by linarith⟩⟩

lemma gauge_base_cube {t : ℝ} (ht : 0≤t) {z : Point} (h : gauge z≤t) :
    |z.1|≤t ∧ |z.2|≤t := by
  have hx : 2*|z.1|/root3≤t := (le_max_left _ _).trans h
  have hy : |z.1|/root3+|z.2|≤t := (le_max_right _ _).trans h
  have hp := root3_pos
  have hn := root3_le_two
  have hxl := (div_le_iff₀ hp).mp hx
  have hxm := mul_le_mul_of_nonneg_left hn ht
  have hy0 : 0≤|z.1|/root3 := by positivity
  exact ⟨by linarith,by linarith⟩

lemma gauge_rotated_cube {c s t : ℝ} (hU : c^2+s^2=1) (ht : 0≤t)
    {z : Point} (h : gaugeR c s z≤t) : |z.1|≤4*t ∧ |z.2|≤4*t := by
  let w := rotate c s z
  have hw : gauge w≤t := h
  have hV : c^2+(-s)^2=1 := by simpa using hU
  have hr := rotate_l1 hV w
  have he : rotate c (-s) w=z := PermCircles.rot_neg_inv hU z
  rw [he] at hr
  obtain ⟨ha,hb⟩ := gauge_base_cube ht hw
  unfold l1 at hr
  exact ⟨by linarith [abs_nonneg z.2],by linarith [abs_nonneg z.1]⟩

lemma tile_around_center_in_box {c s t M : ℝ} (hU : c^2+s^2=1) (ht : 0≤t)
    {p : Point} (hp : p∈box 0 M) :
    atCenter true c s t p ⊆ box (-4*t) (M+4*t) := by
  intro z hz
  have hq := (atCenter_closed_iff c s t p z).mp hz
  obtain ⟨h1,h2⟩ := gauge_rotated_cube hU ht hq
  have hx : |z.1-p.1|≤4*t := h1
  have hy : |z.2-p.2|≤4*t := h2
  rcases abs_le.mp hx with ⟨ha,hb⟩
  rcases abs_le.mp hy with ⟨ha',hb'⟩
  have hp1 : 0≤p.1 ∧ p.1≤M := hp.1
  have hp2 : 0≤p.2 ∧ p.2≤M := hp.2
  exact ⟨⟨by linarith [hp1.1],by linarith [hp1.2]⟩,by linarith [hp2.1],by linarith [hp2.2]⟩

lemma atCenter_open_subset (c s t : ℝ) (p : Point) :
    atCenter false c s t p ⊆ atCenter true c s t p :=
  preimage_mono (body_open_subset c s t)

lemma measure_tile_boundary {c s t : ℝ} (hU : c^2+s^2=1) (ht : 0≤t) (p : Point) :
    volume (atCenter true c s t p \ atCenter false c s t p)=0 := by
  have hFin : volume (atCenter false c s t p) ≠ ∞ := by
    rw [atCenter_volume hU false ht]
    exact ENNReal.ofReal_ne_top
  rw [measure_sdiff (atCenter_open_subset c s t p)
    (atCenter_meas false c s t p).nullMeasurableSet hFin,
    atCenter_volume hU true ht,atCenter_volume hU false ht,tsub_self]

lemma tiles_aeDisjoint {c s t : ℝ} (hU : c^2+s^2=1) (ht : 0<t)
    {p q : Point} (h : 2*t≤gaugeR c s (p-q)) :
    AEDisjoint volume (atCenter true c s t p) (atCenter true c s t q) := by
  change volume (atCenter true c s t p ∩ atCenter true c s t q)=0
  have hO := (separation_iff ht p q).2 h
  rw [interior_atCenter ht,interior_atCenter ht] at hO
  let P := atCenter true c s t p \ atCenter false c s t p
  let Q := atCenter true c s t q \ atCenter false c s t q
  have hNull : volume (P∪Q)=0 := by
    have htop : volume (P∪Q)≤volume P+volume Q := measure_union_le _ _
    have hP : volume P=0 := measure_tile_boundary hU ht.le p
    have hQ : volume Q=0 := measure_tile_boundary hU ht.le q
    rw [hP,hQ,zero_add] at htop
    exact nonpos_iff_eq_zero.mp htop
  apply measure_mono_null _ hNull
  intro z hz
  by_cases hp : z∈atCenter false c s t p
  · have hq : z∉atCenter false c s t q := fun hq => disjoint_left.mp hO hp hq
    exact Or.inr ⟨hz.2,hq⟩
  · exact Or.inl ⟨hz.1,hp⟩

lemma size_ge_radius_div_four {c s t : ℝ} (hU : c^2+s^2=1)
    {n : ℕ} (h : HexFits c s t n) : t≤4*(n:ℝ) := by
  obtain ⟨hn,p,hp⟩ := h
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  have hne : i≠j := by intro hh; have he := congrArg Fin.val hh; simp [i,j] at he
  have hlow := hp i j hne
  have hhigh := gaugeR_l1 hU (center p i-center p j)
  have hi1 : 0≤(center p i).1 ∧ (center p i).1≤(n:ℝ)-1 := (center_in_square p i).1
  have hi2 : 0≤(center p i).2 ∧ (center p i).2≤(n:ℝ)-1 := (center_in_square p i).2
  have hj1 : 0≤(center p j).1 ∧ (center p j).1≤(n:ℝ)-1 := (center_in_square p j).1
  have hj2 : 0≤(center p j).2 ∧ (center p j).2≤(n:ℝ)-1 := (center_in_square p j).2
  have hx : |(center p i).1-(center p j).1| ≤ (n:ℝ)-1 := abs_le.mpr
    ⟨by linarith [hi1.1,hj1.2],by linarith [hi1.2,hj1.1]⟩
  have hy : |(center p i).2-(center p j).2| ≤ (n:ℝ)-1 := abs_le.mpr
    ⟨by linarith [hi2.1,hj2.2],by linarith [hi2.2,hj2.1]⟩
  change gaugeR c s (center p i-center p j) ≤
    4*(|(center p i).1-(center p j).1|+|(center p i).2-(center p j).2|) at hhigh
  linarith

lemma lower_size {c s t : ℝ} (hU : c^2+s^2=1) (ht : 0<t) {n : ℕ} (h : HexFits c s t n) :
    areaUnit*t^2-272*t≤(n:ℝ) := by
  have hrn := size_ge_radius_div_four hU h
  obtain ⟨hn,p,hp⟩ := h
  let F := fun i : Fin n => atCenter true c s t (center p i)
  let M := (n:ℝ)-1
  have hM : 0≤M := by
    have hh : (2:ℝ)≤(n:ℝ) := by exact_mod_cast hn
    dsimp [M]; linarith
  have hSup : (⋃ i, F i) ⊆ box (-4*t) (M+4*t) := by
    intro z hz
    rcases mem_iUnion.mp hz with ⟨i,hi⟩
    exact tile_around_center_in_box hU ht.le (center_in_square p i) hi
  have hD : Pairwise (AEDisjoint volume on F) :=
    fun i j hij => tiles_aeDisjoint hU ht (hp i j hij)
  have hMset : ∀ i, NullMeasurableSet (F i) volume := fun i =>
    (atCenter_meas true c s t (center p i)).nullMeasurableSet
  have ha := measure_mono hSup (μ:=volume)
  rw [measure_iUnion₀ hD hMset,tsum_fintype,volume_box _ _ (by linarith)] at ha
  have hV (i : Fin n) : volume (F i)=ENNReal.ofReal (areaUnit*t^2) :=
    atCenter_volume hU true ht.le (center p i)
  simp_rw [hV] at ha
  have he : (∑ _i : Fin n, ENNReal.ofReal (areaUnit*t^2)) =
      ENNReal.ofReal ((n:ℝ)*(areaUnit*t^2)) := by
    rw [ENNReal.ofReal_mul (p:=(n:ℝ)) (q:=areaUnit*t^2) (by positivity)]
    simp
  rw [he] at ha
  have ha' := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp ha
  have hsum : (M+4*t-(-4*t))^2≤((n:ℝ)+8*t)^2 := by
    apply (sq_le_sq₀ (by linarith) (by positivity)).mpr
    dsimp [M]
    linarith
  have H := ha'.trans hsum
  have hnR : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hrPos := mul_nonneg (show 0≤4*(n:ℝ)-t by linarith) (show 0≤64*t by positivity)
  apply (mul_le_mul_iff_left₀ hnR).mp
  nlinarith only [H,hrPos]

#print axioms lower_size
end PermHex
