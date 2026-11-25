import Counts
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology
namespace Emerging

/-- The order-type equality for a consecutive length-m window starting at i.
Only call this with i+m ≤ n; the counting definitions enforce that by construction. -/
def occurs {n m : Nat} (f : Perm n) (i : Nat) (p : Perm m) : Prop :=
  ∀ r s : Fin m, ext f (i+r.val) < ext f (i+s.val) ↔ p r < p s

def avoids {n m : Nat} (f : Perm n) (forbidden : Finset (Perm m)) : Prop :=
  ∀ p ∈ forbidden, ∀ i : Fin (n-(m-1)), ¬ occurs f i.val p

noncomputable def avoidanceClass (n m : Nat) (forbidden : Finset (Perm m)) : Finset (Perm n) := by
  classical exact Finset.univ.filter (fun f => avoids f forbidden)

/-- Count (permutation,start) pairs, equivalently the sum of occurrence counts over the class. -/
noncomputable def totalPopularity (n m : Nat) (forbidden : Finset (Perm m)) (p : Perm m) : Nat := by
  classical exact (Finset.univ.filter (fun a : Perm n × Fin (n-(m-1)) =>
    a.1 ∈ avoidanceClass n m forbidden ∧ occurs a.1 a.2.val p)).card

noncomputable def relativePopularity (n m : Nat) (forbidden : Finset (Perm m)) (p : Perm m) : ℝ :=
  (totalPopularity n m forbidden p : ℝ) / ((n:ℝ)*(avoidanceClass n m forbidden).card)

/-- Full published implication (if both classes are nonempty eventually).
For a limit equal to zero, use the actual convergence predicate, not a default value
for divergence. -/
def Published : Prop :=
  ∀ (m : Nat), 0<m →
  ∀ (F : Finset (Perm m)) (p : Perm m), p ∉ F →
  (∀ᶠ n in atTop, (avoidanceClass n m F).Nonempty) →
  (∀ᶠ n in atTop, (avoidanceClass n m (insert p F)).Nonempty) →
  Tendsto (fun n => relativePopularity n m F p) atTop (𝓝 0) →
  ∀ (q : Perm m) (L : ℝ), Tendsto (fun n => relativePopularity n m F q) atTop (𝓝 L) →
    Tendsto (fun n => relativePopularity n m (insert p F) q) atTop (𝓝 L)

theorem w_range (k : Fin 7) (i : Fin 5) : 0 < w k i ∧ w k i ≤ 5 := by decide +revert
theorem w_inj (k : Fin 7) : Function.Injective (w k) := by
  intro a b h
  have aux : ∀ (j : Fin 7) (r s : Fin 5), w j r=w j s → r=s := by decide
  exact aux k a b h

noncomputable def wp (k : Fin 7) : Perm 5 :=
  Equiv.ofBijective (fun i => ⟨w k i-1,by have hh := w_range k i; omega⟩)
    (Finite.injective_iff_bijective.mp (fun a b h => (w_inj k) (by
      have ha := (w_range k a).1
      have hb := (w_range k b).1
      have he := congrArg Fin.val h
      change w k a - 1 = w k b - 1 at he
      omega)))

theorem occurs_wp (n : Nat) (f : Perm n) (i : Nat) (k : Fin 7) :
    occurs f i (wp k) ↔ matchWord (ext f) i (w k) := by
  unfold occurs matchWord
  apply forall_congr'
  intro r
  apply forall_congr'
  intro s
  change (_ ↔ w k r - 1 < w k s - 1) ↔ (_ ↔ w k r < w k s)
  have hr := (w_range k r).1
  have hs := (w_range k s).1
  have he : w k r - 1 < w k s - 1 ↔ w k r < w k s := by omega
  rw [he]

noncomputable def forbidden5 : Finset (Perm 5) := by
  classical exact Finset.univ \ Finset.univ.image wp

theorem notForbidden (p : Perm 5) : p ∉ forbidden5 ↔ ∃ k, wp k = p := by
  classical
  simp [forbidden5]

theorem occurs_exists (n m : Nat) (f : Perm n) (i : Nat) (h : i+m≤n) :
    ∃ p : Perm m, occurs f i p := by
  classical
  let g : Fin m → Nat := fun j => ext f (i+j.val)
  have gj : Function.Injective g := by
    intro a b hab
    have h1 : i+a.val<n := by have := a.isLt; omega
    have h2 : i+b.val<n := by have := b.isLt; omega
    have hh : (f ⟨i+a.val,h1⟩).val = (f ⟨i+b.val,h2⟩).val := by simpa [g,ext,h1,h2] using hab
    have hh' := congrArg Fin.val (f.injective (Fin.ext hh))
    exact Fin.ext (by simp at hh'; omega)
  let vals := Finset.univ.image g
  have hc : vals.card=m := by simp [vals,Finset.card_image_of_injective _ gj]
  let e : Fin m ≃ vals := Equiv.ofBijective
    (fun j => ⟨g j, Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun a b h => gj (congrArg Subtype.val h),fun b => by
      obtain ⟨a,_,ha⟩ := Finset.mem_image.mp b.property
      exact ⟨a,Subtype.ext ha⟩⟩
  let ord := vals.orderIsoOfFin hc
  refine ⟨e.trans ord.symm.toEquiv,?_⟩
  intro r s
  change (e r : ℕ) < (e s : ℕ) ↔ ord.symm (e r) < ord.symm (e s)
  exact (ord.symm.lt_iff_lt).symm

theorem occurs_unique (n m : Nat) (f : Perm n) (i : Nat) (p q : Perm m)
    (hp : occurs f i p) (hq : occurs f i q) : p=q := by
  apply Equiv.ext
  intro a
  apply Fin.ext
  let F : Nat → Nat := fun x => if hx : x<m then (p (q.symm ⟨x,hx⟩)).val else 0
  have hh : ∀ x, x + 1 < m → F x < F (x+1) := by
    intro x hx
    have h0 : x<m := by omega
    simp only [F,dif_pos h0,dif_pos hx]
    rw [← Fin.lt_def,← hp, hq]
    simp
  have hb : ∀ x<m, F x < m := by intro x hx; simp [F,hx]
  have rr := unique_ranks F m hh hb (q a).val (q a).isLt
  simpa [F,(q a).isLt] using rr

theorem avoidsA_iff (n : Nat) (f : Perm n) : avoids f forbidden5 ↔ Admis n f := by
  constructor
  · intro h i hi
    obtain ⟨p,hp⟩ := occurs_exists n 5 f i (by omega)
    have hnf : p ∉ forbidden5 := fun hmem => h p hmem ⟨i,by omega⟩ hp
    obtain ⟨k,rfl⟩ := (notForbidden _).mp hnf
    exact ⟨k,(occurs_wp _ _ _ _).mp hp⟩
  · intro h p hmem i hp
    obtain ⟨k,hk⟩ := h i.val (by have := i.isLt; omega)
    have he := occurs_unique _ _ _ _ _ _ hp ((occurs_wp _ _ _ _).mpr hk)
    exact ((notForbidden _).mpr ⟨k,he.symm⟩) hmem

theorem avoidsB_iff (n : Nat) (f : Perm n) :
    avoids f (insert (wp 2) forbidden5) ↔ BAdmis n f := by
  constructor
  · intro h
    constructor
    · apply (avoidsA_iff _ _).mp
      exact fun p hp => h p (Finset.mem_insert_of_mem hp)
    · intro i hi hm
      exact h (wp 2) (Finset.mem_insert_self _ _) ⟨i,by omega⟩ ((occurs_wp _ _ _ _).mpr hm)
  · rintro ⟨ha,hn⟩ p hp i hpi
    rcases Finset.mem_insert.mp hp with rfl|hp'
    · exact hn i.val (by have := i.isLt; omega) ((occurs_wp _ _ _ _).mp hpi)
    · exact (avoidsA_iff _ _).mpr ha p hp' i hpi

theorem sourceA (n : Nat) : avoidanceClass n 5 forbidden5 = aset n := by
  classical
  ext f
  simp [avoidanceClass,avoidsA_iff]

theorem sourceB (n : Nat) : avoidanceClass n 5 (insert (wp 2) forbidden5) = bset n := by
  classical
  ext f
  simp [avoidanceClass,avoidsB_iff]

theorem sourceTA (n : Nat) (k : Fin 7) :
    totalPopularity n 5 forbidden5 (wp k) = (occs n (aset n) k).card := by
  classical
  unfold totalPopularity
  rw [sourceA]
  congr 1
  ext x
  simp [occurs_wp]

theorem sourceTB (n : Nat) (k : Fin 7) :
    totalPopularity n 5 (insert (wp 2) forbidden5) (wp k) = (occs n (bset n) k).card := by
  classical
  unfold totalPopularity
  rw [sourceB]
  congr 1
  ext x
  simp [occurs_wp]

theorem A_nonempty : ∀ᶠ n in atTop, (avoidanceClass n 5 forbidden5).Nonempty := by
  refine (eventually_ge_atTop 6).mono fun n hn => ?_
  rw [sourceA]
  exact ⟨tallPerm n hn ⟨0,by omega⟩,(mem_aset _ _).mpr (tall_admis n hn _)⟩

theorem B_nonempty : ∀ᶠ n in atTop, (avoidanceClass n 5 (insert (wp 2) forbidden5)).Nonempty := by
  refine (eventually_ge_atTop 6).mono fun n hn => ?_
  rw [sourceB]
  exact ⟨tmplPerm n (by omega) 0, (mem_bset _ _).mpr (tmpl_B n (by omega) 0)⟩

theorem a_zero_of_bound (k : Fin 7)
    (hb : ∀ n, 6 ≤ n → (occs n (aset n) k).card ≤ (aset n).card) :
    Tendsto (fun n => relativePopularity n 5 forbidden5 (wp k)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  · apply Eventually.of_forall
    intro n
    unfold relativePopularity
    positivity
  · refine (eventually_ge_atTop 6).mono fun n hn => ?_
    unfold relativePopularity
    rw [sourceA,sourceTA]
    have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hcard : (0:ℝ)<(aset n).card := by
      have h := A_card_lower n hn
      exact_mod_cast (show 0<(aset n).card by omega)
    apply (div_le_div_iff₀ (mul_pos hn' hcard) hn').mpr
    have h := (show ((occs n (aset n) k).card : ℝ) ≤ (aset n).card by exact_mod_cast hb n hn)
    nlinarith

theorem A_p_zero : Tendsto (fun n => relativePopularity n 5 forbidden5 (wp 2)) atTop (𝓝 0) :=
  a_zero_of_bound 2 fun n _ => A_P_card n

theorem A_q_zero : Tendsto (fun n => relativePopularity n 5 forbidden5 (wp 5)) atTop (𝓝 0) :=
  a_zero_of_bound 5 fun n hn => by rw [(Q_counts n (by omega)).1]; exact A_card_lower n hn

theorem B_q_sixth :
    Tendsto (fun n => relativePopularity n 5 (insert (wp 2) forbidden5) (wp 5)) atTop (𝓝 (1/6 : ℝ)) := by
  have hh : Tendsto (fun n : ℕ => 1/6 - (2/3 : ℝ) / n) atTop (𝓝 (1/6 : ℝ)) := by
    simpa only [sub_zero] using
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (2/3 : ℝ))
  apply hh.congr'
  refine (eventually_ge_atTop 6).mono fun n hn => ?_
  change (1/6 - (2/3 : ℝ) / n) = relativePopularity n 5 (insert (wp 2) forbidden5) (wp 5)
  unfold relativePopularity
  rw [sourceB, sourceTB, B_count n hn, (Q_counts n (by omega)).2, Nat.cast_sub (by omega : 4≤n)]
  have hne : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  push_cast
  field_simp
  <;> ring

theorem refutesPublished : ¬ Published := by
  intro h
  have hpf : wp 2 ∉ forbidden5 := (notForbidden _).mpr ⟨2,rfl⟩
  have hz := h 5 (by decide) forbidden5 (wp 2) hpf A_nonempty B_nonempty A_p_zero (wp 5) 0 A_q_zero
  have he : (0:ℝ) = 1/6 := tendsto_nhds_unique hz B_q_sixth
  norm_num at he

#print axioms refutesPublished
end Emerging
