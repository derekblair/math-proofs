import NonconvSource
import NonconvMarked

open Filter Topology Emerging
namespace Nonconv
open scoped BigOperators

@[simp] lemma mem_forbiddenClass (n : Nat) (f : Perm n) :
    f ∈ avoidanceClass n 9 forbidden9 ↔ avoids f forbidden9 := by
  classical
  simp [avoidanceClass]

noncomputable def classEq (m : Nat) : ↥(avoidanceClass (m+9) 9 forbidden9) ≃ Route false m :=
  (Equiv.subtypeEquivRight (mem_forbiddenClass (m+9))).trans (pathsPerms m)

theorem class_card (m : Nat) : (avoidanceClass (m+9) 9 forbidden9).card = totalRoutes m := by
  rw [←Fintype.card_coe,Fintype.card_congr (classEq m),count_routes]

noncomputable def pointsSet (m : Nat) : Finset (Perm (m+9) × Fin (m+1)) := by
  classical
  exact Finset.univ.filter fun p => p.1 ∈ avoidanceClass (m+9) 9 forbidden9 ∧ occurs p.1 p.2.val (permWord q)

lemma mem_pointsSet (m : Nat) (p : Perm (m+9) × Fin (m+1)) :
    p ∈ pointsSet m ↔ p.1 ∈ avoidanceClass (m+9) 9 forbidden9 ∧ occurs p.1 p.2.val (permWord q) := by
  classical
  simp [pointsSet]

noncomputable def pointedRoutes (m : Nat) : ↥(pointsSet m) ≃ Σ i : Fin (m+1), Focus m i where
  toFun p := by
    let hp := (mem_pointsSet _ _).mp p.property
    let f : Avoiders m := ⟨p.val.1,(mem_forbiddenClass _ _).mp hp.1⟩
    let u := routeOf m f
    have hi := p.val.2.isLt
    have hm := matches_routeOf m f p.val.2.val (by omega)
    have hq := (word_occurs _ _ _).mp hp.2
    have h := match_unique _ _ _ _ hm hq
    have he : u.val p.val.2=q := by simpa [u,tagExt,hi] using h
    exact ⟨p.val.2,⟨u,he⟩⟩
  invFun z := by
    let f := permOf m z.2.val
    have hi := z.1.isLt
    have hm := matches_permOf m z.2.val z.1.val (by omega)
    have hq : Matches (ext f.val) z.1.val q := by simpa [f,tagExt,hi,z.2.property] using hm
    exact ⟨(f.val,z.1),(mem_pointsSet _ _).mpr
      ⟨(mem_forbiddenClass _ _).mpr f.property,(word_occurs _ _ _).mpr hq⟩⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · let hp := (mem_pointsSet _ _).mp p.property
      let f : Avoiders m := ⟨p.val.1,(mem_forbiddenClass _ _).mp hp.1⟩
      exact congrArg Subtype.val ((pathsPerms m).left_inv f)
    · rfl
  right_inv p := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact (pathsPerms m).right_inv p.2.val

theorem count_points (m : Nat) : totalPopularity (m+9) 9 forbidden9 (permWord q) = marks m := by
  change (pointsSet m).card = marks m
  rw [←Fintype.card_coe,Fintype.card_congr (pointedRoutes m),marked_count]

private theorem normalize0 (x p : ℝ) (hp : p ≠ 0) (hn : 3*x+9 ≠ 0) :
    ((3*x+1)*p)/((3*x+9)*(p*44)) = (1/44:ℝ) - (2/11)/(3*x+9) := by
  field_simp
  ring

private theorem normalize0_nat (k : Nat) :
    ((3*(k:ℝ)+1)*(2:ℝ)^k)/((3*(k:ℝ)+9)*((2:ℝ)^k*44)) =
      (1/44:ℝ) - (2/11)/(3*(k:ℝ)+9) := by
  have hP : (2:ℝ)^k ≠ 0 := by positivity
  have hN : 3*(k:ℝ)+9 ≠ 0 := by positivity
  exact normalize0 _ _ hP hN

theorem freq0 (k : Nat) :
    relativePopularity (3*k+9) 9 forbidden9 (permWord q) = (1/44:ℝ) - (2/11) / (3*(k:ℝ)+9) := by
  have he : totalRoutes (3*k) = 2^k*44 := by
    simpa only [Nat.add_zero,route_bases.1] using route_scale k 0
  unfold relativePopularity
  rw [class_card,count_points,marks0,he]
  norm_num only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.cast_pow]
  exact normalize0_nat k

theorem freq1 (k : Nat) :
    relativePopularity (3*k+10) 9 forbidden9 (permWord q) = (1/42:ℝ) - (17/84) / (3*(k:ℝ)+10) := by
  unfold relativePopularity
  rw [show 3*k+10=(3*k+1)+9 by omega,class_card,count_points,marks1,route_scale,route_bases.2.1]
  push_cast
  have hN : 3*(k:ℝ)+10 ≠ 0 := by positivity
  have hP : (2:ℝ)^k ≠ 0 := by positivity
  field_simp
  <;> ring

theorem freq2 (k : Nat) :
    relativePopularity (3*k+11) 9 forbidden9 (permWord q) = (5/216:ℝ) - (5/27) / (3*(k:ℝ)+11) := by
  unfold relativePopularity
  rw [show 3*k+11=(3*k+2)+9 by omega,class_card,count_points,marks2,route_scale,route_bases.2.2]
  push_cast
  have hN : 3*(k:ℝ)+11 ≠ 0 := by positivity
  have hP : (2:ℝ)^k ≠ 0 := by positivity
  field_simp
  <;> ring

theorem toTop (d : Nat) : Tendsto (fun k : Nat => 3*k+d) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  refine (eventually_ge_atTop n).mono fun k hk => ?_
  omega

theorem subseq_limit (c d : ℝ) (e : Nat) :
    Tendsto (fun k : Nat => c-d/(3*(k:ℝ)+e)) atTop (𝓝 c) := by
  have hI := tendsto_const_div_atTop_nhds_zero_nat (𝕜:=ℝ) d
  have hd : Tendsto (fun k : Nat => d/(3*(k:ℝ)+e)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hI.comp (toTop e)
  simpa only [sub_zero] using tendsto_const_nhds.sub hd

theorem limitThird :
    Tendsto (fun k : Nat => relativePopularity (3*k+11) 9 forbidden9 (permWord q)) atTop (𝓝 (5/216:ℝ)) := by
  simp_rw [freq2]
  exact subseq_limit _ _ 11

theorem nonconvergence : ¬∃ l : ℝ, Tendsto (fun n => relativePopularity n 9 forbidden9 (permWord q)) atTop (𝓝 l) := by
  rintro ⟨l,hl⟩
  have h0 : Tendsto (fun k : Nat => relativePopularity (3*k+9) 9 forbidden9 (permWord q)) atTop (𝓝 (1/44:ℝ)) := by
    simp_rw [freq0]
    exact subseq_limit _ _ 9
  have h1 : Tendsto (fun k : Nat => relativePopularity (3*k+10) 9 forbidden9 (permWord q)) atTop (𝓝 (1/42:ℝ)) := by
    simp_rw [freq1]
    exact subseq_limit _ _ 10
  have hl0 := tendsto_nhds_unique (hl.comp (toTop 9)) h0
  have hl1 := tendsto_nhds_unique (hl.comp (toTop 10)) h1
  have : (1/44:ℝ)=1/42 := hl0.symm.trans hl1
  norm_num at this

theorem nonempty_eventually : ∀ᶠ n in atTop, (avoidanceClass n 9 forbidden9).Nonempty := by
  refine (eventually_ge_atTop 9).mono fun n hn => ?_
  let m := n-9
  have he : m+9=n := by dsimp [m]; omega
  rw [←he,←Finset.card_pos,class_card]
  let r := m%3
  let k := m/3
  have hm : m=3*k+r := by dsimp [k,r]; omega
  rw [hm,route_scale]
  have hr : r=0 ∨ r=1 ∨ r=2 := by dsimp [r]; omega
  rcases hr with hr|hr|hr
  · rw [hr,route_bases.1]; positivity
  · rw [hr,route_bases.2.1]; positivity
  · rw [hr,route_bases.2.2]; positivity

theorem question4 :
    ∃ (F : Finset (Perm 9)) (p : Perm 9),
      p ∉ F ∧ (∀ᶠ n in atTop, (avoidanceClass n 9 F).Nonempty) ∧
      ¬∃ l : ℝ, Tendsto (fun n => relativePopularity n 9 F p) atTop (𝓝 l) :=
  ⟨forbidden9,permWord q,(allowed9 _).mpr ⟨q,rfl⟩,nonempty_eventually,nonconvergence⟩

#print axioms question4
end Nonconv
