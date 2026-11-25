import IrrMarked

open scoped goldenRatio BigOperators
open Filter Topology Emerging
namespace FibPopularity

@[simp] lemma mem_class4 (n : Nat) (f : Perm n) :
    f ∈ avoidanceClass n 4 forbidden4 ↔ avoids f forbidden4 := by
  classical
  simp [avoidanceClass]

noncomputable def bType (n : Nat) (hn : 4 ≤ n) :
    ↥(avoidanceClass n 4 forbidden4) ≃ Mask n :=
  (Equiv.subtypeEquivRight (mem_class4 n)).trans (avoidEquiv n hn)

theorem size_of_class (n : Nat) (hn : 4 ≤ n) : (avoidanceClass n 4 forbidden4).card = Nat.fib (n+1) := by
  rw [←Fintype.card_coe, Fintype.card_congr (bType n hn),card_mask]

noncomputable def pSet (n : Nat) : Finset (Perm n × Fin (n-3)) := by
  classical
  exact Finset.univ.filter fun a => a.1 ∈ avoidanceClass n 4 forbidden4 ∧ occurs a.1 a.2.val q2143

@[simp] lemma mem_pSet (n : Nat) (a : Perm n × Fin (n-3)) :
    a ∈ pSet n ↔ a.1 ∈ avoidanceClass n 4 forbidden4 ∧ occurs a.1 a.2.val q2143 := by
  classical
  simp [pSet]

abbrev Fiber (n i : Nat) := {s : Mask n // bit s i=true ∧ bit s (i+2)=true}
noncomputable instance fiberFintype (n i : Nat) : Fintype (Fiber n i) := Fintype.ofFinite _

lemma card_fiber (n a b : Nat) (h : a+4+b=n) :
    Fintype.card (Fiber n a) = Nat.fib (a+1)*Nat.fib (b+1) := by
  subst n
  exact card_marked a b

lemma pSet_mask (n : Nat) (hn : 4 ≤ n) (a : ↥(pSet n)) :
    occurs (swPerm (descMask a.val.1 (avoids_far n hn a.val.1 ((mem_class4 _ _).mp ((mem_pSet _ _).mp a.property).1)))) a.val.2.val q2143 := by
  rw [sw_desc_right]
  exact ((mem_pSet _ _).mp a.property).2

noncomputable def pSetEquiv (n : Nat) (hn : 4 ≤ n) : ↥(pSet n) ≃ Σ i : Fin (n-3), Fiber n i.val where
  toFun a := by
    let aa := (mem_pSet _ _).mp a.property
    let ff := (mem_class4 _ _).mp aa.1
    let s := descMask a.val.1 (avoids_far n hn a.val.1 ff)
    have hi := a.val.2.isLt
    exact ⟨a.val.2, ⟨s, (occurs_marked s a.val.2.val (by omega)).mp (pSet_mask n hn a)⟩⟩
  invFun z := by
    have hi := z.1.isLt
    refine ⟨(swPerm z.2.val,z.1),(mem_pSet _ _).mpr ⟨(mem_class4 _ _).mpr (far_avoids n _ (swPerm_far _)),?_⟩⟩
    exact (occurs_marked z.2.val z.1.val (by omega)).mpr z.2.property
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · exact sw_desc_right a.val.1 (avoids_far n hn _ ((mem_class4 _ _).mp ((mem_pSet _ _).mp a.property).1))
    · rfl
  right_inv z := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact desc_sw_left z.2.val

theorem count_marked_exact (n : Nat) (hn : 4 ≤ n) :
    totalPopularity n 4 forbidden4 q2143 =
      ∑ i ∈ Finset.range (n-3), Nat.fib (i+1)*Nat.fib (n-(i+4)+1) := by
  classical
  change (pSet n).card = _
  rw [←Fintype.card_coe,Fintype.card_congr (pSetEquiv n hn),Fintype.card_sigma]
  calc
    _ = ∑ i : Fin (n-3), Nat.fib (i.val+1)*Nat.fib (n-(i.val+4)+1) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := i.isLt
      exact card_fiber n i.val (n-(i.val+4)) (by omega)
    _ = _ := Fin.sum_univ_eq_sum_range (fun i => Nat.fib (i+1)*Nat.fib (n-(i+4)+1)) (n-3)

theorem source_density (z : Nat) :
    relativePopularity (z+4) 4 forbidden4 q2143 = conv z / (((z:ℝ)+4)*Nat.fib (z+5)) := by
  unfold relativePopularity conv
  rw [size_of_class _ (by omega), count_marked_exact _ (by omega)]
  push_cast
  congr 1

theorem q2143_limit :
    Tendsto (fun n => relativePopularity n 4 forbidden4 q2143) atTop (𝓝 (1/(φ^3*t))) := by
  apply (tendsto_add_atTop_iff_nat 4).mp
  simpa only [source_density] using conv_limit

theorem question3 :
    ∃ (F : Finset (Perm 4)) (q : Perm 4) (l : ℝ),
      q ∉ F ∧
      (∀ᶠ n in atTop, (avoidanceClass n 4 F).Nonempty) ∧
      Tendsto (fun n => relativePopularity n 4 F q) atTop (𝓝 l) ∧ Irrational l := by
  classical
  refine ⟨forbidden4,q2143,1/(φ^3*t),?_,?_,q2143_limit,constant_irrational⟩
  · intro h
    obtain ⟨a,b,hab,hbad⟩ := (Finset.mem_filter.mp h).2
    have ha : (swPerm doubleDimer a).val=sw doubleDimer a.val := rfl
    have hb : (swPerm doubleDimer b).val=sw doubleDimer b.val := rfl
    have hg := sw_far doubleDimer b.isLt hab
    change (swPerm doubleDimer b).val < (swPerm doubleDimer a).val at hbad
    omega
  · refine (eventually_ge_atTop 4).mono fun n hn => ?_
    exact ⟨swPerm (mEmpty n),(mem_class4 _ _).mpr (far_avoids n _ (swPerm_far _))⟩

#print axioms question3
end FibPopularity
