import CountableEndpoint

namespace SparseHalfCountableEndpoint
variable {ι : Type*}

private theorem nonneg_tsum {f : ι → ℝ} (hf : Summable f) (h : ∀ i, 0 ≤ f i) :
    0 ≤ ∑' i, f i := by
  simpa using Summable.tsum_le_tsum h (summable_zero (α:=ℝ) (β:=ι)) hf

private theorem take_sum {q : ι → ℝ} (hq : Summable q) (qs : ∀ i,0≤q i)
    (P : ι → Prop) [DecidablePred P] :
    Summable (fun i => if P i then q i else 0) := by
  apply Summable.of_nonneg_of_le (f:=q) _ _ hq <;>
    intro i <;> split <;> simp [qs i]

/-- Find a positive price level bracketing a prescribed strictly interior
mass of *unused* capacity in the descending price order. -/
theorem threshold (p q : ι → ℝ) (R : ℝ)
    (hps : Summable p) (hqs : Summable q)
    (hp : ∀ i, p i≤2) (hq : ∀ i,0≤q i) (hqp : ∀ i,q i≤p i)
    (hr : 0<R) (hrq : R<∑' i,q i) :
    ∃ θ : ℝ, 0<θ ∧ θ≤2 ∧
      (∑' i, if θ<p i then q i else 0)≤R ∧
      R≤∑' i, if θ≤p i then q i else 0 := by
  classical
  have ex : ∃ s : Finset ι, R<∑ i∈s,q i := by
    by_contra! no
    exact (not_le_of_gt hrq) (hqs.tsum_le_of_sum_le no)
  obtain ⟨s,sh⟩ := ex
  let S := s.filter fun i => 0<q i
  have hs : R<∑ i∈S,q i := by
    have e : ∑ i∈S,q i = ∑ i∈s,q i :=
      Finset.sum_subset (Finset.filter_subset _ _) fun i hi hn => by
        have qi : ¬ 0<q i := fun h => hn (Finset.mem_filter.mpr ⟨hi,h⟩)
        exact le_antisymm (le_of_not_gt qi) (hq i)
    rwa [e]
  have Sne : S.Nonempty := by
    by_contra! h
    rw [h,Finset.sum_empty] at hs
    linarith
  let P := S.image p
  have Pne : P.Nonempty := Sne.image _
  let cutoff := P.min' Pne
  have hL : cutoff∈P := P.min'_mem Pne
  obtain ⟨j,jS,jL⟩ := Finset.mem_image.mp hL
  have L0 : 0<cutoff := jL ▸ ((Finset.mem_filter.mp jS).2.trans_le (hqp j))
  let H := (finite_threshold _ hps L0).toFinset
  have hm (i : ι) : i∈H ↔ cutoff≤p i := Set.Finite.mem_toFinset _
  have sub : S⊆H := fun i hi => (hm i).2 (P.min'_le _ (Finset.mem_image_of_mem p hi))
  let U := fun θ : ℝ => ∑ i∈H.filter (fun i => θ≤p i),q i
  have Ul : R≤U cutoff := by
    dsimp [U]
    have sub' : S⊆H.filter (fun i => cutoff≤p i) := fun i hi =>
      Finset.mem_filter.mpr ⟨sub hi,(hm i).1 (sub hi)⟩
    exact hs.le.trans (Finset.sum_le_sum_of_subset_of_nonneg sub' (fun i _ _ => hq i))
  let good := (H.image p).filter fun θ => R≤U θ
  have gne : good.Nonempty := ⟨cutoff, Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨j,sub jS,jL⟩,Ul⟩⟩
  let θ := good.max' gne
  have gt : θ∈good := good.max'_mem gne
  obtain ⟨k,kH,kθ⟩ := Finset.mem_image.mp (Finset.mem_filter.mp gt).1
  have Lθ : cutoff≤θ := kθ ▸ (hm k).1 kH
  have θ2 : θ≤2 := kθ ▸ hp k
  have Ur : R≤U θ := (Finset.mem_filter.mp gt).2
  have Lr : ∑ i∈H.filter (fun i => θ<p i),q i ≤ R := by
    by_contra! sgt
    let M := H.filter fun i => θ<p i
    have Mne : M.Nonempty := by
      by_contra! h
      change R<∑ i∈M,q i at sgt
      rw [h,Finset.sum_empty] at sgt
      linarith
    let a := (M.image p).min' (Mne.image _)
    have aha : a∈M.image p := Finset.min'_mem _ _
    obtain ⟨l,lM,la⟩ := Finset.mem_image.mp aha
    have hlt : θ<a := la ▸ (Finset.mem_filter.mp lM).2
    have eq : H.filter (fun i => a≤p i) = M := by
      ext i
      rw [Finset.mem_filter]
      constructor
      · intro hi; exact Finset.mem_filter.mpr ⟨hi.1,hlt.trans_le hi.2⟩
      · intro hi
        exact ⟨(Finset.mem_filter.mp hi).1, Finset.min'_le _ _ (Finset.mem_image_of_mem _ hi)⟩
    have ar : R≤U a := by dsimp [U]; rw [eq]; exact sgt.le
    have ag : a∈good := Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨l,(Finset.mem_filter.mp lM).1,la⟩,ar⟩
    exact (not_le_of_gt hlt) (good.le_max' _ ag)
  have repr (P : ι → Prop) [DecidablePred P] (hP : ∀ i, P i → cutoff≤p i) :
      (∑' i, if P i then q i else 0) = ∑ i ∈ H.filter P,q i := by
    rw [Finset.sum_filter]
    exact tsum_eq_sum fun i hi => ite_eq_right (fun pp => hi ((hm i).2 (hP i pp)))
  refine ⟨θ,L0.trans_le Lθ,θ2,?_,?_⟩
  · rw [repr (fun i => θ<p i) (fun i h => Lθ.trans h.le)]; exact Lr
  · rw [repr (fun i => θ≤p i) (fun i h => Lθ.trans h)]; exact Ur

#print axioms threshold


/-- A single fractional level suffices for exact optimality in the
countable continuous knapsack, including empty and full fills. -/
theorem greedy (p q : ι → ℝ) (t : ℝ)
    (hps : Summable p) (hqs : Summable q)
    (hp : ∀ i, p i≤2) (hq : ∀ i,0≤q i) (hqp : ∀ i,q i≤p i)
    (ht : 0≤t) (htq : t≤∑' i,q i) :
    ∃ θ k : ℝ, 0≤θ ∧ θ≤2 ∧ 0≤k ∧ k≤1 ∧
      ∃ x : ι → ℝ,
      (∀ i, x i = if p i<θ then q i else if p i=θ then k*q i else 0) ∧
      (∀ i, 0≤x i ∧ x i≤q i) ∧ (∑' i,x i)=t ∧
      (∑' i,p i*x i)=(∑' i,q i*min θ (p i))-θ*((∑' i,q i)-t) ∧
      (∀ z : ι → ℝ, (∀ i, 0≤z i ∧ z i≤q i) → (∑' i,z i)=t →
        (∑' i,p i*x i)≤∑' i,p i*z i) := by
  classical
  let Q := ∑' i,q i
  let R := Q-t
  have pn i : 0≤p i := (hq i).trans (hqp i)
  have bracket : ∃ θ : ℝ, 0≤θ ∧ θ≤2 ∧
      (∑' i, if θ<p i then q i else 0)≤R ∧
      R≤∑' i, if θ≤p i then q i else 0 := by
    by_cases ht0 : t=0
    · refine ⟨0,by norm_num,by norm_num,?_,?_⟩
      · have hs := take_sum hqs hq (fun i => 0<p i)
        have h := Summable.tsum_le_tsum (fun i => show (if 0<p i then q i else 0)≤q i from
          by split <;> simp [hq i]) hs hqs
        simpa [R,Q,ht0] using h
      · simp [R,Q,ht0,pn]
    · by_cases htQ : t=Q
      · refine ⟨2,by norm_num,le_rfl,?_,?_⟩
        · simp [R,htQ,not_lt_of_ge,hp]
        · rw [show R=0 by simp [R,htQ]]
          refine nonneg_tsum (take_sum hqs hq (fun i => 2≤p i)) ?_
          intro i; split <;> simp [hq i]
      · obtain ⟨θ,h0,h2,hL,hU⟩ := threshold p q R hps hqs hp hq hqp
          (sub_pos.mpr (lt_of_le_of_ne htq htQ)) (by have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0); dsimp [R,Q]; linarith)
        exact ⟨θ,h0.le,h2,hL,hU⟩
  obtain ⟨θ,θ0,θ2,hL,hU⟩ := bracket
  let A := fun i => if θ<p i then q i else 0
  let B := fun i => if p i=θ then q i else 0
  have sA : Summable A := take_sum hqs hq _
  have sB : Summable B := take_sum hqs hq _
  let a := ∑' i,A i
  let b := ∑' i,B i
  have b0 : 0≤b := by
    apply nonneg_tsum sB
    intro i; unfold B; split <;> simp [hq i]
  have hab : (∑' i, if θ≤p i then q i else 0)=a+b := by
    rw [←sA.tsum_add sB]
    apply congrArg (fun f : ι→ℝ => ∑' i,f i)
    funext i
    rcases lt_trichotomy (p i) θ with h|h|h
    · simp [A,B,not_le_of_gt h,not_lt_of_ge h.le,h.ne]
    · simp [A,B,h]
    · simp [A,B,h,h.le,h.ne.symm]
  rw [hab] at hU
  have aa : a≤R := hL
  let r := if b=0 then 0 else (R-a)/b
  have r0 : 0≤r := by
    dsimp [r]
    split
    · exact le_rfl
    · exact div_nonneg (sub_nonneg.mpr aa) b0
  have r1 : r≤1 := by
    dsimp [r]
    split
    · norm_num
    · rename_i bne
      exact (div_le_iff₀ (lt_of_le_of_ne b0 (Ne.symm bne))).2 (by linarith)
  have rr : a+r*b=R := by
    dsimp [r]
    by_cases bz : b=0
    · simp [bz]
      linarith
    · rw [ite_eq_right bz,div_mul_cancel₀ _ bz]
      ring
  let y := fun i => A i+r*B i
  let x := fun i => q i-y i
  have sy : Summable y := sA.add (sB.mul_left r)
  have ty : (∑' i,y i)=R := by
    change (∑' i,(A i+r*B i))=R
    rw [sA.tsum_add (sB.mul_left r),sB.tsum_mul_left]
    exact rr
  have sx := hqs.sub sy
  have tx : (∑' i,x i)=t := by
    change (∑' i,(q i-y i))=t
    rw [hqs.tsum_sub sy,ty]
    dsimp [R,Q]
    ring
  have shape (i : ι) : x i = if p i<θ then q i else if p i=θ then (1-r)*q i else 0 := by
    rcases lt_trichotomy (p i) θ with h|h|h
    · simp [x,y,A,B,h,not_lt_of_ge h.le,h.ne]
    · simp [x,y,A,B,h]; ring
    · simp [x,y,A,B,h,not_lt_of_ge h.le,h.ne.symm]
  have xfeas (i : ι) : 0≤x i ∧ x i≤q i := by
    rw [shape]
    split
    · exact ⟨hq i,le_rfl⟩
    · split
      · refine ⟨mul_nonneg (sub_nonneg.mpr r1) (hq i),?_⟩
        simpa using mul_le_mul_of_nonneg_right (show 1-r≤1 by linarith) (hq i)
      · exact ⟨le_rfl,hq i⟩
  have minsum : Summable (fun i => q i*min θ (p i)) := by
    apply Summable.of_nonneg_of_le (f:=fun i => 2*q i) _ _ (hqs.mul_left 2)
    · intro i; exact mul_nonneg (hq i) (le_min θ0 (pn i))
    · intro i
      rw [mul_comm 2]
      exact mul_le_mul_of_nonneg_left ((min_le_right θ (p i)).trans (hp i)) (hq i)
  have point (i : ι) : p i*x i=q i*min θ (p i)-θ*y i := by
    rcases lt_trichotomy (p i) θ with h|h|h
    · simp [x,y,A,B,not_lt_of_ge h.le,h.ne,min_eq_right h.le,mul_comm]
    · simp [x,y,A,B,h]; ring
    · simp [x,y,A,B,h,h.ne.symm,min_eq_left h.le,mul_comm]
  have cost : (∑' i,p i*x i)=(∑' i,q i*min θ (p i))-θ*R := by
    simp only [point]
    rw [minsum.tsum_sub (sy.mul_left θ),sy.tsum_mul_left,ty]
  refine ⟨θ,1-r,θ0,θ2,sub_nonneg.mpr r1,by linarith,x,shape,xfeas,tx,cost,?_⟩
  intro z zfeas tz
  have sz := Summable.of_nonneg_of_le (fun i => (zfeas i).1) (fun i => (zfeas i).2) hqs
  let w := fun i => q i-z i
  have sw : Summable w := hqs.sub sz
  have tw : (∑' i,w i)=R := by
    dsimp [w,R,Q]
    rw [hqs.tsum_sub sz,tz]
  have spz : Summable (fun i => p i*z i) := by
    apply Summable.of_nonneg_of_le (f:=fun i => 2*q i) _ _ (hqs.mul_left 2)
    · intro i; exact mul_nonneg (pn i) (zfeas i).1
    · intro i; exact mul_le_mul (hp i) (zfeas i).2 (zfeas i).1 (by norm_num)
  have lower (i : ι) : q i*min θ (p i)-θ*w i≤p i*z i := by
    rcases le_total (p i) θ with h|h
    · rw [min_eq_right h]
      dsimp [w]
      nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (zfeas i).2)]
    · rw [min_eq_left h]
      dsimp [w]
      nlinarith [mul_nonneg (sub_nonneg.mpr h) (zfeas i).1]
  have bound := Summable.tsum_le_tsum lower (minsum.sub (sw.mul_left θ)) spz
  rw [minsum.tsum_sub (sw.mul_left θ),sw.tsum_mul_left,tw] at bound
  exact cost.trans_le bound

#print axioms greedy
end SparseHalfCountableEndpoint
