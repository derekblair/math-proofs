import PivotPoolOrient

open Set MeasureTheory Function Filter
open SparseHalfCountableEndpoint
namespace SparseHalfGraphon
variable {X I : Type*} [MeasurableSpace X] [Countable I]
variable (μ : Measure X) [IsFiniteMeasure μ]

/-- Strict dominant pivot in the actual graphon, without completing pairs. -/
theorem strict_dominant_active (K : Kernel X) (A S : Set X)
    (ma : MeasurableSet A) (ms : MeasurableSet S) (ad : Disjoint A S)
    (size : μ.real S=3/5)
    (aa : ∀ᵐ z ∂μ.prod μ, z.1∈A → z.2∈A → K.W z=0)
    (P Q C : I→Set X) (mp : ∀ i, MeasurableSet (P i))
    (mq : ∀ i, MeasurableSet (Q i)) (mc : ∀ i, MeasurableSet (C i))
    (ins : ∀ i, P i∪Q i⊆S) (inner : ∀ i, Disjoint (P i) (Q i))
    (outer : Pairwise (Disjoint on fun i=>P i∪Q i))
    (edge : ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict S), 0<K.W z →
      ∃ i, (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i))
    (cap : ∀ i, μ.real (C i∩A)=1/5 ∧ μ.real ((C i)ᶜ∩A)=1/5)
    (rowP : ∀ i, ∀ᵐ x ∂μ.restrict (P i),
      (fun y=>K.W (x,y)) =ᵐ[μ.restrict A] oneOn (C i))
    (rowQ : ∀ i, ∀ᵐ x ∂μ.restrict (Q i),
      (fun y=>K.W (x,y)) =ᵐ[μ.restrict A] oneOn ((C i)ᶜ))
    (j : I) (hp : 1<10*μ.real (P j)) (hq : 1<10*μ.real (Q j))
    (hp2 : 10*μ.real (P j)≤2) (hq2 : 10*μ.real (Q j)≤2)
    (ex : 2+10*μ.real (S\⋃ i,P i∪Q i)<10*μ.real (P j)+10*μ.real (Q j)) :
    ∃ H : Half μ, halfEnergy μ K H<1/50 := by
  classical
  let B := (C j)ᶜ∩A
  let E := C j∩A
  let Z := S\⋃ i,P i∪Q i
  have mb : MeasurableSet B := (mc j).compl.inter ma
  have me : MeasurableSet E := (mc j).inter ma
  have mz : MeasurableSet Z := ms.diff (MeasurableSet.iUnion (fun i=>(mp i).union (mq i)))
  have cover : B∪E=A := by
    ext x; simp [B,E]; tauto
  have bd : Disjoint B E := Set.disjoint_left.mpr (fun _ h g=>h.1 g.1)
  have Bc : μ.real B=1/5 := (cap j).2
  have Ec : μ.real E=1/5 := (cap j).1
  let flip (i : I) : Prop := i≠j ∧ ¬ μ.real (C i∩B)≤1/10
  let L (i : I) := if flip i then Q i else P i
  let M (i : I) := if flip i then P i else Q i
  have lm (i) : MeasurableSet (L i) := by by_cases g : flip i <;> simp [L,g,mp,mq]
  have mm (i) : MeasurableSet (M i) := by by_cases g : flip i <;> simp [M,g,mp,mq]
  have ci (i) : L i∪M i=P i∪Q i := by by_cases g : flip i; simp [L,M,g,union_comm]; simp [L,M,g]
  have ij (i) : Disjoint (L i) (M i) := by
    by_cases g : flip i
    · simpa [L,M,g] using (inner i).symm
    · simpa [L,M,g] using inner i
  have oi : Pairwise (Disjoint on fun i=>L i∪M i) := by simpa only [Function.onFun,ci] using outer
  have Lj : L j=P j := by simp [L,flip]
  have Mj : M j=Q j := by simp [M,flip]
  have easy (i) (ne : i≠j) :
      (∀ᵐ x ∂μ.restrict (L i),deg (μ.restrict B) K x≤1/10) ∧
      (∀ᵐ x ∂μ.restrict (M i),deg (μ.restrict E) K x≤1/10) := by
    have eB : B⊆A := inter_subset_right
    have eE : E⊆A := inter_subset_right
    have pp := pivot_row_inter μ K A B (C i) (P i) (mc i) eB (rowP i)
    have pq := pivot_row_inter μ K A B (C i)ᶜ (Q i) (mc i).compl eB (rowQ i)
    have qp := pivot_row_inter μ K A E (C i) (P i) (mc i) eE (rowP i)
    have qq := pivot_row_inter μ K A E (C i)ᶜ (Q i) (mc i).compl eE (rowQ i)
    have ca := pivot_split_of_cover μ B E (C i) mb me (mc i) bd
    rw [cover,(cap i).1] at ca
    have cb := pivot_split_compl μ B (C i) mb (mc i)
    have cd := pivot_split_compl μ E (C i) me (mc i)
    by_cases g : μ.real (C i∩B)≤1/10
    · simp only [L,M,flip,ne,g,not_true_eq_false,and_false,if_false]
      constructor
      · filter_upwards [pp] with x hx using by linarith
      · filter_upwards [qq] with x hx using by linarith
    · have fl : flip i := ⟨ne,g⟩
      simp only [L,M,fl,if_true]
      constructor
      · filter_upwards [pq] with x hx using by linarith
      · filter_upwards [qp] with x hx using by linarith
  have jb : ∀ᵐ x ∂μ.restrict (L j), deg (μ.restrict B) K x≤0 := by
    rw [Lj]
    have r := pivot_row_inter μ K A B (C j) (P j) (mc j) inter_subset_right (rowP j)
    filter_upwards [r] with x hx
    rw [hx]
    suffices (C j∩B)=∅ by simp [this]
    ext y; simp [B]; tauto
  have je : ∀ᵐ x ∂μ.restrict (M j), deg (μ.restrict E) K x≤0 := by
    rw [Mj]
    have r := pivot_row_inter μ K A E (C j)ᶜ (Q j) (mc j).compl inter_subset_right (rowQ j)
    filter_upwards [r] with x hx
    rw [hx]
    suffices ((C j)ᶜ∩E)=∅ by simp [this]
    ext y; simp [E]; tauto
  have edged : ∀ᵐ z ∂μ.prod μ, z.1∈S → z.2∈S → 0<K.W z →
      ∃ i,(z.1∈L i ∧ z.2∈M i) ∨ (z.1∈M i ∧ z.2∈L i) := by
    filter_upwards [outside_prod_restrict_edge μ K S ms P Q edge] with z hz s t h
    obtain ⟨i,e⟩ := hz s t h
    refine ⟨i,?_⟩
    by_cases g : flip i
    · simpa [L,M,g,or_comm] using e
    · simpa [L,M,g] using e
  have orient (U V : I→Set X) (n : ∀ i, U i∪V i=P i∪Q i)
      (mU : ∀ i, MeasurableSet (U i)) (mV : ∀ i, MeasurableSet (V i))
      (d : ∀ i, Disjoint (U i) (V i))
      (es : ∀ᵐ z ∂μ.prod μ, z.1∈S → z.2∈S → 0<K.W z →
        ∃ i,(z.1∈U i ∧ z.2∈V i) ∨ (z.1∈V i ∧ z.2∈U i))
      (T : Set X) (mT : MeasurableSet T) (inA : T⊆A) (tc : μ.real T=1/5)
      (free : ∀ᵐ x ∂μ.restrict (U j),deg (μ.restrict T) K x≤0)
      (cheap : ∀ i, i≠j → ∀ᵐ x ∂μ.restrict (U i),deg (μ.restrict T) K x≤1/10)
      (k : ℝ) (kl : k<2)
      (fill : PivotFill (10*μ.real (⋃ i,U i)) (10*μ.real (U j)) (10*μ.real Z) k) :
      ∃ H : Half μ, halfEnergy μ K H<1/50 := by
    let F := U j
    let D := ⋃ i : {i : I // i≠j}, U i
    have mD : MeasurableSet D := MeasurableSet.iUnion (fun i=>mU i)
    have oi' : Pairwise (Disjoint on fun i=>U i∪V i) := by simpa only [Function.onFun,n] using outer
    have sub (i) : U i⊆S := subset_union_left.trans (n i ▸ ins i)
    have ds : D⊆S := iUnion_subset (fun i=>sub i)
    have FD : Disjoint F D := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      exact Set.disjoint_left.mp (oi' i.property.symm) (Or.inl hx) (Or.inl hi)
    have FZ : Disjoint F Z := Set.disjoint_left.mpr (fun x h g=>g.2 (mem_iUnion.mpr ⟨j,n j ▸ Or.inl h⟩))
    have DZ : Disjoint D Z := by
      apply Set.disjoint_left.mpr
      intro x h g
      obtain ⟨i,hi⟩ := mem_iUnion.mp h
      exact g.2 (mem_iUnion.mpr ⟨i,n i ▸ Or.inl hi⟩)
    have allD : F∪D=(⋃ i,U i) := by
      ext x
      constructor
      · rintro (h|h)
        · exact mem_iUnion.mpr ⟨j,h⟩
        · obtain ⟨i,g⟩ := mem_iUnion.mp h
          exact mem_iUnion.mpr ⟨i,g⟩
      · intro h
        obtain ⟨i,g⟩ := mem_iUnion.mp h
        by_cases eq : i=j
        · subst i
          exact Or.inl g
        · exact Or.inr (mem_iUnion.mpr ⟨⟨i,eq⟩,g⟩)
    have ao : ∀ᵐ z ∂μ.prod μ, z.1∈T → z.2∈T → K.W z=0 := by
      filter_upwards [aa] with z e s t using e (inA s) (inA t)
    have oo : ∀ᵐ z ∂μ.prod μ, z.1∈F∪D∪Z → z.2∈F∪D∪Z → K.W z=0 := by
      rw [allD]
      have ins' : (⋃ i,U i)∪Z⊆S := union_subset (iUnion_subset sub) sdiff_subset
      have bad (x : X) (hx : x∈(⋃ i,U i)∪Z) (i : I) : x∉V i := by
        intro v
        rcases hx with u|z
        · obtain ⟨a,u⟩ := mem_iUnion.mp u
          by_cases g : a=i
          · exact Set.disjoint_left.mp (d i) (g ▸ u) v
          · exact Set.disjoint_left.mp (oi' g) (Or.inl u) (Or.inr v)
        · exact z.2 (mem_iUnion.mpr ⟨i,n i ▸ Or.inr v⟩)
      filter_upwards [es] with z h s t
      apply le_antisymm _ (K.nonneg z)
      by_contra! pos
      obtain ⟨i,(⟨_,v⟩|⟨v,_⟩)⟩ := h (ins' s) (ins' t) pos
      · exact bad _ t i v
      · exact bad _ s i v
    have cl : ∀ᵐ x ∂μ.restrict D, deg (μ.restrict T) K x≤1/10 := by
      have each (i : {i : I // i≠j}) :
          ∀ᵐ x ∂μ, x∈U i → deg (μ.restrict T) K x≤1/10 :=
        (ae_restrict_iff' (mU i)).mp (cheap i i.property)
      have alls := ae_all_iff.mpr each
      apply (ae_restrict_iff' mD).mpr
      filter_upwards [alls] with x h hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact h i hi
    rw [←allD,measureReal_union FD mD] at fill
    have dis : Pairwise (Disjoint on fun i : Fin 4 => ![T,F,D,Z] i) := by
      intro i l ne
      have tF := ad.mono inA (sub j)
      have tD := ad.mono inA ds
      have tZ := ad.mono inA (show Z⊆S from sdiff_subset)
      fin_cases i <;> fin_cases l <;>
        simp_all only [Function.onFun, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Fin.isValue, ne_eq] <;>
        first | exact tF | exact tF.symm | exact tD | exact tD.symm |
          exact tZ | exact tZ.symm | exact FD | exact FD.symm | exact FZ |
          exact FZ.symm | exact DZ | exact DZ.symm
    exact pivot_fill_half μ K T F D Z mT (mU j) mD mz dis ao oo tc free cl fill kl
  have UV : Disjoint (⋃ i,L i) (⋃ i,M i) := by
    apply Set.disjoint_left.mpr
    intro x h g
    obtain ⟨i,h⟩ := mem_iUnion.mp h
    obtain ⟨a,g⟩ := mem_iUnion.mp g
    by_cases e : i=a
    · exact Set.disjoint_left.mp (ij a) (e ▸ h) g
    · exact Set.disjoint_left.mp (oi e) (Or.inl h) (Or.inr g)
  have bank : (⋃ i,L i)∪(⋃ i,M i) = ⋃ i,P i∪Q i := by
    rw [←iUnion_union_distrib]
    simp_rw [ci]
  have total : 10*μ.real (⋃ i,L i)+10*μ.real (⋃ i,M i)=6-10*μ.real Z := by
    have ms' : MeasurableSet (⋃ i,P i∪Q i) := MeasurableSet.iUnion (fun i=>(mp i).union (mq i))
    rw [show μ.real Z=μ.real S-μ.real (⋃ i,P i∪Q i) from measureReal_sdiff (iUnion_subset ins) ms',
        ←bank,measureReal_union UV (MeasurableSet.iUnion mm),size]
    ring
  have px : 10*μ.real (L j)≤10*μ.real (⋃ i,L i) :=
    mul_le_mul_of_nonneg_left (measureReal_mono (subset_iUnion L j)) (by norm_num)
  have qx : 10*μ.real (M j)≤10*μ.real (⋃ i,M i) :=
    mul_le_mul_of_nonneg_left (measureReal_mono (subset_iUnion M j)) (by norm_num)
  obtain ⟨k,kl,fill⟩|⟨k,kl,fill⟩ := strict_dominant_pivot
      (10*μ.real (⋃ i,L i)) (10*μ.real (⋃ i,M i))
      (10*μ.real (L j)) (10*μ.real (M j)) (10*μ.real Z)
      (by positivity) (Lj ▸ hp) (Mj ▸ hq) (Lj ▸ hp2) (Mj ▸ hq2) px qx total (by simpa [Lj,Mj] using ex)
  · exact orient L M ci lm mm ij edged B mb inter_subset_right Bc jb
      (fun i g=>(easy i g).1) k kl fill
  · exact orient M L (fun i=>by rw [union_comm,ci]) mm lm (fun i=>(ij i).symm)
      (by simpa only [or_comm] using edged) E me inter_subset_right Ec je
      (fun i g=>(easy i g).2) k kl fill

#print axioms strict_dominant_active
end SparseHalfGraphon
