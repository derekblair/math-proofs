import PetersenSharpFast

namespace PetersenSharp

/-- A simple cycle in the actual lifted graph, with its seam edge included. -/
def Cyclic (n : ℕ) : Prop :=
  ∃ v : Fin n → V, Function.Injective v ∧
    ∀ i : Fin n, edge (v i) (v ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

private def ports : List P := [0,1,2]
private theorem port_mem (p : P) : p ∈ ports := by decide +revert

/-- Continue an injective path on the full 50-vertex graph, then test the seam.
Vertices are recorded in lifted coordinates, never just their projection. -/
def check (start u : V) (prev : List V) : ℕ → Bool
  | 0 => decide (edge u start)
  | r+1 => ports.any (fun p =>
    let v := next u p
    !prev.contains v && check start v (v::prev) r)

theorem extend_of_cycle (n : ℕ) (hn : 0<n) (v : Fin n→V) (inj : Function.Injective v)
    (ed : ∀ i : Fin n, edge (v i) (v ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩))
    (r i : ℕ) (hi : i<n) (left : i+r+1=n) (prev : List V)
    (seen : ∀ u ∈ prev, ∃ j : Fin n, j.val ≤ i ∧ v j = u) :
    check (v ⟨0,hn⟩) (v ⟨i,hi⟩) prev r = true := by
  induction r generalizing i prev with
  | zero =>
    have last : i+1=n := by omega
    simpa [check,last] using ed ⟨i,hi⟩
  | succ r ih =>
    have hnext : i+1<n := by omega
    have edgeNext := ed ⟨i,hi⟩
    simp only [Nat.mod_eq_of_lt hnext] at edgeNext
    obtain ⟨c,hc⟩ := edgeNext
    have fresh : v ⟨i+1,hnext⟩ ∉ prev := by
      intro bad
      obtain ⟨j,jle,e⟩ := seen _ bad
      have je := congrArg Fin.val (inj e)
      simp at je
      omega
    have H : check (v ⟨0,hn⟩) (v ⟨i+1,hnext⟩) (v ⟨i+1,hnext⟩ :: prev) r = true := by
      apply ih (i:=i+1) (hi:=hnext) (left:=by omega)
      intro u hu
      rcases List.mem_cons.mp hu with e|e
      · exact ⟨⟨i+1,hnext⟩,Nat.le_refl _,e.symm⟩
      · obtain ⟨j,jle,e⟩ := seen _ e
        exact ⟨j,by omega,e⟩
    rw [check,List.any_eq_true]
    refine ⟨c,port_mem c,?_⟩
    simp [hc,fresh,H]

theorem exists_check (n : ℕ) (hn : 0<n) (H : Cyclic n) :
    ∃ start, check start start [start] (n-1) = true := by
  obtain ⟨v,inj,ed⟩ := H
  let start := v ⟨0,hn⟩
  refine ⟨start,extend_of_cycle n hn v inj ed (n-1) 0 hn (by omega) [start] ?_⟩
  intro u hu
  exact ⟨⟨0,hn⟩,Nat.le_refl _,(List.mem_singleton.mp hu).symm⟩

private theorem contains_shift (d : D) (xs : List V) (v : V) :
    (xs.map (shift d)).contains (shift d v) = xs.contains v := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem,List.contains_iff_mem,List.mem_map]
  constructor
  · rintro ⟨w,h,e⟩
    exact shift_inj d e ▸ h
  · intro h
    exact ⟨v,h,rfl⟩

private theorem check_shift (d : D) (start u : V) (prev : List V) (r : ℕ) :
    check (shift d start) (shift d u) (prev.map (shift d)) r = check start u prev r := by
  induction r generalizing u prev with
  | zero =>
    apply Bool.eq_iff_iff.mpr
    change decide (edge (shift d u) (shift d start)) = true ↔ decide (edge u start) = true
    simpa only [decide_eq_true_eq] using shift_edge d u start
  | succ r ih =>
    simp only [check,← shift_next d u,contains_shift,← List.map_cons,ih]

private def checkNat (start u : ℕ) (prev : List ℕ) : ℕ → Bool
  | 0 => ports.any (fun p => fast u p == start)
  | r+1 => ports.any (fun p =>
    let v := fast u p
    !prev.contains v && checkNat start v (v::prev) r)

private theorem contains_enc (xs : List V) (v : V) :
    (xs.map enc).contains (enc v) = xs.contains v := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem,List.contains_iff_mem,List.mem_map]
  constructor
  · rintro ⟨w,h,e⟩
    exact enc_inj e ▸ h
  · intro h
    exact ⟨v,h,rfl⟩

private theorem check_nat (start u : V) (prev : List V) (r : ℕ) :
    checkNat (enc start) (enc u) (prev.map enc) r = check start u prev r := by
  induction r generalizing u prev with
  | zero =>
    apply Bool.eq_iff_iff.mpr
    change ports.any (fun p => fast (enc u) p == enc start) = true ↔
      decide (edge u start) = true
    rw [decide_eq_true_eq]
    simp only [List.any_eq_true,fast_ok,beq_iff_eq,enc_inj.eq_iff,edge]
    constructor
    · rintro ⟨p,_,h⟩; exact ⟨p,h⟩
    · rintro ⟨p,h⟩; exact ⟨p,port_mem p,h⟩
  | succ r ih =>
    simp only [checkNat,check,fast_ok,contains_enc,← List.map_cons,ih]

set_option maxRecDepth 20000
set_option maxHeartbeats 300000


private theorem combine_step (s u : ℕ) (past : List ℕ) (r : ℕ)
    (h0 : (!past.contains (fast u 0) && checkNat s (fast u 0) (fast u 0 :: past) r) = false)
    (h1 : (!past.contains (fast u 1) && checkNat s (fast u 1) (fast u 1 :: past) r) = false)
    (h2 : (!past.contains (fast u 2) && checkNat s (fast u 2) (fast u 2 :: past) r) = false) :
    checkNat s u past (r+1) = false := by
  simp only [checkNat,ports,List.any_cons,List.any_nil,h0,h1,h2,Bool.false_or]

private theorem part1 : checkNat 0 0 [0] 3 = false := by
  decide
private theorem cert4_0 : checkNat 0 0 [0] 3 = false := part1
private theorem part2 : checkNat 5 5 [5] 3 = false := by
  decide
private theorem cert4_1 : checkNat 5 5 [5] 3 = false := part2
private theorem part3 : checkNat 10 10 [10] 3 = false := by
  decide
private theorem cert4_2 : checkNat 10 10 [10] 3 = false := part3
private theorem part4 : checkNat 15 15 [15] 3 = false := by
  decide
private theorem cert4_3 : checkNat 15 15 [15] 3 = false := part4
private theorem part5 : checkNat 20 20 [20] 3 = false := by
  decide
private theorem cert4_4 : checkNat 20 20 [20] 3 = false := part5
private theorem part6 : checkNat 25 25 [25] 3 = false := by
  decide
private theorem cert4_5 : checkNat 25 25 [25] 3 = false := part6
private theorem part7 : checkNat 30 30 [30] 3 = false := by
  decide
private theorem cert4_6 : checkNat 30 30 [30] 3 = false := part7
private theorem part8 : checkNat 35 35 [35] 3 = false := by
  decide
private theorem cert4_7 : checkNat 35 35 [35] 3 = false := part8
private theorem part9 : checkNat 40 40 [40] 3 = false := by
  decide
private theorem cert4_8 : checkNat 40 40 [40] 3 = false := part9
private theorem part10 : checkNat 45 45 [45] 3 = false := by
  decide
private theorem cert4_9 : checkNat 45 45 [45] 3 = false := part10
private theorem part15 : checkNat 0 20 [20,15,10,5,0] 3 = false := by
  decide
private theorem part16 : checkNat 0 41 [41,15,10,5,0] 3 = false := by
  decide
private theorem part14 : checkNat 0 15 [15,10,5,0] 4 = false := by
  apply combine_step 0 15 [15,10,5,0] 3
  · have h : fast 15 0=20 := by decide
    rw [h]
    simp only [part15,Bool.and_false]
  · have h : fast 15 1=10 := by decide
    rw [h]
    have b : ([15,10,5,0] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 15 2=41 := by decide
    rw [h]
    simp only [part16,Bool.and_false]
private theorem part18 : checkNat 0 49 [49,35,10,5,0] 3 = false := by
  decide
private theorem part19 : checkNat 0 25 [25,35,10,5,0] 3 = false := by
  decide
private theorem part17 : checkNat 0 35 [35,10,5,0] 4 = false := by
  apply combine_step 0 35 [35,10,5,0] 3
  · have h : fast 35 0=49 := by decide
    rw [h]
    simp only [part18,Bool.and_false]
  · have h : fast 35 1=25 := by decide
    rw [h]
    simp only [part19,Bool.and_false]
  · have h : fast 35 2=10 := by decide
    rw [h]
    have b : ([35,10,5,0] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part13 : checkNat 0 10 [10,5,0] 5 = false := by
  apply combine_step 0 10 [10,5,0] 4
  · have h : fast 10 0=15 := by decide
    rw [h]
    simp only [part14,Bool.and_false]
  · have h : fast 10 1=5 := by decide
    rw [h]
    have b : ([10,5,0] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 10 2=35 := by decide
    rw [h]
    simp only [part17,Bool.and_false]
private theorem part22 : checkNat 0 27 [27,42,30,5,0] 3 = false := by
  decide
private theorem part23 : checkNat 0 16 [16,42,30,5,0] 3 = false := by
  decide
private theorem part21 : checkNat 0 42 [42,30,5,0] 4 = false := by
  apply combine_step 0 42 [42,30,5,0] 3
  · have h : fast 42 0=27 := by decide
    rw [h]
    simp only [part22,Bool.and_false]
  · have h : fast 42 1=30 := by decide
    rw [h]
    have b : ([42,30,5,0] : List ℕ).contains 30 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 42 2=16 := by decide
    rw [h]
    simp only [part23,Bool.and_false]
private theorem part25 : checkNat 0 39 [39,48,30,5,0] 3 = false := by
  decide
private theorem part26 : checkNat 0 23 [23,48,30,5,0] 3 = false := by
  decide
private theorem part24 : checkNat 0 48 [48,30,5,0] 4 = false := by
  apply combine_step 0 48 [48,30,5,0] 3
  · have h : fast 48 0=30 := by decide
    rw [h]
    have b : ([48,30,5,0] : List ℕ).contains 30 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 48 1=39 := by decide
    rw [h]
    simp only [part25,Bool.and_false]
  · have h : fast 48 2=23 := by decide
    rw [h]
    simp only [part26,Bool.and_false]
private theorem part20 : checkNat 0 30 [30,5,0] 5 = false := by
  apply combine_step 0 30 [30,5,0] 4
  · have h : fast 30 0=42 := by decide
    rw [h]
    simp only [part21,Bool.and_false]
  · have h : fast 30 1=48 := by decide
    rw [h]
    simp only [part24,Bool.and_false]
  · have h : fast 30 2=5 := by decide
    rw [h]
    have b : ([30,5,0] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part12 : checkNat 0 5 [5,0] 6 = false := by
  apply combine_step 0 5 [5,0] 5
  · have h : fast 5 0=10 := by decide
    rw [h]
    simp only [part13,Bool.and_false]
  · have h : fast 5 1=0 := by decide
    rw [h]
    have b : ([5,0] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 5 2=30 := by decide
    rw [h]
    simp only [part20,Bool.and_false]
private theorem part30 : checkNat 0 5 [5,10,15,20,0] 3 = false := by
  decide
private theorem part31 : checkNat 0 35 [35,10,15,20,0] 3 = false := by
  decide
private theorem part29 : checkNat 0 10 [10,15,20,0] 4 = false := by
  apply combine_step 0 10 [10,15,20,0] 3
  · have h : fast 10 0=15 := by decide
    rw [h]
    have b : ([10,15,20,0] : List ℕ).contains 15 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 10 1=5 := by decide
    rw [h]
    simp only [part30,Bool.and_false]
  · have h : fast 10 2=35 := by decide
    rw [h]
    simp only [part31,Bool.and_false]
private theorem part33 : checkNat 0 26 [26,41,15,20,0] 3 = false := by
  decide
private theorem part34 : checkNat 0 34 [34,41,15,20,0] 3 = false := by
  decide
private theorem part32 : checkNat 0 41 [41,15,20,0] 4 = false := by
  apply combine_step 0 41 [41,15,20,0] 3
  · have h : fast 41 0=26 := by decide
    rw [h]
    simp only [part33,Bool.and_false]
  · have h : fast 41 1=34 := by decide
    rw [h]
    simp only [part34,Bool.and_false]
  · have h : fast 41 2=15 := by decide
    rw [h]
    have b : ([41,15,20,0] : List ℕ).contains 15 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part28 : checkNat 0 15 [15,20,0] 5 = false := by
  apply combine_step 0 15 [15,20,0] 4
  · have h : fast 15 0=20 := by decide
    rw [h]
    have b : ([15,20,0] : List ℕ).contains 20 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 15 1=10 := by decide
    rw [h]
    simp only [part29,Bool.and_false]
  · have h : fast 15 2=41 := by decide
    rw [h]
    simp only [part32,Bool.and_false]
private theorem part37 : checkNat 0 44 [44,32,45,20,0] 3 = false := by
  decide
private theorem part38 : checkNat 0 7 [7,32,45,20,0] 3 = false := by
  decide
private theorem part36 : checkNat 0 32 [32,45,20,0] 4 = false := by
  apply combine_step 0 32 [32,45,20,0] 3
  · have h : fast 32 0=44 := by decide
    rw [h]
    simp only [part37,Bool.and_false]
  · have h : fast 32 1=45 := by decide
    rw [h]
    have b : ([32,45,20,0] : List ℕ).contains 45 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 32 2=7 := by decide
    rw [h]
    simp only [part38,Bool.and_false]
private theorem part40 : checkNat 0 26 [26,36,45,20,0] 3 = false := by
  decide
private theorem part41 : checkNat 0 11 [11,36,45,20,0] 3 = false := by
  decide
private theorem part39 : checkNat 0 36 [36,45,20,0] 4 = false := by
  apply combine_step 0 36 [36,45,20,0] 3
  · have h : fast 36 0=45 := by decide
    rw [h]
    have b : ([36,45,20,0] : List ℕ).contains 45 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 36 1=26 := by decide
    rw [h]
    simp only [part40,Bool.and_false]
  · have h : fast 36 2=11 := by decide
    rw [h]
    simp only [part41,Bool.and_false]
private theorem part35 : checkNat 0 45 [45,20,0] 5 = false := by
  apply combine_step 0 45 [45,20,0] 4
  · have h : fast 45 0=32 := by decide
    rw [h]
    simp only [part36,Bool.and_false]
  · have h : fast 45 1=36 := by decide
    rw [h]
    simp only [part39,Bool.and_false]
  · have h : fast 45 2=20 := by decide
    rw [h]
    have b : ([45,20,0] : List ℕ).contains 20 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part27 : checkNat 0 20 [20,0] 6 = false := by
  apply combine_step 0 20 [20,0] 5
  · have h : fast 20 0=0 := by decide
    rw [h]
    have b : ([20,0] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 20 1=15 := by decide
    rw [h]
    simp only [part28,Bool.and_false]
  · have h : fast 20 2=45 := by decide
    rw [h]
    simp only [part35,Bool.and_false]
private theorem part45 : checkNat 0 31 [31,49,35,25,0] 3 = false := by
  decide
private theorem part46 : checkNat 0 24 [24,49,35,25,0] 3 = false := by
  decide
private theorem part44 : checkNat 0 49 [49,35,25,0] 4 = false := by
  apply combine_step 0 49 [49,35,25,0] 3
  · have h : fast 49 0=31 := by decide
    rw [h]
    simp only [part45,Bool.and_false]
  · have h : fast 49 1=35 := by decide
    rw [h]
    have b : ([49,35,25,0] : List ℕ).contains 35 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 49 2=24 := by decide
    rw [h]
    simp only [part46,Bool.and_false]
private theorem part48 : checkNat 0 15 [15,10,35,25,0] 3 = false := by
  decide
private theorem part49 : checkNat 0 5 [5,10,35,25,0] 3 = false := by
  decide
private theorem part47 : checkNat 0 10 [10,35,25,0] 4 = false := by
  apply combine_step 0 10 [10,35,25,0] 3
  · have h : fast 10 0=15 := by decide
    rw [h]
    simp only [part48,Bool.and_false]
  · have h : fast 10 1=5 := by decide
    rw [h]
    simp only [part49,Bool.and_false]
  · have h : fast 10 2=35 := by decide
    rw [h]
    have b : ([10,35,25,0] : List ℕ).contains 35 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part43 : checkNat 0 35 [35,25,0] 5 = false := by
  apply combine_step 0 35 [35,25,0] 4
  · have h : fast 35 0=49 := by decide
    rw [h]
    simp only [part44,Bool.and_false]
  · have h : fast 35 1=25 := by decide
    rw [h]
    have b : ([35,25,0] : List ℕ).contains 25 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 35 2=10 := by decide
    rw [h]
    simp only [part47,Bool.and_false]
private theorem part52 : checkNat 0 46 [46,33,40,25,0] 3 = false := by
  decide
private theorem part53 : checkNat 0 8 [8,33,40,25,0] 3 = false := by
  decide
private theorem part51 : checkNat 0 33 [33,40,25,0] 4 = false := by
  apply combine_step 0 33 [33,40,25,0] 3
  · have h : fast 33 0=40 := by decide
    rw [h]
    have b : ([33,40,25,0] : List ℕ).contains 40 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 33 1=46 := by decide
    rw [h]
    simp only [part52,Bool.and_false]
  · have h : fast 33 2=8 := by decide
    rw [h]
    simp only [part53,Bool.and_false]
private theorem part55 : checkNat 0 24 [24,19,40,25,0] 3 = false := by
  decide
private theorem part56 : checkNat 0 14 [14,19,40,25,0] 3 = false := by
  decide
private theorem part54 : checkNat 0 19 [19,40,25,0] 4 = false := by
  apply combine_step 0 19 [19,40,25,0] 3
  · have h : fast 19 0=24 := by decide
    rw [h]
    simp only [part55,Bool.and_false]
  · have h : fast 19 1=14 := by decide
    rw [h]
    simp only [part56,Bool.and_false]
  · have h : fast 19 2=40 := by decide
    rw [h]
    have b : ([19,40,25,0] : List ℕ).contains 40 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part50 : checkNat 0 40 [40,25,0] 5 = false := by
  apply combine_step 0 40 [40,25,0] 4
  · have h : fast 40 0=25 := by decide
    rw [h]
    have b : ([40,25,0] : List ℕ).contains 25 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 40 1=33 := by decide
    rw [h]
    simp only [part51,Bool.and_false]
  · have h : fast 40 2=19 := by decide
    rw [h]
    simp only [part54,Bool.and_false]
private theorem part42 : checkNat 0 25 [25,0] 6 = false := by
  apply combine_step 0 25 [25,0] 5
  · have h : fast 25 0=35 := by decide
    rw [h]
    simp only [part43,Bool.and_false]
  · have h : fast 25 1=40 := by decide
    rw [h]
    simp only [part50,Bool.and_false]
  · have h : fast 25 2=0 := by decide
    rw [h]
    have b : ([25,0] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part11 : checkNat 0 0 [0] 7 = false := by
  apply combine_step 0 0 [0] 6
  · have h : fast 0 0=5 := by decide
    rw [h]
    simp only [part12,Bool.and_false]
  · have h : fast 0 1=20 := by decide
    rw [h]
    simp only [part27,Bool.and_false]
  · have h : fast 0 2=25 := by decide
    rw [h]
    simp only [part42,Bool.and_false]
private theorem cert8_0 : checkNat 0 0 [0] 7 = false := part11
private theorem part61 : checkNat 5 0 [0,20,15,10,5] 3 = false := by
  decide
private theorem part62 : checkNat 5 45 [45,20,15,10,5] 3 = false := by
  decide
private theorem part60 : checkNat 5 20 [20,15,10,5] 4 = false := by
  apply combine_step 5 20 [20,15,10,5] 3
  · have h : fast 20 0=0 := by decide
    rw [h]
    simp only [part61,Bool.and_false]
  · have h : fast 20 1=15 := by decide
    rw [h]
    have b : ([20,15,10,5] : List ℕ).contains 15 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 20 2=45 := by decide
    rw [h]
    simp only [part62,Bool.and_false]
private theorem part64 : checkNat 5 26 [26,41,15,10,5] 3 = false := by
  decide
private theorem part65 : checkNat 5 34 [34,41,15,10,5] 3 = false := by
  decide
private theorem part63 : checkNat 5 41 [41,15,10,5] 4 = false := by
  apply combine_step 5 41 [41,15,10,5] 3
  · have h : fast 41 0=26 := by decide
    rw [h]
    simp only [part64,Bool.and_false]
  · have h : fast 41 1=34 := by decide
    rw [h]
    simp only [part65,Bool.and_false]
  · have h : fast 41 2=15 := by decide
    rw [h]
    have b : ([41,15,10,5] : List ℕ).contains 15 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part59 : checkNat 5 15 [15,10,5] 5 = false := by
  apply combine_step 5 15 [15,10,5] 4
  · have h : fast 15 0=20 := by decide
    rw [h]
    simp only [part60,Bool.and_false]
  · have h : fast 15 1=10 := by decide
    rw [h]
    have b : ([15,10,5] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 15 2=41 := by decide
    rw [h]
    simp only [part63,Bool.and_false]
private theorem part68 : checkNat 5 31 [31,49,35,10,5] 3 = false := by
  decide
private theorem part69 : checkNat 5 24 [24,49,35,10,5] 3 = false := by
  decide
private theorem part67 : checkNat 5 49 [49,35,10,5] 4 = false := by
  apply combine_step 5 49 [49,35,10,5] 3
  · have h : fast 49 0=31 := by decide
    rw [h]
    simp only [part68,Bool.and_false]
  · have h : fast 49 1=35 := by decide
    rw [h]
    have b : ([49,35,10,5] : List ℕ).contains 35 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 49 2=24 := by decide
    rw [h]
    simp only [part69,Bool.and_false]
private theorem part71 : checkNat 5 40 [40,25,35,10,5] 3 = false := by
  decide
private theorem part72 : checkNat 5 0 [0,25,35,10,5] 3 = false := by
  decide
private theorem part70 : checkNat 5 25 [25,35,10,5] 4 = false := by
  apply combine_step 5 25 [25,35,10,5] 3
  · have h : fast 25 0=35 := by decide
    rw [h]
    have b : ([25,35,10,5] : List ℕ).contains 35 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 25 1=40 := by decide
    rw [h]
    simp only [part71,Bool.and_false]
  · have h : fast 25 2=0 := by decide
    rw [h]
    simp only [part72,Bool.and_false]
private theorem part66 : checkNat 5 35 [35,10,5] 5 = false := by
  apply combine_step 5 35 [35,10,5] 4
  · have h : fast 35 0=49 := by decide
    rw [h]
    simp only [part67,Bool.and_false]
  · have h : fast 35 1=25 := by decide
    rw [h]
    simp only [part70,Bool.and_false]
  · have h : fast 35 2=10 := by decide
    rw [h]
    have b : ([35,10,5] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part58 : checkNat 5 10 [10,5] 6 = false := by
  apply combine_step 5 10 [10,5] 5
  · have h : fast 10 0=15 := by decide
    rw [h]
    simp only [part59,Bool.and_false]
  · have h : fast 10 1=5 := by decide
    rw [h]
    have b : ([10,5] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 10 2=35 := by decide
    rw [h]
    simp only [part66,Bool.and_false]
private theorem part76 : checkNat 5 10 [10,15,20,0,5] 3 = false := by
  decide
private theorem part77 : checkNat 5 41 [41,15,20,0,5] 3 = false := by
  decide
private theorem part75 : checkNat 5 15 [15,20,0,5] 4 = false := by
  apply combine_step 5 15 [15,20,0,5] 3
  · have h : fast 15 0=20 := by decide
    rw [h]
    have b : ([15,20,0,5] : List ℕ).contains 20 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 15 1=10 := by decide
    rw [h]
    simp only [part76,Bool.and_false]
  · have h : fast 15 2=41 := by decide
    rw [h]
    simp only [part77,Bool.and_false]
private theorem part79 : checkNat 5 32 [32,45,20,0,5] 3 = false := by
  decide
private theorem part80 : checkNat 5 36 [36,45,20,0,5] 3 = false := by
  decide
private theorem part78 : checkNat 5 45 [45,20,0,5] 4 = false := by
  apply combine_step 5 45 [45,20,0,5] 3
  · have h : fast 45 0=32 := by decide
    rw [h]
    simp only [part79,Bool.and_false]
  · have h : fast 45 1=36 := by decide
    rw [h]
    simp only [part80,Bool.and_false]
  · have h : fast 45 2=20 := by decide
    rw [h]
    have b : ([45,20,0,5] : List ℕ).contains 20 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part74 : checkNat 5 20 [20,0,5] 5 = false := by
  apply combine_step 5 20 [20,0,5] 4
  · have h : fast 20 0=0 := by decide
    rw [h]
    have b : ([20,0,5] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 20 1=15 := by decide
    rw [h]
    simp only [part75,Bool.and_false]
  · have h : fast 20 2=45 := by decide
    rw [h]
    simp only [part78,Bool.and_false]
private theorem part83 : checkNat 5 49 [49,35,25,0,5] 3 = false := by
  decide
private theorem part84 : checkNat 5 10 [10,35,25,0,5] 3 = false := by
  decide
private theorem part82 : checkNat 5 35 [35,25,0,5] 4 = false := by
  apply combine_step 5 35 [35,25,0,5] 3
  · have h : fast 35 0=49 := by decide
    rw [h]
    simp only [part83,Bool.and_false]
  · have h : fast 35 1=25 := by decide
    rw [h]
    have b : ([35,25,0,5] : List ℕ).contains 25 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 35 2=10 := by decide
    rw [h]
    simp only [part84,Bool.and_false]
private theorem part86 : checkNat 5 33 [33,40,25,0,5] 3 = false := by
  decide
private theorem part87 : checkNat 5 19 [19,40,25,0,5] 3 = false := by
  decide
private theorem part85 : checkNat 5 40 [40,25,0,5] 4 = false := by
  apply combine_step 5 40 [40,25,0,5] 3
  · have h : fast 40 0=25 := by decide
    rw [h]
    have b : ([40,25,0,5] : List ℕ).contains 25 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 40 1=33 := by decide
    rw [h]
    simp only [part86,Bool.and_false]
  · have h : fast 40 2=19 := by decide
    rw [h]
    simp only [part87,Bool.and_false]
private theorem part81 : checkNat 5 25 [25,0,5] 5 = false := by
  apply combine_step 5 25 [25,0,5] 4
  · have h : fast 25 0=35 := by decide
    rw [h]
    simp only [part82,Bool.and_false]
  · have h : fast 25 1=40 := by decide
    rw [h]
    simp only [part85,Bool.and_false]
  · have h : fast 25 2=0 := by decide
    rw [h]
    have b : ([25,0,5] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part73 : checkNat 5 0 [0,5] 6 = false := by
  apply combine_step 5 0 [0,5] 5
  · have h : fast 0 0=5 := by decide
    rw [h]
    have b : ([0,5] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 0 1=20 := by decide
    rw [h]
    simp only [part74,Bool.and_false]
  · have h : fast 0 2=25 := by decide
    rw [h]
    simp only [part81,Bool.and_false]
private theorem part91 : checkNat 5 37 [37,27,42,30,5] 3 = false := by
  decide
private theorem part92 : checkNat 5 2 [2,27,42,30,5] 3 = false := by
  decide
private theorem part90 : checkNat 5 27 [27,42,30,5] 4 = false := by
  apply combine_step 5 27 [27,42,30,5] 3
  · have h : fast 27 0=37 := by decide
    rw [h]
    simp only [part91,Bool.and_false]
  · have h : fast 27 1=42 := by decide
    rw [h]
    have b : ([27,42,30,5] : List ℕ).contains 42 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 27 2=2 := by decide
    rw [h]
    simp only [part92,Bool.and_false]
private theorem part94 : checkNat 5 21 [21,16,42,30,5] 3 = false := by
  decide
private theorem part95 : checkNat 5 11 [11,16,42,30,5] 3 = false := by
  decide
private theorem part93 : checkNat 5 16 [16,42,30,5] 4 = false := by
  apply combine_step 5 16 [16,42,30,5] 3
  · have h : fast 16 0=21 := by decide
    rw [h]
    simp only [part94,Bool.and_false]
  · have h : fast 16 1=11 := by decide
    rw [h]
    simp only [part95,Bool.and_false]
  · have h : fast 16 2=42 := by decide
    rw [h]
    have b : ([16,42,30,5] : List ℕ).contains 42 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part89 : checkNat 5 42 [42,30,5] 5 = false := by
  apply combine_step 5 42 [42,30,5] 4
  · have h : fast 42 0=27 := by decide
    rw [h]
    simp only [part90,Bool.and_false]
  · have h : fast 42 1=30 := by decide
    rw [h]
    have b : ([42,30,5] : List ℕ).contains 30 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 42 2=16 := by decide
    rw [h]
    simp only [part93,Bool.and_false]
private theorem part98 : checkNat 5 29 [29,39,48,30,5] 3 = false := by
  decide
private theorem part99 : checkNat 5 14 [14,39,48,30,5] 3 = false := by
  decide
private theorem part97 : checkNat 5 39 [39,48,30,5] 4 = false := by
  apply combine_step 5 39 [39,48,30,5] 3
  · have h : fast 39 0=48 := by decide
    rw [h]
    have b : ([39,48,30,5] : List ℕ).contains 48 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 39 1=29 := by decide
    rw [h]
    simp only [part98,Bool.and_false]
  · have h : fast 39 2=14 := by decide
    rw [h]
    simp only [part99,Bool.and_false]
private theorem part101 : checkNat 5 3 [3,23,48,30,5] 3 = false := by
  decide
private theorem part102 : checkNat 5 18 [18,23,48,30,5] 3 = false := by
  decide
private theorem part100 : checkNat 5 23 [23,48,30,5] 4 = false := by
  apply combine_step 5 23 [23,48,30,5] 3
  · have h : fast 23 0=3 := by decide
    rw [h]
    simp only [part101,Bool.and_false]
  · have h : fast 23 1=18 := by decide
    rw [h]
    simp only [part102,Bool.and_false]
  · have h : fast 23 2=48 := by decide
    rw [h]
    have b : ([23,48,30,5] : List ℕ).contains 48 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part96 : checkNat 5 48 [48,30,5] 5 = false := by
  apply combine_step 5 48 [48,30,5] 4
  · have h : fast 48 0=30 := by decide
    rw [h]
    have b : ([48,30,5] : List ℕ).contains 30 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 48 1=39 := by decide
    rw [h]
    simp only [part97,Bool.and_false]
  · have h : fast 48 2=23 := by decide
    rw [h]
    simp only [part100,Bool.and_false]
private theorem part88 : checkNat 5 30 [30,5] 6 = false := by
  apply combine_step 5 30 [30,5] 5
  · have h : fast 30 0=42 := by decide
    rw [h]
    simp only [part89,Bool.and_false]
  · have h : fast 30 1=48 := by decide
    rw [h]
    simp only [part96,Bool.and_false]
  · have h : fast 30 2=5 := by decide
    rw [h]
    have b : ([30,5] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part57 : checkNat 5 5 [5] 7 = false := by
  apply combine_step 5 5 [5] 6
  · have h : fast 5 0=10 := by decide
    rw [h]
    simp only [part58,Bool.and_false]
  · have h : fast 5 1=0 := by decide
    rw [h]
    simp only [part73,Bool.and_false]
  · have h : fast 5 2=30 := by decide
    rw [h]
    simp only [part88,Bool.and_false]
private theorem cert8_1 : checkNat 5 5 [5] 7 = false := part57
private theorem part107 : checkNat 10 5 [5,0,20,15,10] 3 = false := by
  decide
private theorem part108 : checkNat 10 25 [25,0,20,15,10] 3 = false := by
  decide
private theorem part106 : checkNat 10 0 [0,20,15,10] 4 = false := by
  apply combine_step 10 0 [0,20,15,10] 3
  · have h : fast 0 0=5 := by decide
    rw [h]
    simp only [part107,Bool.and_false]
  · have h : fast 0 1=20 := by decide
    rw [h]
    have b : ([0,20,15,10] : List ℕ).contains 20 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 0 2=25 := by decide
    rw [h]
    simp only [part108,Bool.and_false]
private theorem part110 : checkNat 10 32 [32,45,20,15,10] 3 = false := by
  decide
private theorem part111 : checkNat 10 36 [36,45,20,15,10] 3 = false := by
  decide
private theorem part109 : checkNat 10 45 [45,20,15,10] 4 = false := by
  apply combine_step 10 45 [45,20,15,10] 3
  · have h : fast 45 0=32 := by decide
    rw [h]
    simp only [part110,Bool.and_false]
  · have h : fast 45 1=36 := by decide
    rw [h]
    simp only [part111,Bool.and_false]
  · have h : fast 45 2=20 := by decide
    rw [h]
    have b : ([45,20,15,10] : List ℕ).contains 20 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part105 : checkNat 10 20 [20,15,10] 5 = false := by
  apply combine_step 10 20 [20,15,10] 4
  · have h : fast 20 0=0 := by decide
    rw [h]
    simp only [part106,Bool.and_false]
  · have h : fast 20 1=15 := by decide
    rw [h]
    have b : ([20,15,10] : List ℕ).contains 15 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 20 2=45 := by decide
    rw [h]
    simp only [part109,Bool.and_false]
private theorem part114 : checkNat 10 36 [36,26,41,15,10] 3 = false := by
  decide
private theorem part115 : checkNat 10 1 [1,26,41,15,10] 3 = false := by
  decide
private theorem part113 : checkNat 10 26 [26,41,15,10] 4 = false := by
  apply combine_step 10 26 [26,41,15,10] 3
  · have h : fast 26 0=36 := by decide
    rw [h]
    simp only [part114,Bool.and_false]
  · have h : fast 26 1=41 := by decide
    rw [h]
    have b : ([26,41,15,10] : List ℕ).contains 41 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 26 2=1 := by decide
    rw [h]
    simp only [part115,Bool.and_false]
private theorem part117 : checkNat 10 47 [47,34,41,15,10] 3 = false := by
  decide
private theorem part118 : checkNat 10 9 [9,34,41,15,10] 3 = false := by
  decide
private theorem part116 : checkNat 10 34 [34,41,15,10] 4 = false := by
  apply combine_step 10 34 [34,41,15,10] 3
  · have h : fast 34 0=41 := by decide
    rw [h]
    have b : ([34,41,15,10] : List ℕ).contains 41 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 34 1=47 := by decide
    rw [h]
    simp only [part117,Bool.and_false]
  · have h : fast 34 2=9 := by decide
    rw [h]
    simp only [part118,Bool.and_false]
private theorem part112 : checkNat 10 41 [41,15,10] 5 = false := by
  apply combine_step 10 41 [41,15,10] 4
  · have h : fast 41 0=26 := by decide
    rw [h]
    simp only [part113,Bool.and_false]
  · have h : fast 41 1=34 := by decide
    rw [h]
    simp only [part116,Bool.and_false]
  · have h : fast 41 2=15 := by decide
    rw [h]
    have b : ([41,15,10] : List ℕ).contains 15 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part104 : checkNat 10 15 [15,10] 6 = false := by
  apply combine_step 10 15 [15,10] 5
  · have h : fast 15 0=20 := by decide
    rw [h]
    simp only [part105,Bool.and_false]
  · have h : fast 15 1=10 := by decide
    rw [h]
    have b : ([15,10] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 15 2=41 := by decide
    rw [h]
    simp only [part112,Bool.and_false]
private theorem part122 : checkNat 10 15 [15,20,0,5,10] 3 = false := by
  decide
private theorem part123 : checkNat 10 45 [45,20,0,5,10] 3 = false := by
  decide
private theorem part121 : checkNat 10 20 [20,0,5,10] 4 = false := by
  apply combine_step 10 20 [20,0,5,10] 3
  · have h : fast 20 0=0 := by decide
    rw [h]
    have b : ([20,0,5,10] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 20 1=15 := by decide
    rw [h]
    simp only [part122,Bool.and_false]
  · have h : fast 20 2=45 := by decide
    rw [h]
    simp only [part123,Bool.and_false]
private theorem part125 : checkNat 10 35 [35,25,0,5,10] 3 = false := by
  decide
private theorem part126 : checkNat 10 40 [40,25,0,5,10] 3 = false := by
  decide
private theorem part124 : checkNat 10 25 [25,0,5,10] 4 = false := by
  apply combine_step 10 25 [25,0,5,10] 3
  · have h : fast 25 0=35 := by decide
    rw [h]
    simp only [part125,Bool.and_false]
  · have h : fast 25 1=40 := by decide
    rw [h]
    simp only [part126,Bool.and_false]
  · have h : fast 25 2=0 := by decide
    rw [h]
    have b : ([25,0,5,10] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part120 : checkNat 10 0 [0,5,10] 5 = false := by
  apply combine_step 10 0 [0,5,10] 4
  · have h : fast 0 0=5 := by decide
    rw [h]
    have b : ([0,5,10] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 0 1=20 := by decide
    rw [h]
    simp only [part121,Bool.and_false]
  · have h : fast 0 2=25 := by decide
    rw [h]
    simp only [part124,Bool.and_false]
private theorem part129 : checkNat 10 27 [27,42,30,5,10] 3 = false := by
  decide
private theorem part130 : checkNat 10 16 [16,42,30,5,10] 3 = false := by
  decide
private theorem part128 : checkNat 10 42 [42,30,5,10] 4 = false := by
  apply combine_step 10 42 [42,30,5,10] 3
  · have h : fast 42 0=27 := by decide
    rw [h]
    simp only [part129,Bool.and_false]
  · have h : fast 42 1=30 := by decide
    rw [h]
    have b : ([42,30,5,10] : List ℕ).contains 30 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 42 2=16 := by decide
    rw [h]
    simp only [part130,Bool.and_false]
private theorem part132 : checkNat 10 39 [39,48,30,5,10] 3 = false := by
  decide
private theorem part133 : checkNat 10 23 [23,48,30,5,10] 3 = false := by
  decide
private theorem part131 : checkNat 10 48 [48,30,5,10] 4 = false := by
  apply combine_step 10 48 [48,30,5,10] 3
  · have h : fast 48 0=30 := by decide
    rw [h]
    have b : ([48,30,5,10] : List ℕ).contains 30 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 48 1=39 := by decide
    rw [h]
    simp only [part132,Bool.and_false]
  · have h : fast 48 2=23 := by decide
    rw [h]
    simp only [part133,Bool.and_false]
private theorem part127 : checkNat 10 30 [30,5,10] 5 = false := by
  apply combine_step 10 30 [30,5,10] 4
  · have h : fast 30 0=42 := by decide
    rw [h]
    simp only [part128,Bool.and_false]
  · have h : fast 30 1=48 := by decide
    rw [h]
    simp only [part131,Bool.and_false]
  · have h : fast 30 2=5 := by decide
    rw [h]
    have b : ([30,5,10] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part119 : checkNat 10 5 [5,10] 6 = false := by
  apply combine_step 10 5 [5,10] 5
  · have h : fast 5 0=10 := by decide
    rw [h]
    have b : ([5,10] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 5 1=0 := by decide
    rw [h]
    simp only [part120,Bool.and_false]
  · have h : fast 5 2=30 := by decide
    rw [h]
    simp only [part127,Bool.and_false]
private theorem part137 : checkNat 10 43 [43,31,49,35,10] 3 = false := by
  decide
private theorem part138 : checkNat 10 6 [6,31,49,35,10] 3 = false := by
  decide
private theorem part136 : checkNat 10 31 [31,49,35,10] 4 = false := by
  apply combine_step 10 31 [31,49,35,10] 3
  · have h : fast 31 0=43 := by decide
    rw [h]
    simp only [part137,Bool.and_false]
  · have h : fast 31 1=49 := by decide
    rw [h]
    have b : ([31,49,35,10] : List ℕ).contains 49 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 31 2=6 := by decide
    rw [h]
    simp only [part138,Bool.and_false]
private theorem part140 : checkNat 10 4 [4,24,49,35,10] 3 = false := by
  decide
private theorem part141 : checkNat 10 19 [19,24,49,35,10] 3 = false := by
  decide
private theorem part139 : checkNat 10 24 [24,49,35,10] 4 = false := by
  apply combine_step 10 24 [24,49,35,10] 3
  · have h : fast 24 0=4 := by decide
    rw [h]
    simp only [part140,Bool.and_false]
  · have h : fast 24 1=19 := by decide
    rw [h]
    simp only [part141,Bool.and_false]
  · have h : fast 24 2=49 := by decide
    rw [h]
    have b : ([24,49,35,10] : List ℕ).contains 49 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part135 : checkNat 10 49 [49,35,10] 5 = false := by
  apply combine_step 10 49 [49,35,10] 4
  · have h : fast 49 0=31 := by decide
    rw [h]
    simp only [part136,Bool.and_false]
  · have h : fast 49 1=35 := by decide
    rw [h]
    have b : ([49,35,10] : List ℕ).contains 35 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 49 2=24 := by decide
    rw [h]
    simp only [part139,Bool.and_false]
private theorem part144 : checkNat 10 33 [33,40,25,35,10] 3 = false := by
  decide
private theorem part145 : checkNat 10 19 [19,40,25,35,10] 3 = false := by
  decide
private theorem part143 : checkNat 10 40 [40,25,35,10] 4 = false := by
  apply combine_step 10 40 [40,25,35,10] 3
  · have h : fast 40 0=25 := by decide
    rw [h]
    have b : ([40,25,35,10] : List ℕ).contains 25 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 40 1=33 := by decide
    rw [h]
    simp only [part144,Bool.and_false]
  · have h : fast 40 2=19 := by decide
    rw [h]
    simp only [part145,Bool.and_false]
private theorem part147 : checkNat 10 5 [5,0,25,35,10] 3 = false := by
  decide
private theorem part148 : checkNat 10 20 [20,0,25,35,10] 3 = false := by
  decide
private theorem part146 : checkNat 10 0 [0,25,35,10] 4 = false := by
  apply combine_step 10 0 [0,25,35,10] 3
  · have h : fast 0 0=5 := by decide
    rw [h]
    simp only [part147,Bool.and_false]
  · have h : fast 0 1=20 := by decide
    rw [h]
    simp only [part148,Bool.and_false]
  · have h : fast 0 2=25 := by decide
    rw [h]
    have b : ([0,25,35,10] : List ℕ).contains 25 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part142 : checkNat 10 25 [25,35,10] 5 = false := by
  apply combine_step 10 25 [25,35,10] 4
  · have h : fast 25 0=35 := by decide
    rw [h]
    have b : ([25,35,10] : List ℕ).contains 35 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 25 1=40 := by decide
    rw [h]
    simp only [part143,Bool.and_false]
  · have h : fast 25 2=0 := by decide
    rw [h]
    simp only [part146,Bool.and_false]
private theorem part134 : checkNat 10 35 [35,10] 6 = false := by
  apply combine_step 10 35 [35,10] 5
  · have h : fast 35 0=49 := by decide
    rw [h]
    simp only [part135,Bool.and_false]
  · have h : fast 35 1=25 := by decide
    rw [h]
    simp only [part142,Bool.and_false]
  · have h : fast 35 2=10 := by decide
    rw [h]
    have b : ([35,10] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part103 : checkNat 10 10 [10] 7 = false := by
  apply combine_step 10 10 [10] 6
  · have h : fast 10 0=15 := by decide
    rw [h]
    simp only [part104,Bool.and_false]
  · have h : fast 10 1=5 := by decide
    rw [h]
    simp only [part119,Bool.and_false]
  · have h : fast 10 2=35 := by decide
    rw [h]
    simp only [part134,Bool.and_false]
private theorem cert8_2 : checkNat 10 10 [10] 7 = false := part103
private theorem part153 : checkNat 15 10 [10,5,0,20,15] 3 = false := by
  decide
private theorem part154 : checkNat 15 30 [30,5,0,20,15] 3 = false := by
  decide
private theorem part152 : checkNat 15 5 [5,0,20,15] 4 = false := by
  apply combine_step 15 5 [5,0,20,15] 3
  · have h : fast 5 0=10 := by decide
    rw [h]
    simp only [part153,Bool.and_false]
  · have h : fast 5 1=0 := by decide
    rw [h]
    have b : ([5,0,20,15] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 5 2=30 := by decide
    rw [h]
    simp only [part154,Bool.and_false]
private theorem part156 : checkNat 15 35 [35,25,0,20,15] 3 = false := by
  decide
private theorem part157 : checkNat 15 40 [40,25,0,20,15] 3 = false := by
  decide
private theorem part155 : checkNat 15 25 [25,0,20,15] 4 = false := by
  apply combine_step 15 25 [25,0,20,15] 3
  · have h : fast 25 0=35 := by decide
    rw [h]
    simp only [part156,Bool.and_false]
  · have h : fast 25 1=40 := by decide
    rw [h]
    simp only [part157,Bool.and_false]
  · have h : fast 25 2=0 := by decide
    rw [h]
    have b : ([25,0,20,15] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part151 : checkNat 15 0 [0,20,15] 5 = false := by
  apply combine_step 15 0 [0,20,15] 4
  · have h : fast 0 0=5 := by decide
    rw [h]
    simp only [part152,Bool.and_false]
  · have h : fast 0 1=20 := by decide
    rw [h]
    have b : ([0,20,15] : List ℕ).contains 20 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 0 2=25 := by decide
    rw [h]
    simp only [part155,Bool.and_false]
private theorem part160 : checkNat 15 44 [44,32,45,20,15] 3 = false := by
  decide
private theorem part161 : checkNat 15 7 [7,32,45,20,15] 3 = false := by
  decide
private theorem part159 : checkNat 15 32 [32,45,20,15] 4 = false := by
  apply combine_step 15 32 [32,45,20,15] 3
  · have h : fast 32 0=44 := by decide
    rw [h]
    simp only [part160,Bool.and_false]
  · have h : fast 32 1=45 := by decide
    rw [h]
    have b : ([32,45,20,15] : List ℕ).contains 45 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 32 2=7 := by decide
    rw [h]
    simp only [part161,Bool.and_false]
private theorem part163 : checkNat 15 26 [26,36,45,20,15] 3 = false := by
  decide
private theorem part164 : checkNat 15 11 [11,36,45,20,15] 3 = false := by
  decide
private theorem part162 : checkNat 15 36 [36,45,20,15] 4 = false := by
  apply combine_step 15 36 [36,45,20,15] 3
  · have h : fast 36 0=45 := by decide
    rw [h]
    have b : ([36,45,20,15] : List ℕ).contains 45 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 36 1=26 := by decide
    rw [h]
    simp only [part163,Bool.and_false]
  · have h : fast 36 2=11 := by decide
    rw [h]
    simp only [part164,Bool.and_false]
private theorem part158 : checkNat 15 45 [45,20,15] 5 = false := by
  apply combine_step 15 45 [45,20,15] 4
  · have h : fast 45 0=32 := by decide
    rw [h]
    simp only [part159,Bool.and_false]
  · have h : fast 45 1=36 := by decide
    rw [h]
    simp only [part162,Bool.and_false]
  · have h : fast 45 2=20 := by decide
    rw [h]
    have b : ([45,20,15] : List ℕ).contains 20 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part150 : checkNat 15 20 [20,15] 6 = false := by
  apply combine_step 15 20 [20,15] 5
  · have h : fast 20 0=0 := by decide
    rw [h]
    simp only [part151,Bool.and_false]
  · have h : fast 20 1=15 := by decide
    rw [h]
    have b : ([20,15] : List ℕ).contains 15 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 20 2=45 := by decide
    rw [h]
    simp only [part158,Bool.and_false]
private theorem part168 : checkNat 15 20 [20,0,5,10,15] 3 = false := by
  decide
private theorem part169 : checkNat 15 25 [25,0,5,10,15] 3 = false := by
  decide
private theorem part167 : checkNat 15 0 [0,5,10,15] 4 = false := by
  apply combine_step 15 0 [0,5,10,15] 3
  · have h : fast 0 0=5 := by decide
    rw [h]
    have b : ([0,5,10,15] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 0 1=20 := by decide
    rw [h]
    simp only [part168,Bool.and_false]
  · have h : fast 0 2=25 := by decide
    rw [h]
    simp only [part169,Bool.and_false]
private theorem part171 : checkNat 15 42 [42,30,5,10,15] 3 = false := by
  decide
private theorem part172 : checkNat 15 48 [48,30,5,10,15] 3 = false := by
  decide
private theorem part170 : checkNat 15 30 [30,5,10,15] 4 = false := by
  apply combine_step 15 30 [30,5,10,15] 3
  · have h : fast 30 0=42 := by decide
    rw [h]
    simp only [part171,Bool.and_false]
  · have h : fast 30 1=48 := by decide
    rw [h]
    simp only [part172,Bool.and_false]
  · have h : fast 30 2=5 := by decide
    rw [h]
    have b : ([30,5,10,15] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part166 : checkNat 15 5 [5,10,15] 5 = false := by
  apply combine_step 15 5 [5,10,15] 4
  · have h : fast 5 0=10 := by decide
    rw [h]
    have b : ([5,10,15] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 5 1=0 := by decide
    rw [h]
    simp only [part167,Bool.and_false]
  · have h : fast 5 2=30 := by decide
    rw [h]
    simp only [part170,Bool.and_false]
private theorem part175 : checkNat 15 31 [31,49,35,10,15] 3 = false := by
  decide
private theorem part176 : checkNat 15 24 [24,49,35,10,15] 3 = false := by
  decide
private theorem part174 : checkNat 15 49 [49,35,10,15] 4 = false := by
  apply combine_step 15 49 [49,35,10,15] 3
  · have h : fast 49 0=31 := by decide
    rw [h]
    simp only [part175,Bool.and_false]
  · have h : fast 49 1=35 := by decide
    rw [h]
    have b : ([49,35,10,15] : List ℕ).contains 35 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 49 2=24 := by decide
    rw [h]
    simp only [part176,Bool.and_false]
private theorem part178 : checkNat 15 40 [40,25,35,10,15] 3 = false := by
  decide
private theorem part179 : checkNat 15 0 [0,25,35,10,15] 3 = false := by
  decide
private theorem part177 : checkNat 15 25 [25,35,10,15] 4 = false := by
  apply combine_step 15 25 [25,35,10,15] 3
  · have h : fast 25 0=35 := by decide
    rw [h]
    have b : ([25,35,10,15] : List ℕ).contains 35 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 25 1=40 := by decide
    rw [h]
    simp only [part178,Bool.and_false]
  · have h : fast 25 2=0 := by decide
    rw [h]
    simp only [part179,Bool.and_false]
private theorem part173 : checkNat 15 35 [35,10,15] 5 = false := by
  apply combine_step 15 35 [35,10,15] 4
  · have h : fast 35 0=49 := by decide
    rw [h]
    simp only [part174,Bool.and_false]
  · have h : fast 35 1=25 := by decide
    rw [h]
    simp only [part177,Bool.and_false]
  · have h : fast 35 2=10 := by decide
    rw [h]
    have b : ([35,10,15] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part165 : checkNat 15 10 [10,15] 6 = false := by
  apply combine_step 15 10 [10,15] 5
  · have h : fast 10 0=15 := by decide
    rw [h]
    have b : ([10,15] : List ℕ).contains 15 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 10 1=5 := by decide
    rw [h]
    simp only [part166,Bool.and_false]
  · have h : fast 10 2=35 := by decide
    rw [h]
    simp only [part173,Bool.and_false]
private theorem part183 : checkNat 15 45 [45,36,26,41,15] 3 = false := by
  decide
private theorem part184 : checkNat 15 11 [11,36,26,41,15] 3 = false := by
  decide
private theorem part182 : checkNat 15 36 [36,26,41,15] 4 = false := by
  apply combine_step 15 36 [36,26,41,15] 3
  · have h : fast 36 0=45 := by decide
    rw [h]
    simp only [part183,Bool.and_false]
  · have h : fast 36 1=26 := by decide
    rw [h]
    have b : ([36,26,41,15] : List ℕ).contains 26 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 36 2=11 := by decide
    rw [h]
    simp only [part184,Bool.and_false]
private theorem part186 : checkNat 15 6 [6,1,26,41,15] 3 = false := by
  decide
private theorem part187 : checkNat 15 21 [21,1,26,41,15] 3 = false := by
  decide
private theorem part185 : checkNat 15 1 [1,26,41,15] 4 = false := by
  apply combine_step 15 1 [1,26,41,15] 3
  · have h : fast 1 0=6 := by decide
    rw [h]
    simp only [part186,Bool.and_false]
  · have h : fast 1 1=21 := by decide
    rw [h]
    simp only [part187,Bool.and_false]
  · have h : fast 1 2=26 := by decide
    rw [h]
    have b : ([1,26,41,15] : List ℕ).contains 26 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part181 : checkNat 15 26 [26,41,15] 5 = false := by
  apply combine_step 15 26 [26,41,15] 4
  · have h : fast 26 0=36 := by decide
    rw [h]
    simp only [part182,Bool.and_false]
  · have h : fast 26 1=41 := by decide
    rw [h]
    have b : ([26,41,15] : List ℕ).contains 41 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 26 2=1 := by decide
    rw [h]
    simp only [part185,Bool.and_false]
private theorem part190 : checkNat 15 38 [38,47,34,41,15] 3 = false := by
  decide
private theorem part191 : checkNat 15 22 [22,47,34,41,15] 3 = false := by
  decide
private theorem part189 : checkNat 15 47 [47,34,41,15] 4 = false := by
  apply combine_step 15 47 [47,34,41,15] 3
  · have h : fast 47 0=34 := by decide
    rw [h]
    have b : ([47,34,41,15] : List ℕ).contains 34 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 47 1=38 := by decide
    rw [h]
    simp only [part190,Bool.and_false]
  · have h : fast 47 2=22 := by decide
    rw [h]
    simp only [part191,Bool.and_false]
private theorem part193 : checkNat 15 14 [14,9,34,41,15] 3 = false := by
  decide
private theorem part194 : checkNat 15 4 [4,9,34,41,15] 3 = false := by
  decide
private theorem part192 : checkNat 15 9 [9,34,41,15] 4 = false := by
  apply combine_step 15 9 [9,34,41,15] 3
  · have h : fast 9 0=14 := by decide
    rw [h]
    simp only [part193,Bool.and_false]
  · have h : fast 9 1=4 := by decide
    rw [h]
    simp only [part194,Bool.and_false]
  · have h : fast 9 2=34 := by decide
    rw [h]
    have b : ([9,34,41,15] : List ℕ).contains 34 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part188 : checkNat 15 34 [34,41,15] 5 = false := by
  apply combine_step 15 34 [34,41,15] 4
  · have h : fast 34 0=41 := by decide
    rw [h]
    have b : ([34,41,15] : List ℕ).contains 41 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 34 1=47 := by decide
    rw [h]
    simp only [part189,Bool.and_false]
  · have h : fast 34 2=9 := by decide
    rw [h]
    simp only [part192,Bool.and_false]
private theorem part180 : checkNat 15 41 [41,15] 6 = false := by
  apply combine_step 15 41 [41,15] 5
  · have h : fast 41 0=26 := by decide
    rw [h]
    simp only [part181,Bool.and_false]
  · have h : fast 41 1=34 := by decide
    rw [h]
    simp only [part188,Bool.and_false]
  · have h : fast 41 2=15 := by decide
    rw [h]
    have b : ([41,15] : List ℕ).contains 15 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part149 : checkNat 15 15 [15] 7 = false := by
  apply combine_step 15 15 [15] 6
  · have h : fast 15 0=20 := by decide
    rw [h]
    simp only [part150,Bool.and_false]
  · have h : fast 15 1=10 := by decide
    rw [h]
    simp only [part165,Bool.and_false]
  · have h : fast 15 2=41 := by decide
    rw [h]
    simp only [part180,Bool.and_false]
private theorem cert8_3 : checkNat 15 15 [15] 7 = false := part149
private theorem part199 : checkNat 20 15 [15,10,5,0,20] 3 = false := by
  decide
private theorem part200 : checkNat 20 35 [35,10,5,0,20] 3 = false := by
  decide
private theorem part198 : checkNat 20 10 [10,5,0,20] 4 = false := by
  apply combine_step 20 10 [10,5,0,20] 3
  · have h : fast 10 0=15 := by decide
    rw [h]
    simp only [part199,Bool.and_false]
  · have h : fast 10 1=5 := by decide
    rw [h]
    have b : ([10,5,0,20] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 10 2=35 := by decide
    rw [h]
    simp only [part200,Bool.and_false]
private theorem part202 : checkNat 20 42 [42,30,5,0,20] 3 = false := by
  decide
private theorem part203 : checkNat 20 48 [48,30,5,0,20] 3 = false := by
  decide
private theorem part201 : checkNat 20 30 [30,5,0,20] 4 = false := by
  apply combine_step 20 30 [30,5,0,20] 3
  · have h : fast 30 0=42 := by decide
    rw [h]
    simp only [part202,Bool.and_false]
  · have h : fast 30 1=48 := by decide
    rw [h]
    simp only [part203,Bool.and_false]
  · have h : fast 30 2=5 := by decide
    rw [h]
    have b : ([30,5,0,20] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part197 : checkNat 20 5 [5,0,20] 5 = false := by
  apply combine_step 20 5 [5,0,20] 4
  · have h : fast 5 0=10 := by decide
    rw [h]
    simp only [part198,Bool.and_false]
  · have h : fast 5 1=0 := by decide
    rw [h]
    have b : ([5,0,20] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 5 2=30 := by decide
    rw [h]
    simp only [part201,Bool.and_false]
private theorem part206 : checkNat 20 49 [49,35,25,0,20] 3 = false := by
  decide
private theorem part207 : checkNat 20 10 [10,35,25,0,20] 3 = false := by
  decide
private theorem part205 : checkNat 20 35 [35,25,0,20] 4 = false := by
  apply combine_step 20 35 [35,25,0,20] 3
  · have h : fast 35 0=49 := by decide
    rw [h]
    simp only [part206,Bool.and_false]
  · have h : fast 35 1=25 := by decide
    rw [h]
    have b : ([35,25,0,20] : List ℕ).contains 25 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 35 2=10 := by decide
    rw [h]
    simp only [part207,Bool.and_false]
private theorem part209 : checkNat 20 33 [33,40,25,0,20] 3 = false := by
  decide
private theorem part210 : checkNat 20 19 [19,40,25,0,20] 3 = false := by
  decide
private theorem part208 : checkNat 20 40 [40,25,0,20] 4 = false := by
  apply combine_step 20 40 [40,25,0,20] 3
  · have h : fast 40 0=25 := by decide
    rw [h]
    have b : ([40,25,0,20] : List ℕ).contains 25 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 40 1=33 := by decide
    rw [h]
    simp only [part209,Bool.and_false]
  · have h : fast 40 2=19 := by decide
    rw [h]
    simp only [part210,Bool.and_false]
private theorem part204 : checkNat 20 25 [25,0,20] 5 = false := by
  apply combine_step 20 25 [25,0,20] 4
  · have h : fast 25 0=35 := by decide
    rw [h]
    simp only [part205,Bool.and_false]
  · have h : fast 25 1=40 := by decide
    rw [h]
    simp only [part208,Bool.and_false]
  · have h : fast 25 2=0 := by decide
    rw [h]
    have b : ([25,0,20] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part196 : checkNat 20 0 [0,20] 6 = false := by
  apply combine_step 20 0 [0,20] 5
  · have h : fast 0 0=5 := by decide
    rw [h]
    simp only [part197,Bool.and_false]
  · have h : fast 0 1=20 := by decide
    rw [h]
    have b : ([0,20] : List ℕ).contains 20 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 0 2=25 := by decide
    rw [h]
    simp only [part204,Bool.and_false]
private theorem part214 : checkNat 20 0 [0,5,10,15,20] 3 = false := by
  decide
private theorem part215 : checkNat 20 30 [30,5,10,15,20] 3 = false := by
  decide
private theorem part213 : checkNat 20 5 [5,10,15,20] 4 = false := by
  apply combine_step 20 5 [5,10,15,20] 3
  · have h : fast 5 0=10 := by decide
    rw [h]
    have b : ([5,10,15,20] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 5 1=0 := by decide
    rw [h]
    simp only [part214,Bool.and_false]
  · have h : fast 5 2=30 := by decide
    rw [h]
    simp only [part215,Bool.and_false]
private theorem part217 : checkNat 20 49 [49,35,10,15,20] 3 = false := by
  decide
private theorem part218 : checkNat 20 25 [25,35,10,15,20] 3 = false := by
  decide
private theorem part216 : checkNat 20 35 [35,10,15,20] 4 = false := by
  apply combine_step 20 35 [35,10,15,20] 3
  · have h : fast 35 0=49 := by decide
    rw [h]
    simp only [part217,Bool.and_false]
  · have h : fast 35 1=25 := by decide
    rw [h]
    simp only [part218,Bool.and_false]
  · have h : fast 35 2=10 := by decide
    rw [h]
    have b : ([35,10,15,20] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part212 : checkNat 20 10 [10,15,20] 5 = false := by
  apply combine_step 20 10 [10,15,20] 4
  · have h : fast 10 0=15 := by decide
    rw [h]
    have b : ([10,15,20] : List ℕ).contains 15 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 10 1=5 := by decide
    rw [h]
    simp only [part213,Bool.and_false]
  · have h : fast 10 2=35 := by decide
    rw [h]
    simp only [part216,Bool.and_false]
private theorem part221 : checkNat 20 36 [36,26,41,15,20] 3 = false := by
  decide
private theorem part222 : checkNat 20 1 [1,26,41,15,20] 3 = false := by
  decide
private theorem part220 : checkNat 20 26 [26,41,15,20] 4 = false := by
  apply combine_step 20 26 [26,41,15,20] 3
  · have h : fast 26 0=36 := by decide
    rw [h]
    simp only [part221,Bool.and_false]
  · have h : fast 26 1=41 := by decide
    rw [h]
    have b : ([26,41,15,20] : List ℕ).contains 41 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 26 2=1 := by decide
    rw [h]
    simp only [part222,Bool.and_false]
private theorem part224 : checkNat 20 47 [47,34,41,15,20] 3 = false := by
  decide
private theorem part225 : checkNat 20 9 [9,34,41,15,20] 3 = false := by
  decide
private theorem part223 : checkNat 20 34 [34,41,15,20] 4 = false := by
  apply combine_step 20 34 [34,41,15,20] 3
  · have h : fast 34 0=41 := by decide
    rw [h]
    have b : ([34,41,15,20] : List ℕ).contains 41 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 34 1=47 := by decide
    rw [h]
    simp only [part224,Bool.and_false]
  · have h : fast 34 2=9 := by decide
    rw [h]
    simp only [part225,Bool.and_false]
private theorem part219 : checkNat 20 41 [41,15,20] 5 = false := by
  apply combine_step 20 41 [41,15,20] 4
  · have h : fast 41 0=26 := by decide
    rw [h]
    simp only [part220,Bool.and_false]
  · have h : fast 41 1=34 := by decide
    rw [h]
    simp only [part223,Bool.and_false]
  · have h : fast 41 2=15 := by decide
    rw [h]
    have b : ([41,15,20] : List ℕ).contains 15 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part211 : checkNat 20 15 [15,20] 6 = false := by
  apply combine_step 20 15 [15,20] 5
  · have h : fast 15 0=20 := by decide
    rw [h]
    have b : ([15,20] : List ℕ).contains 20 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 15 1=10 := by decide
    rw [h]
    simp only [part212,Bool.and_false]
  · have h : fast 15 2=41 := by decide
    rw [h]
    simp only [part219,Bool.and_false]
private theorem part229 : checkNat 20 29 [29,44,32,45,20] 3 = false := by
  decide
private theorem part230 : checkNat 20 18 [18,44,32,45,20] 3 = false := by
  decide
private theorem part228 : checkNat 20 44 [44,32,45,20] 4 = false := by
  apply combine_step 20 44 [44,32,45,20] 3
  · have h : fast 44 0=29 := by decide
    rw [h]
    simp only [part229,Bool.and_false]
  · have h : fast 44 1=32 := by decide
    rw [h]
    have b : ([44,32,45,20] : List ℕ).contains 32 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 44 2=18 := by decide
    rw [h]
    simp only [part230,Bool.and_false]
private theorem part232 : checkNat 20 12 [12,7,32,45,20] 3 = false := by
  decide
private theorem part233 : checkNat 20 2 [2,7,32,45,20] 3 = false := by
  decide
private theorem part231 : checkNat 20 7 [7,32,45,20] 4 = false := by
  apply combine_step 20 7 [7,32,45,20] 3
  · have h : fast 7 0=12 := by decide
    rw [h]
    simp only [part232,Bool.and_false]
  · have h : fast 7 1=2 := by decide
    rw [h]
    simp only [part233,Bool.and_false]
  · have h : fast 7 2=32 := by decide
    rw [h]
    have b : ([7,32,45,20] : List ℕ).contains 32 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part227 : checkNat 20 32 [32,45,20] 5 = false := by
  apply combine_step 20 32 [32,45,20] 4
  · have h : fast 32 0=44 := by decide
    rw [h]
    simp only [part228,Bool.and_false]
  · have h : fast 32 1=45 := by decide
    rw [h]
    have b : ([32,45,20] : List ℕ).contains 45 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 32 2=7 := by decide
    rw [h]
    simp only [part231,Bool.and_false]
private theorem part236 : checkNat 20 41 [41,26,36,45,20] 3 = false := by
  decide
private theorem part237 : checkNat 20 1 [1,26,36,45,20] 3 = false := by
  decide
private theorem part235 : checkNat 20 26 [26,36,45,20] 4 = false := by
  apply combine_step 20 26 [26,36,45,20] 3
  · have h : fast 26 0=36 := by decide
    rw [h]
    have b : ([26,36,45,20] : List ℕ).contains 36 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 26 1=41 := by decide
    rw [h]
    simp only [part236,Bool.and_false]
  · have h : fast 26 2=1 := by decide
    rw [h]
    simp only [part237,Bool.and_false]
private theorem part239 : checkNat 20 16 [16,11,36,45,20] 3 = false := by
  decide
private theorem part240 : checkNat 20 6 [6,11,36,45,20] 3 = false := by
  decide
private theorem part238 : checkNat 20 11 [11,36,45,20] 4 = false := by
  apply combine_step 20 11 [11,36,45,20] 3
  · have h : fast 11 0=16 := by decide
    rw [h]
    simp only [part239,Bool.and_false]
  · have h : fast 11 1=6 := by decide
    rw [h]
    simp only [part240,Bool.and_false]
  · have h : fast 11 2=36 := by decide
    rw [h]
    have b : ([11,36,45,20] : List ℕ).contains 36 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part234 : checkNat 20 36 [36,45,20] 5 = false := by
  apply combine_step 20 36 [36,45,20] 4
  · have h : fast 36 0=45 := by decide
    rw [h]
    have b : ([36,45,20] : List ℕ).contains 45 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 36 1=26 := by decide
    rw [h]
    simp only [part235,Bool.and_false]
  · have h : fast 36 2=11 := by decide
    rw [h]
    simp only [part238,Bool.and_false]
private theorem part226 : checkNat 20 45 [45,20] 6 = false := by
  apply combine_step 20 45 [45,20] 5
  · have h : fast 45 0=32 := by decide
    rw [h]
    simp only [part227,Bool.and_false]
  · have h : fast 45 1=36 := by decide
    rw [h]
    simp only [part234,Bool.and_false]
  · have h : fast 45 2=20 := by decide
    rw [h]
    have b : ([45,20] : List ℕ).contains 20 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part195 : checkNat 20 20 [20] 7 = false := by
  apply combine_step 20 20 [20] 6
  · have h : fast 20 0=0 := by decide
    rw [h]
    simp only [part196,Bool.and_false]
  · have h : fast 20 1=15 := by decide
    rw [h]
    simp only [part211,Bool.and_false]
  · have h : fast 20 2=45 := by decide
    rw [h]
    simp only [part226,Bool.and_false]
private theorem cert8_4 : checkNat 20 20 [20] 7 = false := part195
private theorem part245 : checkNat 25 43 [43,31,49,35,25] 3 = false := by
  decide
private theorem part246 : checkNat 25 6 [6,31,49,35,25] 3 = false := by
  decide
private theorem part244 : checkNat 25 31 [31,49,35,25] 4 = false := by
  apply combine_step 25 31 [31,49,35,25] 3
  · have h : fast 31 0=43 := by decide
    rw [h]
    simp only [part245,Bool.and_false]
  · have h : fast 31 1=49 := by decide
    rw [h]
    have b : ([31,49,35,25] : List ℕ).contains 49 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 31 2=6 := by decide
    rw [h]
    simp only [part246,Bool.and_false]
private theorem part248 : checkNat 25 4 [4,24,49,35,25] 3 = false := by
  decide
private theorem part249 : checkNat 25 19 [19,24,49,35,25] 3 = false := by
  decide
private theorem part247 : checkNat 25 24 [24,49,35,25] 4 = false := by
  apply combine_step 25 24 [24,49,35,25] 3
  · have h : fast 24 0=4 := by decide
    rw [h]
    simp only [part248,Bool.and_false]
  · have h : fast 24 1=19 := by decide
    rw [h]
    simp only [part249,Bool.and_false]
  · have h : fast 24 2=49 := by decide
    rw [h]
    have b : ([24,49,35,25] : List ℕ).contains 49 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part243 : checkNat 25 49 [49,35,25] 5 = false := by
  apply combine_step 25 49 [49,35,25] 4
  · have h : fast 49 0=31 := by decide
    rw [h]
    simp only [part244,Bool.and_false]
  · have h : fast 49 1=35 := by decide
    rw [h]
    have b : ([49,35,25] : List ℕ).contains 35 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 49 2=24 := by decide
    rw [h]
    simp only [part247,Bool.and_false]
private theorem part252 : checkNat 25 20 [20,15,10,35,25] 3 = false := by
  decide
private theorem part253 : checkNat 25 41 [41,15,10,35,25] 3 = false := by
  decide
private theorem part251 : checkNat 25 15 [15,10,35,25] 4 = false := by
  apply combine_step 25 15 [15,10,35,25] 3
  · have h : fast 15 0=20 := by decide
    rw [h]
    simp only [part252,Bool.and_false]
  · have h : fast 15 1=10 := by decide
    rw [h]
    have b : ([15,10,35,25] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 15 2=41 := by decide
    rw [h]
    simp only [part253,Bool.and_false]
private theorem part255 : checkNat 25 0 [0,5,10,35,25] 3 = false := by
  decide
private theorem part256 : checkNat 25 30 [30,5,10,35,25] 3 = false := by
  decide
private theorem part254 : checkNat 25 5 [5,10,35,25] 4 = false := by
  apply combine_step 25 5 [5,10,35,25] 3
  · have h : fast 5 0=10 := by decide
    rw [h]
    have b : ([5,10,35,25] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 5 1=0 := by decide
    rw [h]
    simp only [part255,Bool.and_false]
  · have h : fast 5 2=30 := by decide
    rw [h]
    simp only [part256,Bool.and_false]
private theorem part250 : checkNat 25 10 [10,35,25] 5 = false := by
  apply combine_step 25 10 [10,35,25] 4
  · have h : fast 10 0=15 := by decide
    rw [h]
    simp only [part251,Bool.and_false]
  · have h : fast 10 1=5 := by decide
    rw [h]
    simp only [part254,Bool.and_false]
  · have h : fast 10 2=35 := by decide
    rw [h]
    have b : ([10,35,25] : List ℕ).contains 35 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part242 : checkNat 25 35 [35,25] 6 = false := by
  apply combine_step 25 35 [35,25] 5
  · have h : fast 35 0=49 := by decide
    rw [h]
    simp only [part243,Bool.and_false]
  · have h : fast 35 1=25 := by decide
    rw [h]
    have b : ([35,25] : List ℕ).contains 25 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 35 2=10 := by decide
    rw [h]
    simp only [part250,Bool.and_false]
private theorem part260 : checkNat 25 37 [37,46,33,40,25] 3 = false := by
  decide
private theorem part261 : checkNat 25 21 [21,46,33,40,25] 3 = false := by
  decide
private theorem part259 : checkNat 25 46 [46,33,40,25] 4 = false := by
  apply combine_step 25 46 [46,33,40,25] 3
  · have h : fast 46 0=33 := by decide
    rw [h]
    have b : ([46,33,40,25] : List ℕ).contains 33 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 46 1=37 := by decide
    rw [h]
    simp only [part260,Bool.and_false]
  · have h : fast 46 2=21 := by decide
    rw [h]
    simp only [part261,Bool.and_false]
private theorem part263 : checkNat 25 13 [13,8,33,40,25] 3 = false := by
  decide
private theorem part264 : checkNat 25 3 [3,8,33,40,25] 3 = false := by
  decide
private theorem part262 : checkNat 25 8 [8,33,40,25] 4 = false := by
  apply combine_step 25 8 [8,33,40,25] 3
  · have h : fast 8 0=13 := by decide
    rw [h]
    simp only [part263,Bool.and_false]
  · have h : fast 8 1=3 := by decide
    rw [h]
    simp only [part264,Bool.and_false]
  · have h : fast 8 2=33 := by decide
    rw [h]
    have b : ([8,33,40,25] : List ℕ).contains 33 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part258 : checkNat 25 33 [33,40,25] 5 = false := by
  apply combine_step 25 33 [33,40,25] 4
  · have h : fast 33 0=40 := by decide
    rw [h]
    have b : ([33,40,25] : List ℕ).contains 40 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 33 1=46 := by decide
    rw [h]
    simp only [part259,Bool.and_false]
  · have h : fast 33 2=8 := by decide
    rw [h]
    simp only [part262,Bool.and_false]
private theorem part267 : checkNat 25 4 [4,24,19,40,25] 3 = false := by
  decide
private theorem part268 : checkNat 25 49 [49,24,19,40,25] 3 = false := by
  decide
private theorem part266 : checkNat 25 24 [24,19,40,25] 4 = false := by
  apply combine_step 25 24 [24,19,40,25] 3
  · have h : fast 24 0=4 := by decide
    rw [h]
    simp only [part267,Bool.and_false]
  · have h : fast 24 1=19 := by decide
    rw [h]
    have b : ([24,19,40,25] : List ℕ).contains 19 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 24 2=49 := by decide
    rw [h]
    simp only [part268,Bool.and_false]
private theorem part270 : checkNat 25 9 [9,14,19,40,25] 3 = false := by
  decide
private theorem part271 : checkNat 25 39 [39,14,19,40,25] 3 = false := by
  decide
private theorem part269 : checkNat 25 14 [14,19,40,25] 4 = false := by
  apply combine_step 25 14 [14,19,40,25] 3
  · have h : fast 14 0=19 := by decide
    rw [h]
    have b : ([14,19,40,25] : List ℕ).contains 19 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 14 1=9 := by decide
    rw [h]
    simp only [part270,Bool.and_false]
  · have h : fast 14 2=39 := by decide
    rw [h]
    simp only [part271,Bool.and_false]
private theorem part265 : checkNat 25 19 [19,40,25] 5 = false := by
  apply combine_step 25 19 [19,40,25] 4
  · have h : fast 19 0=24 := by decide
    rw [h]
    simp only [part266,Bool.and_false]
  · have h : fast 19 1=14 := by decide
    rw [h]
    simp only [part269,Bool.and_false]
  · have h : fast 19 2=40 := by decide
    rw [h]
    have b : ([19,40,25] : List ℕ).contains 40 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part257 : checkNat 25 40 [40,25] 6 = false := by
  apply combine_step 25 40 [40,25] 5
  · have h : fast 40 0=25 := by decide
    rw [h]
    have b : ([40,25] : List ℕ).contains 25 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 40 1=33 := by decide
    rw [h]
    simp only [part258,Bool.and_false]
  · have h : fast 40 2=19 := by decide
    rw [h]
    simp only [part265,Bool.and_false]
private theorem part275 : checkNat 25 15 [15,10,5,0,25] 3 = false := by
  decide
private theorem part276 : checkNat 25 35 [35,10,5,0,25] 3 = false := by
  decide
private theorem part274 : checkNat 25 10 [10,5,0,25] 4 = false := by
  apply combine_step 25 10 [10,5,0,25] 3
  · have h : fast 10 0=15 := by decide
    rw [h]
    simp only [part275,Bool.and_false]
  · have h : fast 10 1=5 := by decide
    rw [h]
    have b : ([10,5,0,25] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 10 2=35 := by decide
    rw [h]
    simp only [part276,Bool.and_false]
private theorem part278 : checkNat 25 42 [42,30,5,0,25] 3 = false := by
  decide
private theorem part279 : checkNat 25 48 [48,30,5,0,25] 3 = false := by
  decide
private theorem part277 : checkNat 25 30 [30,5,0,25] 4 = false := by
  apply combine_step 25 30 [30,5,0,25] 3
  · have h : fast 30 0=42 := by decide
    rw [h]
    simp only [part278,Bool.and_false]
  · have h : fast 30 1=48 := by decide
    rw [h]
    simp only [part279,Bool.and_false]
  · have h : fast 30 2=5 := by decide
    rw [h]
    have b : ([30,5,0,25] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part273 : checkNat 25 5 [5,0,25] 5 = false := by
  apply combine_step 25 5 [5,0,25] 4
  · have h : fast 5 0=10 := by decide
    rw [h]
    simp only [part274,Bool.and_false]
  · have h : fast 5 1=0 := by decide
    rw [h]
    have b : ([5,0,25] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 5 2=30 := by decide
    rw [h]
    simp only [part277,Bool.and_false]
private theorem part282 : checkNat 25 10 [10,15,20,0,25] 3 = false := by
  decide
private theorem part283 : checkNat 25 41 [41,15,20,0,25] 3 = false := by
  decide
private theorem part281 : checkNat 25 15 [15,20,0,25] 4 = false := by
  apply combine_step 25 15 [15,20,0,25] 3
  · have h : fast 15 0=20 := by decide
    rw [h]
    have b : ([15,20,0,25] : List ℕ).contains 20 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 15 1=10 := by decide
    rw [h]
    simp only [part282,Bool.and_false]
  · have h : fast 15 2=41 := by decide
    rw [h]
    simp only [part283,Bool.and_false]
private theorem part285 : checkNat 25 32 [32,45,20,0,25] 3 = false := by
  decide
private theorem part286 : checkNat 25 36 [36,45,20,0,25] 3 = false := by
  decide
private theorem part284 : checkNat 25 45 [45,20,0,25] 4 = false := by
  apply combine_step 25 45 [45,20,0,25] 3
  · have h : fast 45 0=32 := by decide
    rw [h]
    simp only [part285,Bool.and_false]
  · have h : fast 45 1=36 := by decide
    rw [h]
    simp only [part286,Bool.and_false]
  · have h : fast 45 2=20 := by decide
    rw [h]
    have b : ([45,20,0,25] : List ℕ).contains 20 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part280 : checkNat 25 20 [20,0,25] 5 = false := by
  apply combine_step 25 20 [20,0,25] 4
  · have h : fast 20 0=0 := by decide
    rw [h]
    have b : ([20,0,25] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 20 1=15 := by decide
    rw [h]
    simp only [part281,Bool.and_false]
  · have h : fast 20 2=45 := by decide
    rw [h]
    simp only [part284,Bool.and_false]
private theorem part272 : checkNat 25 0 [0,25] 6 = false := by
  apply combine_step 25 0 [0,25] 5
  · have h : fast 0 0=5 := by decide
    rw [h]
    simp only [part273,Bool.and_false]
  · have h : fast 0 1=20 := by decide
    rw [h]
    simp only [part280,Bool.and_false]
  · have h : fast 0 2=25 := by decide
    rw [h]
    have b : ([0,25] : List ℕ).contains 25 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part241 : checkNat 25 25 [25] 7 = false := by
  apply combine_step 25 25 [25] 6
  · have h : fast 25 0=35 := by decide
    rw [h]
    simp only [part242,Bool.and_false]
  · have h : fast 25 1=40 := by decide
    rw [h]
    simp only [part257,Bool.and_false]
  · have h : fast 25 2=0 := by decide
    rw [h]
    simp only [part272,Bool.and_false]
private theorem cert8_5 : checkNat 25 25 [25] 7 = false := part241
private theorem part291 : checkNat 30 46 [46,37,27,42,30] 3 = false := by
  decide
private theorem part292 : checkNat 30 12 [12,37,27,42,30] 3 = false := by
  decide
private theorem part290 : checkNat 30 37 [37,27,42,30] 4 = false := by
  apply combine_step 30 37 [37,27,42,30] 3
  · have h : fast 37 0=46 := by decide
    rw [h]
    simp only [part291,Bool.and_false]
  · have h : fast 37 1=27 := by decide
    rw [h]
    have b : ([37,27,42,30] : List ℕ).contains 27 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 37 2=12 := by decide
    rw [h]
    simp only [part292,Bool.and_false]
private theorem part294 : checkNat 30 7 [7,2,27,42,30] 3 = false := by
  decide
private theorem part295 : checkNat 30 22 [22,2,27,42,30] 3 = false := by
  decide
private theorem part293 : checkNat 30 2 [2,27,42,30] 4 = false := by
  apply combine_step 30 2 [2,27,42,30] 3
  · have h : fast 2 0=7 := by decide
    rw [h]
    simp only [part294,Bool.and_false]
  · have h : fast 2 1=22 := by decide
    rw [h]
    simp only [part295,Bool.and_false]
  · have h : fast 2 2=27 := by decide
    rw [h]
    have b : ([2,27,42,30] : List ℕ).contains 27 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part289 : checkNat 30 27 [27,42,30] 5 = false := by
  apply combine_step 30 27 [27,42,30] 4
  · have h : fast 27 0=37 := by decide
    rw [h]
    simp only [part290,Bool.and_false]
  · have h : fast 27 1=42 := by decide
    rw [h]
    have b : ([27,42,30] : List ℕ).contains 42 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 27 2=2 := by decide
    rw [h]
    simp only [part293,Bool.and_false]
private theorem part298 : checkNat 30 1 [1,21,16,42,30] 3 = false := by
  decide
private theorem part299 : checkNat 30 46 [46,21,16,42,30] 3 = false := by
  decide
private theorem part297 : checkNat 30 21 [21,16,42,30] 4 = false := by
  apply combine_step 30 21 [21,16,42,30] 3
  · have h : fast 21 0=1 := by decide
    rw [h]
    simp only [part298,Bool.and_false]
  · have h : fast 21 1=16 := by decide
    rw [h]
    have b : ([21,16,42,30] : List ℕ).contains 16 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 21 2=46 := by decide
    rw [h]
    simp only [part299,Bool.and_false]
private theorem part301 : checkNat 30 6 [6,11,16,42,30] 3 = false := by
  decide
private theorem part302 : checkNat 30 36 [36,11,16,42,30] 3 = false := by
  decide
private theorem part300 : checkNat 30 11 [11,16,42,30] 4 = false := by
  apply combine_step 30 11 [11,16,42,30] 3
  · have h : fast 11 0=16 := by decide
    rw [h]
    have b : ([11,16,42,30] : List ℕ).contains 16 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 11 1=6 := by decide
    rw [h]
    simp only [part301,Bool.and_false]
  · have h : fast 11 2=36 := by decide
    rw [h]
    simp only [part302,Bool.and_false]
private theorem part296 : checkNat 30 16 [16,42,30] 5 = false := by
  apply combine_step 30 16 [16,42,30] 4
  · have h : fast 16 0=21 := by decide
    rw [h]
    simp only [part297,Bool.and_false]
  · have h : fast 16 1=11 := by decide
    rw [h]
    simp only [part300,Bool.and_false]
  · have h : fast 16 2=42 := by decide
    rw [h]
    have b : ([16,42,30] : List ℕ).contains 42 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part288 : checkNat 30 42 [42,30] 6 = false := by
  apply combine_step 30 42 [42,30] 5
  · have h : fast 42 0=27 := by decide
    rw [h]
    simp only [part289,Bool.and_false]
  · have h : fast 42 1=30 := by decide
    rw [h]
    have b : ([42,30] : List ℕ).contains 30 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 42 2=16 := by decide
    rw [h]
    simp only [part296,Bool.and_false]
private theorem part306 : checkNat 30 44 [44,29,39,48,30] 3 = false := by
  decide
private theorem part307 : checkNat 30 4 [4,29,39,48,30] 3 = false := by
  decide
private theorem part305 : checkNat 30 29 [29,39,48,30] 4 = false := by
  apply combine_step 30 29 [29,39,48,30] 3
  · have h : fast 29 0=39 := by decide
    rw [h]
    have b : ([29,39,48,30] : List ℕ).contains 39 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 29 1=44 := by decide
    rw [h]
    simp only [part306,Bool.and_false]
  · have h : fast 29 2=4 := by decide
    rw [h]
    simp only [part307,Bool.and_false]
private theorem part309 : checkNat 30 19 [19,14,39,48,30] 3 = false := by
  decide
private theorem part310 : checkNat 30 9 [9,14,39,48,30] 3 = false := by
  decide
private theorem part308 : checkNat 30 14 [14,39,48,30] 4 = false := by
  apply combine_step 30 14 [14,39,48,30] 3
  · have h : fast 14 0=19 := by decide
    rw [h]
    simp only [part309,Bool.and_false]
  · have h : fast 14 1=9 := by decide
    rw [h]
    simp only [part310,Bool.and_false]
  · have h : fast 14 2=39 := by decide
    rw [h]
    have b : ([14,39,48,30] : List ℕ).contains 39 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part304 : checkNat 30 39 [39,48,30] 5 = false := by
  apply combine_step 30 39 [39,48,30] 4
  · have h : fast 39 0=48 := by decide
    rw [h]
    have b : ([39,48,30] : List ℕ).contains 48 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 39 1=29 := by decide
    rw [h]
    simp only [part305,Bool.and_false]
  · have h : fast 39 2=14 := by decide
    rw [h]
    simp only [part308,Bool.and_false]
private theorem part313 : checkNat 30 8 [8,3,23,48,30] 3 = false := by
  decide
private theorem part314 : checkNat 30 28 [28,3,23,48,30] 3 = false := by
  decide
private theorem part312 : checkNat 30 3 [3,23,48,30] 4 = false := by
  apply combine_step 30 3 [3,23,48,30] 3
  · have h : fast 3 0=8 := by decide
    rw [h]
    simp only [part313,Bool.and_false]
  · have h : fast 3 1=23 := by decide
    rw [h]
    have b : ([3,23,48,30] : List ℕ).contains 23 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 3 2=28 := by decide
    rw [h]
    simp only [part314,Bool.and_false]
private theorem part316 : checkNat 30 13 [13,18,23,48,30] 3 = false := by
  decide
private theorem part317 : checkNat 30 44 [44,18,23,48,30] 3 = false := by
  decide
private theorem part315 : checkNat 30 18 [18,23,48,30] 4 = false := by
  apply combine_step 30 18 [18,23,48,30] 3
  · have h : fast 18 0=23 := by decide
    rw [h]
    have b : ([18,23,48,30] : List ℕ).contains 23 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 18 1=13 := by decide
    rw [h]
    simp only [part316,Bool.and_false]
  · have h : fast 18 2=44 := by decide
    rw [h]
    simp only [part317,Bool.and_false]
private theorem part311 : checkNat 30 23 [23,48,30] 5 = false := by
  apply combine_step 30 23 [23,48,30] 4
  · have h : fast 23 0=3 := by decide
    rw [h]
    simp only [part312,Bool.and_false]
  · have h : fast 23 1=18 := by decide
    rw [h]
    simp only [part315,Bool.and_false]
  · have h : fast 23 2=48 := by decide
    rw [h]
    have b : ([23,48,30] : List ℕ).contains 48 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part303 : checkNat 30 48 [48,30] 6 = false := by
  apply combine_step 30 48 [48,30] 5
  · have h : fast 48 0=30 := by decide
    rw [h]
    have b : ([48,30] : List ℕ).contains 30 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 48 1=39 := by decide
    rw [h]
    simp only [part304,Bool.and_false]
  · have h : fast 48 2=23 := by decide
    rw [h]
    simp only [part311,Bool.and_false]
private theorem part321 : checkNat 30 20 [20,15,10,5,30] 3 = false := by
  decide
private theorem part322 : checkNat 30 41 [41,15,10,5,30] 3 = false := by
  decide
private theorem part320 : checkNat 30 15 [15,10,5,30] 4 = false := by
  apply combine_step 30 15 [15,10,5,30] 3
  · have h : fast 15 0=20 := by decide
    rw [h]
    simp only [part321,Bool.and_false]
  · have h : fast 15 1=10 := by decide
    rw [h]
    have b : ([15,10,5,30] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 15 2=41 := by decide
    rw [h]
    simp only [part322,Bool.and_false]
private theorem part324 : checkNat 30 49 [49,35,10,5,30] 3 = false := by
  decide
private theorem part325 : checkNat 30 25 [25,35,10,5,30] 3 = false := by
  decide
private theorem part323 : checkNat 30 35 [35,10,5,30] 4 = false := by
  apply combine_step 30 35 [35,10,5,30] 3
  · have h : fast 35 0=49 := by decide
    rw [h]
    simp only [part324,Bool.and_false]
  · have h : fast 35 1=25 := by decide
    rw [h]
    simp only [part325,Bool.and_false]
  · have h : fast 35 2=10 := by decide
    rw [h]
    have b : ([35,10,5,30] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part319 : checkNat 30 10 [10,5,30] 5 = false := by
  apply combine_step 30 10 [10,5,30] 4
  · have h : fast 10 0=15 := by decide
    rw [h]
    simp only [part320,Bool.and_false]
  · have h : fast 10 1=5 := by decide
    rw [h]
    have b : ([10,5,30] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 10 2=35 := by decide
    rw [h]
    simp only [part323,Bool.and_false]
private theorem part328 : checkNat 30 15 [15,20,0,5,30] 3 = false := by
  decide
private theorem part329 : checkNat 30 45 [45,20,0,5,30] 3 = false := by
  decide
private theorem part327 : checkNat 30 20 [20,0,5,30] 4 = false := by
  apply combine_step 30 20 [20,0,5,30] 3
  · have h : fast 20 0=0 := by decide
    rw [h]
    have b : ([20,0,5,30] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 20 1=15 := by decide
    rw [h]
    simp only [part328,Bool.and_false]
  · have h : fast 20 2=45 := by decide
    rw [h]
    simp only [part329,Bool.and_false]
private theorem part331 : checkNat 30 35 [35,25,0,5,30] 3 = false := by
  decide
private theorem part332 : checkNat 30 40 [40,25,0,5,30] 3 = false := by
  decide
private theorem part330 : checkNat 30 25 [25,0,5,30] 4 = false := by
  apply combine_step 30 25 [25,0,5,30] 3
  · have h : fast 25 0=35 := by decide
    rw [h]
    simp only [part331,Bool.and_false]
  · have h : fast 25 1=40 := by decide
    rw [h]
    simp only [part332,Bool.and_false]
  · have h : fast 25 2=0 := by decide
    rw [h]
    have b : ([25,0,5,30] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part326 : checkNat 30 0 [0,5,30] 5 = false := by
  apply combine_step 30 0 [0,5,30] 4
  · have h : fast 0 0=5 := by decide
    rw [h]
    have b : ([0,5,30] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 0 1=20 := by decide
    rw [h]
    simp only [part327,Bool.and_false]
  · have h : fast 0 2=25 := by decide
    rw [h]
    simp only [part330,Bool.and_false]
private theorem part318 : checkNat 30 5 [5,30] 6 = false := by
  apply combine_step 30 5 [5,30] 5
  · have h : fast 5 0=10 := by decide
    rw [h]
    simp only [part319,Bool.and_false]
  · have h : fast 5 1=0 := by decide
    rw [h]
    simp only [part326,Bool.and_false]
  · have h : fast 5 2=30 := by decide
    rw [h]
    have b : ([5,30] : List ℕ).contains 30 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part287 : checkNat 30 30 [30] 7 = false := by
  apply combine_step 30 30 [30] 6
  · have h : fast 30 0=42 := by decide
    rw [h]
    simp only [part288,Bool.and_false]
  · have h : fast 30 1=48 := by decide
    rw [h]
    simp only [part303,Bool.and_false]
  · have h : fast 30 2=5 := by decide
    rw [h]
    simp only [part318,Bool.and_false]
private theorem cert8_6 : checkNat 30 30 [30] 7 = false := part287
private theorem part337 : checkNat 35 28 [28,43,31,49,35] 3 = false := by
  decide
private theorem part338 : checkNat 35 17 [17,43,31,49,35] 3 = false := by
  decide
private theorem part336 : checkNat 35 43 [43,31,49,35] 4 = false := by
  apply combine_step 35 43 [43,31,49,35] 3
  · have h : fast 43 0=28 := by decide
    rw [h]
    simp only [part337,Bool.and_false]
  · have h : fast 43 1=31 := by decide
    rw [h]
    have b : ([43,31,49,35] : List ℕ).contains 31 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 43 2=17 := by decide
    rw [h]
    simp only [part338,Bool.and_false]
private theorem part340 : checkNat 35 11 [11,6,31,49,35] 3 = false := by
  decide
private theorem part341 : checkNat 35 1 [1,6,31,49,35] 3 = false := by
  decide
private theorem part339 : checkNat 35 6 [6,31,49,35] 4 = false := by
  apply combine_step 35 6 [6,31,49,35] 3
  · have h : fast 6 0=11 := by decide
    rw [h]
    simp only [part340,Bool.and_false]
  · have h : fast 6 1=1 := by decide
    rw [h]
    simp only [part341,Bool.and_false]
  · have h : fast 6 2=31 := by decide
    rw [h]
    have b : ([6,31,49,35] : List ℕ).contains 31 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part335 : checkNat 35 31 [31,49,35] 5 = false := by
  apply combine_step 35 31 [31,49,35] 4
  · have h : fast 31 0=43 := by decide
    rw [h]
    simp only [part336,Bool.and_false]
  · have h : fast 31 1=49 := by decide
    rw [h]
    have b : ([31,49,35] : List ℕ).contains 49 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 31 2=6 := by decide
    rw [h]
    simp only [part339,Bool.and_false]
private theorem part344 : checkNat 35 9 [9,4,24,49,35] 3 = false := by
  decide
private theorem part345 : checkNat 35 29 [29,4,24,49,35] 3 = false := by
  decide
private theorem part343 : checkNat 35 4 [4,24,49,35] 4 = false := by
  apply combine_step 35 4 [4,24,49,35] 3
  · have h : fast 4 0=9 := by decide
    rw [h]
    simp only [part344,Bool.and_false]
  · have h : fast 4 1=24 := by decide
    rw [h]
    have b : ([4,24,49,35] : List ℕ).contains 24 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 4 2=29 := by decide
    rw [h]
    simp only [part345,Bool.and_false]
private theorem part347 : checkNat 35 14 [14,19,24,49,35] 3 = false := by
  decide
private theorem part348 : checkNat 35 40 [40,19,24,49,35] 3 = false := by
  decide
private theorem part346 : checkNat 35 19 [19,24,49,35] 4 = false := by
  apply combine_step 35 19 [19,24,49,35] 3
  · have h : fast 19 0=24 := by decide
    rw [h]
    have b : ([19,24,49,35] : List ℕ).contains 24 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 19 1=14 := by decide
    rw [h]
    simp only [part347,Bool.and_false]
  · have h : fast 19 2=40 := by decide
    rw [h]
    simp only [part348,Bool.and_false]
private theorem part342 : checkNat 35 24 [24,49,35] 5 = false := by
  apply combine_step 35 24 [24,49,35] 4
  · have h : fast 24 0=4 := by decide
    rw [h]
    simp only [part343,Bool.and_false]
  · have h : fast 24 1=19 := by decide
    rw [h]
    simp only [part346,Bool.and_false]
  · have h : fast 24 2=49 := by decide
    rw [h]
    have b : ([24,49,35] : List ℕ).contains 49 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part334 : checkNat 35 49 [49,35] 6 = false := by
  apply combine_step 35 49 [49,35] 5
  · have h : fast 49 0=31 := by decide
    rw [h]
    simp only [part335,Bool.and_false]
  · have h : fast 49 1=35 := by decide
    rw [h]
    have b : ([49,35] : List ℕ).contains 35 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 49 2=24 := by decide
    rw [h]
    simp only [part342,Bool.and_false]
private theorem part352 : checkNat 35 46 [46,33,40,25,35] 3 = false := by
  decide
private theorem part353 : checkNat 35 8 [8,33,40,25,35] 3 = false := by
  decide
private theorem part351 : checkNat 35 33 [33,40,25,35] 4 = false := by
  apply combine_step 35 33 [33,40,25,35] 3
  · have h : fast 33 0=40 := by decide
    rw [h]
    have b : ([33,40,25,35] : List ℕ).contains 40 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 33 1=46 := by decide
    rw [h]
    simp only [part352,Bool.and_false]
  · have h : fast 33 2=8 := by decide
    rw [h]
    simp only [part353,Bool.and_false]
private theorem part355 : checkNat 35 24 [24,19,40,25,35] 3 = false := by
  decide
private theorem part356 : checkNat 35 14 [14,19,40,25,35] 3 = false := by
  decide
private theorem part354 : checkNat 35 19 [19,40,25,35] 4 = false := by
  apply combine_step 35 19 [19,40,25,35] 3
  · have h : fast 19 0=24 := by decide
    rw [h]
    simp only [part355,Bool.and_false]
  · have h : fast 19 1=14 := by decide
    rw [h]
    simp only [part356,Bool.and_false]
  · have h : fast 19 2=40 := by decide
    rw [h]
    have b : ([19,40,25,35] : List ℕ).contains 40 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part350 : checkNat 35 40 [40,25,35] 5 = false := by
  apply combine_step 35 40 [40,25,35] 4
  · have h : fast 40 0=25 := by decide
    rw [h]
    have b : ([40,25,35] : List ℕ).contains 25 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 40 1=33 := by decide
    rw [h]
    simp only [part351,Bool.and_false]
  · have h : fast 40 2=19 := by decide
    rw [h]
    simp only [part354,Bool.and_false]
private theorem part359 : checkNat 35 10 [10,5,0,25,35] 3 = false := by
  decide
private theorem part360 : checkNat 35 30 [30,5,0,25,35] 3 = false := by
  decide
private theorem part358 : checkNat 35 5 [5,0,25,35] 4 = false := by
  apply combine_step 35 5 [5,0,25,35] 3
  · have h : fast 5 0=10 := by decide
    rw [h]
    simp only [part359,Bool.and_false]
  · have h : fast 5 1=0 := by decide
    rw [h]
    have b : ([5,0,25,35] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 5 2=30 := by decide
    rw [h]
    simp only [part360,Bool.and_false]
private theorem part362 : checkNat 35 15 [15,20,0,25,35] 3 = false := by
  decide
private theorem part363 : checkNat 35 45 [45,20,0,25,35] 3 = false := by
  decide
private theorem part361 : checkNat 35 20 [20,0,25,35] 4 = false := by
  apply combine_step 35 20 [20,0,25,35] 3
  · have h : fast 20 0=0 := by decide
    rw [h]
    have b : ([20,0,25,35] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 20 1=15 := by decide
    rw [h]
    simp only [part362,Bool.and_false]
  · have h : fast 20 2=45 := by decide
    rw [h]
    simp only [part363,Bool.and_false]
private theorem part357 : checkNat 35 0 [0,25,35] 5 = false := by
  apply combine_step 35 0 [0,25,35] 4
  · have h : fast 0 0=5 := by decide
    rw [h]
    simp only [part358,Bool.and_false]
  · have h : fast 0 1=20 := by decide
    rw [h]
    simp only [part361,Bool.and_false]
  · have h : fast 0 2=25 := by decide
    rw [h]
    have b : ([0,25,35] : List ℕ).contains 25 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part349 : checkNat 35 25 [25,35] 6 = false := by
  apply combine_step 35 25 [25,35] 5
  · have h : fast 25 0=35 := by decide
    rw [h]
    have b : ([25,35] : List ℕ).contains 35 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 25 1=40 := by decide
    rw [h]
    simp only [part350,Bool.and_false]
  · have h : fast 25 2=0 := by decide
    rw [h]
    simp only [part357,Bool.and_false]
private theorem part367 : checkNat 35 0 [0,20,15,10,35] 3 = false := by
  decide
private theorem part368 : checkNat 35 45 [45,20,15,10,35] 3 = false := by
  decide
private theorem part366 : checkNat 35 20 [20,15,10,35] 4 = false := by
  apply combine_step 35 20 [20,15,10,35] 3
  · have h : fast 20 0=0 := by decide
    rw [h]
    simp only [part367,Bool.and_false]
  · have h : fast 20 1=15 := by decide
    rw [h]
    have b : ([20,15,10,35] : List ℕ).contains 15 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 20 2=45 := by decide
    rw [h]
    simp only [part368,Bool.and_false]
private theorem part370 : checkNat 35 26 [26,41,15,10,35] 3 = false := by
  decide
private theorem part371 : checkNat 35 34 [34,41,15,10,35] 3 = false := by
  decide
private theorem part369 : checkNat 35 41 [41,15,10,35] 4 = false := by
  apply combine_step 35 41 [41,15,10,35] 3
  · have h : fast 41 0=26 := by decide
    rw [h]
    simp only [part370,Bool.and_false]
  · have h : fast 41 1=34 := by decide
    rw [h]
    simp only [part371,Bool.and_false]
  · have h : fast 41 2=15 := by decide
    rw [h]
    have b : ([41,15,10,35] : List ℕ).contains 15 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part365 : checkNat 35 15 [15,10,35] 5 = false := by
  apply combine_step 35 15 [15,10,35] 4
  · have h : fast 15 0=20 := by decide
    rw [h]
    simp only [part366,Bool.and_false]
  · have h : fast 15 1=10 := by decide
    rw [h]
    have b : ([15,10,35] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 15 2=41 := by decide
    rw [h]
    simp only [part369,Bool.and_false]
private theorem part374 : checkNat 35 20 [20,0,5,10,35] 3 = false := by
  decide
private theorem part375 : checkNat 35 25 [25,0,5,10,35] 3 = false := by
  decide
private theorem part373 : checkNat 35 0 [0,5,10,35] 4 = false := by
  apply combine_step 35 0 [0,5,10,35] 3
  · have h : fast 0 0=5 := by decide
    rw [h]
    have b : ([0,5,10,35] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 0 1=20 := by decide
    rw [h]
    simp only [part374,Bool.and_false]
  · have h : fast 0 2=25 := by decide
    rw [h]
    simp only [part375,Bool.and_false]
private theorem part377 : checkNat 35 42 [42,30,5,10,35] 3 = false := by
  decide
private theorem part378 : checkNat 35 48 [48,30,5,10,35] 3 = false := by
  decide
private theorem part376 : checkNat 35 30 [30,5,10,35] 4 = false := by
  apply combine_step 35 30 [30,5,10,35] 3
  · have h : fast 30 0=42 := by decide
    rw [h]
    simp only [part377,Bool.and_false]
  · have h : fast 30 1=48 := by decide
    rw [h]
    simp only [part378,Bool.and_false]
  · have h : fast 30 2=5 := by decide
    rw [h]
    have b : ([30,5,10,35] : List ℕ).contains 5 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part372 : checkNat 35 5 [5,10,35] 5 = false := by
  apply combine_step 35 5 [5,10,35] 4
  · have h : fast 5 0=10 := by decide
    rw [h]
    have b : ([5,10,35] : List ℕ).contains 10 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 5 1=0 := by decide
    rw [h]
    simp only [part373,Bool.and_false]
  · have h : fast 5 2=30 := by decide
    rw [h]
    simp only [part376,Bool.and_false]
private theorem part364 : checkNat 35 10 [10,35] 6 = false := by
  apply combine_step 35 10 [10,35] 5
  · have h : fast 10 0=15 := by decide
    rw [h]
    simp only [part365,Bool.and_false]
  · have h : fast 10 1=5 := by decide
    rw [h]
    simp only [part372,Bool.and_false]
  · have h : fast 10 2=35 := by decide
    rw [h]
    have b : ([10,35] : List ℕ).contains 35 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part333 : checkNat 35 35 [35] 7 = false := by
  apply combine_step 35 35 [35] 6
  · have h : fast 35 0=49 := by decide
    rw [h]
    simp only [part334,Bool.and_false]
  · have h : fast 35 1=25 := by decide
    rw [h]
    simp only [part349,Bool.and_false]
  · have h : fast 35 2=10 := by decide
    rw [h]
    simp only [part364,Bool.and_false]
private theorem cert8_7 : checkNat 35 35 [35] 7 = false := part333
private theorem part383 : checkNat 40 31 [31,49,35,25,40] 3 = false := by
  decide
private theorem part384 : checkNat 40 24 [24,49,35,25,40] 3 = false := by
  decide
private theorem part382 : checkNat 40 49 [49,35,25,40] 4 = false := by
  apply combine_step 40 49 [49,35,25,40] 3
  · have h : fast 49 0=31 := by decide
    rw [h]
    simp only [part383,Bool.and_false]
  · have h : fast 49 1=35 := by decide
    rw [h]
    have b : ([49,35,25,40] : List ℕ).contains 35 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 49 2=24 := by decide
    rw [h]
    simp only [part384,Bool.and_false]
private theorem part386 : checkNat 40 15 [15,10,35,25,40] 3 = false := by
  decide
private theorem part387 : checkNat 40 5 [5,10,35,25,40] 3 = false := by
  decide
private theorem part385 : checkNat 40 10 [10,35,25,40] 4 = false := by
  apply combine_step 40 10 [10,35,25,40] 3
  · have h : fast 10 0=15 := by decide
    rw [h]
    simp only [part386,Bool.and_false]
  · have h : fast 10 1=5 := by decide
    rw [h]
    simp only [part387,Bool.and_false]
  · have h : fast 10 2=35 := by decide
    rw [h]
    have b : ([10,35,25,40] : List ℕ).contains 35 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part381 : checkNat 40 35 [35,25,40] 5 = false := by
  apply combine_step 40 35 [35,25,40] 4
  · have h : fast 35 0=49 := by decide
    rw [h]
    simp only [part382,Bool.and_false]
  · have h : fast 35 1=25 := by decide
    rw [h]
    have b : ([35,25,40] : List ℕ).contains 25 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 35 2=10 := by decide
    rw [h]
    simp only [part385,Bool.and_false]
private theorem part390 : checkNat 40 10 [10,5,0,25,40] 3 = false := by
  decide
private theorem part391 : checkNat 40 30 [30,5,0,25,40] 3 = false := by
  decide
private theorem part389 : checkNat 40 5 [5,0,25,40] 4 = false := by
  apply combine_step 40 5 [5,0,25,40] 3
  · have h : fast 5 0=10 := by decide
    rw [h]
    simp only [part390,Bool.and_false]
  · have h : fast 5 1=0 := by decide
    rw [h]
    have b : ([5,0,25,40] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 5 2=30 := by decide
    rw [h]
    simp only [part391,Bool.and_false]
private theorem part393 : checkNat 40 15 [15,20,0,25,40] 3 = false := by
  decide
private theorem part394 : checkNat 40 45 [45,20,0,25,40] 3 = false := by
  decide
private theorem part392 : checkNat 40 20 [20,0,25,40] 4 = false := by
  apply combine_step 40 20 [20,0,25,40] 3
  · have h : fast 20 0=0 := by decide
    rw [h]
    have b : ([20,0,25,40] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 20 1=15 := by decide
    rw [h]
    simp only [part393,Bool.and_false]
  · have h : fast 20 2=45 := by decide
    rw [h]
    simp only [part394,Bool.and_false]
private theorem part388 : checkNat 40 0 [0,25,40] 5 = false := by
  apply combine_step 40 0 [0,25,40] 4
  · have h : fast 0 0=5 := by decide
    rw [h]
    simp only [part389,Bool.and_false]
  · have h : fast 0 1=20 := by decide
    rw [h]
    simp only [part392,Bool.and_false]
  · have h : fast 0 2=25 := by decide
    rw [h]
    have b : ([0,25,40] : List ℕ).contains 25 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part380 : checkNat 40 25 [25,40] 6 = false := by
  apply combine_step 40 25 [25,40] 5
  · have h : fast 25 0=35 := by decide
    rw [h]
    simp only [part381,Bool.and_false]
  · have h : fast 25 1=40 := by decide
    rw [h]
    have b : ([25,40] : List ℕ).contains 40 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 25 2=0 := by decide
    rw [h]
    simp only [part388,Bool.and_false]
private theorem part398 : checkNat 40 27 [27,37,46,33,40] 3 = false := by
  decide
private theorem part399 : checkNat 40 12 [12,37,46,33,40] 3 = false := by
  decide
private theorem part397 : checkNat 40 37 [37,46,33,40] 4 = false := by
  apply combine_step 40 37 [37,46,33,40] 3
  · have h : fast 37 0=46 := by decide
    rw [h]
    have b : ([37,46,33,40] : List ℕ).contains 46 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 37 1=27 := by decide
    rw [h]
    simp only [part398,Bool.and_false]
  · have h : fast 37 2=12 := by decide
    rw [h]
    simp only [part399,Bool.and_false]
private theorem part401 : checkNat 40 1 [1,21,46,33,40] 3 = false := by
  decide
private theorem part402 : checkNat 40 16 [16,21,46,33,40] 3 = false := by
  decide
private theorem part400 : checkNat 40 21 [21,46,33,40] 4 = false := by
  apply combine_step 40 21 [21,46,33,40] 3
  · have h : fast 21 0=1 := by decide
    rw [h]
    simp only [part401,Bool.and_false]
  · have h : fast 21 1=16 := by decide
    rw [h]
    simp only [part402,Bool.and_false]
  · have h : fast 21 2=46 := by decide
    rw [h]
    have b : ([21,46,33,40] : List ℕ).contains 46 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part396 : checkNat 40 46 [46,33,40] 5 = false := by
  apply combine_step 40 46 [46,33,40] 4
  · have h : fast 46 0=33 := by decide
    rw [h]
    have b : ([46,33,40] : List ℕ).contains 33 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 46 1=37 := by decide
    rw [h]
    simp only [part397,Bool.and_false]
  · have h : fast 46 2=21 := by decide
    rw [h]
    simp only [part400,Bool.and_false]
private theorem part405 : checkNat 40 18 [18,13,8,33,40] 3 = false := by
  decide
private theorem part406 : checkNat 40 38 [38,13,8,33,40] 3 = false := by
  decide
private theorem part404 : checkNat 40 13 [13,8,33,40] 4 = false := by
  apply combine_step 40 13 [13,8,33,40] 3
  · have h : fast 13 0=18 := by decide
    rw [h]
    simp only [part405,Bool.and_false]
  · have h : fast 13 1=8 := by decide
    rw [h]
    have b : ([13,8,33,40] : List ℕ).contains 8 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 13 2=38 := by decide
    rw [h]
    simp only [part406,Bool.and_false]
private theorem part408 : checkNat 40 23 [23,3,8,33,40] 3 = false := by
  decide
private theorem part409 : checkNat 40 28 [28,3,8,33,40] 3 = false := by
  decide
private theorem part407 : checkNat 40 3 [3,8,33,40] 4 = false := by
  apply combine_step 40 3 [3,8,33,40] 3
  · have h : fast 3 0=8 := by decide
    rw [h]
    have b : ([3,8,33,40] : List ℕ).contains 8 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 3 1=23 := by decide
    rw [h]
    simp only [part408,Bool.and_false]
  · have h : fast 3 2=28 := by decide
    rw [h]
    simp only [part409,Bool.and_false]
private theorem part403 : checkNat 40 8 [8,33,40] 5 = false := by
  apply combine_step 40 8 [8,33,40] 4
  · have h : fast 8 0=13 := by decide
    rw [h]
    simp only [part404,Bool.and_false]
  · have h : fast 8 1=3 := by decide
    rw [h]
    simp only [part407,Bool.and_false]
  · have h : fast 8 2=33 := by decide
    rw [h]
    have b : ([8,33,40] : List ℕ).contains 33 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part395 : checkNat 40 33 [33,40] 6 = false := by
  apply combine_step 40 33 [33,40] 5
  · have h : fast 33 0=40 := by decide
    rw [h]
    have b : ([33,40] : List ℕ).contains 40 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 33 1=46 := by decide
    rw [h]
    simp only [part396,Bool.and_false]
  · have h : fast 33 2=8 := by decide
    rw [h]
    simp only [part403,Bool.and_false]
private theorem part413 : checkNat 40 9 [9,4,24,19,40] 3 = false := by
  decide
private theorem part414 : checkNat 40 29 [29,4,24,19,40] 3 = false := by
  decide
private theorem part412 : checkNat 40 4 [4,24,19,40] 4 = false := by
  apply combine_step 40 4 [4,24,19,40] 3
  · have h : fast 4 0=9 := by decide
    rw [h]
    simp only [part413,Bool.and_false]
  · have h : fast 4 1=24 := by decide
    rw [h]
    have b : ([4,24,19,40] : List ℕ).contains 24 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 4 2=29 := by decide
    rw [h]
    simp only [part414,Bool.and_false]
private theorem part416 : checkNat 40 31 [31,49,24,19,40] 3 = false := by
  decide
private theorem part417 : checkNat 40 35 [35,49,24,19,40] 3 = false := by
  decide
private theorem part415 : checkNat 40 49 [49,24,19,40] 4 = false := by
  apply combine_step 40 49 [49,24,19,40] 3
  · have h : fast 49 0=31 := by decide
    rw [h]
    simp only [part416,Bool.and_false]
  · have h : fast 49 1=35 := by decide
    rw [h]
    simp only [part417,Bool.and_false]
  · have h : fast 49 2=24 := by decide
    rw [h]
    have b : ([49,24,19,40] : List ℕ).contains 24 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part411 : checkNat 40 24 [24,19,40] 5 = false := by
  apply combine_step 40 24 [24,19,40] 4
  · have h : fast 24 0=4 := by decide
    rw [h]
    simp only [part412,Bool.and_false]
  · have h : fast 24 1=19 := by decide
    rw [h]
    have b : ([24,19,40] : List ℕ).contains 19 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 24 2=49 := by decide
    rw [h]
    simp only [part415,Bool.and_false]
private theorem part420 : checkNat 40 4 [4,9,14,19,40] 3 = false := by
  decide
private theorem part421 : checkNat 40 34 [34,9,14,19,40] 3 = false := by
  decide
private theorem part419 : checkNat 40 9 [9,14,19,40] 4 = false := by
  apply combine_step 40 9 [9,14,19,40] 3
  · have h : fast 9 0=14 := by decide
    rw [h]
    have b : ([9,14,19,40] : List ℕ).contains 14 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 9 1=4 := by decide
    rw [h]
    simp only [part420,Bool.and_false]
  · have h : fast 9 2=34 := by decide
    rw [h]
    simp only [part421,Bool.and_false]
private theorem part423 : checkNat 40 48 [48,39,14,19,40] 3 = false := by
  decide
private theorem part424 : checkNat 40 29 [29,39,14,19,40] 3 = false := by
  decide
private theorem part422 : checkNat 40 39 [39,14,19,40] 4 = false := by
  apply combine_step 40 39 [39,14,19,40] 3
  · have h : fast 39 0=48 := by decide
    rw [h]
    simp only [part423,Bool.and_false]
  · have h : fast 39 1=29 := by decide
    rw [h]
    simp only [part424,Bool.and_false]
  · have h : fast 39 2=14 := by decide
    rw [h]
    have b : ([39,14,19,40] : List ℕ).contains 14 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part418 : checkNat 40 14 [14,19,40] 5 = false := by
  apply combine_step 40 14 [14,19,40] 4
  · have h : fast 14 0=19 := by decide
    rw [h]
    have b : ([14,19,40] : List ℕ).contains 19 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 14 1=9 := by decide
    rw [h]
    simp only [part419,Bool.and_false]
  · have h : fast 14 2=39 := by decide
    rw [h]
    simp only [part422,Bool.and_false]
private theorem part410 : checkNat 40 19 [19,40] 6 = false := by
  apply combine_step 40 19 [19,40] 5
  · have h : fast 19 0=24 := by decide
    rw [h]
    simp only [part411,Bool.and_false]
  · have h : fast 19 1=14 := by decide
    rw [h]
    simp only [part418,Bool.and_false]
  · have h : fast 19 2=40 := by decide
    rw [h]
    have b : ([19,40] : List ℕ).contains 40 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part379 : checkNat 40 40 [40] 7 = false := by
  apply combine_step 40 40 [40] 6
  · have h : fast 40 0=25 := by decide
    rw [h]
    simp only [part380,Bool.and_false]
  · have h : fast 40 1=33 := by decide
    rw [h]
    simp only [part395,Bool.and_false]
  · have h : fast 40 2=19 := by decide
    rw [h]
    simp only [part410,Bool.and_false]
private theorem cert8_8 : checkNat 40 40 [40] 7 = false := part379
private theorem part429 : checkNat 45 39 [39,29,44,32,45] 3 = false := by
  decide
private theorem part430 : checkNat 45 4 [4,29,44,32,45] 3 = false := by
  decide
private theorem part428 : checkNat 45 29 [29,44,32,45] 4 = false := by
  apply combine_step 45 29 [29,44,32,45] 3
  · have h : fast 29 0=39 := by decide
    rw [h]
    simp only [part429,Bool.and_false]
  · have h : fast 29 1=44 := by decide
    rw [h]
    have b : ([29,44,32,45] : List ℕ).contains 44 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 29 2=4 := by decide
    rw [h]
    simp only [part430,Bool.and_false]
private theorem part432 : checkNat 45 23 [23,18,44,32,45] 3 = false := by
  decide
private theorem part433 : checkNat 45 13 [13,18,44,32,45] 3 = false := by
  decide
private theorem part431 : checkNat 45 18 [18,44,32,45] 4 = false := by
  apply combine_step 45 18 [18,44,32,45] 3
  · have h : fast 18 0=23 := by decide
    rw [h]
    simp only [part432,Bool.and_false]
  · have h : fast 18 1=13 := by decide
    rw [h]
    simp only [part433,Bool.and_false]
  · have h : fast 18 2=44 := by decide
    rw [h]
    have b : ([18,44,32,45] : List ℕ).contains 44 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part427 : checkNat 45 44 [44,32,45] 5 = false := by
  apply combine_step 45 44 [44,32,45] 4
  · have h : fast 44 0=29 := by decide
    rw [h]
    simp only [part428,Bool.and_false]
  · have h : fast 44 1=32 := by decide
    rw [h]
    have b : ([44,32,45] : List ℕ).contains 32 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 44 2=18 := by decide
    rw [h]
    simp only [part431,Bool.and_false]
private theorem part436 : checkNat 45 17 [17,12,7,32,45] 3 = false := by
  decide
private theorem part437 : checkNat 45 37 [37,12,7,32,45] 3 = false := by
  decide
private theorem part435 : checkNat 45 12 [12,7,32,45] 4 = false := by
  apply combine_step 45 12 [12,7,32,45] 3
  · have h : fast 12 0=17 := by decide
    rw [h]
    simp only [part436,Bool.and_false]
  · have h : fast 12 1=7 := by decide
    rw [h]
    have b : ([12,7,32,45] : List ℕ).contains 7 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 12 2=37 := by decide
    rw [h]
    simp only [part437,Bool.and_false]
private theorem part439 : checkNat 45 22 [22,2,7,32,45] 3 = false := by
  decide
private theorem part440 : checkNat 45 27 [27,2,7,32,45] 3 = false := by
  decide
private theorem part438 : checkNat 45 2 [2,7,32,45] 4 = false := by
  apply combine_step 45 2 [2,7,32,45] 3
  · have h : fast 2 0=7 := by decide
    rw [h]
    have b : ([2,7,32,45] : List ℕ).contains 7 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 2 1=22 := by decide
    rw [h]
    simp only [part439,Bool.and_false]
  · have h : fast 2 2=27 := by decide
    rw [h]
    simp only [part440,Bool.and_false]
private theorem part434 : checkNat 45 7 [7,32,45] 5 = false := by
  apply combine_step 45 7 [7,32,45] 4
  · have h : fast 7 0=12 := by decide
    rw [h]
    simp only [part435,Bool.and_false]
  · have h : fast 7 1=2 := by decide
    rw [h]
    simp only [part438,Bool.and_false]
  · have h : fast 7 2=32 := by decide
    rw [h]
    have b : ([7,32,45] : List ℕ).contains 32 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part426 : checkNat 45 32 [32,45] 6 = false := by
  apply combine_step 45 32 [32,45] 5
  · have h : fast 32 0=44 := by decide
    rw [h]
    simp only [part427,Bool.and_false]
  · have h : fast 32 1=45 := by decide
    rw [h]
    have b : ([32,45] : List ℕ).contains 45 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 32 2=7 := by decide
    rw [h]
    simp only [part434,Bool.and_false]
private theorem part444 : checkNat 45 34 [34,41,26,36,45] 3 = false := by
  decide
private theorem part445 : checkNat 45 15 [15,41,26,36,45] 3 = false := by
  decide
private theorem part443 : checkNat 45 41 [41,26,36,45] 4 = false := by
  apply combine_step 45 41 [41,26,36,45] 3
  · have h : fast 41 0=26 := by decide
    rw [h]
    have b : ([41,26,36,45] : List ℕ).contains 26 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 41 1=34 := by decide
    rw [h]
    simp only [part444,Bool.and_false]
  · have h : fast 41 2=15 := by decide
    rw [h]
    simp only [part445,Bool.and_false]
private theorem part447 : checkNat 45 6 [6,1,26,36,45] 3 = false := by
  decide
private theorem part448 : checkNat 45 21 [21,1,26,36,45] 3 = false := by
  decide
private theorem part446 : checkNat 45 1 [1,26,36,45] 4 = false := by
  apply combine_step 45 1 [1,26,36,45] 3
  · have h : fast 1 0=6 := by decide
    rw [h]
    simp only [part447,Bool.and_false]
  · have h : fast 1 1=21 := by decide
    rw [h]
    simp only [part448,Bool.and_false]
  · have h : fast 1 2=26 := by decide
    rw [h]
    have b : ([1,26,36,45] : List ℕ).contains 26 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part442 : checkNat 45 26 [26,36,45] 5 = false := by
  apply combine_step 45 26 [26,36,45] 4
  · have h : fast 26 0=36 := by decide
    rw [h]
    have b : ([26,36,45] : List ℕ).contains 36 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 26 1=41 := by decide
    rw [h]
    simp only [part443,Bool.and_false]
  · have h : fast 26 2=1 := by decide
    rw [h]
    simp only [part446,Bool.and_false]
private theorem part451 : checkNat 45 21 [21,16,11,36,45] 3 = false := by
  decide
private theorem part452 : checkNat 45 42 [42,16,11,36,45] 3 = false := by
  decide
private theorem part450 : checkNat 45 16 [16,11,36,45] 4 = false := by
  apply combine_step 45 16 [16,11,36,45] 3
  · have h : fast 16 0=21 := by decide
    rw [h]
    simp only [part451,Bool.and_false]
  · have h : fast 16 1=11 := by decide
    rw [h]
    have b : ([16,11,36,45] : List ℕ).contains 11 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 16 2=42 := by decide
    rw [h]
    simp only [part452,Bool.and_false]
private theorem part454 : checkNat 45 1 [1,6,11,36,45] 3 = false := by
  decide
private theorem part455 : checkNat 45 31 [31,6,11,36,45] 3 = false := by
  decide
private theorem part453 : checkNat 45 6 [6,11,36,45] 4 = false := by
  apply combine_step 45 6 [6,11,36,45] 3
  · have h : fast 6 0=11 := by decide
    rw [h]
    have b : ([6,11,36,45] : List ℕ).contains 11 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 6 1=1 := by decide
    rw [h]
    simp only [part454,Bool.and_false]
  · have h : fast 6 2=31 := by decide
    rw [h]
    simp only [part455,Bool.and_false]
private theorem part449 : checkNat 45 11 [11,36,45] 5 = false := by
  apply combine_step 45 11 [11,36,45] 4
  · have h : fast 11 0=16 := by decide
    rw [h]
    simp only [part450,Bool.and_false]
  · have h : fast 11 1=6 := by decide
    rw [h]
    simp only [part453,Bool.and_false]
  · have h : fast 11 2=36 := by decide
    rw [h]
    have b : ([11,36,45] : List ℕ).contains 36 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part441 : checkNat 45 36 [36,45] 6 = false := by
  apply combine_step 45 36 [36,45] 5
  · have h : fast 36 0=45 := by decide
    rw [h]
    have b : ([36,45] : List ℕ).contains 45 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 36 1=26 := by decide
    rw [h]
    simp only [part442,Bool.and_false]
  · have h : fast 36 2=11 := by decide
    rw [h]
    simp only [part449,Bool.and_false]
private theorem part459 : checkNat 45 10 [10,5,0,20,45] 3 = false := by
  decide
private theorem part460 : checkNat 45 30 [30,5,0,20,45] 3 = false := by
  decide
private theorem part458 : checkNat 45 5 [5,0,20,45] 4 = false := by
  apply combine_step 45 5 [5,0,20,45] 3
  · have h : fast 5 0=10 := by decide
    rw [h]
    simp only [part459,Bool.and_false]
  · have h : fast 5 1=0 := by decide
    rw [h]
    have b : ([5,0,20,45] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 5 2=30 := by decide
    rw [h]
    simp only [part460,Bool.and_false]
private theorem part462 : checkNat 45 35 [35,25,0,20,45] 3 = false := by
  decide
private theorem part463 : checkNat 45 40 [40,25,0,20,45] 3 = false := by
  decide
private theorem part461 : checkNat 45 25 [25,0,20,45] 4 = false := by
  apply combine_step 45 25 [25,0,20,45] 3
  · have h : fast 25 0=35 := by decide
    rw [h]
    simp only [part462,Bool.and_false]
  · have h : fast 25 1=40 := by decide
    rw [h]
    simp only [part463,Bool.and_false]
  · have h : fast 25 2=0 := by decide
    rw [h]
    have b : ([25,0,20,45] : List ℕ).contains 0 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part457 : checkNat 45 0 [0,20,45] 5 = false := by
  apply combine_step 45 0 [0,20,45] 4
  · have h : fast 0 0=5 := by decide
    rw [h]
    simp only [part458,Bool.and_false]
  · have h : fast 0 1=20 := by decide
    rw [h]
    have b : ([0,20,45] : List ℕ).contains 20 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 0 2=25 := by decide
    rw [h]
    simp only [part461,Bool.and_false]
private theorem part466 : checkNat 45 5 [5,10,15,20,45] 3 = false := by
  decide
private theorem part467 : checkNat 45 35 [35,10,15,20,45] 3 = false := by
  decide
private theorem part465 : checkNat 45 10 [10,15,20,45] 4 = false := by
  apply combine_step 45 10 [10,15,20,45] 3
  · have h : fast 10 0=15 := by decide
    rw [h]
    have b : ([10,15,20,45] : List ℕ).contains 15 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 10 1=5 := by decide
    rw [h]
    simp only [part466,Bool.and_false]
  · have h : fast 10 2=35 := by decide
    rw [h]
    simp only [part467,Bool.and_false]
private theorem part469 : checkNat 45 26 [26,41,15,20,45] 3 = false := by
  decide
private theorem part470 : checkNat 45 34 [34,41,15,20,45] 3 = false := by
  decide
private theorem part468 : checkNat 45 41 [41,15,20,45] 4 = false := by
  apply combine_step 45 41 [41,15,20,45] 3
  · have h : fast 41 0=26 := by decide
    rw [h]
    simp only [part469,Bool.and_false]
  · have h : fast 41 1=34 := by decide
    rw [h]
    simp only [part470,Bool.and_false]
  · have h : fast 41 2=15 := by decide
    rw [h]
    have b : ([41,15,20,45] : List ℕ).contains 15 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part464 : checkNat 45 15 [15,20,45] 5 = false := by
  apply combine_step 45 15 [15,20,45] 4
  · have h : fast 15 0=20 := by decide
    rw [h]
    have b : ([15,20,45] : List ℕ).contains 20 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
  · have h : fast 15 1=10 := by decide
    rw [h]
    simp only [part465,Bool.and_false]
  · have h : fast 15 2=41 := by decide
    rw [h]
    simp only [part468,Bool.and_false]
private theorem part456 : checkNat 45 20 [20,45] 6 = false := by
  apply combine_step 45 20 [20,45] 5
  · have h : fast 20 0=0 := by decide
    rw [h]
    simp only [part457,Bool.and_false]
  · have h : fast 20 1=15 := by decide
    rw [h]
    simp only [part464,Bool.and_false]
  · have h : fast 20 2=45 := by decide
    rw [h]
    have b : ([20,45] : List ℕ).contains 45 = true := by decide
    simp only [b,Bool.not_true,Bool.false_and]
private theorem part425 : checkNat 45 45 [45] 7 = false := by
  apply combine_step 45 45 [45] 6
  · have h : fast 45 0=32 := by decide
    rw [h]
    simp only [part426,Bool.and_false]
  · have h : fast 45 1=36 := by decide
    rw [h]
    simp only [part441,Bool.and_false]
  · have h : fast 45 2=20 := by decide
    rw [h]
    simp only [part456,Bool.and_false]
private theorem cert8_9 : checkNat 45 45 [45] 7 = false := part425
attribute [local irreducible] checkNat check enc
private theorem cert4 (s : V) : check s s [s] 3 = false := by
  rcases s with ⟨b,d⟩
  have base : check (b,0) (b,0) [(b,0)] 3 = false := by
    rw [← check_nat (b,0) (b,0) [(b,0)]]
    rw [List.map_singleton]
    fin_cases b
    · change checkNat (enc ((0 : B), (0 : D))) (enc ((0 : B), (0 : D))) [enc ((0 : B), (0 : D))] 3 = false
      have e : enc ((0 : B),(0 : D)) = 0 := by unfold enc; decide
      rw [e]
      exact cert4_0
    · change checkNat (enc ((1 : B), (0 : D))) (enc ((1 : B), (0 : D))) [enc ((1 : B), (0 : D))] 3 = false
      have e : enc ((1 : B),(0 : D)) = 5 := by unfold enc; decide
      rw [e]
      exact cert4_1
    · change checkNat (enc ((2 : B), (0 : D))) (enc ((2 : B), (0 : D))) [enc ((2 : B), (0 : D))] 3 = false
      have e : enc ((2 : B),(0 : D)) = 10 := by unfold enc; decide
      rw [e]
      exact cert4_2
    · change checkNat (enc ((3 : B), (0 : D))) (enc ((3 : B), (0 : D))) [enc ((3 : B), (0 : D))] 3 = false
      have e : enc ((3 : B),(0 : D)) = 15 := by unfold enc; decide
      rw [e]
      exact cert4_3
    · change checkNat (enc ((4 : B), (0 : D))) (enc ((4 : B), (0 : D))) [enc ((4 : B), (0 : D))] 3 = false
      have e : enc ((4 : B),(0 : D)) = 20 := by unfold enc; decide
      rw [e]
      exact cert4_4
    · change checkNat (enc ((5 : B), (0 : D))) (enc ((5 : B), (0 : D))) [enc ((5 : B), (0 : D))] 3 = false
      have e : enc ((5 : B),(0 : D)) = 25 := by unfold enc; decide
      rw [e]
      exact cert4_5
    · change checkNat (enc ((6 : B), (0 : D))) (enc ((6 : B), (0 : D))) [enc ((6 : B), (0 : D))] 3 = false
      have e : enc ((6 : B),(0 : D)) = 30 := by unfold enc; decide
      rw [e]
      exact cert4_6
    · change checkNat (enc ((7 : B), (0 : D))) (enc ((7 : B), (0 : D))) [enc ((7 : B), (0 : D))] 3 = false
      have e : enc ((7 : B),(0 : D)) = 35 := by unfold enc; decide
      rw [e]
      exact cert4_7
    · change checkNat (enc ((8 : B), (0 : D))) (enc ((8 : B), (0 : D))) [enc ((8 : B), (0 : D))] 3 = false
      have e : enc ((8 : B),(0 : D)) = 40 := by unfold enc; decide
      rw [e]
      exact cert4_8
    · change checkNat (enc ((9 : B), (0 : D))) (enc ((9 : B), (0 : D))) [enc ((9 : B), (0 : D))] 3 = false
      have e : enc ((9 : B),(0 : D)) = 45 := by unfold enc; decide
      rw [e]
      exact cert4_9
  simpa only [List.map_singleton,shift,zero_add] using ((check_shift d (b,0) (b,0) [(b,0)] 3).trans base)

private theorem cert8 (s : V) : check s s [s] 7 = false := by
  rcases s with ⟨b,d⟩
  have base : check (b,0) (b,0) [(b,0)] 7 = false := by
    rw [← check_nat (b,0) (b,0) [(b,0)]]
    rw [List.map_singleton]
    fin_cases b
    · change checkNat (enc ((0 : B), (0 : D))) (enc ((0 : B), (0 : D))) [enc ((0 : B), (0 : D))] 7 = false
      have e : enc ((0 : B),(0 : D)) = 0 := by unfold enc; decide
      rw [e]
      exact cert8_0
    · change checkNat (enc ((1 : B), (0 : D))) (enc ((1 : B), (0 : D))) [enc ((1 : B), (0 : D))] 7 = false
      have e : enc ((1 : B),(0 : D)) = 5 := by unfold enc; decide
      rw [e]
      exact cert8_1
    · change checkNat (enc ((2 : B), (0 : D))) (enc ((2 : B), (0 : D))) [enc ((2 : B), (0 : D))] 7 = false
      have e : enc ((2 : B),(0 : D)) = 10 := by unfold enc; decide
      rw [e]
      exact cert8_2
    · change checkNat (enc ((3 : B), (0 : D))) (enc ((3 : B), (0 : D))) [enc ((3 : B), (0 : D))] 7 = false
      have e : enc ((3 : B),(0 : D)) = 15 := by unfold enc; decide
      rw [e]
      exact cert8_3
    · change checkNat (enc ((4 : B), (0 : D))) (enc ((4 : B), (0 : D))) [enc ((4 : B), (0 : D))] 7 = false
      have e : enc ((4 : B),(0 : D)) = 20 := by unfold enc; decide
      rw [e]
      exact cert8_4
    · change checkNat (enc ((5 : B), (0 : D))) (enc ((5 : B), (0 : D))) [enc ((5 : B), (0 : D))] 7 = false
      have e : enc ((5 : B),(0 : D)) = 25 := by unfold enc; decide
      rw [e]
      exact cert8_5
    · change checkNat (enc ((6 : B), (0 : D))) (enc ((6 : B), (0 : D))) [enc ((6 : B), (0 : D))] 7 = false
      have e : enc ((6 : B),(0 : D)) = 30 := by unfold enc; decide
      rw [e]
      exact cert8_6
    · change checkNat (enc ((7 : B), (0 : D))) (enc ((7 : B), (0 : D))) [enc ((7 : B), (0 : D))] 7 = false
      have e : enc ((7 : B),(0 : D)) = 35 := by unfold enc; decide
      rw [e]
      exact cert8_7
    · change checkNat (enc ((8 : B), (0 : D))) (enc ((8 : B), (0 : D))) [enc ((8 : B), (0 : D))] 7 = false
      have e : enc ((8 : B),(0 : D)) = 40 := by unfold enc; decide
      rw [e]
      exact cert8_8
    · change checkNat (enc ((9 : B), (0 : D))) (enc ((9 : B), (0 : D))) [enc ((9 : B), (0 : D))] 7 = false
      have e : enc ((9 : B),(0 : D)) = 45 := by unfold enc; decide
      rw [e]
      exact cert8_9
  simpa only [List.map_singleton,shift,zero_add] using ((check_shift d (b,0) (b,0) [(b,0)] 7).trans base)

theorem no4 : ¬ Cyclic 4 := by
  intro H
  obtain ⟨v,e⟩ := exists_check 4 (by decide) H
  rw [cert4] at e
  contradiction

theorem no8 : ¬ Cyclic 8 := by
  intro H
  obtain ⟨v,e⟩ := exists_check 8 (by decide) H
  rw [cert8] at e
  contradiction

end PetersenSharp

#print axioms PetersenSharp.no4
#print axioms PetersenSharp.no8

