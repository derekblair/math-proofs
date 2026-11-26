import HaarSharpGraph

namespace HaarHalfCollision
open HaarCycle HaarAllNoncommuting
variable {G : Type*} [Group G]
def port (x y : G) (c : Fin 3) : G := if c=0 then 1 else if c=1 then x else y
def signPort (x y : G) (i : ℕ) (c : Fin 3) : G :=
  if i%2=0 then port x y c else (port x y c)⁻¹
def prodFrom (x y : G) (j : ℕ) : List (Fin 3) → G
  | [] => 1
  | c::t => signPort x y j c * prodFrom x y (j+1) t
abbrev segment := HaarSharpGraph.segment
theorem branch (x y : G) (p q : Bool × G) (e : haarAdj x y p q) :
    q.1 = !p.1 ∧ ∃ c : Fin 3,
      q.2 = p.2 * (if p.1 then (port x y c)⁻¹ else port x y c) := by
  cases h : p.1
  · simp [haarAdj,h] at e
    rcases e with ⟨a,b|b|b⟩
    · exact ⟨by simp [a],0,by simp [port,b]⟩
    · exact ⟨by simp [a],1,by simpa [port,h] using b⟩
    · exact ⟨by simp [a],2,by simpa [port,h] using b⟩
  · simp [haarAdj,h] at e
    rcases e with ⟨a,b|b|b⟩
    · exact ⟨by simp [a],0,by simp [port,b]⟩
    · exact ⟨by simp [a],1,by simpa [port,h] using (eq_mul_inv_iff_mul_eq.mpr b.symm)⟩
    · exact ⟨by simp [a],2,by simpa [port,h] using (eq_mul_inv_iff_mul_eq.mpr b.symm)⟩

theorem segment_product (x y : G) (g : ℕ → G) (c : ℕ → Fin 3) (bias j n : ℕ)
    (hh : ∀ k<n, g (j+k+1)=g (j+k)*signPort x y (bias+(j+k)) (c (j+k))) :
    g (j+n)=g j*prodFrom x y (bias+j) (segment c j n) := by
  induction n generalizing j with
  | zero => simp [segment,HaarSharpGraph.segment,prodFrom]
  | succ n ih =>
    have h1 := hh 0 (by omega)
    have h2 := ih (j+1) (fun k hk => by
      simpa only [Nat.add_assoc,Nat.add_comm 1 k] using hh (k+1) (by omega))
    rw [show j+(n+1)=(j+1)+n by omega,h2]
    simp only [segment,HaarSharpGraph.segment,prodFrom,← mul_assoc]
    have he : bias+(j+1)=bias+j+1 := by omega
    rw [he, ← show g (j+1)=g j*signPort x y (bias+j) (c j) by simpa using h1]

theorem symmetric (x y : G) {a b : Bool × G} (h : haarAdj x y a b) :
    haarAdj x y b a := by
  rcases a with ⟨p,u⟩
  rcases b with ⟨q,v⟩
  cases p <;> cases q <;> simp_all [haarAdj]

structure Labeled (x y : G) (k : ℕ) (a : ℕ → Bool × G) where
  labels : ℕ → Fin 3
  positive : (a 0).1=false
  steps : ∀ i, (a (i+1)).1 = !(a i).1
  edge : ∀ i, (a (i+1)).2 = (a i).2 * (if (a i).1 then (port x y (labels i))⁻¹ else port x y (labels i))
  nonbounce : ∀ i<k-1, a (i+2)≠a i

noncomputable def labeled (x y : G) (k : ℕ) (a : ℕ → Bool × G)
    (h0 : (a 0).1=false) (adj : ∀ i, haarAdj x y (a i) (a (i+1)))
    (hb : ∀ i<k-1, a (i+2)≠a i) : Labeled x y k a :=
  ⟨fun i => Classical.choose (branch x y _ _ (adj i)).2,h0,
    fun i => (branch x y _ _ (adj i)).1,
    fun i => Classical.choose_spec (branch x y _ _ (adj i)).2,hb⟩

theorem parity (x y : G) {k : ℕ} {a : ℕ → Bool × G} (L : Labeled x y k a) (i : ℕ) :
    (a i).1 = decide (i%2=1) := by
  induction i with
  | zero => simpa using L.positive
  | succ i ih =>
    rw [L.steps,ih]
    by_cases q : i%2=1
    · have r : (i+1)%2≠1 := by omega
      simp [q,r]
    · have r : (i+1)%2=1 := by omega
      simp [q,r]

theorem good_label (x y : G) {k : ℕ} {a : ℕ → Bool × G} (L : Labeled x y k a) :
    HaarSharpCore.good (segment L.labels 0 k)=true := by
  apply HaarSharpGraph.segment_good
  intro i hi e
  simp only [Nat.zero_add] at e
  apply L.nonbounce i hi
  apply Prod.ext
  · rw [show i+2=i+1+1 by omega,L.steps (i+1), L.steps i]; simp
  · rw [show i+2=i+1+1 by omega,L.edge (i+1),L.edge i,L.steps i,←e]
    cases h : (a i).1 <;> simp [mul_assoc]

theorem product (x y : G) {k : ℕ} {a : ℕ → Bool × G} (L : Labeled x y k a) :
    (a k).2=(a 0).2*prodFrom x y 0 (segment L.labels 0 k) := by
  simpa using segment_product x y (fun i => (a i).2) L.labels 0 0 k (fun i _ => by
    simp only [Nat.zero_add]
    rw [L.edge i,parity x y L]
    have h : i%2=0 ∨ i%2=1 := by omega
    rcases h with h|h <;> simp [signPort,h])


def point (n : ℕ) (hn : 0<n) (i : ℤ) : Fin n :=
  ⟨(i%(n:ℤ)).toNat, by
    have z : (0:ℤ)<n := by exact_mod_cast hn
    have lo := Int.emod_nonneg i z.ne'
    have hi := Int.emod_lt_of_pos i z
    omega⟩

theorem point_cast (n : ℕ) (hn : 0<n) (i : ℤ) :
    ((point n hn i).val : ℤ) = i%(n:ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg i (by exact_mod_cast hn.ne'))

theorem point_next (n : ℕ) (hn : 0<n) (i : ℤ) :
    point n hn (i+1) = ⟨((point n hn i).val+1)%n,Nat.mod_lt _ hn⟩ := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  push_cast
  rw [point_cast,point_cast,Int.emod_add_emod]


theorem point_ne_small (n : ℕ) (hn : 0<n) (i j : ℤ)
    (lo : 0<j-i) (hi : j-i<n) : point n hn i ≠ point n hn j := by
  intro e
  have h : i ≡ j [ZMOD (n:ℤ)] := by
    change i%(n:ℤ) = j%(n:ℤ)
    rw [← point_cast n hn i, ← point_cast n hn j,e]
  have dz := Int.emod_eq_zero_of_dvd h.dvd
  rw [Int.emod_eq_of_lt lo.le hi] at dz
  omega

theorem exists_collision (x y : G) (k : ℕ) (hk : 2≤k) (cycle : HasCycle x y (2*k)) :
    ∃ L R : List (Fin 3), L.length=k ∧ R.length=k ∧
      HaarSharpCore.good L=true ∧ HaarSharpCore.good R=true ∧ L≠R ∧
      prodFrom x y 0 L = prodFrom x y 0 R := by
  obtain ⟨v,inj,edges⟩ := cycle
  let n := 2*k
  have hn : 0<n := by dsimp [n]; omega
  let a (i : ℤ) := v (point n hn i)
  have step (i : ℤ) : haarAdj x y (a i) (a (i+1)) := by
    unfold a
    rw [point_next]
    exact edges _
  let t : ℤ := if (a 0).1 then 1 else 0
  have bt : (a t).1=false := by
    unfold t
    split
    · rename_i b
      have h := (branch x y _ _ (step 0)).1
      simpa [b] using h
    · rename_i b
      simpa using b
  let F (i : ℕ) := a (t+i)
  let R (i : ℕ) := a (t-i)
  have fstep (i : ℕ) : haarAdj x y (F i) (F (i+1)) := by
    simpa [F,add_assoc] using step (t+i)
  have rstep (i : ℕ) : haarAdj x y (R i) (R (i+1)) := by
    apply symmetric
    have e : t-((i:ℤ)+1)+1=t-i := by ring
    simpa only [R,Nat.cast_add,Nat.cast_one,e] using step (t-((i:ℤ)+1))
  have fn (i : ℕ) (_ : i<k-1) : F (i+2)≠F i := by
    intro e
    apply point_ne_small n hn (t+i) (t+(↑(i+2):ℤ)) (by push_cast; omega)
      (by dsimp [n]; omega)
    exact (inj e).symm
  have rn (i : ℕ) (_ : i<k-1) : R (i+2)≠R i := by
    intro e
    apply point_ne_small n hn (t-(↑(i+2):ℤ)) (t-i) (by push_cast; omega)
      (by dsimp [n]; omega)
    exact inj e
  let LF := labeled x y k F (by simpa [F] using bt) fstep fn
  let LR := labeled x y k R (by simpa [R] using bt) rstep rn
  have sameStart : F 0=R 0 := by simp [F,R]
  have sameEnd : F k=R k := by
    apply congrArg v
    apply Fin.ext
    apply Int.ofNat_inj.mp
    rw [point_cast,point_cast]
    have h : t+(k:ℤ)=t-(k:ℤ)+(n:ℤ) := by dsimp [n]; ring
    rw [h,Int.add_emod_right]
  refine ⟨segment LF.labels 0 k,segment LR.labels 0 k,
    HaarSharpGraph.segment_len _ _ _,HaarSharpGraph.segment_len _ _ _,
    good_label x y LF,good_label x y LR,?_,?_⟩
  · intro e
    have eq : LF.labels 0 = LR.labels 0 := by
      cases k with
      | zero => omega
      | succ k => exact (List.cons.inj e).1
    have hF := LF.edge 0
    have hR := LR.edge 0
    rw [sameStart,eq] at hF
    have q : F 1=R 1 := by
      apply Prod.ext
      · rw [LF.steps 0,LR.steps 0,sameStart]
      · exact hF.trans hR.symm
    exact point_ne_small n hn (t-1) (t+1) (by omega)
      (by dsimp [n]; omega) ((inj q).symm)
  · have a := product x y LF
    have b := product x y LR
    rw [sameStart,sameEnd] at a
    exact mul_left_cancel (a.symm.trans b)

end HaarHalfCollision
#print axioms HaarHalfCollision.exists_collision
