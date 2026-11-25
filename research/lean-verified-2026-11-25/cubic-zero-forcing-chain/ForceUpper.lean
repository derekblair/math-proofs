import DomUpper
namespace ZFChain
open Finset
set_option maxHeartbeats 1400000

def zPick {n} (i : Fin (n+2)) : Finset (Fin 8) :=
  if i.val = 0 then {0,1,3,4} else {0,1,4}
theorem zPick_legal {n} (i : Fin (n+2)) (a) (h : a ∈ zPick i) :
    legal (mid i) a := by
  unfold zPick at h
  split at h <;> simp at h
  · rcases h with rfl|rfl|rfl|rfl <;> exact Or.inr (by decide)
  · rcases h with rfl|rfl|rfl <;> exact Or.inr (by decide)

def localStep (m : Bool) (T : Finset (Fin 8)) (p : Fin 8 × Fin 8) : Prop :=
  p.1.val < 6 ∧ p.1 ∈ T ∧ legal m p.2 ∧ localEdge m p.1 p.2 = true ∧
    ∀ z : Fin 8, localEdge m p.1 z = true → z ∈ T ∨ z = p.2
instance (m) (T) (p) : Decidable (localStep m T p) := by unfold localStep; infer_instance

def validPlan (m : Bool) (T : Finset (Fin 8)) : List (Fin 8 × Fin 8) → Prop
  | [] => ∀ a : Fin 8, legal m a → a ∈ T
  | p::ps => localStep m T p ∧ validPlan m (insert p.2 T) ps
instance planDec (m) (T) (ps) : Decidable (validPlan m T ps) := by
  induction ps generalizing T with
  | nil => simp only [validPlan]; infer_instance
  | cons p ps ih =>
    let _ := ih (insert p.2 T)
    simp only [validPlan]
    infer_instance

theorem firstPlan : validPlan false {0,1,3,4} [(1,5),(0,6),(3,2)] := by decide
theorem midPlan : validPlan true {0,1,4,6} [(0,5),(5,2),(2,3),(1,7)] := by decide
theorem lastPlan : validPlan false {0,1,4,6} [(0,5),(1,3),(3,2)] := by decide

def IncludeLocal {n} (B : Finset (V n)) (i : Fin (n+2)) (T : Finset (Fin 8)) : Prop :=
  ∀ a (ha : legal (mid i) a), a ∈ T → lift i a ha ∈ B
def BlockBlue {n} (B : Finset (V n)) (i : Fin (n+2)) : Prop :=
  ∀ v, blk v = i → v ∈ B
theorem blockBlue_mono {n} {B C : Finset (V n)} {i} (h : BlockBlue B i) (hBC : B ⊆ C) :
    BlockBlue C i := fun v hv => hBC (h v hv)
theorem local_mono {n} {B C : Finset (V n)} {i T} (h : IncludeLocal B i T)
    (hBC : B ⊆ C) : IncludeLocal C i T := fun a ha hT => hBC (h a ha hT)

theorem runLocal {n} (i : Fin (n+2)) (S B : Finset (V n)) (hReach : Reach adj S B)
    (T) (ps) (hp : validPlan (mid i) T ps) (hT : IncludeLocal B i T) :
    ∃ C, Reach adj S C ∧ B ⊆ C ∧ BlockBlue C i := by
  induction ps generalizing B T with
  | nil =>
    refine ⟨B, hReach, Subset.rfl, ?_⟩
    intro x hx
    subst i
    rw [← lift_eta x]
    exact hT _ x.property (hp _ x.property)
  | cons p ps ih =>
    rcases hp with ⟨⟨hcore,hpB,hp2,hE,hu⟩,htail⟩
    let x := lift i p.1 (Or.inr (by omega))
    let y := lift i p.2 hp2
    have hx : x ∈ B := hT _ _ hpB
    have extendLocal {C : Finset (V n)} (hBC : B ⊆ C) (hy : y ∈ C) :
        IncludeLocal C i (insert p.2 T) := by
      intro a ha hh
      rcases mem_insert.mp hh with h|h
      · subst a
        exact hy
      · exact hBC (hT _ _ h)
    by_cases hy : y ∈ B
    · exact ih B hReach _ htail (extendLocal Subset.rfl hy)
    · have hforce : CanForce adj B x y := by
        refine ⟨hx,hy,(adj_same (x := x) (y := y) rfl).mpr hE,?_⟩
        intro z hz hzb
        rcases hz with ⟨hz,he⟩|hz
        · rcases hu (wire z) he with h | h
          · have hzi : blk z = i := hz.symm
            have hw : legal (mid i) (wire z) := by rw [← hzi]; exact z.property
            have heq : lift i (wire z) hw = z := vertex_ext hzi.symm rfl
            exact (hzb (heq ▸ hT _ hw h)).elim
          · exact vertex_ext hz.symm h
        · exact (core_not_cross (x := x) hcore hz).elim
      have hsub : B ⊆ insert y B := subset_insert _ _
      obtain ⟨C,hC,hh,hblue⟩ := ih (insert y B) (Reach.step hReach hforce) _ htail
           (extendLocal hsub (mem_insert_self _ _))
      exact ⟨C,hC,hsub.trans hh,hblue⟩

theorem runBridge {n} (e : Fin (n+1)) (S B : Finset (V n)) (hR : Reach adj S B)
    (hB : BlockBlue B e.castSucc) :
    ∃ C, Reach adj S C ∧ B ⊆ C ∧ right e ∈ C := by
  by_cases hr : right e ∈ B
  · exact ⟨B,hR,Subset.rfl,hr⟩
  · have hforce : CanForce adj B (left e) (right e) := by
      refine ⟨hB _ rfl,hr,Or.inr ((cross_left _ _).mpr rfl),?_⟩
      intro z hz hzw
      rcases hz with ⟨hh,_⟩|hh
      · exact (hzw (hB _ hh.symm)).elim
      · exact (cross_left _ _).mp hh
    exact ⟨insert (right e) B,Reach.step hR hforce,subset_insert _ _,mem_insert_self _ _⟩

theorem forceWitness (n : ℕ) : ∃ S : Finset (V n),
    Reach adj S univ ∧ S.card = 3*(n+2)+1 := by
  let S := chooseSet (@zPick n)
  have allSeeds (i : Fin (n+2)) : IncludeLocal S i (zPick i) := by
    intro a ha h
    exact (mem_chooseSet _ _).mpr h
  have ind : ∀ (j : ℕ) (hj : j < n+2), ∃ B : Finset (V n), Reach adj S B ∧
      S ⊆ B ∧ ∀ i : Fin (n+2), i.val ≤ j → BlockBlue B i := by
    intro j
    induction j with
    | zero =>
      intro hj
      let i : Fin (n+2) := ⟨0, hj⟩
      have hm : mid i = false := by simp [mid,i]
      have hp : validPlan (mid i) (zPick i) [(1,5),(0,6),(3,2)] := by
        simpa [mid,zPick,i] using firstPlan
      obtain ⟨B,hB,hSB,hi⟩ := runLocal i S S Reach.zero _ _ hp (allSeeds i)
      refine ⟨B,hB,hSB,?_⟩
      intro q hq
      have eq : q = i := Fin.ext (by change q.val = 0; omega)
      simpa [eq] using hi
    | succ j ih =>
      intro hj
      obtain ⟨B,hB,hSB,hblue⟩ := ih (by omega)
      let e : Fin (n+1) := ⟨j,by omega⟩
      let i : Fin (n+2) := e.succ
      obtain ⟨C,hC,hBC,hport⟩ := runBridge e S B hB (hblue _ (by change j ≤ j; omega))
      have hSeeds : IncludeLocal C i {0,1,4,6} := by
        intro a ha hmem
        by_cases he : a = 6
        · subst a
          exact hport
        · apply hBC
          apply hSB
          apply allSeeds i _ _
          have hh : i.val ≠ 0 := by change j+1 ≠ 0; omega
          simp [zPick,hh] at hmem ⊢
          tauto
      have ex : ∃ D : Finset (V n), Reach adj S D ∧ C ⊆ D ∧ BlockBlue D i := by
        cases hm : mid i
        · exact runLocal i S C hC _ _ (hm ▸ lastPlan) hSeeds
        · exact runLocal i S C hC _ _ (hm ▸ midPlan) hSeeds
      obtain ⟨D,hD,hCD,hDi⟩ := ex
      refine ⟨D,hD,hSB.trans (hBC.trans hCD),?_⟩
      intro q hq
      by_cases hn : q.val ≤ j
      · exact blockBlue_mono (hblue _ hn) (hBC.trans hCD)
      · have he : q = i := Fin.ext (by change q.val = j+1; omega)
        exact he.symm ▸ hDi
  obtain ⟨B,hB,_,hBB⟩ := ind (n+1) (by omega)
  have heq : B = univ := eq_univ_of_forall fun x => hBB (blk x) (by have := (blk x).isLt; omega) x rfl
  refine ⟨S,heq ▸ hB,?_⟩
  rw [card_chooseSet _ zPick_legal]
  have he (i : Fin (n+2)) : (zPick i).card = 3+(if i.val = 0 then 1 else 0) := by
    unfold zPick
    split <;> decide
  simp_rw [he]
  rw [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,Fintype.card_fin,sum_boole]
  have h0 : (univ.filter fun i : Fin (n+2) => i.val = 0) = {0} := by
    ext i
    simp only [mem_filter,mem_univ,true_and,mem_singleton]
    exact ⟨fun h => Fin.ext (by simpa using h),fun h => h ▸ rfl⟩
  rw [h0,card_singleton]
  change (n+2)*3+1 = 3*(n+2)+1
  omega

end ZFChain
