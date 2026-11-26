import RibbonClass4Core
namespace RibbonClass4
open HaarClass4Table HaarClass4Normal HaarClass4Projection RibbonClass4Data
variable {G H : Type*} [Group G] [Group H]
private def side (n : Nat) : Bool := decide ((n/2)%2=1)

private def walk (M : Data G) (sel : Fin 3) (n : Nat) : Bool×G :=
  (side n,eval M (row (pick sel) ((n+1)/2)))

private theorem walk_step (M : Data G) (sel : Fin 3) (n : Nat) (hn : n<64) :
    Ribbon.Adj M.x M.y (walk M sel n) (walk M sel (n+1)) := by
  let t := n/2
  by_cases E : n%2=0
  · have f : (n+1)/2=t := by dsimp [t]; omega
    have g : (n+1+1)/2=t+1 := by dsimp [t]; omega
    have s : (n+1)/2%2=n/2%2 := by rw [f]
    have Q := eval_step M sel t (by dsimp [t]; omega)
    change Ribbon.Adj M.x M.y (side n,eval M (row (pick sel) ((n+1)/2)))
      (side (n+1),eval M (row (pick sel) ((n+1+1)/2)))
    rw [f,g]
    by_cases even : t%2=0
    · have ss : side n=false := by simp [side,←show t=n/2 from rfl,even]
      have tt : side (n+1)=false := by simp [side,f,even]
      left
      refine ⟨ss,tt,?_⟩
      by_cases sign : signs (pick sel) t
      · exact Or.inl (by simpa [even,sign] using Q.symm)
      · exact Or.inr (by rw [Q,ite_eq_right sign,ite_eq_left even,mul_assoc,inv_mul_cancel,mul_one])
    · have hodd : t%2=1 := by omega
      have ss : side n=true := by simp [side,←show t=n/2 from rfl,hodd]
      have tt : side (n+1)=true := by simp [side,f,hodd]
      right; left
      refine ⟨ss,tt,?_⟩
      by_cases sign : signs (pick sel) t
      · exact Or.inl (by simpa [even,sign] using Q.symm)
      · exact Or.inr (by rw [Q,ite_eq_right sign,ite_eq_right even,mul_assoc,inv_mul_cancel,mul_one])
  · have e : (n+1+1)/2=(n+1)/2 := by omega
    have f : (n+1)/2=t+1 := by dsimp [t]; omega
    right; right
    refine ⟨?_,congrArg (fun j => eval M (row (pick sel) j)) e.symm⟩
    change decide ((n/2)%2=1) ≠ decide (((n+1)/2)%2=1)
    rw [f]
    change decide (t%2=1) ≠ decide ((t+1)%2=1)
    by_cases h : t%2=1
    · simp [h,show (t+1)%2≠1 by omega]
    · simp [h,show (t+1)%2=1 by omega]

def wrap (i : Fin 64) : Fin 32 := ⟨((i.val+1)/2)%32,Nat.mod_lt _ (by decide)⟩

private theorem geometry : ∀ r s : Fin 64, side r.val=side s.val → wrap r=wrap s → r=s :=
  by decide +kernel

private theorem normalization (sel : Fin 3) (i : Fin 64) :
    row (pick sel) ((i.val+1)/2) = P (pick sel) (wrap i) := by
  change row (pick sel) ((i.val+1)/2) = row (pick sel) (((i.val+1)/2)%32)
  by_cases hi : (i.val+1)/2<32
  · rw [Nat.mod_eq_of_lt hi]
  · have e : (i.val+1)/2=32 := by omega
    rw [e,Nat.mod_self,closed sel]
    rfl

theorem cycle64 (M : Data G) (φ : G →* H) (k : KillsMid M φ)
    (good : rootGood (φ M.c)) (sel : Fin 3) (h : target M sel≠1) :
    Ribbon.Cycle M.x M.y 64 := by
  let f : Fin 64 → Bool×G := fun i => walk M sel i.val
  refine ⟨f,?_,?_⟩
  · intro r s E
    apply geometry r s (congrArg Prod.fst E)
    apply inject_rows M φ k good sel h
    have F : eval M (row (pick sel) ((r.val+1)/2)) =
        eval M (row (pick sel) ((s.val+1)/2)) := congrArg Prod.snd E
    rw [normalization,normalization] at F
    exact F
  · intro i
    have F := walk_step M sel i.val i.isLt
    change Ribbon.Adj M.x M.y (walk M sel i.val) (walk M sel ((i.val+1)%64))
    by_cases E : i.val+1<64
    · simpa [Nat.mod_eq_of_lt E] using F
    · have H : i.val+1=64 := by omega
      have K : walk M sel 64=walk M sel 0 := by
        apply Prod.ext
        · rfl
        · change eval M (row (pick sel) 32)=eval M (row (pick sel) 0)
          rw [closed sel]
          rfl
      rw [H,Nat.mod_self]
      rwa [H,K] at F

end RibbonClass4
#print axioms RibbonClass4.cycle64
