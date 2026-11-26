import HaarDerivedWreathTrace

namespace HaarDerivedWreathAllFlow
open HaarDerivedWreathTrace HaarDerivedWreathCore
variable {Q : Type*} [Group Q] [DecidableEq Q]

def oneEdge (x y : Q) (a : Bool × Q) (i j : Fin 3) (q : Q) : ℤ :=
  if i=j then
    if a.1 then if (step x y a i).2=q then -1 else 0
    else if a.2=q then 1 else 0
  else 0

def allFlow (x y : Q) (a : Bool × Q) (tags : List (Fin 3)) (j : Fin 3) (q : Q) : ℤ :=
  match tags with
  | [] => 0
  | i::is => oneEdge x y a i j q + allFlow x y (step x y a i) is j q

def potential (q : Q) (a : Bool × Q) : ℤ := if a.1=false ∧ a.2=q then 1 else 0

theorem edge_gauge (x y : Q) (a : Bool × Q) (i : Fin 3) (q : Q) :
    oneEdge x y a i 0 q+oneEdge x y a i 1 q+oneEdge x y a i 2 q =
      potential q a - potential q (step x y a i) := by
  rcases a with ⟨b,a⟩
  cases b <;> fin_cases i <;> simp [oneEdge,potential,step,basePort,HaarSharpPortGeometry.oriented]
  all_goals (split <;> simp_all)

theorem gauge (x y : Q) (a : Bool × Q) (tags : List (Fin 3)) (q : Q) :
    allFlow x y a tags 0 q+allFlow x y a tags 1 q+allFlow x y a tags 2 q =
      potential q a - potential q (tags.foldl (step x y) a) := by
  induction tags generalizing a with
  | nil => simp [allFlow]
  | cons i is ih =>
    have g := edge_gauge x y a i q
    have g' := ih (step x y a i)
    simp only [allFlow,List.foldl_cons]
    omega

theorem agrees (x y : Q) (a : Bool × Q) (tags : List (Fin 3)) (b : Bool) (q : Q) :
    allFlow x y a tags (if b then 2 else 1) q = walkFlow x y a tags b q := by
  induction tags generalizing a with
  | nil => rfl
  | cons i is ih =>
    rw [allFlow,walkFlow,ih]
    congr 1
    cases b <;> fin_cases i <;> simp [oneEdge,edgeFlow]

theorem fold_proj (x y : Q) (a : Bool × W Q) (tags : List (Fin 3)) :
    proj (tags.foldl (topStep x y) a) = tags.foldl (step x y) (proj a) := by
  induction tags generalizing a with
  | nil => rfl
  | cons i is ih => rw [List.foldl_cons,List.foldl_cons,ih,step_proj]

theorem every_edge_divisible (x y : Q) (a : Bool × W Q) (tags : List (Fin 3))
    (closed : tags.foldl (topStep x y) a=a) (j : Fin 3) (q : Q) :
    (3:ℤ) ∣ allFlow x y (proj a) tags j q := by
  have mod1 : (3:ℤ) ∣ allFlow x y (proj a) tags 1 q := by
    rw [show (1:Fin 3)= (if false then 2 else 1) by rfl,agrees]
    exact closed_mod_flow x y a tags closed false q
  have mod2 : (3:ℤ) ∣ allFlow x y (proj a) tags 2 q := by
    rw [show (2:Fin 3)= (if true then 2 else 1) by rfl,agrees]
    exact closed_mod_flow x y a tags closed true q
  have clos : tags.foldl (step x y) (proj a)=proj a := by
    rw [←fold_proj,closed]
  have z := gauge x y (proj a) tags q
  rw [clos,sub_self] at z
  have mod0 : (3:ℤ) ∣ allFlow x y (proj a) tags 0 q := by
    rw [show allFlow x y (proj a) tags 0 q=-(allFlow x y (proj a) tags 1 q+allFlow x y (proj a) tags 2 q) by omega]
    exact dvd_neg.mpr (dvd_add mod1 mod2)
  fin_cases j
  · exact mod0
  · exact mod1
  · exact mod2

end HaarDerivedWreathAllFlow
#print axioms HaarDerivedWreathAllFlow.every_edge_divisible
