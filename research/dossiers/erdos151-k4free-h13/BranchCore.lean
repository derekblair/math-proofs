import RamseySeed53Core

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096

def cut (x : Fin 52) (s : List (Fin 52)) : List (Fin 52) :=
  s.filter (fun y=>decide (x<y) && !adj x y)

lemma forbidden_kids (k : Nat) (s : List (Fin 52))
    (h : ∀ x ∈ s, findIndependent adj k (cut x s)=false) :
    findIndependent adj (k+1) s=false := by
  by_cases hs : s.length<k+1
  · simp [findIndependent,hs]
  · rw [findIndependent,if_neg hs,List.any_eq_false]
    intro x hx hh
    have eq := h x hx
    change findIndependent adj k (cut x s)=true at hh
    rw [eq] at hh
    contradiction

def rowKids (a b : Fin 52) : Bool :=
  let s := cut a (List.finRange 52)
  if b∈s then findIndependent adj 10 (cut b s) else false

def pairKids (a b c : Fin 52) : Bool :=
  let s := cut a (List.finRange 52)
  let t := cut b s
  if b∈s ∧ c∈t then findIndependent adj 9 (cut c t) else false

theorem row_of_kids (a : Fin 52) (h : ∀ b,rowKids a b=false) : rowCheck a=false := by
  apply forbidden_kids
  intro x hx
  change x∈cut a (List.finRange 52) at hx
  change findIndependent adj 10 (cut x (cut a (List.finRange 52)))=false
  simpa [rowKids,hx] using h x

theorem pair_of_kids (a b : Fin 52) (h : ∀ c,pairKids a b c=false) : rowKids a b=false := by
  unfold rowKids
  dsimp
  split
  next e =>
    apply forbidden_kids
    intro x hx
    simpa [pairKids,e,hx] using h x
  next _ => rfl

end Erdos151Ramsey.Seed53
