import RibbonSchreierCollect

namespace RibbonSchreierCollect
open scoped commutatorElement
variable {G : Type*} [Group G]

def evalSigned {A : Type*} (g : A→G) (w : List (A×Bool)) : G :=
  (w.map (fun a => sgn (g a.1) a.2)).prod

def reduceSigned {A : Type*} [DecidableEq A] : List (A×Bool)→List (A×Bool)
  | [] => []
  | a::t =>
    match reduceSigned t with
    | [] => [a]
    | b::w => if a.1=b.1 ∧ a.2≠b.2 then w else a::b::w

theorem reduce_sound {A : Type*} [DecidableEq A] (g : A→G) (w : List (A×Bool)) :
    evalSigned g (reduceSigned w)=evalSigned g w := by
  induction w with
  | nil => rfl
  | cons a t ih =>
    change evalSigned g (reduceSigned (a::t))=sgn (g a.1) a.2*evalSigned g t
    rw [←ih]
    cases e : reduceSigned t with
    | nil => simp [reduceSigned,e,evalSigned]
    | cons b z =>
      by_cases h : a.1=b.1 ∧ a.2≠b.2
      · have E : sgn (g a.1) a.2*sgn (g b.1) b.2=1 := by
          rw [h.1]
          have H := h.2
          cases ea : a.2 <;> cases eb : b.2 <;> simp_all [sgn]
        simp only [reduceSigned,e,if_pos h,evalSigned,List.map_cons,List.prod_cons]
        rw [←mul_assoc,E,one_mul]
      · simp [reduceSigned,e,h,evalSigned]

def commLE (a b : Com) : Prop := a.1.1<b.1.1 ∨ a.1.1=b.1.1 ∧ a.1.2≤b.1.2
instance (a b : Com) : Decidable (commLE a b) := by unfold commLE; infer_instance

def insertC (a : Com) : List Com→List Com
  | [] => [a]
  | b::w => if commLE a b then a::b::w else b::insertC a w

def sortC : List Com→List Com
  | [] => []
  | a::w => insertC a (sortC w)

theorem insertC_sound (c : Central₂ G) (g : Nat→G) (a : Com) (w : List Com) :
    evalC g (insertC a w)=cs g a*evalC g w := by
  induction w with
  | nil => simp [insertC,evalC]
  | cons b w ih =>
    by_cases H : commLE a b
    · simp [insertC,H,evalC]
    · simp only [insertC,if_neg H]
      change cs g b*evalC g (insertC a w)=cs g a*(cs g b*evalC g w)
      rw [ih,←mul_assoc,←mul_assoc,(central_cs c g a (cs g b)).eq]

theorem sortC_sound (c : Central₂ G) (g : Nat→G) (w : List Com) :
    evalC g (sortC w)=evalC g w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change evalC g (insertC a (sortC w))=cs g a*evalC g w
    rw [insertC_sound c,ih]

def normal (w : List Letter) : List Letter × List Com :=
  let (base,comm) := collect w
  (reduceSigned base,reduceSigned (sortC comm))

theorem normal_sound (c : Central₂ G) (g : Nat→G) (w : List Letter) :
    evalL g w=evalL g (normal w).1*evalC g (normal w).2 := by
  have a := reduce_sound g (collect w).1
  have b := reduce_sound (fun p : Nat×Nat => ⁅g p.1,g p.2⁆) (sortC (collect w).2)
  change evalL g (reduceSigned (collect w).1)=evalL g (collect w).1 at a
  change evalC g (reduceSigned (sortC (collect w).2))=evalC g (sortC (collect w).2) at b
  change evalL g w=evalL g (reduceSigned (collect w).1)*evalC g (reduceSigned (sortC (collect w).2))
  rw [a,b,sortC_sound c]
  exact collected c g w

theorem same_normal (c : Central₂ G) (g : Nat→G) (u v : List Letter)
    (e : normal u=normal v) : evalL g u=evalL g v := by
  rw [normal_sound c g u,normal_sound c g v,e]

end RibbonSchreierCollect
#print axioms RibbonSchreierCollect.same_normal
