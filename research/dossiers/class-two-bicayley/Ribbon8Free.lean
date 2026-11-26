import Ribbon5LawWords

namespace Ribbon8Free
abbrev Ltr := Fin 4
def flip (p : Ltr) : Ltr := ![1,0,3,2] p
def letter (x y : G) [Group G] (p : Ltr) : G :=
  (![x,x⁻¹,y,y⁻¹] : Fin 4 → G) p

variable {G : Type*} [Group G]
def ev (x y : G) : List Ltr → G
  | [] => 1
  | p::v => letter x y p * ev x y v

def rev (w : List Ltr) : List Ltr := w.reverse.map flip

def reduce : List Ltr → List Ltr
  | [] => []
  | p::ps =>
    match reduce ps with
    | [] => [p]
    | q::qs => if flip p=q then qs else p::q::qs

theorem flip_letter (x y : G) (p : Ltr) : letter x y (flip p) = (letter x y p)⁻¹ := by
  fin_cases p <;> simp [letter,flip]

theorem ev_append (x y : G) (a b : List Ltr) : ev x y (a++b)=ev x y a*ev x y b := by
  induction a with
  | nil => simp [ev]
  | cons p ps ih => simp [ev,ih,mul_assoc]

theorem ev_rev (x y : G) (a : List Ltr) : ev x y (rev a)=(ev x y a)⁻¹ := by
  induction a with
  | nil => simp [rev,ev]
  | cons p ps ih =>
    change ev x y (rev (p::ps)) = (letter x y p * ev x y ps)⁻¹
    rw [show rev (p::ps)=rev ps++[flip p] by simp [rev],ev_append,ih,
      mul_inv_rev]
    simp [ev,flip_letter]

theorem ev_reduce (x y : G) (a : List Ltr) : ev x y (reduce a)=ev x y a := by
  induction a with
  | nil => rfl
  | cons p ps ih =>
    rw [ev,←ih]
    cases E : reduce ps with
    | nil => simp [reduce,E,ev]
    | cons q qs =>
      by_cases H : flip p=q
      · rw [←H]
        simp [reduce,E,←H,ev,flip_letter,←mul_assoc]
      · simp [reduce,E,H,ev]

def encode : Bool → List (Fin 3) → List Ltr
  | _, [] => []
  | s,p::w => if p=2 then encode (!s) w
    else (if s then (if p=0 then 2 else 3) else (if p=0 then 0 else 1)) :: encode s w

theorem ev_encode (x y : G) (w : List (Fin 3)) (s : Bool) :
    ev x y (encode s w)=Ribbon5Law.trace x y s w := by
  induction w generalizing s with
  | nil => rfl
  | cons p w ih =>
    cases s <;> fin_cases p <;>
      simp [encode,Ribbon5Law.trace,ev,letter,ih]

theorem sound (x y : G) (u v : List Ltr) (E : reduce u=reduce v) : ev x y u=ev x y v := by
  rw [←ev_reduce x y u,←ev_reduce x y v,E]

end Ribbon8Free
#print axioms Ribbon8Free.sound
#print axioms Ribbon8Free.ev_encode
