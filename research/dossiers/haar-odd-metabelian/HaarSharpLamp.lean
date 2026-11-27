import HaarAllNoncommuting
import Mathlib.Data.ZMod.Basic

namespace HaarSharpLamp
abbrev S := ZMod 7
abbrev L := Bool → S → ZMod 3

structure G where
  left : L
  right : S

@[ext] theorem G.ext' {a b : G} (hl : ∀ t j, a.left t j = b.left t j)
    (hr : a.right = b.right) : a = b := by
  cases a; cases b; congr; funext t j; exact hl t j

def mul (a b : G) : G :=
  ⟨fun t j => a.left t j + b.left t (j-a.right), a.right+b.right⟩

def unit : G := ⟨fun _ _ => 0,0⟩

def inv (a : G) : G := ⟨fun t j => -(a.left t (j+a.right)), -a.right⟩

instance : Group G where
  mul := mul
  one := unit
  inv := inv
  mul_assoc := by
    intro a b c
    apply G.ext'
    · intro t j; change (mul (mul a b) c).left t j = (mul a (mul b c)).left t j
      simp [mul,sub_sub,add_assoc]
    · change (mul (mul a b) c).right = (mul a (mul b c)).right
      simp [mul,add_assoc]
  one_mul := by
    intro a; apply G.ext'
    · intro t j; change (mul unit a).left t j = a.left t j; simp [mul,unit]
    · change (mul unit a).right = a.right; simp [mul,unit]
  mul_one := by
    intro a; apply G.ext'
    · intro t j; change (mul a unit).left t j = a.left t j; simp [mul,unit]
    · change (mul a unit).right = a.right; simp [mul,unit]
  inv_mul_cancel := by
    intro a; apply G.ext'
    · intro t j; change (mul (inv a) a).left t j = unit.left t j
      simp [mul,inv,unit,sub_neg_eq_add]
    · change (mul (inv a) a).right = unit.right
      simp [mul,inv,unit]

def lamp (b : Bool) : L := fun c j => if b = c ∧ j = 0 then 1 else 0

def port : Fin 3 → G := fun c =>
  if c = 0 then 1 else if c = 1 then ⟨lamp false,1⟩ else ⟨lamp true,2⟩

def x : G := port 1
def y : G := port 2

def key (a : G) : Nat :=
  (List.ofFn (fun j : Fin 7 => (a.left false (j.val : S)).val) ++
    List.ofFn (fun j : Fin 7 => (a.left true (j.val : S)).val)).foldl
      (fun acc q => 3*acc+q) a.right.val

def value : Bool → List (Fin 3) → G
  | _, [] => 1
  | f, j::js => (if f then port j else (port j)⁻¹) * value (!f) js

def words : Nat → Option (Fin 3) → List (List (Fin 3))
  | 0, _ => [[]]
  | n+1, p => ([0,1,2] : List (Fin 3)).flatMap fun j =>
      if p = some j then [] else (words n (some j)).map (j :: ·)


end HaarSharpLamp

namespace HaarSharpLamp
structure Row where
  k : Nat
  first : Option (Fin 3)
  last : Option (Fin 3)

def row (w : List (Fin 3)) : Row :=
  ⟨key (value true w), w.head?, w.getLast?⟩

def compatible (a b : Row) : Prop :=
  a.k ≠ b.k ∨ a.first = b.first ∨ a.last = b.last
instance (a b : Row) : Decidable (compatible a b) := by unfold compatible; infer_instance

def scan : List Row → Bool
  | a::b::c::xs => decide (compatible a b ∧ a.k < c.k) && scan (b::c::xs)
  | [a,b] => decide (compatible a b)
  | _ => true

theorem scan_good (xs : List Row) (h : scan xs = true)
    (sorted : xs.Pairwise (fun a b => a.k ≤ b.k)) : xs.Pairwise compatible := by
  induction xs with
  | nil => simp
  | cons a tail ih =>
    cases tail with
    | nil => simp
    | cons b tail =>
      cases tail with
      | nil => simpa [scan] using h
      | cons c tail =>
        simp only [scan, Bool.and_eq_true, decide_eq_true_eq] at h
        rw [List.pairwise_cons] at sorted ⊢
        refine ⟨?_, ih h.2 sorted.2⟩
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact h.1.1
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Or.inl (ne_of_lt h.1.2)
        exact Or.inl (ne_of_lt (lt_of_lt_of_le h.1.2
          ((List.pairwise_cons.mp (List.pairwise_cons.mp sorted.2).2).1 d hd)))

theorem compat_members {xs : List Row} (pw : xs.Pairwise compatible)
    {a b : Row} (ha : a ∈ xs) (hb : b ∈ xs) : compatible a b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨ph,pt⟩ := List.pairwise_cons.mp pw
    rcases List.mem_cons.mp ha with e | ha
    · rcases List.mem_cons.mp hb with f | hb
      · subst a; subst b; exact Or.inr (Or.inl rfl)
      · subst a; exact ph _ hb
    · rcases List.mem_cons.mp hb with f | hb
      · subst b
        have e := ph a ha
        rcases e with e | e | e
        · exact Or.inl (Ne.symm e)
        · exact Or.inr (Or.inl e.symm)
        · exact Or.inr (Or.inr e.symm)
      · exact ih pt ha hb

def rankLe (a b : Row) : Prop := a.k ≤ b.k
instance (a b : Row) : Decidable (rankLe a b) := by unfold rankLe; infer_instance
instance : Std.Total rankLe := ⟨fun a b => Nat.le_total a.k b.k⟩
instance : IsTrans Row rankLe := ⟨fun _ _ _ => Nat.le_trans⟩
def table (n : Nat) := List.insertionSort rankLe ((words n none).map row)

theorem cert_sound {n : Nat} (ok : scan (table n) = true) {u v : List (Fin 3)}
    (hu : u ∈ words n none) (hv : v ∈ words n none) (he : value true u = value true v) :
    u.head? = v.head? ∨ u.getLast? = v.getLast? := by
  have sorted : (table n).Pairwise (fun a b => a.k ≤ b.k) := by
    unfold table
    exact List.pairwise_insertionSort rankLe _
  have mem (w : List (Fin 3)) (hw : w ∈ words n none) : row w ∈ table n :=
    (List.perm_insertionSort _ _).mem_iff.mpr (List.mem_map.mpr ⟨w,hw,rfl⟩)
  have c := compat_members (scan_good _ ok sorted) (mem _ hu) (mem _ hv)
  simpa [compatible,row,he] using c


set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem check2 : scan (table 2) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem check4 : scan (table 4) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem check8 : scan (table 8) = true := by decide +kernel
end HaarSharpLamp
