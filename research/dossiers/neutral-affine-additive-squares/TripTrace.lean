import CutLift
import AffineAddress
import Mathlib.Tactic

namespace TripTrace

open CutLift AffineAddress

structure Triple (w : List ℤ) where
  a : Cut w
  b : Cut w
  c : Cut w

variable {w : List ℤ}

def delta (T : Triple w) : ℤ × ℤ :=
  σ T.a.head + σ T.c.head - (σ T.b.head + σ T.b.head)

structure Offset (f : ℤ → List ℤ) (T : Triple w) where
  a : Cut (f T.a.letter)
  b : Cut (f T.b.letter)
  c : Cut (f T.c.letter)

def desc (f : ℤ → List ℤ) (T : Triple w) (D : Offset f T) : Triple (w.flatMap f) :=
  ⟨lift f T.a D.a, lift f T.b D.b, lift f T.c D.c⟩

theorem desc_delta (f : ℤ → List ℤ) (A : (ℤ×ℤ) →+ (ℤ×ℤ))
    (aff : ∀ x, σ (f x)=A (σ [x])) (T : Triple w) (D : Offset f T) :
    delta (desc f T D) = A (delta T) + (σ D.a.head + σ D.c.head - (σ D.b.head + σ D.b.head)) := by
  simp only [delta,desc,lift,sig_append,sig_exp f A aff]
  exact diff_step _ _ _ _ _ _ _

theorem exists_ancestor (f : ℤ → List ℤ) (U : Triple (w.flatMap f)) :
    ∃ (T : Triple w) (D : Offset f T), desc f T D = U := by
  obtain ⟨X,a,ha⟩ := unlift f U.a
  obtain ⟨Y,b,hb⟩ := unlift f U.b
  obtain ⟨Z,c,hc⟩ := unlift f U.c
  refine ⟨⟨X,Y,Z⟩,⟨a,b,c⟩,?_⟩
  cases U
  unfold desc at *
  congr

def iter (f : ℤ → List ℤ) (a : ℤ) : ℕ → List ℤ
  | 0 => [a]
  | n+1 => (iter f a n).flatMap f

def rootCut (a : ℤ) : Cut [a] := ⟨[],a,[],rfl⟩

def root (a : ℤ) : Triple [a] := ⟨rootCut a,rootCut a,rootCut a⟩

inductive FromRoot (f : ℤ → List ℤ) (a : ℤ) : (n : ℕ) → Triple (iter f a n) → Prop
  | base : FromRoot f a 0 (root a)
  | grow {n} (T : Triple (iter f a n)) (d : Offset f T) :
      FromRoot f a n T → FromRoot f a (n+1) (desc f T d)

theorem every_representable (f : ℤ → List ℤ) (a : ℤ) (n : ℕ)
    (T : Triple (iter f a n)) : FromRoot f a n T := by
  induction n with
  | zero =>
    suffices eq : T=root a by rw [eq]; exact .base
    have r : ∀ U : Cut [a], U=rootCut a := by
      intro U
      apply unique_pos
      change U.head.length = 0
      have h := congrArg List.length U.decomp
      simp only [List.length_cons,List.length_nil,List.length_append] at h
      omega
    cases T with
    | mk x y z =>
      change Triple.mk x y z = Triple.mk (rootCut a) (rootCut a) (rootCut a)
      rw [r x,r y,r z] <;> rfl
  | succ n ih =>
    obtain ⟨U,d,e⟩ := exists_ancestor f T
    rw [← e]
    exact .grow U d (ih U)

theorem actual_square (T : Triple w) (ab : idx T.a < idx T.b)
    (bc : idx T.b < idx T.c) (zero : delta T=0) :
    ∃ u v r s : List ℤ, w=u++v++r++s ∧
        0<v.length ∧ v.length=r.length ∧ v.sum=r.sum ∧ s ≠ [] := by
  have preA : T.a.head <+: T.b.head := by
    rw [← pre_eq T.a,← pre_eq T.b]
    exact List.take_prefix_take_left ab.le
  have preB : T.b.head <+: T.c.head := by
    rw [← pre_eq T.b,← pre_eq T.c]
    exact List.take_prefix_take_left bc.le
  obtain ⟨v,hv⟩ := preA
  obtain ⟨r,hr⟩ := preB
  have z := (diff_zero_iff T.a.head T.b.head T.c.head).mp zero
  have hlen : v.length=r.length := by
    have q := z.1
    rw [←hr,←hv] at q
    simp only [List.length_append, Nat.cast_add] at q
    omega
  have hs : v.sum=r.sum := by
    have q := z.2
    rw [←hr,←hv] at q
    simp only [List.sum_append] at q
    omega
  have hp : 0<v.length := by
    change T.a.head.length<T.b.head.length at ab
    rw [←hv,List.length_append] at ab
    omega
  refine ⟨T.a.head,v,r,T.c.letter::T.c.tail,?_,hp,hlen,hs,by simp⟩
  calc
    w = T.c.head ++ T.c.letter::T.c.tail := T.c.decomp
    _ = _ := by rw [←hr,←hv]

theorem from_square (u v r s : List ℤ) (e : w=u++v++r++s)
    (hp : 0<v.length) (hl : v.length=r.length) (hs : v.sum=r.sum)
    (ne : s ≠ []) :
    ∃ T : Triple w, idx T.a < idx T.b ∧ idx T.b < idx T.c ∧ delta T=0 := by
  cases v with
  | nil => simp at hp
  | cons a v =>
    cases r with
    | nil => simp at hl
    | cons b r =>
      cases s with
      | nil => contradiction
      | cons c s =>
        let U : Cut w := ⟨u,a,v++b::r++c::s,by simpa [List.append_assoc] using e⟩
        let V : Cut w := ⟨u++a::v,b,r++c::s,by simpa [List.append_assoc] using e⟩
        let W : Cut w := ⟨u++a::v++b::r,c,s,e⟩
        refine ⟨⟨U,V,W⟩, ?_, ?_, ?_⟩
        · simp [idx,U,V]
        · simp [idx,V,W]
        · apply (diff_zero_iff _ _ _).mpr
          constructor
          · simp only [U,V,W,List.length_append,Nat.cast_add]
            omega
          · simp only [U,V,W,List.sum_append]
            omega

end TripTrace

#print axioms TripTrace.desc_delta
#print axioms TripTrace.every_representable

#print axioms TripTrace.actual_square

#print axioms TripTrace.from_square
