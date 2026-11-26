import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Tactic

namespace SemilinearWords
variable {G : Type*} [AddCommMonoid G] [DecidableEq G]
open AddSubmonoid

structure Lin (G : Type*) where
  b : G
  p : Finset G

def vec (L : Lin G) : Set G := {x | ∃ q∈closure (L.p : Set G), L.b+q=x}
def sem (L : List (Lin G)) : Set G := {x | ∃ l∈L, x∈vec l}

def one (x : G) : Lin G := ⟨x,∅⟩
def both (a b : Lin G) : Lin G := ⟨a.b+b.b,a.p∪b.p⟩
def cross (a b : List (Lin G)) : List (Lin G) :=
  a.flatMap (fun x => b.map (both x))
def pump (l : Lin G) : List (Lin G) := [one 0,⟨l.b,insert l.b l.p⟩]
def star : List (Lin G) → List (Lin G)
  | [] => [one 0]
  | l::Ls => cross (pump l) (star Ls)

theorem one_eq (x : G) : vec (one x) = {x} := by
  ext y
  change (∃ q ∈ closure ((∅ : Finset G) : Set G), x+q=y) ↔ y=x
  simp [eq_comm]

theorem both_iff (a b : Lin G) (x : G) :
    x∈vec (both a b) ↔ ∃ y∈vec a, ∃ z∈vec b, y+z=x := by
  change (∃ q ∈ closure ((a.p∪b.p : Finset G) : Set G), (a.b+b.b)+q=x) ↔ _
  rw [Finset.coe_union,AddSubmonoid.closure_union]
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨p,hp,t,ht,rfl⟩ := AddSubmonoid.mem_sup.mp hq
    exact ⟨a.b+p,⟨p,hp,rfl⟩,b.b+t,⟨t,ht,rfl⟩,by ac_rfl⟩
  · rintro ⟨y,⟨p,hp,rfl⟩,z,⟨q,hq,rfl⟩,rfl⟩
    exact ⟨p+q,AddSubmonoid.mem_sup.mpr ⟨p,hp,q,hq,rfl⟩,by ac_rfl⟩

theorem cross_iff (a b : List (Lin G)) (x : G) :
    x∈sem (cross a b) ↔ ∃ y∈sem a, ∃ z∈sem b, y+z=x := by
  change (∃ l∈cross a b, x∈vec l) ↔ _
  constructor
  · rintro ⟨l,hl,hx⟩
    obtain ⟨p,hp,ht⟩ := List.mem_flatMap.mp hl
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ht
    obtain ⟨y,hy,z,hz,eq⟩ := (both_iff p q x).mp hx
    exact ⟨y,⟨p,hp,hy⟩,z,⟨q,hq,hz⟩,eq⟩
  · rintro ⟨y,⟨p,hp,hy⟩,z,⟨q,hq,hz⟩,rfl⟩
    exact ⟨both p q,List.mem_flatMap.mpr ⟨p,hp,List.mem_map.mpr ⟨q,hq,rfl⟩⟩,
      (both_iff p q _).mpr ⟨y,hy,z,hz,rfl⟩⟩

theorem pump_iff (a : Lin G) (x : G) :
    x∈sem (pump a) ↔ x∈closure (vec a) := by
  let P := closure (a.p : Set G)
  let Q := closure ((insert a.b a.p : Finset G) : Set G)
  have qP : P ≤ Q := closure_mono (by intro w hw; exact Finset.mem_insert_of_mem hw)
  have ab : a.b∈Q := subset_closure (Finset.mem_insert_self _ _)
  have hard : x∈sem (pump a) ↔ x=0 ∨ ∃ y∈Q, a.b+y=x := by
    change (∃ q ∈ [one 0,⟨a.b,insert a.b a.p⟩], x∈vec q) ↔ _
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    constructor
    · rintro ⟨q,(rfl|rfl),hx⟩
      · rw [one_eq] at hx; exact Or.inl hx
      · exact Or.inr hx
    · rintro (rfl|⟨q,hq,rfl⟩)
      · exact ⟨one 0,Or.inl rfl,by rw [one_eq]; exact rfl⟩
      · exact ⟨_,Or.inr rfl,⟨q,hq,rfl⟩⟩
  rw [hard]
  clear hard
  constructor
  · rintro (rfl|⟨v,hv,rfl⟩)
    · exact zero_mem _
    · change v ∈ closure ((insert a.b a.p : Finset G) : Set G) at hv
      rw [Finset.coe_insert,Set.insert_eq,AddSubmonoid.closure_union,mem_sup] at hv
      obtain ⟨p,hp,q,hq,rfl⟩ := hv
      obtain ⟨n,rfl⟩ := mem_closure_singleton.mp hp
      have h1 : a.b+q∈closure (vec a) := subset_closure ⟨q,hq,rfl⟩
      have h2 : a.b∈closure (vec a) := subset_closure ⟨0,zero_mem _,add_zero _⟩
      have h3 := add_mem h1 (nsmul_mem h2 n)
      convert h3 using 1 <;> ac_rfl
  · intro h
    induction h using AddSubmonoid.closure_induction with
    | mem x h =>
      obtain ⟨q,hq,rfl⟩ := h
      exact Or.inr ⟨q,qP hq,rfl⟩
    | zero => exact Or.inl rfl
    | add x y hx hy ih ih' =>
      rcases ih with rfl | ⟨u,hu,rfl⟩
      · simpa using ih'
      · rcases ih' with rfl | ⟨v,hv,rfl⟩
        · exact Or.inr ⟨u,hu,by simp⟩
        · exact Or.inr ⟨u+(a.b+v),add_mem hu (add_mem ab hv),by abel⟩

theorem star_iff (L : List (Lin G)) (x : G) :
    x∈sem (star L) ↔ x∈closure (sem L) := by
  induction L generalizing x with
  | nil =>
    have e : sem ([] : List (Lin G)) = ∅ := by ext; simp [sem]
    rw [e,AddSubmonoid.closure_empty]
    simp [star,sem,one_eq]
  | cons a L ih =>
    have e : sem (a::L)=vec a ∪ sem L := by
      ext y
      change (∃ l∈a::L, y∈vec l) ↔ y∈vec a ∪ sem L
      simp only [List.mem_cons,Set.mem_union]
      constructor
      · rintro ⟨l,(rfl|h),hy⟩
        · exact Or.inl hy
        · exact Or.inr ⟨l,h,hy⟩
      · rintro (h|⟨l,hl,h⟩)
        · exact ⟨a,Or.inl rfl,h⟩
        · exact ⟨l,Or.inr hl,h⟩
    rw [e,AddSubmonoid.closure_union,mem_sup]
    simp only [star,cross_iff,ih,pump_iff]

end SemilinearWords

#print axioms SemilinearWords.pump_iff
#print axioms SemilinearWords.star_iff
