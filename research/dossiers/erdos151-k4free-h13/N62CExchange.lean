import N62PrivateLowCases
import N62SimpleOwner

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13 Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]
variable {S X : Finset V}

theorem c_column_plus_double_impossible (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    {g u x : V} (um : u∈F.marks) (xx : x∈X) (cx : Ccol G S x)
    (gx : Lone G g x) (ux : G u x) (xs : support G S x={g,u}) (gu : DoubleRel G F g u) :
    False := by
  classical
  have own := drel_owners G F gu
  have neq := drel_ne G F gu
  obtain ⟨d,dd,ds⟩ := gu
  let a := F.leaf u
  let P : Finset V := {g,u}
  let Z : Finset V := {x,d,a}
  have al : Lone G u a := (F.leafData u um).2.1
  have gd : Lone G g d := near_double_lone_of_support G F dd (by simp [ds])
  have ud : Lone G u d := near_double_lone_of_support G F dd (by simp [ds])
  have ax : a≠x := by
    intro e
    have h := near_single_support G F sym um
    change support G S a={u} at h
    rw [e,xs] at h
    have hg : g∈({g,u}:Finset V) := by simp
    rw [h,mem_singleton] at hg
    exact neq hg
  have ad : a≠d := by
    intro e
    have h := near_single_support G F sym um
    change support G S a={u} at h
    rw [e,ds] at h
    have hg : g∈({g,u}:Finset V) := by simp
    rw [h,mem_singleton] at hg
    exact neq hg
  have xd : x≠d := by
    intro e
    have l : (ls (G:=G) S x).card=1 := cx.2
    have lg := (mem_ls (G:=G) S x).mpr ⟨own.1,lone_symm G sym gx⟩
    have lu := (mem_ls (G:=G) S x).mpr ⟨own.2,lone_symm G sym (e.symm ▸ ud)⟩
    have p : P⊆ls (G:=G) S x := by simp [P,insert_subset_iff,lg,lu]
    have hc := card_le_card p
    rw [l] at hc
    simp [P,card_insert_of_notMem,neq] at hc
  have pc : P.card=2 := by simp [P,card_insert_of_notMem,neq]
  have zc : Z.card=3 := by simp [Z,card_insert_of_notMem,xd,ax.symm,ad.symm]
  have zX : Z⊆X := by simp [Z,insert_subset_iff,xx,(F.dblData d dd).1,(F.leafData u um).1,a]
  have ps : P⊆S := by simp [P,insert_subset_iff,own.1,own.2]
  have ind : ∀ p∈Z, ∀ q∈Z, ¬G p q := by
    simp only [Z,mem_insert,mem_singleton]
    rintro p (rfl|rfl|rfl) q (rfl|rfl|rfl)
    all_goals first
    | exact irr _
    | exact lone_neighbors_nonadjacent G sym gx gd.1
    | exact lone_neighbors_nonadjacent G sym gd gx.1
    | exact lone_neighbors_nonadjacent G sym al ux
    | exact lone_neighbors_nonadjacent G sym ud al.1
    | exact lone_neighbors_nonadjacent G sym al ud.1
    | exact fun e => lone_neighbors_nonadjacent G sym al ux (sym e)
  have su : ∀ p∈Z, support G S p⊆P := by
    intro p hp
    simp only [Z,mem_insert,mem_singleton] at hp
    rcases hp with rfl|rfl|rfl
    · rw [xs]
    · rw [ds]
    · rw [near_single_support G F sym um]; simp [P]
  have h := independent_supported_count G sym irr S P Z sc ps sf upper
    (out.symm.mono_right zX) ind su
  omega

#print axioms c_column_plus_double_impossible
end Erdos151N62
