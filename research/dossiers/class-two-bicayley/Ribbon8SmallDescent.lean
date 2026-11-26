import Ribbon8SmallData
import Ribbon7AuxLayers

namespace Ribbon8Small
open Ribbon5Bridge HaarClass4Ports HaarClass4Generate HaarClass4Structure
open scoped commutatorElement
variable {G H : Type*} [Group G] [Group H]

def LowCollision (p : Fin 2) (k : Fin 3) (x y : G) : Prop :=
  ∃ i j : Fin 128, i.val<j.val ∧
    di (rowC k i.val) (rowC k j.val)=0 ∧ dj (rowC k i.val) (rowC k j.val)=0 ∧
    (dc (rowC k i.val) (rowC k j.val)).natAbs=prime p ∧
    pathAt x y (word k) i.val=pathAt x y (word k) j.val

theorem map_path (f : G→*H) (x y : G) (w : Array P) (i : Nat) :
    (fun v : Bool × G => (v.1,f v.2)) (pathAt x y w i) =
      pathAt (f x) (f y) w i := by
  simpa [pathAt,start] using mapped_run f x y (start G) (w.toList.take i)

theorem map_coll (f : G→*H) (p : Fin 2) (k : Fin 3) (x y : G)
    (E : LowCollision p k x y) : LowCollision p k (f x) (f y) := by
  obtain ⟨i,j,a,b,c,d,e⟩ := E
  refine ⟨i,j,a,b,c,d,?_⟩
  rw [←map_path f x y,←map_path f x y,e]

theorem all_collisions_force (p : Fin 2) (x y : G) (nil : LS G 3=⊥)
    (central : ∀ g, Commute ((portC x y)^(prime p)) g)
    (E : ∀ k : Fin 3, LowCollision p k x y) :
    portU x y=1 ∧ portV x y=1 := by
  let u := portU x y
  let v := portV x y
  let c := portC x y
  have U : u^(prime p)=1 := torsion c x u (prime p) (central_u x y nil c) (cx x y nil) (central x)
  have V : v^(prime p)=1 := torsion c y v (prime p) (central_v x y nil c) (cy x y nil) (central y)
  have R (k : Fin 3) :
      c^(prime p)*u^((coefficients p k).1)*v^((coefficients p k).2)=1 := by
    obtain ⟨i,j,h,a,b,d,f⟩ := E k
    exact collision_relation p k x y nil U V i j h a b d f
  have A := R 0
  have B := R 1
  have C := R 2
  change u=1 ∧ v=1
  fin_cases p
  · apply rank5 (c^5) u v U A
    · simpa [coefficients,prime] using B
    · simpa [coefficients,prime] using C
  · apply rank7 (c^7) u v U A
    · simpa [coefficients,prime] using B
    · simpa [coefficients,prime] using C

theorem project_both (p : Fin 2) (x y : G)
    (pow_mem : (portC x y)^(prime p) ∈ LS G 2)
    (E : ∀ k : Fin 3, LowCollision p k x y) :
    portU x y∈LS G 3 ∧ portV x y∈LS G 3 := by
  let N := LS G 3
  let f := QuotientGroup.mk' N
  have nil : LS (G ⧸ N) 3=⊥ := Ribbon7Aux.quotient_nil (G:=G) 3
  have cp : (portC (f x) (f y))^(prime p)∈ LS (G ⧸ N) 2 := by
    have e := Subgroup.mem_map_of_mem f pow_mem
    rw [map_ls f (QuotientGroup.mk'_surjective N) 2] at e
    simpa [portC,map_commutatorElement] using e
  have C : ∀ g, Commute ((portC (f x) (f y))^(prime p)) g := by
    intro g
    exact (Subgroup.mem_center_iff.mp
      ((Subgroup.commutator_top_right_eq_bot_iff_le_center.mp nil) cp) g).symm
  obtain ⟨U,V⟩ := all_collisions_force p (f x) (f y) nil C (fun k => map_coll f p k x y (E k))
  constructor
  · apply (QuotientGroup.eq_one_iff (N:=N) _).mp
    change f (portU x y)=1
    simpa only [portU,portC,map_commutatorElement,map_inv] using U
  · apply (QuotientGroup.eq_one_iff (N:=N) _).mp
    change f (portV x y)=1
    simpa only [portV,portC,map_commutatorElement,map_inv] using V

theorem class_drop (n : ℕ) (nil : LS G n=⊥) (lo : 2≤n) (x y : G) (gen : Generates x y)
    (u : portU x y∈LS G 3) (v : portV x y∈LS G 3) : LS G 2=⊥ := by
  let S := LS G 3
  let f := QuotientGroup.mk' S
  have du : f (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr u
  have dv : f (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr v
  have X : Commute (f (portC x y)) (f x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [portU,map_commutatorElement] using du
  have Y : Commute (f (portC x y)) (f y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [portV,map_commutatorElement] using dv
  have g := map_gen f (QuotientGroup.mk'_surjective S) gen
  have xy : f x*f y=f y*f x*f (portC x y) := by simpa using congrArg f (ports_xy x y)
  have h := c_center_class_two (f x) (f y) (f (portC x y)) g xy (gen_center _ _ _ g X Y)
  have M := map_ls f (QuotientGroup.mk'_surjective S) 2
  rw [h,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at M
  have e : LS G 2=LS G 3 := le_antisymm M
    ((Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)) (by decide : 2≤3))
  have all (j : Nat) : LS G (2+j)=LS G 2 := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change ⁅LS G (2+j),(⊤ : Subgroup G)⁆=LS G 2
      rw [ih]
      exact e.symm
  have F := all (n-2)
  rwa [show 2+(n-2)=n by omega,nil,eq_comm] at F

theorem descent (p : Fin 2) (n : Nat) (nil : LS G n=⊥) (lo : 2≤n)
    (x y : G) (gen : Generates x y) (pow_mem : (portC x y)^(prime p) ∈ LS G 2)
    (E : ∀ k : Fin 3, LowCollision p k x y) : LS G 2=⊥ := by
  obtain ⟨u,v⟩ := project_both p x y pow_mem E
  exact class_drop n nil lo x y gen u v

end Ribbon8Small
#print axioms Ribbon8Small.descent
