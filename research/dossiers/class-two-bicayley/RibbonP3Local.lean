import RibbonP3Cycle
import RibbonP3Structure

namespace RibbonP3
open Ribbon5Bridge HaarClass4Structure HaarClass4Generate HaarClass4Ports
open scoped commutatorElement
variable {G H Q : Type*} [Group G] [Group H] [Group Q]

private theorem residue_rep (z : ZMod 3) :
    ∃ t : Fin 3, ((t.val:ℤ):ZMod 3)=z := by
  exact ⟨⟨z.val,ZMod.val_lt z⟩,by push_cast; exact ZMod.natCast_zmod_val z⟩

theorem local_p3 (nil : LS G 5=⊥) (x y : G) (p : G →* H) (f : H →* Q)
    (nilH : LS H 3=⊥) (genH : Generates (p x) (p y))
    (ker : f.ker = LS H 2)
    (ord : orderOf (f (portC (p x) (p y)))=3)
    (nz : portU (p x) (p y)≠1) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
  let X := p x
  let Y := p y
  let c := portC X Y
  let u := portU X Y
  let v := portV X Y
  have cu : u ∈ LS H 2 := layer_u X Y
  have cv : v ∈ LS H 2 := layer_v X Y
  have c3 : c^3 ∈ LS H 2 := by
    rw [←ker]
    change f (c^3)=1
    rw [map_pow,←ord,pow_orderOf_eq_one]
  obtain ⟨χ,fu⟩ := char_exists nilH X Y genH c3 nz
  obtain ⟨q,hq⟩ := residue_rep (Multiplicative.toAdd (χ ⟨v,cv⟩))
  obtain ⟨t,ht⟩ := residue_rep (Multiplicative.toAdd (χ ⟨c^3,c3⟩))
  have Fc : χ ⟨c^3,c3⟩ = Multiplicative.ofAdd ((t.val:ℤ):ZMod 3) := congrArg Multiplicative.ofAdd ht.symm
  have Fv : χ ⟨v,cv⟩ = Multiplicative.ofAdd ((q.val:ℤ):ZMod 3) := congrArg Multiplicative.ofAdd hq.symm
  have kill (z : H) (hz : z ∈ LS H 2) : f z=1 := by
    rw [←ker] at hz
    exact hz
  have cx : Commute (f c) (f X) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [u,portU,map_commutatorElement] using kill u cu
  have cy : Commute (f c) (f Y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [v,portV,map_commutatorElement] using kill v cv
  have xy : f X*f Y=f Y*f X*f c := by simpa only [map_mul] using congrArg f (ports_xy X Y)
  apply ribbon_cycle x y t nil
  intro i j e
  have projected (i : Fin 64) :
    (fun s : Bool × G => (s.1,p s.2)) (vertAt x y t i) =
      ((row t i).rim, eval X Y c u v (row t i)) := by
    unfold vertAt
    rw [mapped_run]
    have h : ((start G).1,p (start G).2) = start H := by simp [start]
    rw [h]
    exact projected_wordAt (class3_ports nilH X Y) t i
  have E := (projected i).symm.trans ((congrArg (fun s : Bool × G => (s.1,p s.2)) e).trans (projected j))
  apply collision_rep q t i j
  exact key_sound f X Y c u v cx cy xy ord (kill u cu) (kill v cv)
    (LS H 2) c3 cu cv χ q t Fc fu Fv i j (congrArg Prod.fst E) (congrArg Prod.snd E)

end RibbonP3
#print axioms RibbonP3.local_p3
