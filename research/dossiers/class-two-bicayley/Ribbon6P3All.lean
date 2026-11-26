import Ribbon6P3Transport
import RibbonP3Structure

namespace Ribbon6
open Ribbon5Bridge RibbonP3 HaarClass4Structure HaarClass4Generate HaarClass4Ports
open scoped commutatorElement
variable {G H Q : Type*} [Group G] [Group H] [Group Q]

private theorem residue_rep (z : ZMod 3) :
    ∃ t : Fin 3, ((t.val:ℤ):ZMod 3)=z := by
  exact ⟨⟨z.val,ZMod.val_lt z⟩,by push_cast; exact ZMod.natCast_zmod_val z⟩

private theorem neg_rep (q : Fin 3) :
    (((-q).val:ℤ):ZMod 3)= -((q.val:ℤ):ZMod 3) := by fin_cases q <;> decide

private theorem kill_of_ker (f : H →* Q) (ker : f.ker=LS H 2) (a : H)
    (m : a∈LS H 2) : f a=1 := by rw [←ker] at m; exact m

private theorem keys (x y : G) (p : G →* H) (f : H →* Q)
    (nilH : LS H 3=⊥) (ker : f.ker=LS H 2)
    (ord : orderOf (f (portC (p x) (p y)))=3)
    (c3 : (portC (p x) (p y))^3 ∈ LS H 2)
    (χ : LS H 2 →* Multiplicative (ZMod 3)) (q t : Fin 3)
    (Fc : χ ⟨(portC (p x) (p y))^3,c3⟩ = Multiplicative.ofAdd ((t.val:ℤ):ZMod 3))
    (Fu : χ ⟨portU (p x) (p y),layer_u _ _⟩ = Multiplicative.ofAdd (1:ZMod 3))
    (Fv : χ ⟨portV (p x) (p y),layer_v _ _⟩ = Multiplicative.ofAdd ((q.val:ℤ):ZMod 3))
    (i j : Fin 64) (e : pathAt x y wc i.val=pathAt x y wc j.val) :
    pkey q t i=pkey q t j := by
  let X := p x
  let Y := p y
  let c := portC X Y
  let u := portU X Y
  let v := portV X Y
  have ku := kill_of_ker f ker u (layer_u X Y)
  have kv := kill_of_ker f ker v (layer_v X Y)
  have cx : Commute (f c) (f X) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [u,portU,map_commutatorElement] using ku
  have cy : Commute (f c) (f Y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [v,portV,map_commutatorElement] using kv
  have xy : f X*f Y=f Y*f X*f c := by simpa only [map_mul] using congrArg f (ports_xy X Y)
  have cl := class3_ports nilH X Y
  have E := (eval_prow p x y c u v cl i).symm.trans
    ((congrArg (fun s : Bool×G => (s.1,p s.2)) e).trans (eval_prow p x y c u v cl j))
  exact key_sound f X Y c u v cx cy xy ord ku kv (LS H 2) c3
    (layer_u X Y) (layer_v X Y) χ q t Fc Fu Fv i j
    (congrArg Prod.fst E) (congrArg Prod.snd E)

theorem local_p3 (nil : LS G 6=⊥) (x y : G) (p : G →* H) (f : H →* Q)
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
  let c' := portC X⁻¹ Y
  let u' := portU X⁻¹ Y
  let v' := portV X⁻¹ Y
  have cu : u∈LS H 2 := layer_u X Y
  have cv : v∈LS H 2 := layer_v X Y
  have c3 : c^3 ∈ LS H 2 := by
    rw [←ker]
    change f (c^3)=1
    rw [map_pow,←ord,pow_orderOf_eq_one]
  have hu := center_of_L2 nilH cu
  have hv := center_of_L2 nilH cv
  have u3 : u^3=1 := congrArg Subtype.val (cube_L2 nilH X Y genH c3 ⟨u,cu⟩)
  have inv := invert_Hall X Y hu hv
  have Ccube : c'^3 = (c^3)⁻¹ := invert_cube X Y hu hv u3
  have c3' : c'^3 ∈ LS H 2 := Ccube ▸ (LS H 2).inv_mem c3
  have OC : orderOf (f c')=3 := by
    change orderOf (f (portC X⁻¹ Y))=3
    rw [inv.1,map_mul,map_inv,kill_of_ker f ker u cu,mul_one,orderOf_inv]
    exact ord
  obtain ⟨χ,Fu⟩ := char_exists nilH X Y genH c3 nz
  obtain ⟨q,hq⟩ := residue_rep (Multiplicative.toAdd (χ ⟨v,cv⟩))
  obtain ⟨t,ht⟩ := residue_rep (Multiplicative.toAdd (χ ⟨c^3,c3⟩))
  have Fc : χ ⟨c^3,c3⟩ = Multiplicative.ofAdd ((t.val:ℤ):ZMod 3) :=
    congrArg Multiplicative.ofAdd ht.symm
  have Fv : χ ⟨v,cv⟩ = Multiplicative.ofAdd ((q.val:ℤ):ZMod 3) :=
    congrArg Multiplicative.ofAdd hq.symm
  have CC : (⟨c'^3,c3'⟩ : LS H 2) = (⟨c^3,c3⟩ : LS H 2)⁻¹ := Subtype.ext Ccube
  have UU : (⟨u',layer_u X⁻¹ Y⟩ : LS H 2) = ⟨u,cu⟩ := Subtype.ext inv.2.1
  have VV : (⟨v',layer_v X⁻¹ Y⟩ : LS H 2) = (⟨v,cv⟩ : LS H 2)⁻¹ := Subtype.ext inv.2.2
  have Fc' : χ ⟨c'^3,c3'⟩ = Multiplicative.ofAdd (((-t).val:ℤ):ZMod 3) := by
    rw [CC,map_inv,Fc,neg_rep]; rfl
  have Fu' : χ ⟨u',layer_u X⁻¹ Y⟩ = Multiplicative.ofAdd (1:ZMod 3) := by rw [UU,Fu]
  have Fv' : χ ⟨v',layer_v X⁻¹ Y⟩ = Multiplicative.ofAdd (((-q).val:ℤ):ZMod 3) := by
    rw [VV,map_inv,Fv,neg_rep]; rfl
  apply cycle_of_tables nil x y q t
  · exact keys x y p f nilH ker ord c3 χ q t Fc Fu Fv
  · have PX : p x⁻¹=X⁻¹ := map_inv p x
    have O : orderOf (f (portC (p x⁻¹) (p y)))=3 := by rw [PX]; exact OC
    have C' : (portC (p x⁻¹) (p y))^3 ∈ LS H 2 := by rw [PX]; exact c3'
    refine keys x⁻¹ y p f nilH ker O C' χ (-q) (-t) ?_ ?_ ?_
    · have e : (⟨(portC (p x⁻¹) (p y))^3,C'⟩ : LS H 2) = ⟨c'^3,c3'⟩ := by
        apply Subtype.val_injective
        change (portC (p x⁻¹) (p y))^3 = c'^3
        rw [PX]
      rw [e]; exact Fc'
    · have e : (⟨portU (p x⁻¹) (p y),layer_u _ _⟩ : LS H 2) = ⟨u',layer_u X⁻¹ Y⟩ :=
        Subtype.ext (by rw [PX])
      rw [e]; exact Fu'
    · have e : (⟨portV (p x⁻¹) (p y),layer_v _ _⟩ : LS H 2) = ⟨v',layer_v X⁻¹ Y⟩ :=
        Subtype.ext (by rw [PX])
      rw [e]; exact Fv'

end Ribbon6
#print axioms Ribbon6.local_p3
