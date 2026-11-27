import RibbonD3P3Transport
import RibbonDumbbellMain
import RibbonP3Structure

namespace RibbonD3P3
open RibbonDumbbell RibbonDerived3 HaarClass4Structure HaarClass4Ports HaarClass4Generate
open RibbonClass4Fallback
open scoped commutatorElement

variable {G H Q : Type*} [Group G] [Group H] [Group Q]

theorem from_character (d3 : DLS G 3 = ⊥) (x y : G) (p : G→*H) (f : H→*Q)
    (kill : ∀ z ∈ DLS G 1, p z=1)
    (c u v : H) (d : RibbonP3.Class3 (p x) (p y) c u v)
    (cu : Commute (f c) (f (p x))) (cv : Commute (f c) (f (p y)))
    (order : orderOf (f c)=3) (zu : f u=1) (zv : f v=1)
    (S : Subgroup H) (hc : c^3∈S) (hu : u∈S) (hv : v∈S)
    (χ : S →* Multiplicative (ZMod 3)) (q t : Fin 3)
    (fc : χ ⟨c^3,hc⟩ = Multiplicative.ofAdd ((t.val:ℤ):ZMod 3))
    (fu : χ ⟨u,hu⟩ = Multiplicative.ofAdd (1:ZMod 3))
    (fv : χ ⟨v,hv⟩ = Multiplicative.ofAdd ((q.val:ℤ):ZMod 3)) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 128 ∨ Ribbon.Cycle x y 256 := by
  let D := spec q t
  let o : Bool × G := (false,1)
  let W := D.W
  let e := terminus x y o W
  have BS : e.1 = D.bside := bridge_side p x y c u v d q t
  have N : NeutralWord e.1 W.b := BS.symm ▸ D.nb
  let r := displacement x y o W.a
  let s := displacement x y e W.b
  have R : r ∈ DLS G 1 := neutral_gain x y o W.a W.aSize D.na
  have T : s ∈ DLS G 1 := neutral_gain x y e W.b W.bSize N
  apply derived_three x y r s d3 R T p (kill r R) (kill s T) (wordPoint x y o W)
  · intro i j E
    change project p (wordPoint x y (false,1) W i) = project p (wordPoint x y (false,1) W j) at E
    rw [map_point,map_point,point_collect (p x) (p y) c u v d q t,
      point_collect (p x) (p y) c u v d q t] at E
    have A := bounds_checked q t i
    have B := bounds_checked q t j
    unfold atBounds at A B
    dsimp only at A B
    have impI : -3 < (rowPoint q t i).i-(rowPoint q t j).i ∧
        (rowPoint q t i).i-(rowPoint q t j).i < 3 := by omega
    have impJ : -3 < (rowPoint q t i).j-(rowPoint q t j).j ∧
        (rowPoint q t i).j-(rowPoint q t j).j < 3 := by omega
    have xy : f (p x)*f (p y)=f (p y)*f (p x)*f c := by
      simpa only [map_mul] using congrArg f d.xy
    apply key_injective q t
    exact key_of_equal f (p x) (p y) c u v cu cv xy order zu zv S hc hu hv χ q t fc fu fv
      _ _ impI impJ (congrArg Prod.fst E) (congrArg Prod.snd E)
  · exact forward_words x y o W (neutral_side x y o W.a W.aSize D.na)
      (neutral_side x y e W.b W.bSize N)

private theorem residue_rep (z : ZMod 3) :
    ∃ t : Fin 3, ((t.val:ℤ):ZMod 3)=z := by
  exact ⟨⟨z.val,ZMod.val_lt z⟩,by push_cast; exact ZMod.natCast_zmod_val z⟩

theorem local_visible (d3 : DLS G 3 = ⊥) (x y : G) (p : G→*H) (f : H→*Q)
    (kill : ∀ z ∈ DLS G 1, p z=1) (nilH : LS H 3=⊥) (genH : Generates (p x) (p y))
    (ker : f.ker=LS H 2) (order : orderOf (f (portC (p x) (p y)))=3)
    (visible : portU (p x) (p y)≠1) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 128 ∨ Ribbon.Cycle x y 256 := by
  let X := p x
  let Y := p y
  let c := portC X Y
  let u := portU X Y
  let v := portV X Y
  have hc : c^3 ∈ LS H 2 := by
    rw [←ker]
    change f (c^3)=1
    rw [map_pow,←order,pow_orderOf_eq_one]
  have hu : u ∈ LS H 2 := layer_u X Y
  have hv : v ∈ LS H 2 := layer_v X Y
  have zu : f u=1 := MonoidHom.mem_ker.mp (ker.symm ▸ hu)
  have zv : f v=1 := MonoidHom.mem_ker.mp (ker.symm ▸ hv)
  have cu : Commute (f c) (f X) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [u,portU,map_commutatorElement] using zu
  have cv : Commute (f c) (f Y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [v,portV,map_commutatorElement] using zv
  obtain ⟨χ,fu⟩ := RibbonP3.char_exists nilH X Y genH hc visible
  obtain ⟨q,hq⟩ := residue_rep (Multiplicative.toAdd (χ ⟨v,hv⟩))
  obtain ⟨t,ht⟩ := residue_rep (Multiplicative.toAdd (χ ⟨c^3,hc⟩))
  have fc : χ ⟨c^3,hc⟩ = Multiplicative.ofAdd ((t.val:ℤ):ZMod 3) :=
    congrArg Multiplicative.ofAdd ht.symm
  have fv : χ ⟨v,hv⟩ = Multiplicative.ofAdd ((q.val:ℤ):ZMod 3) :=
    congrArg Multiplicative.ofAdd hq.symm
  exact from_character d3 x y p f kill c u v (RibbonP3.class3_ports nilH X Y)
    cu cv order zu zv (LS H 2) hc hu hv χ q t fc fu fv

#print axioms from_character
#print axioms local_visible
end RibbonD3P3
