import RibbonMetaClose
import RibbonP3Compare
import RibbonP3Transport

namespace RibbonMeta
open Ribbon5Bridge HaarClass4Structure HaarClass4Ports
open scoped commutatorElement
variable {G : Type*} [Group G]

def word3 : Array P := #[1,2,0,0,2,0,0,2,1,2,1,1,2,1,2,0,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1]
def table3 : Array Q := #[(false,0,0,0),(false,-1,0,0),(true,-1,0,0),(true,-1,1,-1),(true,-1,2,-2),(false,-1,2,-2),(false,0,2,-2),(false,1,2,-2),(true,1,2,-2),(true,1,1,-3),(false,1,1,-3),(false,0,1,-3),(false,-1,1,-3),(true,-1,1,-3),(true,-1,0,-2),(false,-1,0,-2),(false,0,0,-2),(false,1,0,-2),(true,1,0,-2),(true,1,1,-1),(true,1,2,0),(false,1,2,0),(false,0,2,0),(false,-1,2,0),(true,-1,2,0),(true,-1,1,1),(false,-1,1,1),(false,0,1,1),(false,1,1,1),(true,1,1,1),(true,1,0,0),(false,1,0,0),(false,0,0,0)]

set_option maxRecDepth 12000
set_option maxHeartbeats 0

private theorem step3 (i : Fin 32) : push table3[i.val]! word3[i.val]! = table3[i.val+1]! := by
  decide +kernel +revert

def key3 (r : Q) : ℕ :=
  (if r.1 then 1 else 0) + 2*(r.2.1%3).toNat + 6*(r.2.2.1%3).toNat + 18*(r.2.2.2%3).toNat

private theorem chart3 (i j : Fin 32) (l : i.val<j.val) :
    key3 table3[i.val]! ≠ key3 table3[j.val]! := by decide +kernel +revert

private theorem windows3 (i : Fin 32) :
    (-1 ≤ table3[i.val]!.2.1 ∧ table3[i.val]!.2.1 ≤ 1) ∧
      (0 ≤ table3[i.val]!.2.2.1 ∧ table3[i.val]!.2.2.1 ≤ 2) := by decide +kernel +revert

private theorem end3 (x y : G) :
    pathAt x y word3 32 = (false,x⁻¹ * RibbonP3.trace y x false RibbonP3.a * x) := by
  norm_num [pathAt,run,start,action,word3,RibbonP3.trace,RibbonP3.a]
  group

private theorem a_zero (m : Meta G) (x y : G) :
    RibbonP3.trace x y false RibbonP3.a=1 := by
  rw [RibbonP3.factorA]
  let H := ⁅x,y*y⁆
  have A : H ∈ LS G 1 := next_layer (Subgroup.mem_top x) (y*y)
  have B : x⁻¹ * H⁻¹ * x ∈ LS G 1 := by
    simpa only [inv_inv] using
      (inferInstance : (LS G 1).Normal).conj_mem _ ((LS G 1).inv_mem A) x⁻¹
  rw [(m _ A _ B).commutator_eq,mul_one,mul_inv_cancel]

/-- The rotated word closes in every metabelian group and is already seen
to be simple in the class-two projection, even when c has order three. -/
theorem direct3_cycle (m : Meta G) (x y : G)
    (ord : orderOf (QuotientGroup.mk' (LS G 2) (portC x y))=3) :
    Ribbon.Cycle x y 32 := by
  let f := QuotientGroup.mk' (LS G 2)
  let C := f (portC x y)
  have U : f (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_u x y)
  have V : f (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_v x y)
  have cx : Commute C (f x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C,portU,map_commutatorElement] using U
  have cy : Commute C (f y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C,portV,map_commutatorElement] using V
  have xy : f x*f y=f y*f x*C := by simpa only [C,map_mul] using congrArg f (ports_xy x y)
  let F : Bool×G → Bool × (G ⧸ LS G 2) := fun u => (u.1,f u.2)
  apply cycle_from_at x y word3 (by decide) (by rw [end3,a_zero m,mul_one,inv_mul_cancel]; rfl)
  have tr := transported f x y word3 table3 C cx cy xy (by decide +kernel)
    (fun i hi => step3 ⟨i,hi⟩)
  intro i j le E
  let I := table3[i.val]!
  let J := table3[j.val]!
  have e : vert (f x) (f y) C I = vert (f x) (f y) C J :=
    (tr i.val i.isLt.le).symm.trans ((congrArg F E).trans (tr j.val j.isLt.le))
  have h := RibbonP3.abelian_residues (f x) (f y) C cx cy xy ord I.2 J.2 (congrArg Prod.snd e)
  have eI : I.2.1=J.2.1 := by
    have bi := (windows3 i).1
    have bj := (windows3 j).1
    have hh := h.1
    change -1 ≤ I.2.1 ∧ I.2.1 ≤ 1 at bi
    change -1 ≤ J.2.1 ∧ J.2.1 ≤ 1 at bj
    omega
  have eJ : I.2.2.1=J.2.2.1 := by
    have bi := (windows3 i).2
    have bj := (windows3 j).2
    have hh := h.2
    change 0 ≤ I.2.2.1 ∧ I.2.2.1 ≤ 2 at bi
    change 0 ≤ J.2.2.1 ∧ J.2.2.1 ≤ 2 at bj
    omega
  have g := congrArg Prod.snd e
  change HaarCycle.norm (f x) (f y) C (I.2.1,I.2.2.1,I.2.2.2) =
    HaarCycle.norm (f x) (f y) C (J.2.1,J.2.2.1,J.2.2.2) at g
  rw [eI,eJ] at g
  have k := RibbonP3.commutator_residue (f x) (f y) C ord J.2.1 J.2.2.1 I.2.2.2 J.2.2.2 g
  have S : I.1=J.1 := congrArg (Prod.fst : Bool × (G ⧸ LS G 2) → Bool) e
  apply chart3 i j le
  change key3 I=key3 J
  simp only [key3,S,eI,eJ,k]

end RibbonMeta
#print axioms RibbonMeta.direct3_cycle
