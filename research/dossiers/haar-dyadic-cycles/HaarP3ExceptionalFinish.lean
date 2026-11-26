import HaarP3ExceptionalFinishCore
import HaarClass5P3MetaCycle
import HaarP3Class4Order

namespace HaarP3ExceptionalFinish

open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports HaarClass4Data HaarP3LayerGen
open HaarAllNoncommuting
variable {G : Type*} [Group G]

theorem exceptional_cycle32 (nil : LS G 5=⊥) (x y : G)
    (gen : HaarClass4Generate.Generates x y)
    (rel : let φ := QuotientGroup.mk' (LS G 4)
           let e := make (ls4quot_class4 G) (φ x) (φ y)
           e.v=e.u^(2:ℕ)*e.a^(2:ℕ) ∧ e.u^(3:ℕ)=1 ∧ e.a^(3:ℕ)=1)
    (ident : let u := portU x y; let v := portV x y
             let A := ⁅u,x⁆
             let P := ⁅A,x⁆
             let Q := ⁅A,y⁆
             Q=P⁻¹ ∧ v*u*A=P⁻¹ ∧ u^(3:ℕ)=P⁻¹ ∧ ⁅u,y⁆*A=P⁻¹ ∧ P≠1)
    : HasCycle x y 32 := by
  let c := portC x y
  let u := portU x y
  let v := portV x y
  let A := ⁅u,x⁆
  let P := ⁅A,x⁆
  let Q := ⁅A,y⁆
  let z := u^(3:ℕ)
  change Q=P⁻¹ ∧ v*u*A=P⁻¹ ∧ z=P⁻¹ ∧ ⁅u,y⁆*A=P⁻¹ ∧ P≠1 at ident
  obtain ⟨hq,hv,hz,hb,hp⟩ := ident
  have hcL : c∈LS G 1 := layer_c x y
  have huL : u∈LS G 2 := layer_u x y
  have hvL : v∈LS G 2 := layer_v x y
  have hAL : A∈LS G 3 := next_layer huL x
  have hPL : P∈LS G 4 := next_layer hAL x
  have hzc : z∈LS G 4 := hz.symm ▸ (LS G 4).inv_mem hPL
  have cZ : z∈Subgroup.center G := ls4_center_of_class5 nil hzc
  have zc : ∀ w : G, Commute z w := fun w => (Subgroup.mem_center_iff.mp cZ w).symm
  have zQ : Q=z := hq.trans hz.symm
  have zP : P=z⁻¹ := by rw [hz,inv_inv]
  have zne : z≠1 := by intro e; apply hp; rw [zP,e,inv_one]
  have hcA : Commute c A :=
    (HaarClass5Commute.centralizes_commutator 3 nil hAL x⁻¹ y⁻¹).symm
  have huA : Commute u A := HaarClass5L2Abelian.l2_comm nil huL
    ((Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)) (by decide : 2≤3) hAL)
  have ha3 : A^(3:ℕ)=1 := by
    have e : rc x⁻¹ (u^(3:ℕ))=u^(3:ℕ) := rc_center zc x⁻¹
    rw [map_pow,HaarClass5P3Meta.conjugation,show ⁅u,x⁆=A by rfl,
      huA.inv_right.symm.mul_pow] at e
    have ez : (A⁻¹)^(3:ℕ)=1 := mul_right_cancel (e.trans (one_mul _).symm)
    simpa only [inv_pow,inv_eq_one] using ez
  have hp3 := (fifth_layer_exceptional nil x y gen rel).2 P hPL
  have z3 : z^(3:ℕ)=1 := by rw [hz,inv_pow,hp3,inv_one]
  have hu9 : u^(9:ℕ)=1 := by rw [show (9:ℕ)=3*3 by decide,pow_mul]; exact z3
  let ψ := QuotientGroup.mk' (LS G 3)
  have psiu3 : (ψ u)^(3:ℕ)=1 := by
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      ((Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)) (by decide : 3≤4) hzc)
  have psiu1 : ψ u≠1 := by
    intro e
    have h := (QuotientGroup.eq_one_iff _).mp e
    have hA : A∈LS G 4 := next_layer h x
    exact hp ((commutatorElement_eq_one_iff_commute.mpr
      ((Subgroup.mem_center_iff.mp (ls4_center_of_class5 nil hA) x).symm)))
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have u9 : orderOf u=9 := orderOf_eq_prime_pow (p:=3) (n:=1)
    (by simpa only [pow_one] using zne) (by simpa only [show (3:ℕ)^(1+1)=9 by decide] using hu9)
  have psiord : orderOf (ψ u)=3 := orderOf_eq_prime psiu3 psiu1
  have nA : A∉Subgroup.zpowers u := by
    intro h
    obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp h
    have k : (ψ u)^n=1 := by
      rw [←map_zpow,hn]
      exact (QuotientGroup.eq_one_iff _).mpr hAL
    have d := orderOf_dvd_iff_zpow_eq_one.mpr k
    rw [psiord] at d
    obtain ⟨m,hm⟩ := d
    have central : A∈Subgroup.center G := by
      rw [←hn,hm,zpow_mul,show u^((↑(3:ℕ)):ℤ)=z by simp [z]]
      exact (Subgroup.center G).zpow_mem cZ _
    exact hp (commutatorElement_eq_one_iff_commute.mpr
      ((Subgroup.mem_center_iff.mp central x).symm))
  have vEq : v=u^(2:ℕ)*A⁻¹ := by
    have e : v=z*A⁻¹*u⁻¹ := by rw [hz,hv.symm]; group
    rw [e,mul_assoc,←(huA.inv_left.inv_right).eq,←mul_assoc]
    change u^(3:ℕ)*u⁻¹*A⁻¹=u^(2:ℕ)*A⁻¹
    group
  have bEq : ⁅u,y⁆=z*A⁻¹ := by rw [hz,←hb]; group
  have xu : rc x⁻¹ u=u*A⁻¹ := by
    rw [HaarClass5P3Meta.conjugation,show ⁅u,x⁆=A by rfl,huA.inv_right.symm.eq]
  have xa : rc x⁻¹ A=z*A := by
    rw [HaarClass5P3Meta.conjugation,show ⁅A,x⁆=P by rfl,zP,inv_inv]
  have yu : rc y⁻¹ u=A*(u^(2:ℕ))⁻¹ := by
    rw [HaarClass5P3Meta.conjugation,bEq,mul_inv_rev,inv_inv]
    change A*(u^(3:ℕ))⁻¹*u=A*(u^2)⁻¹
    group
  have ya : rc y⁻¹ A=z⁻¹*A := by
    rw [HaarClass5P3Meta.conjugation,show ⁅A,y⁆=Q by rfl,zQ]
  have cu := exceptional_comm x y c u A huA (ports_xy x y) ha3 xu xa yu ya
  let M := HaarClass5P3Meta.of_comm x y c u A cu hcA huA (ports_xy x y) hu9 ha3
    rfl rfl (by rw [show ⁅A,x⁆=P by rfl,zP]; simp [z])
    vEq bEq zQ
  let φ := QuotientGroup.mk' (LS G 2)
  have kc : φ u=1 := (QuotientGroup.eq_one_iff _).mpr huL
  have kv : φ v=1 := (QuotientGroup.eq_one_iff _).mpr hvL
  have kA : φ A=1 := (QuotientGroup.eq_one_iff _).mpr
    ((Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)) (by decide : 2≤3) hAL)
  have cx : Commute (φ c) (φ x) := commutatorElement_eq_one_iff_commute.mp
    ((map_commutatorElement φ c x).symm.trans kc)
  have cy : Commute (φ c) (φ y) := commutatorElement_eq_one_iff_commute.mp
    ((map_commutatorElement φ c y).symm.trans kv)
  have div3 : 3∣orderOf (φ c) := HaarP3Class4Order.c_order3 c x hcL psiord
  exact HaarClass5P3Meta.cycle32 M φ kc kA cx cy div3 u9 nA

end HaarP3ExceptionalFinish
#print axioms HaarP3ExceptionalFinish.exceptional_cycle32
