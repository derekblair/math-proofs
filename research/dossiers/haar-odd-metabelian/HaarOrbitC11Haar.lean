import HaarOrbitC11Checks
import HaarOrbitC11RealCover
import HaarOrbitActual
import HaarK33OddCover
import Mathlib.Algebra.BigOperators.Fin

namespace HaarOrbitC11Haar
open HaarOrbitC11Voltage HaarOrbitC11Checks HaarMetaVoltagePullback HaarOrbitActual HaarOrbitChains HaarAllNoncommuting

variable {G Q : Type*} [Group G] [Group Q]
variable {f : G →* Q} {x y : G}
variable [hc : Fact (∀ (a b : f.ker), a*b=b*a)]
local instance kerComm : CommGroup f.ker where
  __ := (inferInstance : Group f.ker)
  mul_comm := hc.out
local instance addCommK : AddCommGroup (Additive f.ker) := inferInstance

variable (T : Setup f x y B)
variable (tn : T.next = next) (ts : ∀ u, T.side u=decide (11≤u.val))

def Preserves (g : S → G) : Prop :=
  ∀ s e, active s e=true →
    f (g s*T.repr (src e))=f (T.repr (tv s (src e))) ∧
    f (g s*T.repr (dst e))=f (T.repr (tv s (dst e)))

include tn ts in
theorem frame (e : E) : T.side (src e)=false ∧ src e≠dst e ∧ T.next (src e) (label e)=dst e := by
  obtain ⟨h,a,b⟩ := edges_correct e
  refine ⟨?_,a,?_⟩
  · simp [ts,show ¬ 11≤(src e).val by omega]
  · simpa only [tn] using b

theorem normalized (W : B → B → Additive f.ker) (antiW : ∀ u v, W v u = -W u v) (e : E) :
    HaarOrbitChains.normalized cot (HaarOrbitC11Gauge.weights W) e =
      W (src e) (dst e) + HaarOrbitC11Gauge.potential W (src e) - HaarOrbitC11Gauge.potential W (dst e) := by
  obtain ⟨_,hn,he⟩ := edges_correct e
  have g := HaarOrbitC11Gauge.map_gauge W antiW (src e) (label e)
  rw [he] at g
  unfold HaarOrbitC11Gauge.clean at g
  rw [if_neg hn] at g
  rw [←g]
  unfold HaarOrbitChains.normalized
  change _ = ∑ i : Fin 12, gauge (src e) (dst e) i • HaarOrbitC11Gauge.weights W i
  apply Finset.sum_congr rfl
  intro i _
  rw [gauge_edges e i]
  by_cases h : cot i=e <;> simp [h]

include tn ts in
theorem any_of_setup (g : S → G) (pg : Preserves T g)
    (noTwo : ∀ a : Additive f.ker, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle x y n := by
  let W := weight T
  let w := HaarOrbitC11Gauge.weights W
  have H : laws w := by
    intro s
    apply normalized_law T src dst label (frame T tn ts) cot w (HaarOrbitC11Gauge.potential W)
      (normalized W (anti T)) (tv s) (te s) (g s) (fun e => active s e=true)
    intro e h
    obtain ⟨u,v,j⟩ := translated_incidence s e h
    obtain ⟨a,b⟩ := pg s e h
    exact ⟨u,v,j,a,b⟩
  obtain ⟨n,nn,C⟩ := any_voltage w H noTwo
  have cg : HaarOrbitC11Gauge.HasCycle W n := HaarOrbitC11Gauge.ungauge W (anti T) C
  have npos : 2≤n := by simp at nn; omega
  obtain ⟨v,vi,vc⟩ := HaarOrbitC11RealCover.real npos W cg
  have E : CoverCycle T (weight T) n := by
    refine ⟨v,vi,fun i => ?_⟩
    obtain ⟨h,j,hj,eq⟩ := vc i
    exact ⟨h,j,by simpa only [tn] using hj,eq⟩
  exact ⟨n,nn,lift_cycle T E⟩

include tn ts in
theorem finite_odd [Finite G] (g : S → G) (pg : Preserves T g) (odd : Odd (Nat.card G)) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle x y n :=
  any_of_setup T tn ts g pg (HaarK33OddCover.finite_odd_noTwo
    (Odd.of_dvd_nat odd (Subgroup.card_subgroup_dvd_card f.ker)))

end HaarOrbitC11Haar
#print axioms HaarOrbitC11Haar.finite_odd
