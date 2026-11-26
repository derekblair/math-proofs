import Ribbon7Algebra
import Ribbon7Mates

namespace Ribbon7
open HaarClass4Structure HaarClass4Ports Ribbon5Bridge
variable {G : Type*} [Group G]
set_option maxRecDepth 32000
set_option maxHeartbeats 0

private theorem relative_ne {u v : Bool×G} {g : G} (N : g≠1)
    (E : ∃ c : G,u.2⁻¹*v.2=c*g*c⁻¹) : u≠v := by
  intro eq
  obtain ⟨c,h⟩ := E
  rw [eq,inv_mul_cancel] at h
  apply N
  calc
    g = c⁻¹*(c*g*c⁻¹)*c := by group
    _ = 1 := by rw [←h]; group

private theorem low_sep (x y : G)
    (good : ∀ k : Nat, 1≤k → k≤4 → (QuotientGroup.mk' (LS G 2) (portC x y))^k ≠ 1)
    (w : Array P) (tab : Array Q)
    (h0 : tab[0]! = (false,0,0,0))
    (step : ∀ i, i<w.size → push tab[i]! w[i]! = tab[i+1]!)
    (i j : Nat) (hi : i≤w.size) (hj : j≤w.size)
    (h : separated tab[i]! tab[j]!) :
    pathAt x y w i ≠ pathAt x y w j := by
  let f := QuotientGroup.mk' (LS G 2)
  let C := f (portC x y)
  have U' : f (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_u x y)
  have V' : f (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_v x y)
  have cx : Commute C (f x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C,portU,map_commutatorElement] using U'
  have cy : Commute C (f y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C,portV,map_commutatorElement] using V'
  have xy : f x*f y=f y*f x*C := by simpa only [C,map_mul] using congrArg f (ports_xy x y)
  let F : Bool×G → Bool × (G ⧸ LS G 2) := fun u => (u.1,f u.2)
  intro E
  have T := transported f x y w tab C cx cy xy h0 step
  have e : vert (f x) (f y) C tab[i]! = vert (f x) (f y) C tab[j]! :=
    (T i hi).symm.trans ((congrArg F E).trans (T j hj))
  exact separates_low (f x) (f y) C cx cy xy good _ _ h e

private theorem fin32 (i : Fin 32) : i.val ≤ wa.size := i.isLt.le
private theorem fin64 (i : Fin 64) : i.val ≤ ww.size := i.isLt.le
private theorem fin128 (i : Fin 128) : i.val ≤ wt.size := i.isLt.le

def exceptional (x y : G) : Prop :=
  pathAt x y wt 48 ≠ pathAt x y wt 98 ∧
    pathAt x y wt 49 ≠ pathAt x y wt 99 ∧
    pathAt x y wt 50 ≠ pathAt x y wt 100

theorem local_bound_if (nil : LS G 7=⊥) (x y : G)
    (good : ∀ k : Nat, 1≤k → k≤4 → (QuotientGroup.mk' (LS G 2) (portC x y))^k ≠ 1)
    (ex : Z x y ≠ 1 → exceptional x y) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  by_cases r : R x y=1
  · left
    apply cycle_from_at x y wa (by decide) (by rw [a_end,r]; rfl)
    intro i j l
    exact low_sep x y good wa ta (by decide +kernel) (fun n hn => astep ⟨n,hn⟩) _ _
      (fin32 i) (fin32 j) (achart i j l)
  · right
    by_cases z : Z x y=1
    · left
      apply cycle_from_at x y ww (by decide) (by rw [w_end,z]; rfl)
      intro i j l
      rcases wchart i j l with h|h
      · exact low_sep x y good ww tw (by decide +kernel) (fun n hn => wstep ⟨n,hn⟩) _ _
          (fin64 i) (fin64 j) h
      · have N : (R x y)⁻¹ * Z x y ≠ 1 := by
          rw [z,mul_one]
          exact fun h => r (inv_eq_one.mp h)
        rcases h with ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩
        · rw [hi,hj]
          exact relative_ne r (w_0_32 x y)
        · rw [hi,hj]
          exact relative_ne r (w_1_33 x y)
        · rw [hi,hj]
          exact relative_ne r (w_2_34 x y)
        · rw [hi,hj]
          exact relative_ne r (w_3_35 x y)
        · rw [hi,hj]
          exact relative_ne r (w_4_36 x y)
        · rw [hi,hj]
          exact relative_ne r (w_5_37 x y)
        · rw [hi,hj]
          exact relative_ne N (w_29_61 x y)
        · rw [hi,hj]
          exact relative_ne N (w_30_62 x y)
        · rw [hi,hj]
          exact relative_ne N (w_31_63 x y)
    · right
      apply cycle_from_at x y wt (by decide) (close128 nil x y)
      intro i j l
      rcases tchart i j l with h|h
      · exact low_sep x y good wt tt (by decide +kernel) (fun n hn => tstep ⟨n,hn⟩) _ _
          (fin128 i) (fin128 j) h
      · have M := nz_mix nil x y z
        rcases h with ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩
        · rw [hi,hj]
          exact relative_ne r (t_0_32 x y)
        · rw [hi,hj]
          exact relative_ne z (t_0_64 x y)
        · rw [hi,hj]
          exact relative_ne M (t_32_64 x y)
        · rw [hi,hj]
          exact relative_ne r (t_1_33 x y)
        · rw [hi,hj]
          exact relative_ne z (t_1_65 x y)
        · rw [hi,hj]
          exact relative_ne M (t_33_65 x y)
        · rw [hi,hj]
          exact relative_ne r (t_2_34 x y)
        · rw [hi,hj]
          exact relative_ne z (t_2_66 x y)
        · rw [hi,hj]
          exact relative_ne M (t_34_66 x y)
        · rw [hi,hj]
          exact relative_ne r (t_3_35 x y)
        · rw [hi,hj]
          exact relative_ne r (t_4_36 x y)
        · rw [hi,hj]
          exact relative_ne r (t_5_37 x y)
        · rw [hi,hj]
          exact relative_ne M (t_29_61 x y)
        · rw [hi,hj]
          exact relative_ne M (t_30_62 x y)
        · rw [hi,hj]
          exact relative_ne M (t_31_63 x y)
        · rw [hi,hj]
          exact (ex z).1
        · rw [hi,hj]
          exact (ex z).2.1
        · rw [hi,hj]
          exact (ex z).2.2
        · rw [hi,hj]
          exact relative_ne r (t_86_118 x y)
        · rw [hi,hj]
          exact relative_ne r (t_87_119 x y)
        · rw [hi,hj]
          exact relative_ne r (t_88_120 x y)
        · rw [hi,hj]
          exact relative_ne r (t_89_121 x y)
        · rw [hi,hj]
          exact relative_ne r (t_90_122 x y)
        · rw [hi,hj]
          exact relative_ne r (t_91_123 x y)
        · rw [hi,hj]
          exact relative_ne r (t_92_124 x y)
        · rw [hi,hj]
          exact relative_ne r (t_93_125 x y)
        · rw [hi,hj]
          exact relative_ne r (t_94_126 x y)

end Ribbon7
#print axioms Ribbon7.local_bound_if
