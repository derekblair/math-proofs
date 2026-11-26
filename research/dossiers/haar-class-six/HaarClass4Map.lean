import HaarClassFourFinite

namespace HaarClass4Map
open HaarClass4Normal HaarClass4Table HaarClass4Structure HaarClass4Generate HaarClass4Ports
open scoped commutatorElement

variable {G H : Type*} [Group G] [Group H]

theorem class_map (f : G →* H) (onto : Function.Surjective f) {n : ℕ}
    (h : LS G n=⊥) : LS H n=⊥ := by
  rw [← map_ls f onto n,h,Subgroup.map_bot]

theorem map_portC (f : G →* H) (x y : G) : f (portC x y)=portC (f x) (f y) := by
  simp [portC,map_commutatorElement]

theorem map_portU (f : G →* H) (x y : G) : f (portU x y)=portU (f x) (f y) := by
  simp [portU,map_commutatorElement,map_portC]

theorem map_portV (f : G →* H) (x y : G) : f (portV x y)=portV (f x) (f y) := by
  simp [portV,map_commutatorElement,map_portC]

theorem evaluation_map (f : G →* H) (onto : Function.Surjective f) (h : LS G 4=⊥)
    (x y : G) (r : Row) :
    f (eval (make h x y) r)=eval (make (class_map f onto h) (f x) (f y)) r := by
  simp [eval,mid,tail,make,map_commutatorElement,map_portC,map_portU,map_portV]

theorem nonabelian_c_survives (x y : G) (gen : Generates x y)
    {n : ℕ} (h : LS G n = ⊥) (nonabel : LS G 1 ≠ ⊥) : portC x y ∉ LS G 2 := by
  intro hc
  let S := LS G 2
  let f := QuotientGroup.mk' S
  have e : f (portC x y)=1 := (QuotientGroup.eq_one_iff _).mpr hc
  have cxy : Commute (f x) (f y) := by
    change f x*f y=f y*f x
    simpa [e] using congrArg f (ports_xy x y)
  let : IsMulCommutative (G ⧸ S) := gen_comm _ _ (map_gen f (QuotientGroup.mk'_surjective S) gen) cxy
  have bot : LS (G ⧸ S) 1 = ⊥ := Subgroup.top_lowerCentralSeries_one.trans (commutator_eq_bot _)
  have map := map_ls f (QuotientGroup.mk'_surjective S) 1
  rw [bot,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at map
  have anti := Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)
  have same : LS G 1 = LS G 2 := le_antisymm map (anti (by decide : 1 ≤ 2))
  have each : ∀ k, LS G (k+1)=LS G 1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change ⁅LS G (k+1),(⊤ : Subgroup G)⁆ = LS G 1
      rw [ih]
      exact same.symm
  apply nonabel
  exact (each n).symm.trans (le_bot_iff.mp ((anti (Nat.le_succ n)).trans (le_of_eq h)))

end HaarClass4Map

#print axioms HaarClass4Map.evaluation_map
#print axioms HaarClass4Map.nonabelian_c_survives
