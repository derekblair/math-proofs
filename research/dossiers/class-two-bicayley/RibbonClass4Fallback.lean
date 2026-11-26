import HaarClass4Generate
import RibbonClass3

namespace RibbonClass4Fallback

open HaarClass4Ports HaarClass4Structure HaarClass4Generate
open scoped commutatorElement

variable {G H : Type*} [Group G] [Group H]

theorem cycle_map (f : G →* H) (fi : Function.Injective f) (x y : G) (n : ℕ)
    (h : Ribbon.Cycle x y n) : Ribbon.Cycle (f x) (f y) n := by
  obtain ⟨g,gi,ge⟩ := h
  refine ⟨fun i => ((g i).1,f (g i).2), ?_, ?_⟩
  · intro u v e
    exact gi (Prod.ext (congrArg (Prod.fst : Bool × H → Bool) e) (fi (congrArg (Prod.snd : Bool × H → H) e)))
  · intro i
    rcases ge i with ⟨hl,hr,he|he⟩ | ⟨hl,hr,he|he⟩ | ⟨hs,hg⟩
    · exact Or.inl ⟨hl,hr,Or.inl (by simpa using congrArg f he)⟩
    · exact Or.inl ⟨hl,hr,Or.inr (by simpa using congrArg f he)⟩
    · exact Or.inr (Or.inl ⟨hl,hr,Or.inl (by simpa using congrArg f he)⟩)
    · exact Or.inr (Or.inl ⟨hl,hr,Or.inr (by simpa using congrArg f he)⟩)
    · exact Or.inr (Or.inr ⟨hs,congrArg f hg⟩)

/-- The three fourth-layer coordinates of a generating pair suffice to
detect whether the whole nilpotency-class-four layer vanishes. -/
theorem class_drop (x y : G) (gen : Generates x y) (nil : LS G 4=⊥)
    (ha : (make nil x y).a=1) (hb : (make nil x y).b=1)
    (hd : (make nil x y).d=1) : LS G 3=⊥ := by
  let M := make nil x y
  have ux : Commute (portU x y) x := by
    change M.u*M.x=M.x*M.u
    have e := M.ux
    change M.a=1 at ha
    simpa only [ha,mul_one] using e
  have uy : Commute (portU x y) y := by
    change M.u*M.y=M.y*M.u
    have e := M.uy
    change M.b=1 at hb
    simpa only [hb,mul_one] using e
  have vx : Commute (portV x y) x := by
    change M.v*M.x=M.x*M.v
    have e := M.vx
    change M.b=1 at hb
    simpa only [hb,mul_one] using e
  have vy : Commute (portV x y) y := by
    change M.v*M.y=M.y*M.v
    have e := M.vy
    change M.d=1 at hd
    simpa only [hd,mul_one] using e
  let Z := Subgroup.center G
  let f := QuotientGroup.mk' Z
  have g := map_gen f (QuotientGroup.mk'_surjective Z) gen
  have cu : f (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr (gen_center x y _ gen ux uy)
  have cv : f (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr (gen_center x y _ gen vx vy)
  have cux : Commute (f (portC x y)) (f x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [portU,map_commutatorElement] using cu
  have cvy : Commute (f (portC x y)) (f y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [portV,map_commutatorElement] using cv
  have ce : f x*f y=f y*f x*f (portC x y) := by
    simpa only [map_mul] using congrArg f (ports_xy x y)
  have Q := c_center_class_two (f x) (f y) (f (portC x y)) g ce
    (gen_center _ _ _ g cux cvy)
  have L := map_ls f (QuotientGroup.mk'_surjective Z) 2
  rw [Q,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at L
  exact Subgroup.lowerCentralSeries_succ_eq_bot ⊤ L

def Pair (x y : G) : Subgroup G := Subgroup.closure ({x,y} : Set G)

def leftPort (x y : G) : Pair x y := ⟨x,Subgroup.subset_closure (by simp)⟩
def rightPort (x y : G) : Pair x y := ⟨y,Subgroup.subset_closure (by simp)⟩

theorem pair_generates (x y : G) : Generates (leftPort x y) (rightPort x y) := by
  apply Subgroup.map_subtype_inj.mp
  rw [MonoidHom.map_closure,Set.image_pair,Subgroup.map_top,Subgroup.subtype_range]
  rfl

theorem pair_nil (x y : G) (i : ℕ) (h : LS G i=⊥) : LS (Pair x y) i=⊥ := by
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_bot,Subgroup.top_subtype_lowerCentralSeries,← le_bot_iff]
  exact (Subgroup.lowerCentralSeries_mono i (show Pair x y ≤ ⊤ from le_top)).trans (le_of_eq h)

theorem pair_lift (x y : G) (n : ℕ)
    (h : Ribbon.Cycle (leftPort x y) (rightPort x y) n) : Ribbon.Cycle x y n :=
  cycle_map (Pair x y).subtype Subtype.val_injective _ _ n h

end RibbonClass4Fallback
#print axioms RibbonClass4Fallback.class_drop
#print axioms RibbonClass4Fallback.cycle_map
#print axioms RibbonClass4Fallback.pair_generates
#print axioms RibbonClass4Fallback.pair_nil
#print axioms RibbonClass4Fallback.pair_lift
