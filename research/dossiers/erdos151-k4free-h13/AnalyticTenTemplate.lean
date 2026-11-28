import NeutralHostColor
import CubicTenDelete
import Mathlib.Tactic.FinCases

open scoped BigOperators
namespace H13MixedComponents
set_option linter.style.haveILetI false
open Finset NineLinkPivot H13PetersenComponents Erdős151.H13
open Erdos151H12

/-- The only missing combinatorial step if supplied independently:
squareless cubic order ten is Petersen. -/
def MooreTen : Prop :=
  ∀ (G : Fin 10→Fin 10→Prop) [DecidableRel G],
    (∀ a b, G a b ↔ G b a) → (∀ a, ¬G a a) →
    (∀ v a b, G v a → G v b → ¬G a b) →
    (∀ a b x y, a≠b → G a x → G b x → G a y → G b y → x=y) →
    (∀ a, deg G univ a=3) →
    ∃ f : Fin 10 ≃ Fin 10, ∀ a b, G a b ↔ PetersenAdj (f a) (f b)

theorem no_square_one_common {V : Type*} (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (h : ¬∃ x : Fin 4→V, Function.Injective x ∧ ∀ i, G (x i) (x (i+1))) :
    ∀ a b x y, a≠b → G a x → G b x → G a y → G b y → x=y := by
  intro a b x y ab ax bx ay by'
  by_contra xy
  have anx : a≠x := fun e => irr a (e.symm ▸ ax)
  have any : a≠y := fun e => irr a (e.symm ▸ ay)
  have bnx : b≠x := fun e => irr b (e.symm ▸ bx)
  have bny : b≠y := fun e => irr b (e.symm ▸ by')
  let f : Fin 4→V := fun i => if i=0 then a else if i=1 then x else if i=2 then b else y
  apply h
  refine ⟨f,?_,?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f,Ne.symm ab,Ne.symm anx,Ne.symm any,
        Ne.symm bnx,Ne.symm bny,Ne.symm xy]
  · intro i
    fin_cases i
    · simpa [f] using ax
    · simpa [f] using sym bx
    · simpa [f] using by'
    · simpa [f] using sym ay

def analyticTenModel (moore : MooreTen) (D : Fin 10→Fin 10→Prop) [DecidableRel D]
    (sym : ∀ {a b}, D a b → D b a) (irr : ∀ a, ¬D a a)
    (tf : ∀ w a b, D w a → D w b → ¬D a b) (cube : ∀ a, deg D univ a=3) : Template where
  n := 10
  adj := fun a b => decide (D a b)
  cubic := by intro a; simpa [deg,near] using cube a
  delete := by
    intro U sm a b ha hb
    simpa using cubic_ten_delete D (fun {_ _} h => sym h) irr tf cube (by simp) U sm a b ha hb
  cut := by
    intro U non all
    simpa [cross] using cubic_ten_cut D (fun {_ _} h => sym h) irr tf cube (by simp) U non all
  kind := by
    by_cases h : ∃ x : Fin 4→Fin 10, Function.Injective x ∧ ∀ i, D (x i) (x (i+1))
    · obtain ⟨x,hi,he⟩ := h
      exact Or.inl ⟨x,hi,by simpa using he⟩
    · obtain ⟨f,hf⟩ := moore D (fun a b=>⟨sym,sym⟩) irr tf
        (no_square_one_common D (fun {_ _} e=>sym e) irr h) cube
      exact Or.inr ⟨f,by simpa using hf⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Produces an actual local model from the analytic cubic shape, without
calling a host or graph enumeration. -/
theorem actual_ten_template (moore : MooreTen) (C : V→V→Prop) [DecidableRel C]
    (sym : BikovLocal.Sym C) (irr : BikovLocal.Loopless C)
    (tf : ∀ w a b c, C w a → C w b → C w c → C a b → C a c → ¬C b c)
    (w : V) (hc : (neighbors C w).card=10)
    (cube : ∀ a∈neighbors C w, deg C (neighbors C w) a=3) :
    HasTemplate (graphOf C sym irr) w := by
  classical
  let J := {x : V // C w x}
  let f : J ≃ Fin 10 := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype]
    exact hc)
  let D : Fin 10→Fin 10→Prop := fun a b => C (f.symm a).val (f.symm b).val
  letI : DecidableRel D := fun a b => inferInstanceAs (Decidable (C (f.symm a).val (f.symm b).val))
  have dC (a : Fin 10) : deg D univ a=3 := by
    let N := (neighbors C w).filter (C (f.symm a).val)
    let e : Fin 10 ↪ V := f.symm.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
    have h : (near D univ a).map e = N := by
      ext x
      constructor
      · intro hx
        obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
        exact mem_filter.mpr ⟨(mem_neighbors C).mpr (f.symm i).property,
          (mem_filter.mp hi).2⟩
      · intro hx
        obtain ⟨hw,ha⟩ := mem_filter.mp hx
        let u : J := ⟨x,(mem_neighbors C).mp hw⟩
        refine mem_map.mpr ⟨f u,mem_filter.mpr ⟨mem_univ _,?_⟩,?_⟩
        · change C (f.symm a).val (f.symm (f u)).val
          rw [f.symm_apply_apply]
          exact ha
        · change (f.symm (f u)).val = x
          rw [f.symm_apply_apply]
    have hh := congrArg Finset.card h
    rw [card_map] at hh
    exact hh.trans (cube _ ((mem_neighbors C).mpr (f.symm a).property))
  let T := analyticTenModel moore D
    (fun {_ _} h=>sym h) (fun a h=>irr (f.symm a).val h)
    (fun v a b ha hb => tf w _ _ _ (f.symm v).property (f.symm a).property (f.symm b).property ha hb) dC
  refine ⟨T,f,?_⟩
  intro a b
  change C a.val b.val ↔ decide (C (f.symm (f a)).val (f.symm (f b)).val) = true
  have ha : (f.symm (f a)).val = a.val := congrArg Subtype.val (f.symm_apply_apply a)
  have hb : (f.symm (f b)).val = b.val := congrArg Subtype.val (f.symm_apply_apply b)
  rw [decide_eq_true_eq,ha,hb]

#print axioms actual_ten_template
end H13MixedComponents
