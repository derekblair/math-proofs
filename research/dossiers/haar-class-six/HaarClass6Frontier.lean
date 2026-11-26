import HaarClass6RankTwoActual
import HaarClass6OddNoThree
import HaarP3RankSplit
import HaarP3CollectCore

namespace HaarClass6Frontier
open HaarUniversal36 HaarAllNoncommuting HaarClass4Generate HaarClass4Ports
open HaarClass5TemplateClosure HaarClass6ParallelCycle
open HaarClass5P3Meta HaarP3Class4Order
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem dependent_card (u v : G) (hu : u^(3:ℕ)=1) (hv : v^(3:ℕ)=1)
    (nn : ¬(u=1 ∧ v=1)) {a b : ℤ} (eq : u^a*v^b=1) (nz : ¬(a%3=0 ∧ b%3=0)) :
    Nat.card (Subgroup.closure ({u,v}:Set G))=3 := by
  by_cases ve : v=1
  · rw [Set.pair_comm]
    exact HaarP3RankSplit.card_span v u (fun e => nn ⟨e,ve⟩) hu (by rw [ve]; exact Subgroup.one_mem _)
  apply HaarP3RankSplit.card_span u v ve hv
  have hU : u^(3:ℤ)=1 := by exact_mod_cast hu
  have hV : v^(3:ℤ)=1 := by exact_mod_cast hv
  have au : u^(a%3)=u^a := HaarP3CollectCore.pow_period u hU a
  have na : a%3≠0 := by
    intro e
    have vo : orderOf v=3 := by
      let : Fact (Nat.Prime 3) := ⟨by decide⟩
      exact orderOf_eq_prime hv ve
    rw [←au,e,zpow_zero,one_mul] at eq
    have dv := orderOf_dvd_iff_zpow_eq_one.mpr eq
    rw [vo] at dv
    exact nz ⟨e,Int.emod_eq_zero_of_dvd dv⟩
  have h : a%3=1 ∨ a%3=2 := by omega
  have mem (g : G) (r : ℤ) (s : g*v^r=1) : g∈Subgroup.zpowers v := by
    rw [eq_inv_of_mul_eq_one_left s]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _)
  rw [←au] at eq
  rcases h with h|h
  · rw [h,zpow_one] at eq
    exact mem u b eq
  · rw [h] at eq
    have z : u^(2:ℤ)=u^(2:ℕ) := zpow_natCast u (2:ℕ)
    rw [z] at eq
    have hi : u = (u^(2:ℕ))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [←pow_succ',hu]
    rw [hi]
    exact Subgroup.inv_mem _ (mem (u^(2:ℕ)) b eq)

theorem rank_result (nil : L G 6=⊥) (deep : L G 5≠⊥)
    (odd : Odd (Nat.card G)) (x y : G) (gen : Generates x y) :
    HasCycle x y 64 ∨ Nat.card ((L G 2).map (QuotientGroup.mk' (L G 3)))=3 := by
  classical
  let S := L G 3
  let f := QuotientGroup.mk' S
  let X := f x
  let Y := f y
  let u := portU X Y
  let v := portV X Y
  have mu : f (portU x y)=u := by simp [u,X,Y,portU,portC,map_commutatorElement,map_inv]
  have mv : f (portV x y)=v := by simp [v,X,Y,portV,portC,map_commutatorElement,map_inv]
  by_cases hv : v^(3:ℕ)=1
  · by_cases hu : u^(3:ℕ)=1
    · have nn : ¬(u=1 ∧ v=1) := by
        rintro ⟨un,vn⟩
        have cx : Commute (portC X Y) X := commutatorElement_eq_one_iff_commute.mp un
        have cy : Commute (portC X Y) Y := commutatorElement_eq_one_iff_commute.mp vn
        have g : Generates X Y := map_gen f (QuotientGroup.mk'_surjective S) gen
        have bot : L (G ⧸ S) 2=⊥ := c_center_class_two X Y _ g (ports_xy X Y) (gen_center X Y _ g cx cy)
        have M : (L G 2).map f = L (G ⧸ S) 2 := map_ls f (QuotientGroup.mk'_surjective S) 2
        rw [bot,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at M
        have same : L G 2=L G 3 := le_antisymm M
          (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G) (by decide : 2≤3))
        have next' (a b : ℕ) (h : L G a=L G b) : L G (a+1)=L G (b+1) :=
          congrArg (fun T : Subgroup G => ⁅T,(⊤ : Subgroup G)⁆) h
        exact deep ((next' 4 5 (next' 3 4 (next' 2 3 same))).trans nil)
      by_cases indep : ∀ a b : ℤ, u^a*v^b=1 → a%3=0 ∧ b%3=0
      · exact Or.inl (HaarClass6RankTwoActual.cycle nil deep x y gen
          (by change (f (portU x y))^(3:ℕ)=1; rw [mu]; exact hu)
          (by
            intro a b e
            change (f (portU x y))^a*(f (portV x y))^b=1 at e
            rw [mu,mv] at e
            exact indep a b e))
      · push Not at indep
        obtain ⟨a,b,e,nz⟩ := indep
        have span : (L G 2).map f=Subgroup.closure ({u,v}:Set (G ⧸ S)) := HaarP3LayerGen.ls2_mod_ls3 x y gen
        right
        change Nat.card ((L G 2).map f)=3
        rw [span]
        exact dependent_card u v hu hv nn e (fun z => nz z.1 z.2)
    · apply Or.inl
      apply HaarClass6OddNoThree.swap_cycle
      apply case_v nil odd y x
      change (portV Y X)^(3:ℕ)≠1
      simpa only [HaarClass6OddNoThree.v_swapped (quote_nil 3),inv_pow,ne_eq,inv_eq_one] using hu
  · exact Or.inl (case_v nil odd x y hv)

end HaarClass6Frontier
#print axioms HaarClass6Frontier.rank_result
