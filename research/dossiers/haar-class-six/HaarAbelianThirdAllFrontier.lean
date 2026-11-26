import HaarClass6Frontier
import HaarAbelianThirdOdd
import HaarThirdAbelianRankTwo

namespace HaarAbelianThirdAllFrontier
open HaarUniversal36 HaarAllNoncommuting HaarClass4Generate HaarClass4Ports
open HaarClass5TemplateClosure HaarClass6ParallelCycle HaarAbelianThirdOdd
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem rank_result (nil : ∃ n, L G n=⊥) (ab : AbelianThird G) (deep : L G 3≠⊥)
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
        have all (n : ℕ) : L G (2+n)=L G 2 := by
          induction n with
          | zero => rfl
          | succ n ih =>
            change ⁅L G (2+n),(⊤ : Subgroup G)⁆=L G 2
            rw [ih]
            exact same.symm
        obtain ⟨n,ht⟩ := nil
        have bn : L G (2+n)≤⊥ :=
          (Subgroup.lowerCentralSeries_antitone _ (show n≤2+n by omega)).trans (le_of_eq ht)
        exact deep (same.symm.trans ((all n).symm.trans (le_bot_iff.mp bn)))
      by_cases indep : ∀ a b : ℤ, u^a*v^b=1 → a%3=0 ∧ b%3=0
      · exact Or.inl (HaarThirdAbelianRankTwo.cycle nil deep ab x y gen
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
        exact HaarClass6Frontier.dependent_card u v hu hv nn e (fun z => nz z.1 z.2)
    · apply Or.inl
      apply HaarClass6OddNoThree.swap_cycle
      apply case_v_with_close odd y x (close_abelian ab y x)
      change (portV Y X)^(3:ℕ)≠1
      simpa only [HaarClass6OddNoThree.v_swapped (quote_nil 3),inv_pow,ne_eq,inv_eq_one] using hu
  · exact Or.inl (case_v_with_close odd x y (close_abelian ab x y) hv)

end HaarAbelianThirdAllFrontier
#print axioms HaarAbelianThirdAllFrontier.rank_result
