import H12UnblockedWitness
import H12DegreeTenCounts

namespace Erdos151H12
open Erdős151
open scoped BigOperators
variable {V : Type*} [DecidableEq V] (G : V → V → Prop)

theorem degreeEleven_ambient_unblocked_h13
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (tf : TriangleFreeLinks G)
    (S U : Finset V) (h10 : S.card = 11) (dis : Disjoint U S)
    (upper : ∀ F : Finset V, Free (Forbidden G) (F : Set V) → F.card ≤ 12)
    (add : ∀ x ∈ U, Free (Forbidden G) (insert x (S : Set V))) :
    U.card ≤ 3 ∧
      (U.card = 3 → 6 ≤ ∑ x∈U,ncol G S x) ∧
      (U.card = 2 → (∑ x∈U,ncol G S x) = 0 →
        ∃ u v, u ∈ U ∧ v ∈ U ∧ u ≠ v ∧ Lone G u v ∧
          ∀ s∈S, ¬ G u s ∧ ¬ G v s) := by
  classical
  have out {x : V} (hx : x ∈ U) : x ∉ S := Finset.disjoint_left.mp dis hx
  have hbad (x y : V) (hx : x ∈ U) (hy : y ∈ U) (hne : x ≠ y) :
      ¬ Free (Forbidden G) (insert x (insert y (S : Set V))) := by
    intro hf
    have hu : x ∉ insert y S := by simp [hne,out hx]
    have hc := upper (insert x (insert y S)) (by simpa only [Finset.coe_insert] using hf)
    rw [Finset.card_insert_of_notMem hu, Finset.card_insert_of_notMem (out hy),h10] at hc
    omega
  have clique (x : V) (hx : x ∈ U) (y : V) (hy : y ∈ U) (hne : x ≠ y) : G x y :=
    private_adjacent (Forbidden G) G _ x y hne
      (fun A hA a ha b hb e => forbidden_clique G sym A hA a b ha hb e)
      (add x hx) (add y hy) (hbad x y hx hy hne)
  refine ⟨?_,?_,?_⟩
  · by_contra! hh
    obtain ⟨a,b,c,d,ha,hb,hc,hd,hab,hac,had,hbc,hbd,hcd⟩ := Finset.three_lt_card_iff.mp hh
    exact tf a b c d (clique _ ha _ hb hab) (clique _ ha _ hc hac) (clique _ ha _ hd had)
      (clique _ hb _ hc hbc) (clique _ hc _ hd hcd) (clique _ hb _ hd hbd)
  · intro h3
    have d2 (u : V) (hu : u ∈ U) : 2 ≤ ncol G S u := by
      have hcard : (U.erase u).card = 2 := by
        have := Finset.card_erase_add_one hu
        omega
      obtain ⟨v,w,hvw,hvwset⟩ := Finset.card_eq_two.mp hcard
      have hv' : v∈U.erase u := by simp [hvwset]
      have hw' : w∈U.erase u := by simp [hvwset]
      obtain ⟨hvu,hv⟩ := Finset.mem_erase.mp hv'
      obtain ⟨hwu,hw⟩ := Finset.mem_erase.mp hw'
      exact unblocked_triangle_two_neighbors G sym irr tf S u v w hvu.symm hwu.symm
        (clique _ hu _ hv hvu.symm) (clique _ hu _ hw hwu.symm) (clique _ hv _ hw hvw)
        (add u hu) (add v hv) (add w hw) (hbad _ _ hu hv hvu.symm) (hbad _ _ hu hw hwu.symm)
    have hh := Finset.sum_le_sum (f:=fun _ => 2) d2
    simpa [h3] using hh
  · intro h2 h0
    obtain ⟨u,v,hne,hEq⟩ := Finset.card_eq_two.mp h2
    have hu : u∈U := by simp [hEq]
    have hv : v∈U := by simp [hEq]
    have none (w : V) (hw : w∈U) (s : V) (hs : s∈S) : ¬ G w s := by
      intro hws
      have hmem := (mem_ns (G:=G) S w).mpr ⟨hs,hws⟩
      have hp : 0 < ncol G S w := Finset.card_pos.mpr ⟨s,hmem⟩
      have hsum := Finset.single_le_sum (f:=ncol G S) (fun _ _ => Nat.zero_le _) hw
      omega
    refine ⟨u,v,hu,hv,hne,?_,fun s hs => ⟨none _ hu _ hs,none _ hv _ hs⟩⟩
    by_contra hl
    obtain ⟨x,hx,hux,-⟩ := unblocked_both_nonLone_common G sym irr _ u v hne
      (add u hu) (add v hv) (hbad _ _ hu hv hne) hl
    exact none u hu x hx hux

#print axioms degreeEleven_ambient_unblocked_h13
end Erdos151H12
