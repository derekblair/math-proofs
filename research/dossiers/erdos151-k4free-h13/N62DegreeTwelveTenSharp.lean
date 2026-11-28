import N62DegreeTwelveTen
import N62LowCasesClose
import N62A10BBridge
import N62A10CBridge
import N62A11CoreActual
import N62A11Ghost
import N62A12Actual

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G C : V→V→Prop) [DecidableRel G] [DecidableRel C]

/-- Order 62 already excludes every positive d12/r10 source row.
The proof uses exact owner and two-neighbor private-column exchange. -/
theorem degreeTwelve_r10_at_least62_sharp
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (csym : ∀ {a b}, C a b → C b a)
    (sub : ∀ {a b}, C a b → G a b) (two : TwoTriangles C)
    (deg : ∀ v, (neighbors G v).card≤12)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (hn : 62≤Fintype.card V) (w : V) (s12 : (neighbors G w).card=12)
    (t10 : (neighbors C w).card=10)
    (hmin : ∀ u∈neighbors C w, 8≤(neighbors C u).card)
    (e : Nat) (he : ∑ u∈neighbors C w,row C (neighbors C w) u=2*e) :
    e≤15 := by
  classical
  have e16 := degreeTwelve_r10_at_least62 G C sym irr tf sub two deg upper hn w s12 t10 hmin e he
  by_contra! pos
  have eq : e=16 := by omega
  have h16 : ∑ u∈neighbors C w,row C (neighbors C w) u=32 := by rw [he,eq]
  let S := neighbors G w
  let T := neighbors C w
  let X := ext S w
  let H := S\T
  have ts : T⊆S := fun _ hs => (mem_neighbors G).mpr (sub ((mem_neighbors C).mp hs))
  have hw : w∉S := fun h=>irr w ((mem_neighbors G).mp h)
  have wx : w∉X := fun h => (mem_sdiff.mp h).2 (mem_insert_self _ _)
  have hc : H.card=2 := by
    change (S\T).card=2
    rw [card_sdiff_of_subset ts,s12,t10]
  obtain ⟨g,h,gh,ge⟩ := card_eq_two.mp hc
  have gH : g∈H := by rw [ge]; simp
  have hH : h∈H := by rw [ge]; simp
  have gt : g∉T := (mem_sdiff.mp gH).2
  have ht : h∉T := (mem_sdiff.mp hH).2
  have se : S=insert g (insert h T) := by
    have e := sdiff_union_of_subset ts
    change H∪T=S at e
    rw [ge] at e
    simpa [insert_union] using e.symm
  have sf : Free (Forbidden G) (S : Set V) := by
    convert neighborhood_free G sym tf w using 1
    ext x
    exact mem_neighbors G
  have out : Disjoint X S := Finset.disjoint_left.mpr (fun x hx hs => (mem_sdiff.mp hx).2 (mem_insert_of_mem hs))
  have triS : ∀ a∈S,∀ b∈S,∀ c∈S, G a b → G a c → G b c → False := by
    intro a ha b hb c hc ab ac bc
    exact tf w a b c ((mem_neighbors G).mp ha) ((mem_neighbors G).mp hb) ((mem_neighbors G).mp hc) ab bc ac
  have rigid := sixteen_link_exact G C sym irr tf csym sub two deg upper hn w s12 t10 hmin h16
  have iso (u : V) (hu : u∈H) (v : V) (hv : v∈S) : ¬G u v :=
    fun h => (mem_sdiff.mp hu).2 (rigid u (mem_sdiff.mp hu).1 v hv h).1
  have lw (u : V) (hu : u∈H) : Lone G u w :=
    ⟨sym ((mem_neighbors G).mp (mem_sdiff.mp hu).1),fun z zr =>
      iso u hu z ((mem_neighbors G).mpr zr.2) zr.1⟩
  have sh : H⊆S := sdiff_subset
  obtain ⟨cap,cT,hit⟩ := tight_lone_row_caps G C sym irr sub two deg w s12 t10 hmin
  obtain ⟨_,lc⟩ := degreeTwelve_upper_slots_h13 G C sym irr sub two deg w s12 hmin 16
    (by simpa only using h16)
  have lcap : (∑ x∈X,lcol G S x)≤62 := by
    change (∑ x∈X,lcol G S x)+7*T.card≤132 at lc
    have ct : T.card=10 := t10
    omega
  let F := nearFrame G S X sym irr tf s12 sf out upper
  have ac : F.marks.card=acnt G S X := nearFrame_count_marks G S X sym irr tf s12 sf out upper
  have dc : F.doubles.card=dcnt G S X := rfl
  have dMarked (u : V) (ut : u∈T) (um : u∈F.marks) : (Dstar G F u).card≤3 := by
    have q := near_Dstar_lone_bound G F sym u
    rw [if_pos um] at q
    have c : ambientLoneRow G X u≤4 := cT u ut
    omega
  have dAny (u : V) (ut : u∈T) : (Dstar G F u).card≤4 := by
    have q := near_Dstar_lone_bound G F sym u
    have c : ambientLoneRow G X u≤4 := cT u ut
    omega
  have low (cases' : (acnt G S X=8 ∧ dcnt G S X=27 ∧ bcnt G S X=4 ∧ ccnt G S X=0) ∨
      (acnt G S X=9 ∧ dcnt G S X=26 ∧ bcnt G S X+ccnt G S X=3 ∧ ccnt G S X≤1) ∨
      (acnt G S X=10 ∧ dcnt G S X=26 ∧ 1≤bcnt G S X ∧ ccnt G S X=0)) : False :=
    tight16_low_private_impossible G S X H sym irr tf s12 sf out upper deg sh hc iso triS cap hit lcap cases'
  have cases' := e16_actual_private_cases G C sym irr tf sub two deg upper hn w s12 t10 hmin h16
  rcases cases' with h8|h9|h10|h10|h11|h12
  · exact low (Or.inl ⟨h8.1,h8.2.1,h8.2.2.1,h8.2.2.2.1⟩)
  · exact low (Or.inr (Or.inl h9))
  · exact low (Or.inr (Or.inr ⟨h10.1,h10.2.1,h10.2.2.1,h10.2.2.2.1⟩))
  · obtain ⟨a,d,bc⟩ := h10
    rcases a10_private_split G S X sym irr tf s12 sf out upper a bc with ⟨b,c⟩|⟨b,c,p,ps,q,qs,pq,ep,U,bc⟩
    · exact a10_c_columns_impossible G S X T w g h gt ht gh t10 se wx sym irr tf s12
        sf out upper deg (ge ▸ iso) (ge ▸ lw) cap cT (ge ▸ hit) lcap a b c d
    · change dcnt G S X=25 at d
      have bound := a10_b_columns_bound G S X T g h gt ht gh t10 se sym irr tf s12
        sf out upper (ge ▸ iso) cT b p q ps qs pq ep U bc
      omega
  · obtain ⟨a,d⟩ := h11
    have qe : (S\F.marks).card=1 := by
      rw [card_sdiff_of_subset F.markSub,s12,ac,a]
    obtain ⟨p,pe⟩ := card_eq_one.mp qe
    have ms : F.marks=S.erase p := by
      rw [←sdiff_singleton_eq_erase,←pe,Finset.sdiff_sdiff_eq_self F.markSub]
    have pS : p∈S := (mem_sdiff.mp (show p∈S\F.marks by simp [pe])).1
    rw [se,mem_insert,mem_insert] at pS
    rcases pS with pg|ph|pt
    · subst p
      exact a11_unmarked_ghost_excluded G F sym irr s12 sf out upper deg T h g ht gt gh.symm t10
        (by rw [se]; ext z; simp [or_left_comm,or_comm,or_assoc])
        (by rw [ms]; exact mem_erase.mpr ⟨gh.symm,sh hH⟩)
        (fun u ut=>by rw [ms]; exact mem_erase.mpr ⟨fun e=>gt (e ▸ ut),ts ut⟩)
        (fun u ut=>dMarked u ut (by rw [ms]; exact mem_erase.mpr ⟨fun e=>gt (e ▸ ut),ts ut⟩))
        (by rw [dc]; exact d)
    · subst p
      exact a11_unmarked_ghost_excluded G F sym irr s12 sf out upper deg T g h gt ht gh t10 se
        (by rw [ms]; exact mem_erase.mpr ⟨gh,sh gH⟩)
        (fun u ut=>by rw [ms]; exact mem_erase.mpr ⟨fun e=>ht (e ▸ ut),ts ut⟩)
        (fun u ut=>dMarked u ut (by rw [ms]; exact mem_erase.mpr ⟨fun e=>ht (e ▸ ut),ts ut⟩))
        (by rw [dc]; exact d)
    · change 24≤dcnt G S X at d
      have b := a11_core_actual_owner_bound G F sym irr s12 sf out upper T g h gt ht gh t10 se
        p pt ms (fun u ut=>by
          by_cases ue : u=p
          · simpa [ue] using dAny u ut
          · simp [ue]
            exact dMarked u ut (by rw [ms]; exact mem_erase.mpr ⟨ue,ts ut⟩))
      rw [dc] at b
      omega
  · obtain ⟨a,d⟩ := h12
    change 23≤dcnt G S X at d
    have ms : F.marks=S := eq_of_subset_of_card_le F.markSub (by rw [s12,ac,a])
    have b := a12_actual_owner_bound G F sym irr s12 sf out upper T g h gt ht gh t10 se ms
      (fun u ut=>dMarked u ut (by rw [ms]; exact ts ut))
    rw [dc] at b
    omega

#print axioms degreeTwelve_r10_at_least62_sharp
end Erdos151N62
