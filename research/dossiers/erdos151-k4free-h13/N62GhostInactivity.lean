import N62TenAmbientRigidity

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V→V→Prop) [DecidableRel G] [DecidableRel C]

theorem sixteen_ghosts_inactive
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (csym : ∀ {a b}, C a b → C b a)
    (sub : ∀ {a b}, C a b → G a b) (two : TwoTriangles C)
    (deg : ∀ v, (neighbors G v).card≤12)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (hn : 62≤Fintype.card V) (w : V) (s12 : (neighbors G w).card=12)
    (t10 : (neighbors C w).card=10)
    (hmin : ∀ u, (neighbors C u).card=0 ∨ 8≤(neighbors C u).card)
    (h16 : ∑ u∈neighbors C w,row C (neighbors C w) u = 32) :
    ∀ g∈neighbors G w \ neighbors C w,
      Lone G g w ∧ 7≤ambientLoneRow G (ext (neighbors G w) w) g ∧
      (neighbors C g).card=0 := by
  classical
  let S := neighbors G w
  let T := neighbors C w
  let X := ext S w
  let I := ∑ x∈X,ncol G S x
  let L := ∑ x∈X,lcol G S x
  let P := (specialCols G S X).card
  have ts : T⊆S := fun _ hu => (mem_neighbors G).mpr (sub ((mem_neighbors C).mp hu))
  have coreMin (u : V) (hu : u∈T) : 8≤(neighbors C u).card := by
    rcases hmin u with h|h
    · have uc := (mem_neighbors C).mpr (csym ((mem_neighbors C).mp hu))
      have dh := Finset.card_pos.mpr ⟨w,uc⟩
      omega
    · exact h
  have rigid := sixteen_link_exact G C sym irr tf csym sub two deg upper hn w s12 t10 coreMin h16
  have hw : w∉S := fun h => irr w ((mem_neighbors G).mp h)
  have hf : Free (Forbidden G) (S : Set V) := by
    convert neighborhood_free G sym tf w using 1
    ext x
    exact mem_neighbors G
  have dx : Disjoint X S := Finset.disjoint_left.mpr (fun x hx h => (Finset.mem_sdiff.mp hx).2
    (Finset.mem_insert_of_mem h))
  have cX : 49≤X.card := by
    change 49≤((Finset.univ : Finset V)\insert w S).card
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Finset.card_insert_of_notMem hw]
    change S.card=12 at s12
    omega
  have lo := degreeTwelve_lower_incidence_h13 G S X sym irr tf s12 hf dx upper
  have sp := degreeTwelve_special_cost_h13 G S X sym irr tf s12 hf dx upper
  obtain ⟨hi,_⟩ := degreeTwelve_upper_slots_h13 G C sym irr sub two deg w s12 coreMin 16 (by simpa only using h16)
  change 3*X.card≤I+12+P at lo
  change 2*P≤L+12 at sp
  change I+32≤132 at hi
  have total : 58≤∑ u∈S,ambientLoneRow G X u := by
    have h := lcol_eq_incidence G S X sym
    rw [transpose] at h
    change L = ∑ u∈S,ambientLoneRow G X u at h
    omega
  have xc (u : V) : Disjoint (X.filter (Lone G u)) (neighbors C u) := by
    apply Finset.disjoint_left.mpr
    intro z hz hc
    obtain ⟨v,_,_,hv,hv',_,_⟩ := two u z ((mem_neighbors C).mp hc)
    exact (Finset.mem_filter.mp hz).2.2 v ⟨sub hv,sub hv'⟩
  have xu (u : V) : (X.filter (Lone G u)) ∪ neighbors C u ⊆ neighbors G u := by
    intro z hz
    rcases Finset.mem_union.mp hz with h|h
    · exact (mem_neighbors G).mpr (Finset.mem_filter.mp h).2.1
    · exact (mem_neighbors G).mpr (sub ((mem_neighbors C).mp h))
  have small (u : V) (hu : u∈T) : ambientLoneRow G X u≤4 := by
    have h := Finset.card_le_card (xu u)
    rw [Finset.card_union_of_disjoint (xc u)] at h
    have d := deg u
    have k := coreMin u hu
    change (X.filter (Lone G u)).card≤4
    omega
  have cap (u : V) (hu : u∈S) : ambientLoneRow G X u≤11 := by
    have h := row_degree G sym w u hu hw
    have d := deg u
    have l : ambientLoneRow G X u ≤ row G X u :=
      Finset.card_le_card (fun x hx => Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2.1⟩)
    change row G X u + row G S u + 1=(neighbors G u).card at h
    omega
  intro g hg
  obtain ⟨gs,gt⟩ := Finset.mem_sdiff.mp hg
  have lw : Lone G g w := ⟨sym ((mem_neighbors G).mp gs),fun z q =>
    gt (rigid g gs z ((mem_neighbors G).mpr q.2) q.1).1⟩
  have f : (S\T).card=2 := by
    rw [Finset.card_sdiff_of_subset ts,s12,t10]
  have one : (((S\T).erase g)).card=1 := by
    rw [Finset.card_erase_of_mem hg,f]
  have p1 := Finset.sum_le_sum (s:=T) (g:=fun _=>4) small
  have p2 := Finset.sum_le_sum (s:=(S\T).erase g) (g:=fun _=>11)
    (fun u hu=>cap u (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hu)).1)
  have e1 := Finset.sum_sdiff ts (f:=ambientLoneRow G X)
  have e2 := Finset.sum_erase_add (s:=S\T) (f:=ambientLoneRow G X) hg
  simp only [Finset.sum_const,nsmul_eq_mul,show T.card=10 from t10,one] at p1 p2
  have ge : 7≤ambientLoneRow G X g := by omega
  have fin : (neighbors C g).card=0 := by
    have h := Finset.card_le_card (xu g)
    rw [Finset.card_union_of_disjoint (xc g)] at h
    have d := deg g
    change 7≤(X.filter (Lone G g)).card at ge
    rcases hmin g with h|h'
    · exact h
    · omega
  exact ⟨lw,ge,fin⟩

#print axioms sixteen_ghosts_inactive
end Erdos151N62
