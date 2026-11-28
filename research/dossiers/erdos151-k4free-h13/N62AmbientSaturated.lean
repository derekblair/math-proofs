import N62OwnerPressure

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V→V→Prop) [DecidableRel G] [DecidableRel C]

private theorem count_one_per_owner
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (S X : Finset V) (s12 : S.card=12) (sf : Free (Forbidden G) (S : Set V))
    (dx : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (blocked : ∀ x∈X, ¬Free (Forbidden G) (insert x (S : Set V)))
    (u : V) (hu : u∈S) : (singlesFor G S X u).card≤1 := by
  have h0 := degreeTwelve_private_capacity_h13 G sym irr tf S X s12 sf dx upper u hu
  have hL := privatePool_isolated G sym S X sf dx blocked u
  have hqi := Finset.card_le_card hL.1
  have hAq := Finset.card_le_card (show singlesFor G S X u ⊆ lonePrivatePool G S X u from
    fun x hx => (singlesFor_ownership G sym irr S X sf blocked u x hx).2.2)
  omega

/-- Graph-to-label saturation step. All sets are exact ambient owners,
outer singleton leaves, or exterior double-lone columns. -/
noncomputable def frame_of_ambient_saturated (w : V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sub : ∀ {a b}, C a b → G a b) (two : TwoTriangles C)
    (deg : ∀ v, (neighbors G v).card≤12)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (hn : 62≤Fintype.card V) (s12 : (neighbors G w).card=12) (t10 : (neighbors C w).card=10)
    (hmin : ∀ u∈neighbors C w, 8≤(neighbors C u).card)
    (e : Nat) (he : ∑ u∈neighbors C w,row C (neighbors C w) u = 2*e)
    (hambient : 34≤∑ u∈neighbors G w,row G (neighbors G w) u) :
    SaturationFrame G (neighbors G w) (ext (neighbors G w) w) := by
  classical
  let S := neighbors G w
  let T := neighbors C w
  let X := ext S w
  let A := weightedSet X (Acol G S)
  let D := weightedSet X (Dcol G S)
  let I := ∑ x∈X,ncol G S x
  let L := ∑ x∈X,lcol G S x
  have hwS : w∉S := fun h => irr w ((mem_neighbors G).mp h)
  have hTS : T⊆S := fun _ hx => (mem_neighbors G).mpr (sub ((mem_neighbors C).mp hx))
  have hXS : Disjoint X S := Finset.disjoint_left.mpr (fun x hx hs => (Finset.mem_sdiff.mp hx).2
    (Finset.mem_insert_of_mem hs))
  have hx49 : 49≤X.card := by
    change 49≤((Finset.univ : Finset V) \ insert w S).card
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Finset.card_insert_of_notMem hwS]
    change S.card=12 at s12
    omega
  have sfree : Free (Forbidden G) (S : Set V) := by
    convert neighborhood_free G sym tf w using 1
    ext x
    exact mem_neighbors G
  have blocked (x : V) (hx : x∈X) : ¬Free (Forbidden G) (insert x (S : Set V)) :=
    all_exterior_blocked_12 G S s12 upper x (fun hs => Finset.disjoint_left.mp hXS hx hs)
  have dAD : Disjoint A D := Finset.disjoint_left.mpr (by
    intro x hA hD
    have a : ncol G S x=1 := (Finset.mem_filter.mp hA).2
    have d : ncol G S x=2 := ((Finset.mem_filter.mp hD).2 : Dcol G S x).1
    omega)
  have Sp : (specialCols G S X).card=A.card+D.card := by
    have he : specialCols G S X=A∪D := by
      ext x
      simp only [specialCols,A,D,weightedSet,Finset.mem_filter,Finset.mem_union]
      tauto
    rw [he,Finset.card_union_of_disjoint dAD]
  have leafCap (u : V) (hu : u∈S) := count_one_per_owner G sym irr tf S X s12 sfree hXS upper blocked u hu
  have a12 : A.card≤12 := by
    change (weightedSet X (Acol G S)).card≤12
    rw [←singlesFor_sum G S X]
    calc
      _ ≤ ∑ _u∈S,(1:Nat) := Finset.sum_le_sum leafCap
      _ = _ := by simp [show S.card=12 from s12]
  have xA {x : V} (hx : x∈A) : lcol G S x=1 := by
    have hb := Finset.mem_filter.mp hx
    exact (blocked_one_lone (G:=G) S x sym irr sfree (blocked x hb.1) hb.2).1
  have xD {x : V} (hx : x∈D) : lcol G S x=2 := ((Finset.mem_filter.mp hx).2 : Dcol G S x).2
  let val (x : V) : Nat := (if x∈A then 1 else 0)+(if x∈D then 2 else 0)
  have bVal (x : V) (hx : x∈X) : val x≤lcol G S x := by
    by_cases ha : x∈A
    · have hn := Finset.disjoint_left.mp dAD ha
      simp [val,ha,hn,xA ha]
    · by_cases hd : x∈D
      · simp [val,ha,hd,xD hd]
      · simp [val,ha,hd]
  have valSum : (∑ x∈X,val x)=A.card+2*D.card := by
    have Aeq : weightedSet X (fun x => x∈A)=A := by ext x; simp [weightedSet,A]
    have Deq : weightedSet X (fun x => x∈D)=D := by ext x; simp [weightedSet,D]
    unfold val
    rw [Finset.sum_add_distrib]
    have a1 := indicator_count_flexible X (fun x => x∈A) 1
      (fun x => if x∈A then 1 else 0) (fun x hx h => by simp [h]) (fun x hx h => by simp [h])
    have d2 := indicator_count_flexible X (fun x => x∈D) 2
      (fun x => if x∈D then 2 else 0) (fun x hx h => by simp [h]) (fun x hx h => by simp [h])
    rw [Aeq] at a1
    rw [Deq] at d2
    rw [←a1,←d2]
    omega
  have lo := degreeTwelve_lower_incidence_h13 G S X sym irr tf s12 sfree hXS upper
  have spe := degreeTwelve_special_cost_h13 G S X sym irr tf s12 sfree hXS upper
  obtain ⟨_,hl⟩ := degreeTwelve_upper_slots_h13 G C sym irr sub two deg w s12 hmin e he
  have hi : I+34≤132 := by
    have hrow (u : V) (hu : u∈S) : row G X u + row G S u≤11 := by
      have h := row_degree G sym w u hu hwS
      change row G X u + row G S u + 1 = (neighbors G u).card at h
      have d := deg u
      omega
    have h := Finset.sum_le_sum hrow
    rw [Finset.sum_add_distrib] at h
    simp only [Finset.sum_const,nsmul_eq_mul,show S.card=12 from s12] at h
    have heq := ncol_eq_incidence G S X sym
    rw [transpose] at heq
    change I=∑ u∈S,row G X u at heq
    change 34≤∑ u∈S,row G S u at hambient
    omega
  change L+7*T.card≤132 at hl
  change T.card=10 at t10
  rw [t10] at hl
  rw [Sp] at lo spe
  change 3*X.card≤I+12+(A.card+D.card) at lo
  change 2*(A.card+D.card)≤L+12 at spe
  have bv := Finset.sum_le_sum bVal
  rw [valSum] at bv
  obtain ⟨i98,l62,ac,dc⟩ := saturated_seventeen I L A.card D.card
    (by omega) hi spe bv (by omega) a12
  have exhaust (x : V) (hx : x∈X) : lcol G S x=val x := by
    by_contra! ne
    have hp := bVal x hx
    have s := Finset.sum_lt_sum bVal ⟨x,hx,show val x<lcol G S x by omega⟩
    change (∑ u∈X,val u)<L at s
    rw [valSum,ac,dc,l62] at s
    omega
  have one (u : V) (hu : u∈S) : (singlesFor G S X u).card=1 := by
    by_contra! h
    have hu' := leafCap u hu
    have sum := Finset.sum_lt_sum leafCap ⟨u,hu,show (singlesFor G S X u).card<1 by omega⟩
    rw [singlesFor_sum] at sum
    change A.card < ∑ _a∈S,(1:Nat) at sum
    simp [ac,show S.card=12 from s12] at sum
  let leaf (u : V) : V := if hu : u∈S
    then Classical.choose (Finset.card_pos.mp (show 0<(singlesFor G S X u).card by rw [one u hu]; decide))
    else w
  have hleaf (u : V) (hu : u∈S) : leaf u∈singlesFor G S X u := by
    unfold leaf
    rw [dif_pos hu]
    exact Classical.choose_spec _
  have lcap (u : V) (hu : u∈S) : ambientLoneRow G X u≤11 := by
    unfold ambientLoneRow
    have hs : row (Lone G) X u ≤ row G X u :=
      Finset.card_le_card (fun x hx => Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2.1⟩)
    have hd := row_degree G sym w u hu hwS
    change row G X u + row G S u + 1=(neighbors G u).card at hd
    have hb := deg u
    omega
  have coreCap (u : V) (hu : u∈T) : ambientLoneRow G X u≤4 := by
    unfold ambientLoneRow
    let F := X.filter (Lone G u)
    have hd : Disjoint F (neighbors C u) := Finset.disjoint_left.mpr (fun x hx hxn => by
      obtain ⟨z,_,_,hz,hz',_,_⟩ := two u x ((mem_neighbors C).mp hxn)
      exact (Finset.mem_filter.mp hx).2.2 z ⟨sub hz,sub hz'⟩)
    have hs : F ∪ neighbors C u ⊆ neighbors G u := by
      intro x hx
      rcases Finset.mem_union.mp hx with h|h
      · exact (mem_neighbors G).mpr (Finset.mem_filter.mp h).2.1
      · exact (mem_neighbors G).mpr (sub ((mem_neighbors C).mp h))
    have he := Finset.card_le_card hs
    rw [Finset.card_union_of_disjoint hd] at he
    have hb := deg u
    have hm := hmin u hu
    change F.card≤4
    omega
  have hLsum : (∑ u∈S,ambientLoneRow G X u)=62 := by
    have h := lcol_eq_incidence G S X sym
    rw [transpose] at h
    change L = ∑ u∈S,ambientLoneRow G X u at h
    omega
  have gexists : ∃ u∈S\T, ambientLoneRow G X u=11 := by
    by_contra! g
    have cg : (S\T).card=2 := by
      rw [Finset.card_sdiff_of_subset hTS,t10]
      exact congrArg (·-10) s12
    have s1 := Finset.sum_le_sum (s:=T) (g:=fun _ => 4) coreCap
    have s2 := Finset.sum_le_sum (s:=S\T) (g:=fun _ => 10) (fun u hu => by
      have a := lcap u (Finset.mem_sdiff.mp hu).1
      have b := g u hu
      show ambientLoneRow G X u≤10
      omega)
    have part := Finset.sum_sdiff hTS (f:=ambientLoneRow G X)
    simp only [Finset.sum_const,nsmul_eq_mul,t10,cg] at s1 s2
    omega
  let ghost := Classical.choose gexists
  have hghost := Classical.choose_spec gexists
  refine ⟨leaf,D,ghost,(Finset.mem_sdiff.mp hghost.1).1,hghost.2,lcap,?_,?_,dc,?_⟩
  · intro u hu
    have h := singlesFor_ownership G sym irr S X sfree blocked u (leaf u) (hleaf u hu)
    exact ⟨((mem_singlesFor G).mp (hleaf u hu)).1,h.1,
      fun a ha hg => Finset.mem_singleton.mpr (h.2.1 a ha hg)⟩
  · intro x hx
    have h := Finset.mem_filter.mp hx
    have hc : Dcol G S x := h.2
    obtain ⟨u,v,uv,eh⟩ := Finset.card_eq_two.mp hc.1
    have a2 : (ns (G:=G) S x).card=2 := hc.1
    have b2 : (ls (G:=G) S x).card=2 := hc.2
    have heq := Finset.eq_of_subset_of_card_le (lone_support_subset (G:=G) S x)
      (show (ns (G:=G) S x).card≤(ls (G:=G) S x).card by omega)
    have uN : u∈ns (G:=G) S x := by simp [eh]
    have vN : v∈ns (G:=G) S x := by simp [eh]
    have uL := (mem_ls (G:=G) S x).mp (heq ▸ uN)
    have vL := (mem_ls (G:=G) S x).mp (heq ▸ vN)
    exact ⟨h.1,u,uL.1,v,vL.1,uv,lone_symm G sym uL.2,lone_symm G sym vL.2,
      fun a ha hg => eh ▸ ((mem_ns (G:=G) S x).mpr ⟨ha,hg⟩)⟩
  · intro u hu x hx hl
    by_cases ha : x∈A
    · left
      have hn := (mem_ns (G:=G) S x).mpr ⟨hu,sym hl.1⟩
      have h := (mem_singlesFor G).mpr ⟨hx,(Finset.mem_filter.mp ha).2,hn⟩
      obtain ⟨y,hy⟩ := Finset.card_eq_one.mp (one u hu)
      have hh := hleaf u hu
      change x∈singlesFor G S X u at h
      rw [hy,Finset.mem_singleton] at h hh
      exact h.trans hh.symm
    · right
      by_contra! hd
      have hh := exhaust x hx
      have hmem := (mem_ls (G:=G) S x).mpr ⟨hu,lone_symm G sym hl⟩
      have hp : 0<lcol G S x := Finset.card_pos.mpr ⟨u,hmem⟩
      simp [val,ha,hd] at hh
      omega

#print axioms frame_of_ambient_saturated
end Erdos151N62
