import N62PrivateLowCases

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13 Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

theorem a10_private_split
    (S X : Finset V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (a10 : acnt G S X=10) (bc : bcnt G S X+ccnt G S X=2) :
    (bcnt G S X=0 ∧ ccnt G S X=2) ∨
      (bcnt G S X=2 ∧ ccnt G S X=0 ∧
      ∃ p∈S, ∃ q∈S, p≠q ∧ G p q ∧
        S\(nearFrame G S X sym irr tf sc sf out upper).marks={p,q} ∧
        ∀ z∈X, Bcol G S z → G p z ∧ G q z ∧ support G S z={p,q}) := by
  classical
  let F := nearFrame G S X sym irr tf sc sf out upper
  let B := weightedSet X (Bcol G S)
  let C := weightedSet X (Ccol G S)
  by_cases b0 : bcnt G S X=0
  · exact Or.inl ⟨b0,by omega⟩
  have bb : 0<B.card := by change 0<bcnt G S X; omega
  have blk (z : V) (zx : z∈X) := all_exterior_blocked_12 G S sc upper z (Finset.disjoint_left.mp out zx)
  obtain ⟨x,xB⟩ := card_pos.mp bb
  obtain ⟨xx,bx⟩ := mem_filter.mp xB
  obtain ⟨p,ps,q,qs,pq,e,gp,gq,sup⟩ := Bcol_adjacent_support G S x sym irr sf (blk x xx) bx
  have nm (u : V) (us : u∈support G S x) : u∉F.marks :=
    B_support_unmarked G S X sym irr tf sc sf out upper xx bx us
  have pp : p∉F.marks := nm p (by simp [sup])
  have qq : q∉F.marks := nm q (by simp [sup])
  have U : S\F.marks={p,q} := by
    symm
    apply eq_of_subset_of_card_le
    · simp [insert_subset_iff,ps,qs,pp,qq]
    · have m : F.marks.card=10 := (nearFrame_count_marks G S X sym irr tf sc sf out upper).trans a10
      rw [card_sdiff_of_subset F.markSub,sc,m,card_insert_of_notMem (by simp [pq]),card_singleton]
  have hitB (u : V) (hu : u∈({p,q}:Finset V)) : x∈privateFirst G S X u := by
    have s : u∈support G S x := by rw [sup]; exact hu
    exact mem_filter.mpr ⟨xx,Or.inl ⟨Or.inr bx,(mem_ns (G:=G) S x).mpr (mem_filter.mp s)⟩⟩
  have c0 : ccnt G S X=0 := by
    by_contra! c
    have h : 0<C.card := by change 0<ccnt G S X; omega
    obtain ⟨z,hz⟩ := card_pos.mp h
    obtain ⟨zx,cz⟩ := mem_filter.mp hz
    obtain ⟨u,ue⟩ := card_eq_one.mp (show (ls (G:=G) S z).card=1 from cz.2)
    have ul : u∈ls (G:=G) S z := by simp [ue]
    have us := ((mem_ls (G:=G) S z).mp ul).1
    have zp : z∈privateFirst G S X u := mem_filter.mpr ⟨zx,Or.inr ⟨cz,ul⟩⟩
    have zq : z∈privateSecond G S X u := mem_filter.mpr ⟨zx,Or.inr cz,ul⟩
    have um : u∉F.marks := by
      intro um
      have p := marked_private_full G S X sym irr tf sc sf out upper um
      rw [p.1,mem_singleton] at zp
      have ss := near_single_support G F sym um
      have f : support G S z=ns (G:=G) S z := by ext v; simp [support,Support]
      have ct : (support G S z).card=2 := by rw [f]; exact cz.1
      change z=F.leaf u at zp
      rw [zp,ss,card_singleton] at ct
      omega
    have hu : u∈({p,q}:Finset V) := U ▸ mem_sdiff.mpr ⟨us,um⟩
    have ne : x≠z := by
      intro ez
      have a := bx.2
      rw [ez] at a
      have b := cz.2
      omega
    have sb : ({x,z}:Finset V)⊆privateFirst G S X u := by simp [insert_subset_iff,hitB u hu,zp]
    have cb := card_le_card sb
    rw [card_insert_of_notMem (by simp [ne]),card_singleton] at cb
    have cq := card_pos.mpr ⟨z,zq⟩
    have d := private_slots_charged G S X sym irr tf sc sf out upper u us
    omega
  refine Or.inr ⟨by omega,c0,p,ps,q,qs,pq,e,U,?_⟩
  intro z zx bz
  obtain ⟨u,us,v,vs,uv,ed,uz,vz,sz⟩ := Bcol_adjacent_support G S z sym irr sf (blk z zx) bz
  have um := B_support_unmarked G S X sym irr tf sc sf out upper zx bz
    (show u∈support G S z by simp [sz])
  have vm := B_support_unmarked G S X sym irr tf sc sf out upper zx bz
    (show v∈support G S z by simp [sz])
  have both : ({u,v}:Finset V)⊆({p,q}:Finset V) := by
    rw [←U]
    exact insert_subset_iff.mpr ⟨mem_sdiff.mpr ⟨us,um⟩,singleton_subset_iff.mpr (mem_sdiff.mpr ⟨vs,vm⟩)⟩
  have eq : ({u,v}:Finset V)={p,q} := by
    apply eq_of_subset_of_card_le both
    simp [card_insert_of_notMem,uv,pq]
  have hp : p∈({u,v}:Finset V) := by simp [eq]
  have hq : q∈({u,v}:Finset V) := by simp [eq]
  simp only [mem_insert,mem_singleton] at hp hq
  exact ⟨hp.elim (· ▸ uz) (· ▸ vz),hq.elim (· ▸ uz) (· ▸ vz),sz.trans eq⟩

#print axioms a10_private_split
end Erdos151N62
