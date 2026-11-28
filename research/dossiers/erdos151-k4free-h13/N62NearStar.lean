import N62NearOwner

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V→V→Prop) [DecidableRel G]
variable {S X : Finset V}

noncomputable def Dstar (F : NearOwnerFrame G S X) (u : V) : Finset V := by
  classical exact F.doubles.filter (Lone G u)

theorem near_double_lone_of_support (F : NearOwnerFrame G S X)
    {x u : V} (hx : x∈F.doubles) (hu : u∈support G S x) : Lone G u x := by
  obtain ⟨_,a,_,b,_,_,al,bl,eq⟩ := F.dblData x hx
  rw [eq] at hu
  rcases mem_insert.mp hu with rfl|h
  · exact al
  · exact mem_singleton.mp h ▸ bl

theorem near_double_partner (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) {g x : V} (gs : g∈S)
    (hx : x∈Dstar G F g) :
    ∃ u∈S, u≠g ∧ support G S x={g,u} := by
  classical
  obtain ⟨xd,xg⟩ := mem_filter.mp hx
  obtain ⟨_,u,us,v,vs,ne,_,_,e⟩ := F.dblData x xd
  have gz : g∈support G S x := mem_filter.mpr ⟨gs,sym xg.1⟩
  rw [e] at gz
  simp only [mem_insert,mem_singleton] at gz
  rcases gz with rfl|rfl
  · exact ⟨v,vs,ne.symm,e⟩
  · exact ⟨u,us,ne,by rw [e,pair_comm]⟩

theorem near_single_support (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) {g : V} (hg : g∈F.marks) :
    support G S (F.leaf g)={g} := by
  obtain ⟨_,l,s⟩ := F.leafData g hg
  ext u
  simp only [support,mem_filter,mem_singleton]
  constructor
  · exact fun h => mem_singleton.mp (s u h.1 h.2)
  · rintro rfl
    exact ⟨F.markSub hg,sym l.1⟩

theorem near_marked_star_injOn (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V))
    (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (g : V) (gm : g∈F.marks) :
    Set.InjOn (support G S) (Dstar G F g : Set V) := by
  classical
  have gs := F.markSub gm
  intro x hx y hy eq
  change x∈Dstar G F g at hx
  change y∈Dstar G F g at hy
  by_contra! ne
  obtain ⟨u,us,ug,xe⟩ := near_double_partner G F sym gs hx
  let a := F.leaf g
  let R : Finset V := {g,u}
  let Z : Finset V := {x,y,a}
  have ps : R⊆S := by simp [R,insert_subset_iff,gs,us]
  have ex : support G S x=R := xe
  have ey : support G S y=R := eq.symm.trans ex
  have ea : support G S a={g} := near_single_support G F sym gm
  have ds (z : V) (hz : support G S z=R) : z≠a := by
    intro za
    have hu : u∈support G S z := by simp [hz,R]
    rw [za,ea,mem_singleton] at hu
    exact ug hu
  have z3 : Z.card=3 := by simp [Z,card_insert_of_notMem,ne,ds x ex,ds y ey]
  have r2 : R.card=2 := by simp [R,card_insert_of_notMem,ug.symm]
  have extZ : Z⊆X := by
    intro z hz
    simp only [Z,mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl|rfl
    · exact (F.dblData _ (mem_filter.mp hx).1).1
    · exact (F.dblData _ (mem_filter.mp hy).1).1
    · exact (F.leafData g gm).1
  have hit : ∀ z∈Z, Lone G g z := by
    intro z hz
    simp only [Z,mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl|rfl
    · exact (mem_filter.mp hx).2
    · exact (mem_filter.mp hy).2
    · exact (F.leafData g gm).2.1
  have supp : ∀ z∈Z, support G S z⊆R := by
    intro z hz
    simp only [Z,mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl|rfl
    · exact ex.le
    · exact ey.le
    · rw [ea]; simp [R]
  have h := commonLone_supported_count G sym irr S R Z sc ps sf upper
    (out.symm.mono_right extZ) g hit supp
  omega

/-- Ten distinct D-incidences at a marked ghost are impossible
already at special-column count 35. -/
theorem near_ten_marked_star_impossible (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V))
    (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (deg : ∀ u, (neighbors G u).card≤12)
    (cap : ∀ u∈S, (Dstar G F u).card≤11)
    (large : 35≤F.marks.card+F.doubles.card)
    (g : V) (gm : g∈F.marks) (ten : (Dstar G F g).card=10) : False := by
  classical
  let D := F.doubles
  let star := Dstar G F
  have gs := F.markSub gm
  have part := fun z (h : z∈star g) => near_double_partner G F sym gs h
  let p (z : V) : V := if hz : z∈star g then Classical.choose (part z hz) else g
  have pp (z : V) (hz : z∈star g) : p z∈S ∧ p z≠g ∧ support G S z={g,p z} := by
    unfold p
    rw [dif_pos hz]
    exact Classical.choose_spec (part z hz)
  let N := (star g).image p
  have Nsub : N⊆S.erase g := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hu
    exact mem_erase.mpr ⟨(pp z hz).2.1,(pp z hz).1⟩
  have hij : Set.InjOn p (star g : Set V) := by
    intro x hx y hy h
    apply near_marked_star_injOn G F sym irr sc sf out upper g gm hx hy
    rw [(pp x hx).2.2,(pp y hy).2.2,h]
  have Nc : N.card=10 := (card_image_of_injOn hij).trans ten
  have missing : ((S.erase g)\N).card=1 := by
    rw [card_sdiff_of_subset Nsub,card_erase_of_mem gs,sc,Nc]
  obtain ⟨q,hq⟩ := card_eq_one.mp missing
  have qs : q∈S := by
    have h : q∈(S.erase g)\N := by simp [hq]
    exact mem_of_mem_erase (mem_sdiff.mp h).1
  let R := D \ (star g ∪ star q)
  have Rcount : D.card≤10+(star q).card+R.card := by
    have su : star g∪star q⊆D := union_subset (filter_subset _ _) (filter_subset _ _)
    have a := card_sdiff_add_card_eq_card su
    change R.card+(star g∪star q).card=D.card at a
    have b := card_union_le (s := star g) (t := star q)
    change (star g).card=10 at ten
    omega
  have endpoints (z : V) (hz : z∈R) :
      ∃ u∈N, ∃ v∈N, u≠v ∧
        Lone G u z ∧ Lone G v z ∧ support G S z={u,v} := by
    obtain ⟨hzD,hzn⟩ := mem_sdiff.mp hz
    obtain ⟨_,u,hu,v,hv,uv,lu,lv,s⟩ := F.dblData z hzD
    have inN (k : V) (hk : k∈S) (kl : Lone G k z) : k∈N := by
      have kg : k≠g := by
        rintro rfl
        exact hzn (mem_union_left _ (mem_filter.mpr ⟨hzD,kl⟩))
      by_contra hn
      have h : k∈(S.erase g)\N := mem_sdiff.mpr ⟨mem_erase.mpr ⟨kg,hk⟩,hn⟩
      rw [hq,mem_singleton] at h
      subst k
      exact hzn (mem_union_right _ (mem_filter.mpr ⟨hzD,kl⟩))
    exact ⟨u,inN u hu lu,v,inN v hv lv,uv,lu,lv,s⟩
  have paired (u : V) (hu : u∈N) :
      ∃ z∈X, Lone G g z ∧ Lone G u z ∧ support G S z={g,u} := by
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hu
    have zd := (mem_filter.mp hz).1
    have eq := (pp z hz).2.2
    exact ⟨z,(F.dblData z zd).1,(mem_filter.mp hz).2,
      near_double_lone_of_support G F zd (by simp [eq]),eq⟩
  have inter := card_union_add_card_inter N F.marks
  have hunion : (N∪F.marks).card≤12 := by
    rw [←sc]
    exact card_le_card (union_subset (fun _ h => mem_of_mem_erase (Nsub h)) F.markSub)
  have nm : F.marks.card≤(N∩F.marks).card+2 := by omega
  have prox := marked_leaf_pressure G sym irr S X F.marks N R g F.leaf out sc sf upper
    gs gm F.markSub Nsub F.leafData paired endpoints
    (fun z hz => (F.dblData z (mem_sdiff.mp hz).1).1)
  have h := marked_ten_star_degree _ _ _ _ _ large nm (cap q qs) Rcount
  have := deg (F.leaf g)
  omega

#print axioms near_ten_marked_star_impossible
end Erdos151N62
