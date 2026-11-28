import N62OwnerGeometry

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V→V→Prop) [DecidableRel G]

private theorem double_lone_mem {S X : Finset V} (F : SaturationFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) {z u : V} (hz : z∈F.doubles)
    (hu : u∈support G S z) : Lone G u z := by
  obtain ⟨_,a,ha,b,hb,_,la,lb,hs⟩ := F.doubleData z hz
  rw [support_pair G sym ha hb la lb hs] at hu
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu
  rcases hu with rfl|rfl
  · exact la
  · exact lb

private theorem support_wrap {S P : Finset V} {z : V} (h : support G S z=P) :
    supported G S P z := fun y hy hG => h ▸ Finset.mem_filter.mpr ⟨hy,hG⟩

/-- Actual owner-to-graph contradiction for the saturated 25-double,
12-singleton configuration. No projected counting graph is a premise. -/
theorem frame_impossible {S X : Finset V} (F : SaturationFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (dXS : Disjoint X S) (s12 : S.card=12)
    (hS : Free (Forbidden G) (S : Set V))
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (degree : ∀ u, (neighbors G u).card≤12) : False := by
  classical
  let D := F.doubles
  let g := F.ghost
  let star (u : V) := D.filter (Lone G u)
  have gS : g∈S := F.gmem
  have no : ∀ T : Finset V, 13≤T.card → ¬Free (Forbidden G) (T : Set V) :=
    fun T h f => by have := upper T f; omega
  have dev (u : V) (hu : u∈S) : (X.filter (Lone G u)) = insert (F.leaf u) (star u) := by
    ext z
    constructor
    · intro hz
      obtain ⟨zx,zl⟩ := Finset.mem_filter.mp hz
      rcases F.cover u hu z zx zl with eq|hd
      · exact Finset.mem_insert.mpr (Or.inl eq)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hd,zl⟩))
    · intro hz
      rcases Finset.mem_insert.mp hz with rfl|h
      · exact Finset.mem_filter.mpr ⟨(F.leafData u hu).1,(F.leafData u hu).2.1⟩
      · exact Finset.mem_filter.mpr ⟨(F.doubleData _ (Finset.mem_filter.mp h).1).1,(Finset.mem_filter.mp h).2⟩
  have stEq (u : V) (hu : u∈S) : ambientLoneRow G X u=(star u).card+1 := by
    change (X.filter (Lone G u)).card=_
    rw [dev u hu,Finset.card_insert_of_notMem]
    exact fun h => leaf_not_double G F sym u hu ((Finset.mem_filter.mp h).1)
  have stg : (star g).card=10 := by
    have e := stEq g gS
    have f := F.ghits
    change ambientLoneRow G X g=11 at f
    omega
  have stCap (u : V) (hu : u∈S) : (star u).card≤10 := by
    have h := F.lbound u hu
    rw [stEq u hu] at h
    omega
  have part (z : V) (hz : z∈star g) :
      ∃ u∈S, u≠g ∧ support G S z={g,u} := by
    obtain ⟨zd,zg⟩ := Finset.mem_filter.mp hz
    obtain ⟨_,u,hu,v,hv,uv,lu,lv,sz⟩ := F.doubleData z zd
    have sf := support_pair G sym hu hv lu lv sz
    have ms : g∈support G S z := Finset.mem_filter.mpr ⟨gS,sym zg.1⟩
    rw [sf] at ms
    simp only [Finset.mem_insert,Finset.mem_singleton] at ms
    rcases ms with rfl|rfl
    · exact ⟨v,hv,uv.symm,sf⟩
    · exact ⟨u,hu,uv,by rw [sf,Finset.pair_comm]⟩
  let p (z : V) : V := if hz : z∈star g then Classical.choose (part z hz) else g
  have pp (z : V) (hz : z∈star g) : p z∈S ∧ p z≠g ∧ support G S z={g,p z} := by
    unfold p
    rw [dif_pos hz]
    exact Classical.choose_spec (part z hz)
  let N := (star g).image p
  have Nsub : N⊆S.erase g := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_erase.mpr ⟨(pp z hz).2.1,(pp z hz).1⟩
  have hij : Set.InjOn p (star g : Set V) := by
    intro x hx y hy h
    have s : Set.InjOn (support G S) (F.doubles : Set V) :=
      support_injOn_doubles G F sym irr dXS s12 hS upper
    apply s (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
    rw [(pp x hx).2.2,(pp y hy).2.2,h]
  have Nc : N.card=10 := (Finset.card_image_of_injOn hij).trans stg
  have nmiss : ((S.erase g)\N).card=1 := by
    rw [Finset.card_sdiff_of_subset Nsub,Finset.card_erase_of_mem gS,s12,Nc]
  obtain ⟨q,hq⟩ := Finset.card_eq_one.mp nmiss
  have qS : q∈S := by
    have h : q∈(S.erase g)\N := by simp [hq]
    exact Finset.mem_of_mem_erase (Finset.mem_sdiff.mp h).1
  let R := D\(star g∪star q)
  have r5 : 5≤R.card := by
    have su : star g∪star q⊆D :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have a := Finset.card_sdiff_add_card_eq_card su
    change R.card+(star g∪star q).card=D.card at a
    have b := Finset.card_union_le (star g) (star q)
    have c := stCap q qS
    have d := F.doubleCount
    change D.card=25 at d
    omega
  have endpoints (z : V) (hz : z∈R) :
      ∃ u∈N, ∃ v∈N, u≠v ∧
        Lone G u z ∧ Lone G v z ∧ support G S z={u,v} := by
    obtain ⟨hzD,hzn⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨_,u,hu,v,hv,uv,lu,lv,s⟩ := F.doubleData z hzD
    have inN (k : V) (hk : k∈S) (kl : Lone G k z) : k∈N := by
      have kg : k≠g := by
        rintro rfl
        exact hzn (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hzD,kl⟩))
      by_contra hn
      have h : k∈(S.erase g)\N := Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨kg,hk⟩,hn⟩
      rw [hq,Finset.mem_singleton] at h
      subst k
      exact hzn (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hzD,kl⟩))
    exact ⟨u,inN u hu lu,v,inN v hv lv,uv,lu,lv,support_pair G sym hu hv lu lv s⟩
  have paired (u : V) (hu : u∈N) :
      ∃ z∈X, Lone G g z ∧ Lone G u z ∧ support G S z={g,u} := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hu
    have zd := (Finset.mem_filter.mp hz).1
    have eq := (pp z hz).2.2
    exact ⟨z,(F.doubleData z zd).1,(Finset.mem_filter.mp hz).2,
      double_lone_mem G F sym zd (by simp [eq]),eq⟩
  let a := F.leaf g
  have aX : a∈X := (F.leafData g gS).1
  have ga := (F.leafData g gS).2.1
  have asup := support_single G F sym g gS
  have nS (u : V) (hu : u∈N) : u∈S := Finset.mem_of_mem_erase (Nsub hu)
  have ng (u : V) (hu : u∈N) : u≠g := (Finset.mem_erase.mp (Nsub hu)).1
  have outside (z : V) (hz : z∈X) : z∉S := fun hs => Finset.disjoint_left.mp dXS hz hs
  have one_ne_pair {l z u v : V} (hs : support G S l={u})
      (hd : support G S z={u,v}) (ne : u≠v) : l≠z := by
    intro eq
    have k : v∈support G S z := by simp [hd]
    rw [←eq,hs,Finset.mem_singleton] at k
    exact ne k.symm
  have distinct_single_double (u : V) (hu : u∈S) (z : V) (hz : (support G S z).card=2) :
      F.leaf u≠z := by
    intro h
    rw [←h,support_single G F sym u hu,Finset.card_singleton] at hz
    omega
  have L1 (u : V) (hu : u∈N) : Lone G a (F.leaf u) := by
    obtain ⟨z,zX,gz,uz,zsupp⟩ := paired u hu
    have ud := F.leafData u (nS u hu)
    have zu : (support G S z).card=2 := by
      rw [zsupp,Finset.card_insert_of_notMem]
      · simp
      · simpa using (ng u hu).symm
    exact owner_pair_forces_lone G sym irr S g u a (F.leaf u) z gS (nS u hu) (ng u hu).symm
      (outside a aX) (outside _ ud.1) (outside z zX)
      (fun eq => ng u hu ((leaf_injOn G F sym gS (nS u hu) eq).symm))
      (distinct_single_double g gS z zu) (distinct_single_double u (nS u hu) z zu)
      ga ud.2.1 gz uz (support_wrap G asup) ud.2.2 (support_wrap G zsupp) s12 hS no
  have L2 (z : V) (hz : z∈R) : Lone G a z := by
    obtain ⟨u,hu,v,hv,uv,uz,vz,zsup⟩ := endpoints z hz
    obtain ⟨x,xX,gx,ux,xsup⟩ := paired u hu
    obtain ⟨y,yX,gy,vy,ysup⟩ := paired v hv
    have zX := (F.doubleData z (Finset.mem_sdiff.mp hz).1).1
    have supp_ne {x y : V} (m : V) (hm : m∈support G S x) (hn : m∉support G S y) : x≠y :=
      fun h => hn (h ▸ hm)
    have xy : x≠y := supp_ne u (by simp [xsup]) (by simp [ysup,ng u hu,uv])
    have zx : z≠x := supp_ne v (by simp [zsup]) (by simp [xsup,ng v hv,uv.symm])
    have zy : z≠y := supp_ne u (by simp [zsup]) (by simp [ysup,ng u hu,uv])
    have s_two {z i j : V} (h : support G S z={i,j}) (ne : i≠j) :
        (support G S z).card=2 := by rw [h]; simp [Finset.card_insert_of_notMem,ne]
    exact owner_triangle_forces_lone G sym irr S g u v x y z a gS (nS u hu) (nS v hv)
      (ng u hu).symm (ng v hv).symm uv (outside x xX) (outside y yX) (outside z zX) (outside a aX)
      xy (distinct_single_double g gS x (s_two xsup (ng u hu).symm))
      (distinct_single_double g gS y (s_two ysup (ng v hv).symm))
      zx zy (distinct_single_double g gS z (s_two zsup uv))
      gx ux gy vy uz vz ga (support_wrap G xsup) (support_wrap G ysup)
      (support_wrap G zsup) (support_wrap G asup) s12 hS no
  let M := N.image F.leaf
  have mc : M.card=10 := by
    rw [Finset.card_image_of_injOn (fun x hx y hy e => leaf_injOn G F sym (nS x hx) (nS y hy) e)]
    exact Nc
  have gm : g∉M := by
    intro h
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp h
    exact outside _ (F.leafData x (nS x hx)).1 (he ▸ gS)
  have gr : g∉R := fun h => outside g (F.doubleData g (Finset.mem_sdiff.mp h).1).1 gS
  have dis : Disjoint M R := Finset.disjoint_left.mpr (by
    intro z hz hzR
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    exact leaf_not_double G F sym u (nS u hu) (Finset.mem_sdiff.mp hzR).1)
  have pack : insert g (M∪R)⊆ neighbors G a := by
    intro z hz
    apply (mem_neighbors G).mpr
    rcases Finset.mem_insert.mp hz with rfl|h
    · exact sym ga.1
    · rcases Finset.mem_union.mp h with hm|hr
      · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hm
        exact (L1 u hu).1
      · exact (L2 z hr).1
  have h := (Finset.card_le_card pack).trans (degree a)
  rw [Finset.card_insert_of_notMem (by simp [gm,gr]),Finset.card_union_of_disjoint dis,mc] at h
  omega

#print axioms frame_impossible
end Erdos151N62
