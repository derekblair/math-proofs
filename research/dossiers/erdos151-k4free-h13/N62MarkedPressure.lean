import N62OwnerPressure

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

private theorem support_wrap {S P : Finset V} {z : V} (h : support G S z=P) :
    supported G S P z := fun y hy hG => h ▸ Finset.mem_filter.mpr ⟨hy,hG⟩

/-- The degree of a marked owner's singleton leaf is at least one
plus the marked neighbors and all inner double columns of its star. -/
theorem marked_leaf_pressure
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (S X M N R : Finset V) (g : V) (leaf : V→V)
    (dXS : Disjoint X S) (s12 : S.card=12)
    (hS : Free (Forbidden G) (S : Set V))
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (gS : g∈S) (gm : g∈M) (mS : M⊆S)
    (Nsub : N⊆S.erase g)
    (leafData : ∀ u∈M, leaf u∈X ∧ Lone G u (leaf u) ∧ supported G S {u} (leaf u))
    (paired : ∀ u∈N, ∃ z∈X, Lone G g z ∧ Lone G u z ∧ support G S z={g,u})
    (endpoints : ∀ z∈R, ∃ u∈N, ∃ v∈N, u≠v ∧
        Lone G u z ∧ Lone G v z ∧ support G S z={u,v})
    (rOutside : R⊆X) :
    1+(N∩M).card+R.card ≤ (neighbors G (leaf g)).card := by
  classical
  have no : ∀ T : Finset V, 13≤T.card → ¬Free (Forbidden G) (T : Set V) :=
    fun T h f => by have := upper T f; omega
  have single_id (u : V) (hu : u∈M) : support G S (leaf u)={u} := by
    obtain ⟨_,hl,hs⟩ := leafData u hu
    ext x
    simp only [support,Finset.mem_filter,Finset.mem_singleton]
    constructor
    · exact fun h => Finset.mem_singleton.mp (hs x h.1 h.2)
    · rintro rfl
      exact ⟨mS hu,sym hl.1⟩
  have leaf_inj {x y : V} (hx : x∈M) (hy : y∈M) (eq : leaf x=leaf y) : x=y := by
    have h := congrArg (support G S) eq
    rwa [single_id x hx,single_id y hy,Finset.singleton_inj] at h
  let a := leaf g
  have aX : a∈X := (leafData g gm).1
  have ga := (leafData g gm).2.1
  have asup := single_id g gm
  have nS (u : V) (hu : u∈N) : u∈S := Finset.mem_of_mem_erase (Nsub hu)
  have ng (u : V) (hu : u∈N) : u≠g := (Finset.mem_erase.mp (Nsub hu)).1
  have outside (z : V) (hz : z∈X) : z∉S := fun hs => Finset.disjoint_left.mp dXS hz hs
  have one_ne_pair {l z u v : V} (hs : support G S l={u})
      (hd : support G S z={u,v}) (ne : u≠v) : l≠z := by
    intro eq
    have k : v∈support G S z := by simp [hd]
    rw [←eq,hs,Finset.mem_singleton] at k
    exact ne k.symm
  have distinct_single_double (u : V) (hu : u∈M) (z : V) (hz : (support G S z).card=2) :
      leaf u≠z := by
    intro h
    rw [←h,single_id u hu,Finset.card_singleton] at hz
    omega
  have L1 (u : V) (hu : u∈N) (hm : u∈M) : Lone G a (leaf u) := by
    obtain ⟨z,zX,gz,uz,zsupp⟩ := paired u hu
    have ud := leafData u hm
    have zu : (support G S z).card=2 := by
      rw [zsupp,Finset.card_insert_of_notMem]
      · simp
      · simpa using (ng u hu).symm
    exact owner_pair_forces_lone G sym irr S g u a (leaf u) z gS (nS u hu) (ng u hu).symm
      (outside a aX) (outside _ ud.1) (outside z zX)
      (fun eq => ng u hu ((leaf_inj gm hm eq).symm))
      (distinct_single_double g gm z zu) (distinct_single_double u hm z zu)
      ga ud.2.1 gz uz (support_wrap G asup) ud.2.2 (support_wrap G zsupp) s12 hS no
  have L2 (z : V) (hz : z∈R) : Lone G a z := by
    obtain ⟨u,hu,v,hv,uv,uz,vz,zsup⟩ := endpoints z hz
    obtain ⟨x,xX,gx,ux,xsup⟩ := paired u hu
    obtain ⟨y,yX,gy,vy,ysup⟩ := paired v hv
    have zX := rOutside hz
    have supp_ne {x y : V} (m : V) (hm : m∈support G S x) (hn : m∉support G S y) : x≠y :=
      fun h => hn (h ▸ hm)
    have xy : x≠y := supp_ne u (by simp [xsup]) (by simp [ysup,ng u hu,uv])
    have zx : z≠x := supp_ne v (by simp [zsup]) (by simp [xsup,ng v hv,uv.symm])
    have zy : z≠y := supp_ne u (by simp [zsup]) (by simp [ysup,ng u hu,uv])
    have s_two {z i j : V} (h : support G S z={i,j}) (ne : i≠j) :
        (support G S z).card=2 := by rw [h]; simp [Finset.card_insert_of_notMem,ne]
    exact owner_triangle_forces_lone G sym irr S g u v x y z a gS (nS u hu) (nS v hv)
      (ng u hu).symm (ng v hv).symm uv (outside x xX) (outside y yX) (outside z zX) (outside a aX)
      xy (distinct_single_double g gm x (s_two xsup (ng u hu).symm))
      (distinct_single_double g gm y (s_two ysup (ng v hv).symm))
      zx zy (distinct_single_double g gm z (s_two zsup uv))
      gx ux gy vy uz vz ga (support_wrap G xsup) (support_wrap G ysup)
      (support_wrap G zsup) (support_wrap G asup) s12 hS no
  let L := (N∩M).image leaf
  have mc : L.card=(N∩M).card := by
    exact Finset.card_image_of_injOn (fun x hx y hy e =>
      leaf_inj (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hy).2 e)
  have gnL : g∉L := by
    intro h
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp h
    exact outside _ (leafData x (Finset.mem_inter.mp hx).2).1 (he ▸ gS)
  have gr : g∉R := fun h => outside g (rOutside h) gS
  have dis : Disjoint L R := Finset.disjoint_left.mpr (by
    intro z hz hzR
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨p,hp,q,hq,pq,_,_,sp⟩ := endpoints (leaf u) hzR
    have sc : (support G S (leaf u)).card=2 := by
      rw [sp]; simp [Finset.card_insert_of_notMem,pq]
    exact distinct_single_double u (Finset.mem_inter.mp hu).2 (leaf u) sc rfl)
  have pack : insert g (L∪R)⊆ neighbors G a := by
    intro z hz
    apply (mem_neighbors G).mpr
    rcases Finset.mem_insert.mp hz with rfl|h
    · exact sym ga.1
    · rcases Finset.mem_union.mp h with hm|hr
      · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hm
        exact (L1 u (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hu).2).1
      · exact (L2 z hr).1
  have h := Finset.card_le_card pack
  rw [Finset.card_insert_of_notMem (by simp [gnL,gr]),Finset.card_union_of_disjoint dis,mc] at h
  change 1+(N∩M).card+R.card ≤ (neighbors G a).card
  omega

#print axioms marked_leaf_pressure
end Erdos151N62
