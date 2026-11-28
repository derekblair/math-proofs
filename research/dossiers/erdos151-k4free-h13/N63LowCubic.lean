import N63TwoHighPrice
import N63CrossCharge

namespace Erdos151H13
open Finset NineLinkPivot
open Erdős151 Erdos151H12 Erdos151Ramsey

private theorem short_medium_pair : ∀ a b s : Fin 4,
    12 ≤ (a.val+3)+(b.val+3)+s.val+2+outerFloor (a.val+3) (b.val+3) s.val := by decide

theorem medium_pair_price (a b s : ℕ) (ha : 3≤a) (hb : 3≤b) :
    12 ≤ a+b+s+2+outerFloor a b s := by
  by_cases h : 10 ≤ a+b+s
  · omega
  · let i : Fin 4 := ⟨a-3,by omega⟩
    let j : Fin 4 := ⟨b-3,by omega⟩
    let k : Fin 4 := ⟨s,by omega⟩
    have ia : i.val+3=a := by change a-3+3=a; omega
    have jb : j.val+3=b := by change b-3+3=b; omega
    simpa only [ia,jb] using short_medium_pair i j k

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

theorem low_ambient_cubic_ten_free13
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : ∀ a b, C a b → G a b) (symC : ∀ {a b}, C a b → C b a)
    (coreNonlone : ∀ a b, C a b → ¬Lone G a b)
    (w : V) (r10 : (neighbors C w).card=10) (d11 : (neighbors G w).card≤11)
    (cubic : ∀ x ∈ neighbors C w, deg G (neighbors C w) x=3)
    (min8 : ∀ x ∈ neighbors C w, 8≤(neighbors C x).card)
    (max12 : ∀ a, (neighbors G a).card ≤ 12) (size63 : 63 ≤ Fintype.card V) :
    ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V) := by
  let S := neighbors C w
  have cw (x : V) (hx : x∈S) : C w x := (mem_neighbors C).mp hx
  have gw (x : V) (hx : x∈S) : G w x := sub _ _ (cw x hx)
  have r10' : S.card=10 := r10
  obtain ⟨p,hp⟩ := card_pos.mp (show 0 < S.card by omega)
  have p3 : (near G S p).card=3 := cubic p hp
  obtain ⟨x,hx,y,hy,xy⟩ := pick_two (near G S p) (by omega)
  obtain ⟨xs,px⟩ := mem_filter.mp hx
  obtain ⟨ys,py⟩ := mem_filter.mp hy
  have nxy : ¬G x y := fun q => link w p x y (gw p hp) (gw x xs) (gw y ys) px q py
  let X := near G S x
  let Y := near G S y
  let F := (X∪Y)∪({x,y}:Finset V)
  let M := S \ F
  have x3 : X.card=3 := cubic x xs
  have y3 : Y.card=3 := cubic y ys
  have many : 1≤(X∩Y).card := by
    apply card_pos.mpr
    exact ⟨p,mem_inter.mpr ⟨mem_filter.mpr ⟨hp,sym px⟩,mem_filter.mpr ⟨hp,sym py⟩⟩⟩
  have u5 : (X∪Y).card≤5 := by
    have := card_union_add_card_inter X Y
    omega
  have fc : F.card≤7 := by
    have f := card_union_le (X∪Y) ({x,y}:Finset V)
    have g : ({x,y}:Finset V).card≤2 := by simpa using card_insert_le x ({y}:Finset V)
    change ((X∪Y)∪({x,y}:Finset V)).card≤7
    omega
  have fS : F ⊆ S := union_subset (union_subset (filter_subset _ _) (filter_subset _ _)) (by
    intro a ha
    simp only [mem_insert,mem_singleton] at ha
    rcases ha with rfl|rfl
    · exact xs
    · exact ys)
  have hM : 3≤M.card := by
    have eM := card_sdiff_add_card_eq_card fS
    change M.card+F.card=S.card at eM
    omega
  let H (a b : V) := a∈S ∧ b∈S ∧ G a b
  letI : DecidableRel H := fun a b => inferInstanceAs (Decidable (a∈S ∧ b∈S ∧ G a b))
  have htf : TriangleFree H := by
    intro a b c ab bc ac
    exact link w a b c (gw a ab.1) (gw b ab.2.1) (gw c ac.2.1) ab.2.2 bc.2.2 ac.2.2
  obtain ⟨A,ha,a2,ai⟩ := independent_two_of_three H
    (fun {_ _} z => ⟨z.2.1,z.1,sym z.2.2⟩) (fun a z => irr a z.2.2) htf M hM
  have ah (a : V) (ha' : a∈A) := mem_sdiff.mp (ha ha')
  have aKeep : ∀ a ∈ A, C w a ∧ a≠x ∧ a≠y ∧ ¬G x a ∧ ¬G y a := by
    intro a am
    obtain ⟨as,af⟩ := ah a am
    refine ⟨cw a as,?_,?_,?_,?_⟩
    · intro ax
      exact af (mem_union_right _ (by simp [ax]))
    · intro ay
      exact af (mem_union_right _ (by simp [ay]))
    · intro xa
      exact af (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨as,xa⟩)))
    · intro ya
      exact af (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨as,ya⟩)))
  have aInd : Independent G A :=
    fun a am b bm ab => ai a am b bm ⟨(ah a am).1,(ah b bm).1,ab⟩
  have ac (u : V) (hu : u∈S) : 3≤(neighbors G u∩neighbors G w).card := by
    have e : near G S u ⊆ neighbors G u∩neighbors G w := by
      intro z hz
      obtain ⟨zs,uz⟩ := mem_filter.mp hz
      exact mem_inter.mpr ⟨(mem_neighbors G).mpr uz,(mem_neighbors G).mpr (gw z zs)⟩
    have q := card_le_card e
    have t : (near G S u).card=3 := cubic u hu
    omega
  apply free13_of_chart_price G C sym irr link R41 sub coreNonlone x w y (symC (cw x xs)) (symC (cw y ys))
    nxy xy (min8 _ xs) (min8 _ ys) A (actual_center_witness G C w x y A sub aKeep) aInd
  let a := (neighbors G x∩neighbors G w).card
  let b := (neighbors G y∩neighbors G w).card
  let s := ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card
  have price := medium_pair_price a b s (ac x xs) (ac y ys)
  have d : (neighbors G x).card+(neighbors G y).card+(neighbors G w).card≤35 := by
    have := max12 x
    have := max12 y
    omega
  change _ ≤ Fintype.card V+a+b+s+A.card+outerFloor a b s
  omega

#print axioms low_ambient_cubic_ten_free13
end Erdos151H13
