import UnblockingLocal
import UnblockingLower

namespace Erdős151

variable {V : Type*} [DecidableEq V] {G : V → V → Prop}
variable (S : Finset V) (x : V)

noncomputable def ns : Finset V := by
  classical
  exact S.filter (fun u => G x u)

noncomputable def ls : Finset V := by
  classical
  exact S.filter (fun u => Lone G x u)

noncomputable def ps : Finset V := by
  classical
  exact S.filter (fun u => Free (Forbidden G) (insert x ((S : Set V) \ {u})))

noncomputable def qs : Finset V := by
  classical
  exact S.filter (fun u => Lone G x u ∧
    Free (Forbidden G) (insert x ((S : Set V) \ {u})))

@[simp] theorem mem_ns {u : V} : u ∈ ns (G := G) S x ↔ u ∈ Support G S x := by
  classical
  simp [ns, Support]

@[simp] theorem mem_ls {u : V} : u ∈ ls (G := G) S x ↔ u ∈ S ∧ Lone G x u := by
  classical
  simp [ls]

@[simp] theorem mem_ps {u : V} : u ∈ ps (G := G) S x ↔
    u ∈ S ∧ Free (Forbidden G) (insert x ((S : Set V) \ {u})) := by
  classical
  simp [ps]

@[simp] theorem mem_qs {u : V} : u ∈ qs (G := G) S x ↔
    u ∈ S ∧ Lone G x u ∧ Free (Forbidden G) (insert x ((S : Set V) \ {u})) := by
  classical
  simp [qs]

theorem lone_support_subset : ls (G := G) S x ⊆ ns (G := G) S x := by
  intro u hu
  exact (mem_ns (G := G) S x).mpr ⟨((mem_ls (G := G) S x).mp hu).1, ((mem_ls (G := G) S x).mp hu).2.1⟩

theorem blocked_support_ne
    (sym : ∀ {a b}, G a b → G b a) (loopless : ∀ u, ¬ G u u)
    (hS : Free (Forbidden G) S) (hb : ¬ Free (Forbidden G) (insert x S)) :
    (ns (G := G) S x).Nonempty := by
  rcases blocked_witness (G := G) (S := ↑S) (x := x) sym loopless hS hb with
    ⟨a,ha,_⟩ | ⟨a,ha,_⟩
  all_goals exact ⟨a,(mem_ns (G := G) S x).mpr ha⟩

theorem owner_of_small_support
    (sym : ∀ {a b}, G a b → G b a) (loopless : ∀ u, ¬ G u u)
    (hS : Free (Forbidden G) S) {u : V} (hu : u ∈ ns (G := G) S x)
    (small : (ns (G := G) S x).card ≤ 2)
    (loneHere : ∀ a ∈ ls (G := G) S x, a = u) :
    u ∈ ps (G := G) S x := by
  classical
  refine (mem_ps (G := G) S x).mpr ⟨((mem_ns (G := G) S x).mp hu).1, ?_⟩
  apply private_of_residual_support (G := G) sym loopless hS
  · intro a ha hau hl
    exact hau (loneHere a ((mem_ls (G := G) S x).mpr ⟨ha.1,hl⟩))
  · intro a ha b hb hau hbu
    by_contra hab
    have hsub : ({u,a,b} : Finset V) ⊆ ns (G := G) S x := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl|rfl|rfl
      · exact hu
      · exact (mem_ns (G := G) S x).mpr ha
      · exact (mem_ns (G := G) S x).mpr hb
    have hcard : ({u,a,b} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using hab
      · simp [Ne.symm hau, Ne.symm hbu]
    have h := Finset.card_le_card hsub
    omega

theorem blocked_one_lone
    (sym : ∀ {a b}, G a b → G b a) (loopless : ∀ u, ¬ G u u)
    (hS : Free (Forbidden G) S) (hb : ¬ Free (Forbidden G) (insert x S))
    (hn : (ns (G := G) S x).card = 1) :
    (ls (G := G) S x).card = 1 ∧ 1 ≤ (ps (G := G) S x).card ∧
      1 ≤ (qs (G := G) S x).card := by
  classical
  obtain ⟨u,hu⟩ := Finset.card_eq_one.mp hn
  have supportOnly {a : V} (ha : a ∈ Support G S x) : a = u := by
    simpa [hu] using (mem_ns (G := G) S x).mpr ha
  have hl : u ∈ ls (G := G) S x := by
    rcases blocked_witness (G := G) (S := ↑S) (x := x) sym loopless hS hb with
      ⟨a,ha,hl⟩ | ⟨a,ha,b,hb,hab,_⟩
    · have hEq := supportOnly ha
      subst a
      exact (mem_ls (G := G) S x).mpr ⟨ha.1,hl⟩
    · exact False.elim (hab ((supportOnly ha).trans (supportOnly hb).symm))
  have hsub := lone_support_subset (G := G) S x
  have hcap := Finset.card_le_card hsub
  have hpos : 1 ≤ (ls (G := G) S x).card := Finset.card_pos.mpr ⟨u,hl⟩
  have hp := owner_of_small_support (G := G) S x sym loopless hS (hsub hl) (by omega)
    (fun a ha => supportOnly ((mem_ns (G := G) S x).mp (hsub ha)))
  have hq : u ∈ qs (G := G) S x :=
    (mem_qs (G := G) S x).mpr ⟨((mem_ls (G := G) S x).mp hl).1,
      ((mem_ls (G := G) S x).mp hl).2, ((mem_ps (G := G) S x).mp hp).2⟩
  exact ⟨by omega, Finset.card_pos.mpr ⟨u,hp⟩, Finset.card_pos.mpr ⟨u,hq⟩⟩

theorem blocked_two_no_lone
    (sym : ∀ {a b}, G a b → G b a) (loopless : ∀ u, ¬ G u u)
    (hS : Free (Forbidden G) S) (hn : (ns (G := G) S x).card = 2)
    (hl : (ls (G := G) S x).card = 0) : 2 ≤ (ps (G := G) S x).card := by
  rw [← hn]
  apply Finset.card_le_card
  intro u hu
  apply owner_of_small_support (G := G) S x sym loopless hS hu hn.le
  intro a ha
  have hp := Finset.card_pos.mpr (show (ls (G := G) S x).Nonempty from ⟨a,ha⟩)
  omega

theorem blocked_two_one_lone
    (sym : ∀ {a b}, G a b → G b a) (loopless : ∀ u, ¬ G u u)
    (hS : Free (Forbidden G) S) (hn : (ns (G := G) S x).card = 2)
    (hl : (ls (G := G) S x).card = 1) :
    1 ≤ (ps (G := G) S x).card ∧ 1 ≤ (qs (G := G) S x).card := by
  classical
  obtain ⟨u,hu⟩ := Finset.card_eq_one.mp hl
  have hmem : u ∈ ls (G := G) S x := by simp [hu]
  have hp := owner_of_small_support (G := G) S x sym loopless hS
    (lone_support_subset (G := G) S x hmem) hn.le (fun a ha => by simpa [hu] using ha)
  have hq : u ∈ qs (G := G) S x :=
    (mem_qs (G := G) S x).mpr ⟨((mem_ls (G := G) S x).mp hmem).1,
      ((mem_ls (G := G) S x).mp hmem).2, ((mem_ps (G := G) S x).mp hp).2⟩
  exact ⟨Finset.card_pos.mpr ⟨u,hp⟩,Finset.card_pos.mpr ⟨u,hq⟩⟩

theorem blocked_graph_charge
    (sym : ∀ {a b}, G a b → G b a) (loopless : ∀ u, ¬ G u u)
    (hS : Free (Forbidden G) S) (hb : ¬ Free (Forbidden G) (insert x S)) :
    let s := (ns (G := G) S x).card
    let l := (ls (G := G) S x).card
    let p := (ps (G := G) S x).card
    let q := (qs (G := G) S x).card
    (12 ≤ 4*s+3*(p+q)+2*l ∧ 12 ≤ 4*s+2*p+3*q+3*l) ∧ (l = 0 → 6 ≤ 2*s+p) := by
  dsimp
  have hl := Finset.card_le_card (lone_support_subset (G := G) S x)
  have hp := Finset.card_pos.mpr (blocked_support_ne (G := G) S x sym loopless hS hb)
  have h1 := blocked_one_lone (G := G) S x sym loopless hS hb
  have h20 := blocked_two_no_lone (G := G) S x sym loopless hS
  have h21 := blocked_two_one_lone (G := G) S x sym loopless hS
  refine ⟨blocked_lower_charge _ _ _ _ hl hp h1 h20 h21, ?_⟩
  intro hz
  apply blocked_lower_charge_no_lone
  · by_contra hh
    have hs : (ns (G := G) S x).card = 1 := by omega
    have h := (h1 hs).1
    omega
  · intro hs
    exact h20 hs hz

#print axioms blocked_graph_charge
#print axioms blocked_one_lone
#print axioms blocked_two_no_lone
#print axioms blocked_two_one_lone
#print axioms owner_of_small_support
#print axioms blocked_support_ne
end Erdős151
