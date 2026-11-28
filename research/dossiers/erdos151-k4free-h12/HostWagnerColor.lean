import HostSquareData
import WagnerHostDegree
import Mathlib.Data.Finset.Powerset

open scoped BigOperators
namespace Erdős151.H12.Wagner

variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]
  [DecidableEq V] [DecidableEq L] [DecidableEq R]

@[simp] theorem hostInc_mem (E : L ↪ Finset V) (Tr : R ↪ Finset V) (e : L) (t : R) :
    e∈hostIncEdge E Tr t ↔ E e⊆Tr t := by simp [hostIncEdge]

theorem hostInc_row (E : L ↪ Finset V) (Tr : R ↪ Finset V)
    (ec : ∀ e,(E e).card=2) (tc : ∀ t,(Tr t).card=3)
    (cl : HostWagnerLinks.TrianglesClosed E Tr) :
    ∀ t, (∑ e : L, if e∈hostIncEdge E Tr t then (1:ℕ) else 0)=3 := by
  classical
  intro t
  have he : (hostIncEdge E Tr t).map E = (Tr t).powersetCard 2 := by
    ext q
    simp only [Finset.mem_map,Finset.mem_powersetCard]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨(hostInc_mem E Tr x t).mp hx,ec x⟩
    · rintro ⟨sub,card⟩
      obtain ⟨x,y,ne,rfl⟩ := Finset.card_eq_two.mp card
      obtain ⟨e,hx,hy⟩ := cl t x y ne (sub (by simp)) (sub (by simp))
      have eq : E e = ({x,y}:Finset V) := by
        apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
        · intro a ha
          simp only [Finset.mem_insert,Finset.mem_singleton] at ha
          rcases ha with rfl|rfl
          · exact hx
          · exact hy
        · rw [ec]
          simp [ne]
      exact ⟨e,(hostInc_mem E Tr e t).mpr (by rw [eq]; exact sub),eq⟩
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,Nat.nsmul_eq_mul,mul_one]
  have hh := congrArg Finset.card he
  rw [Finset.card_map,Finset.card_powersetCard,tc] at hh
  exact hh

private theorem host_coTriangle_from_paths {E : L ↪ Finset V} {Tr : R ↪ Finset V}
    (w : HostWagnerLinks E Tr) (ec : ∀ e,(E e).card=2)
    (conn : ∀ a b : V, Relation.ReflTransGen (hostRel E) a b)
    (p : L) (origin : V) (hp : origin ∈ E p) :
    ∀ e, ∃ n, Erdős151.H12.Steps (coTriangle (hostIncEdge E Tr)) n e p := by
  let P (a : V) := ∀ e : L, a∈E e →
    ∃ n, Erdős151.H12.Steps (coTriangle (hostIncEdge E Tr)) n e p
  have localStep {a b : V} (ab : hostRel E a b) : P b → P a := by
    intro pb e ea
    obtain ⟨f,fa,fb⟩ := ab
    obtain ⟨_,ef⟩ := w.local_coTriangle ec a e f ea fa
    obtain ⟨_,fp⟩ := pb f fb
    exact Steps.concat ef fp
  have walk {a b : V} (gh : Relation.ReflTransGen (hostRel E) a b) : P b → P a := by
    induction gh with
    | refl => exact id
    | tail _ step ih => intro hb; exact ih (localStep step hb)
  intro e
  have eno : (E e).Nonempty := Finset.card_pos.mp (by rw [ec]; decide)
  obtain ⟨v,hv⟩ := eno
  exact walk (conn v origin) (fun f hf => w.local_coTriangle ec origin f p hf hp) e hv

/-- Classification-free locally Wagner coloring in the exact actual host
incidence. Explicit local link isomorphisms certify all its premises. -/
theorem HostWagnerLinks.edge_triangle_bichromatic {E : L ↪ Finset V} {Tr : R ↪ Finset V}
    (w : HostWagnerLinks E Tr) (reflect : w.Reflects)
    (ec : ∀ e,(E e).card=2) (tc : ∀ t,(Tr t).card=3)
    (cl : HostWagnerLinks.TrianglesClosed E Tr)
    (conn : ∀ a b : V, Relation.ReflTransGen (hostRel E) a b)
    (origin : V) :
    ∃ c : L → Bool, ∀ t : R, Mixed c (hostIncEdge E Tr t) := by
  classical
  obtain ⟨spoke,tr,outside,si,ti,oi,shape,h0⟩ := w.square_data ec origin
  have col : ∀ e, (∑ t : R, if e∈hostIncEdge E Tr t then (1:ℕ) else 0)=3 :=
    w.degree_column reflect cl ec tc
  have small (S : Finset L) (T : Finset R)
      (d : Disjoint S (Finset.univ.image spoke)) (s3 : 3 ≤ S.card)
      (cut : cutMass (fun l t => l∈hostIncEdge E Tr t) S T ≤ 5) :
      mass (fun l t => l∈hostIncEdge E Tr t) S T < S.card + T.card := by
    have p4 : 4 ≤ (Finset.univ.image spoke).card := by
      rw [Finset.card_image_of_injective _ si, Finset.card_univ,Fintype.card_fin]
    have hh := w.small_cut ec tc conn origin (Finset.univ.image spoke) p4 S T d s3
      (by simpa only [cutMass,mass,hostInc_mem] using cut)
    simpa only [mass,hostInc_mem] using hh
  exact cubic_coloring_of_ordered_square (hostIncEdge E Tr) (hostInc_row E Tr ec tc cl) col
    spoke tr outside si ti oi shape small
    (host_coTriangle_from_paths w ec conn (spoke 0) origin h0)

#print axioms HostWagnerLinks.edge_triangle_bichromatic
end Erdős151.H12.Wagner
