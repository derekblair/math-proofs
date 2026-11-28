import CubicSquareCertificate
import Mathlib.Data.Finset.Powerset

open scoped BigOperators
namespace Erdős151.H12.Wagner

variable {V : Type*} [DecidableEq V]

def edgesIn (E T : Finset (Finset V)) (t : ↥T) : Finset ↥E :=
  Finset.univ.filter (fun e => e.val ⊆ t.val)

theorem edgesIn_row (E T : Finset (Finset V))
    (e2 : ∀ e∈E, (e : Finset V).card=2) (t3 : ∀ t∈T, (t : Finset V).card=3)
    (closed : ∀ t∈T, ∀ e ⊆ t, (e : Finset V).card=2 → e∈E) :
    ∀ t : ↥T, (∑ e : ↥E, if e ∈ edgesIn E T t then (1:ℕ) else 0) = 3 := by
  classical
  intro t
  let f : ↥E ↪ Finset V := ⟨Subtype.val,Subtype.val_injective⟩
  have he : (edgesIn E T t).map f = t.val.powersetCard 2 := by
    ext e
    simp only [Finset.mem_map, Finset.mem_powersetCard]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨(Finset.mem_filter.mp hx).2,e2 x.val x.property⟩
    · rintro ⟨sub,card⟩
      have he := closed t.val t.property e sub card
      exact ⟨⟨e,he⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,sub⟩,rfl⟩
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,Nat.nsmul_eq_mul,mul_one]
  have hh := congrArg Finset.card he
  rw [Finset.card_map,Finset.card_powersetCard,t3 _ t.property] at hh
  exact hh

/-- Connect edge nodes by walking through host vertices, given that
all edges through one vertex lie in a single co-triangle component. -/
theorem host_paths_to_edges
    (E T : Finset (Finset V)) (origin : V) (p : ↥E) (hp : origin ∈ p.val)
    (edgeNonempty : ∀ e ∈ E, (e : Finset V).Nonempty)
    (localPath : ∀ v : V, ∀ e f : ↥E, v∈e.val → v∈f.val →
      ∃ n, Erdős151.H12.Steps (coTriangle (edgesIn E T)) n e f)
    (hostPath : ∀ v, ∃ n, Erdős151.H12.Steps
      (fun x y => ∃ e : ↥E, x∈e.val ∧ y∈e.val) n v origin) :
    ∀ e : ↥E, ∃ n, Erdős151.H12.Steps (coTriangle (edgesIn E T)) n e p := by
  let canReach (a : V) : Prop := ∀ e : ↥E, a∈e.val →
    ∃ n, Erdős151.H12.Steps (coTriangle (edgesIn E T)) n e p
  have walk {n a b} (path : Erdős151.H12.Steps
      (fun x y => ∃ e : ↥E, x∈e.val ∧ y∈e.val) n a b) : canReach b → canReach a := by
    induction path with
    | zero _ => exact id
    | more rel _ ih =>
      intro endok e he
      obtain ⟨f,hf,hf'⟩ := rel
      obtain ⟨_,ef⟩ := localPath _ e f he hf
      obtain ⟨_,fp⟩ := ih endok f hf'
      exact Steps.concat ef fp
  intro e
  obtain ⟨v,hv⟩ := edgeNonempty e.val e.property
  obtain ⟨_,path⟩ := hostPath v
  exact walk path (fun f hf => localPath origin f p hf hp) e hv

#print axioms edgesIn_row
#print axioms host_paths_to_edges
end Erdős151.H12.Wagner
