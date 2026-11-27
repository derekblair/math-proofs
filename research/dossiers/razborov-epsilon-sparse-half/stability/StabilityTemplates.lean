import PetersenCharts
import Mathlib.Data.Finset.Powerset

namespace PetersenStability

def adj (u v : V) : Bool := edge u v || edge v u
def outer (u v : Fin 5) : Bool :=
  ((u.val + 1) % 5 == v.val) || ((v.val + 1) % 5 == u.val)

/-- Every nonedge, including a same-template-cell pair of distinct
blowup vertices, has an original common-neighbor cell. -/
theorem petersen_common : ∀ u v : V, adj u v = false →
    ∃ j : V, j.val < 10 ∧ adj u j = true ∧ adj v j = true := by decide

theorem petersen_triangle_free : ∀ u v j : V,
    adj u v = true → adj u j = true → adj v j = false := by decide

theorem petersen_loopless : ∀ v : V, adj v v = false := by decide

def base : Finset V := Finset.univ.filter (fun v => v.val < 10)

def independent (s : Finset V) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, adj u v = false

instance (s : Finset V) : Decidable (independent s) := by
  unfold independent
  infer_instance

private theorem single_neighbor : ∀ a : V, a.val < 10 →
    ∃ i : V, adj a i = true := by decide

set_option maxRecDepth 512 in
set_option maxHeartbeats 1000000 in
private theorem triple_pattern :
    ∀ a b : V, a.val < 10 → b.val < 10 → a ≠ b → adj a b = false →
      ∃ i : Fin 5, adj a (extra i) = true ∧ adj b (extra i) = true ∧
        ∀ c : V, c.val < 10 → adj a c = false → adj b c = false →
          adj c (extra i) = false →
          ∃ j : V, j.val < 10 ∧ ∀ d : V, d.val < 10 →
            adj a d = false → adj b d = false → adj c d = false →
            adj d j = true := by decide

/-- Every independent pattern among the ten original classes is
contained in the original neighborhood of a class of the extension. -/
theorem petersen_pattern (s : Finset V) (h : s ⊆ base) (hi : independent s) :
    ∃ i : V, ∀ a ∈ s, adj a i = true := by
  have hbase (a : V) (ha : a ∈ s) : a.val < 10 := (Finset.mem_filter.mp (h ha)).2
  by_cases hn : s.Nonempty
  · obtain ⟨a,ha⟩ := hn
    by_cases hb : ∃ b ∈ s, a ≠ b
    · obtain ⟨b,hb,hab⟩ := hb
      obtain ⟨i,_,_,H⟩ := triple_pattern a b (hbase _ ha) (hbase _ hb) hab (hi _ ha _ hb)
      by_cases hc : ∀ d ∈ s, adj d (extra i) = true
      · exact ⟨extra i,hc⟩
      · push Not at hc
        obtain ⟨c,hc,hci⟩ := hc
        obtain ⟨j,_,hj⟩ := H c (hbase _ hc) (hi _ ha _ hc) (hi _ hb _ hc) (by simpa using hci)
        exact ⟨j,fun d hd => hj d (hbase _ hd) (hi _ ha _ hd) (hi _ hb _ hd) (hi _ hc _ hd)⟩
    · obtain ⟨i,hi'⟩ := single_neighbor a (hbase _ ha)
      refine ⟨i,fun d hd => ?_⟩
      have hd' : a = d := by
        by_contra hne
        exact hb ⟨d,hd,hne⟩
      simpa only [← hd'] using hi'
  · exact ⟨0,fun a ha => False.elim (hn ⟨a,ha⟩)⟩

theorem c5_common : ∀ u v : Fin 5, outer u v = false →
    ∃ j : Fin 5, outer u j = true ∧ outer v j = true := by decide

theorem c5_triangle_free : ∀ u v j : Fin 5,
    outer u v = true → outer u j = true → outer v j = false := by decide

theorem c5_pattern (s : Finset (Fin 5))
    (hi : ∀ u ∈ s, ∀ v ∈ s, outer u v = false) :
    ∃ i : Fin 5, ∀ a ∈ s, outer a i = true := by
  have H : ∀ s ∈ (Finset.univ : Finset (Fin 5)).powerset,
      (∀ u ∈ s, ∀ v ∈ s, outer u v = false) →
      ∃ i : Fin 5, ∀ a ∈ s, outer a i = true := by decide
  exact H s (Finset.mem_powerset.mpr (Finset.subset_univ s)) hi

#print axioms petersen_pattern
#print axioms petersen_common
#print axioms c5_pattern
end PetersenStability
