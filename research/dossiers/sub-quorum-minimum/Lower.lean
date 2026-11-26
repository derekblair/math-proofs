import Optimum

namespace QuorumMinimum

open Classical QuorumBounds
variable {V : Type}
noncomputable section

def CliqueOn (G : SimpleGraph V) (t : Finset V) : Prop :=
  ∀ x ∈ t, ∀ y ∈ t, x ≠ y → G.Adj x y

def NoClique (G : SimpleGraph V) (k : Nat) (s : Finset V) : Prop :=
  ∀ t ⊆ s, t.card = k → ¬ CliqueOn G t

theorem neigh_no (G : SimpleGraph V) (s : Finset V) (v : V) (hv : v ∈ s)
    (k : Nat) (h : NoClique G (k+1) s) :
    NoClique G k ((s.erase v).filter (G.Adj v)) := by
  intro t sub ct cl
  have notin : v ∉ t := by
    intro c
    exact G.irrefl ((Finset.mem_filter.mp (sub c)).2)
  apply h (insert v t)
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hv
    · exact (Finset.mem_erase.mp (Finset.mem_filter.mp (sub hx)).1).2
  · rw [Finset.card_insert_of_notMem notin,ct]
  · intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with he|hxt
    · subst x
      rcases Finset.mem_insert.mp hy with he|hyt
      · exact (hxy he.symm).elim
      · exact (Finset.mem_filter.mp (sub hyt)).2
    · rcases Finset.mem_insert.mp hy with he|hyt
      · subst y
        exact (show G.Adj v x from (Finset.mem_filter.mp (sub hxt)).2).symm
      · exact cl x hxt y hyt hxy

theorem small_of_no_single (G : SimpleGraph V) (s : Finset V) (h : NoClique G 1 s) :
    s.card = 0 := by
  by_contra hn
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hn)
  apply h {v} (by simpa using hv) (by simp)
  intro x hx y hy hxy
  have ex : x=v := Finset.mem_singleton.mp hx
  have ey : y=v := Finset.mem_singleton.mp hy
  exact (hxy (ex.trans ey.symm)).elim

theorem ramsey_power (G : SimpleGraph V) (s : Finset V) (a b : Nat)
    (ha : NoClique G (a+1) s) (hb : NoClique Gᶜ (b+1) s) :
    s.card < 2^(a+b) := by
  have aux (d : Nat) :
      ∀ a b : Nat, a+b=d → ∀ s : Finset V,
        NoClique G (a+1) s → NoClique Gᶜ (b+1) s → s.card < 2^d := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro a b eq s ha hb
      cases a with
      | zero =>
        rw [small_of_no_single G s ha]; positivity
      | succ a =>
        cases b with
        | zero =>
          rw [small_of_no_single Gᶜ s hb]; positivity
        | succ b =>
          by_cases ns : s.card = 0
          · rw [ns]; positivity
          obtain ⟨v,hv⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero ns)
          letI : DecidablePred (Gᶜ.Adj v) := fun _ => Classical.propDecidable _
          let A := (s.erase v).filter (G.Adj v)
          let B := (s.erase v).filter (Gᶜ.Adj v)
          have subA : A ⊆ s := fun _ hx =>
            (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2
          have subB : B ⊆ s := fun _ hx =>
            (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2
          have hA := ih (a+(b+1)) (by omega) a (b+1) rfl A (neigh_no G s v hv _ ha)
            (fun t ht => hb t (ht.trans subA))
          have nhB : NoClique Gᶜ (b+1) B := by
            intro t ht
            apply neigh_no Gᶜ s v hv _ hb t
            intro w hw
            have hh := ht hw
            exact Finset.mem_filter.mpr (Finset.mem_filter.mp hh)
          have hB := ih ((a+1)+b) (by omega) (a+1) b rfl B
            (fun t ht => ha t (ht.trans subB)) nhB
          have eqAB : A.card+B.card+1=s.card := by
            have he : B=(s.erase v).filter (fun w => ¬ G.Adj v w) := by
              ext w
              simp only [B,Finset.mem_filter]
              constructor
              · rintro ⟨h,e⟩
                exact ⟨h, (SimpleGraph.compl_adj _ _ _).mp e |>.2⟩
              · rintro ⟨h,e⟩
                exact ⟨h, (SimpleGraph.compl_adj _ _ _).mpr
                  ⟨(Finset.mem_erase.mp h).1.symm,e⟩⟩
            rw [he]
            change ((s.erase v).filter (G.Adj v)).card +
                ((s.erase v).filter (fun w => ¬ G.Adj v w)).card + 1 = s.card
            rw [Finset.card_filter_add_card_filter_not,Finset.card_erase_of_mem hv]
            have : 0<s.card := Finset.card_pos.mpr ⟨v,hv⟩
            omega
          have dd : d=(a+(b+1))+1 := by omega
          have ee : (a+1)+b=a+(b+1) := by omega
          rw [ee] at hB
          rw [dd,Nat.pow_succ]
          omega
  exact aux (a+b) a b rfl s ha hb

#print axioms ramsey_power
end
end QuorumMinimum
