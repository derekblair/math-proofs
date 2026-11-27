import FanoTransfer
import TightShoreLift

namespace FolkmanB4.Fano
open Finset
open FolkmanB4.Tight

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {S : Finset (Finset (Finset V))}

theorem point_port_fragment (A : Line S → Bool) (B : Point S → Bool)
    (r : Fin 7 ≃ In A) (c : Fin 7 ≃ Option (In B))
    (iso : ∀ l p : Fin 7, pointsContraction (FolkmanB4.inc S) A B (r l) (c p) ↔ inc l p)
    (none6 : c 6=none) (rows : ∀ l : Line S, l.val.card=3)
    (edges : ∀ p : Point S, p.val.card=2) : HasPointFragment S := by
  have z : inc 2 6 := by decide
  have cut : pointsContraction (FolkmanB4.inc S) A B (r 2) none := by
    simpa only [none6] using (iso 2 6).mpr z
  obtain ⟨u,hout,hu⟩ := cut
  let w : Fin 7 ↪ Finset V :=
    (c.toEmbedding.trans ⟨inLabel B u,inLabel_injective B u hout⟩).trans
      (Function.Embedding.subtype (fun e => e∈points S))
  have W (i : Fin 7) : (w i).card=2 := edges (inLabel B u (c i))
  have row (l : Fin 7) (avoid : ¬inc l 6 ∨ l=2) : named S w l := by
    let v := (r l).val
    refine ⟨v,v.property,rows v,fun p pl => ?_⟩
    have gi := (iso l p).mpr pl
    cases eq : c p with
    | none =>
      have e : p=6 := c.injective (eq.trans none6.symm)
      have ll : l=2 := avoid.resolve_left (fun h => h (e ▸ pl))
      change (inLabel B u (c p)).val∈v.val
      rw [eq]
      subst l
      exact hu
    | some q =>
      change (inLabel B u (c p)).val∈v.val
      rw [eq]
      rwa [eq] at gi
  exact point_fragment_of_named w W (row 0 (.inl (by decide))) (row 1 (.inl (by decide)))
    (row 3 (.inl (by decide))) (row 6 (.inl (by decide))) (row 2 (.inr rfl))

/-- A point-side Heawood contraction yields the normalized deleted-point
fragment; the independent point relabeling must also relabel the lines. -/
theorem normalize_point_port (A : Line S → Bool) (B : Point S → Bool)
    (r : Fin 7 ≃ In A) (c : Fin 7 ≃ Option (In B))
    (iso : ∀ l p : Fin 7, pointsContraction (FolkmanB4.inc S) A B (r l) (c p) ↔ inc l p)
    (rows : ∀ l : Line S, l.val.card=3) (edges : ∀ p : Point S, p.val.card=2) :
    HasPointFragment S := by
  obtain ⟨k,hk⟩ := can_pin_column (c.symm none)
  let r' := (lineCycle^k.val).trans r
  let c' := (pointCycle^k.val).trans c
  have eq (l p : Fin 7) : pointsContraction (FolkmanB4.inc S) A B (r' l) (c' p) ↔ inc l p :=
    (iso _ _).trans (powers_preserve k.val l p)
  have e : c' 6=none := by
    change c ((pointCycle^k.val) 6)=none
    rw [hk,c.apply_symm_apply]
  exact point_port_fragment A B r' c' eq e rows edges

#print axioms normalize_point_port
end FolkmanB4.Fano
