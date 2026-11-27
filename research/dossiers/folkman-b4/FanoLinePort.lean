import FanoPointPort

namespace FolkmanB4.Fano
open Finset
open FolkmanB4.Tight
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {S : Finset (Finset (Finset V))}

theorem line_port_fragment (A : Line S → Bool) (B : Point S → Bool)
    (r : Fin 7 ≃ Option (In A)) (c : Fin 7 ≃ In B)
    (iso : ∀ l p : Fin 7,
      pointsContraction (fun x y => FolkmanB4.inc S y x) B A (c p) (r l) ↔ inc l p)
    (none0 : r 0=none) (rows : ∀ l : Line S, l.val.card=3)
    (edges : ∀ p : Point S, p.val.card=2) : HasLineFragment S := by
  let w : Fin 7 ↪ Finset V :=
    (c.toEmbedding.trans (Function.Embedding.subtype (fun e => B e=true))).trans
      (Function.Embedding.subtype (fun e => e∈points S))
  apply line_fragment_of_named w (fun i => edges (c i).val)
  intro l ln
  cases eq : r l with
  | none => exact False.elim (ln (r.injective (eq.trans none0.symm)))
  | some t =>
    let tr := t.val
    refine ⟨tr,tr.property,rows tr,fun p hp => ?_⟩
    have I := (iso l p).mpr hp
    rw [eq] at I
    exact I

theorem normalize_line_port (A : Line S → Bool) (B : Point S → Bool)
    (r : Fin 7 ≃ Option (In A)) (c : Fin 7 ≃ In B)
    (iso : ∀ l p : Fin 7,
      pointsContraction (fun x y => FolkmanB4.inc S y x) B A (c p) (r l) ↔ inc l p)
    (rows : ∀ l : Line S, l.val.card=3) (edges : ∀ p : Point S, p.val.card=2) :
    HasLineFragment S := by
  obtain ⟨k,hk⟩ := can_pin_row (r.symm none)
  let r' := (lineCycle^k.val).trans r
  let c' := (pointCycle^k.val).trans c
  have eq (l p : Fin 7) :
      pointsContraction (fun x y => FolkmanB4.inc S y x) B A (c' p) (r' l) ↔ inc l p :=
    (iso _ _).trans (powers_preserve k.val l p)
  have e : r' 0=none := by
    change r ((lineCycle^k.val) 0)=none
    rw [hk,r.apply_symm_apply]
  exact line_port_fragment A B r' c' eq e rows edges

theorem full_fano_fragment (r : Fin 7 ↪ Line S) (c : Fin 7 ↪ Point S)
    (iso : ∀ l p : Fin 7, FolkmanB4.inc S (r l) (c p) ↔ inc l p)
    (rows : ∀ l : Line S, l.val.card=3) (edges : ∀ p : Point S, p.val.card=2) :
    HasLineFragment S := by
  let w := c.trans (Function.Embedding.subtype (fun e => e∈points S))
  exact line_fragment_of_named w (fun i => edges (c i))
    (fun l _ => ⟨(r l).val,(r l).property,rows (r l),fun p hp => (iso l p).mpr hp⟩)

#print axioms normalize_line_port
#print axioms full_fano_fragment
end FolkmanB4.Fano
