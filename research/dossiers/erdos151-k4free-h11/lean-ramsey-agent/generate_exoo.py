"""Compile Exoo's 46x46 listing (off-diagonal zeros are edges) to Lean masks."""
from pathlib import Path
import sys
src = Path(sys.argv[1] if len(sys.argv) > 1 else "../ramsey47/exoo-paper-46.txt")
ls = src.read_text().split()
assert len(ls) == 46 and all(len(s) == 46 and set(s) <= set("01") for s in ls)
assert all(ls[i][j] == ls[j][i] for i in range(46) for j in range(46))
masks = [sum(1 << j for j, bit in enumerate(s) if i != j and bit == "0") for i, s in enumerate(ls)]
out = '''import RamseySearch

namespace Erdos151Ramsey.Exoo
set_option maxHeartbeats 0
set_option maxRecDepth 4096

def masks : Array Nat := #[MASKS]

def adj (a b : Fin 46) : Bool :=
  masks[a.val]!.testBit b.val

def graph (a b : Fin 46) : Prop := adj a b = true

instance : DecidableRel graph := fun a b => inferInstanceAs (Decidable (adj a b = true))

def rowCheck (a : Fin 46) : Bool :=
  findIndependent adj 10 ((List.finRange 46).filter
    (fun b => decide (a < b) && !adj a b))

def tfCheck (a : Fin 46) : Bool :=
  (List.finRange 46).all fun b =>
    if adj a b then (List.finRange 46).all (fun c => !(adj b c && adj a c)) else true

theorem tfCheck_sound (h : ∀ a, tfCheck a = true) : TriangleFree graph := by
  intro a b c hab hbc hac
  have hb := List.all_eq_true.mp (h a) b (List.mem_finRange b)
  change adj a b = true at hab
  rw [if_pos hab] at hb
  have hc := List.all_eq_true.mp hb c (List.mem_finRange c)
  change adj b c = true at hbc
  change adj a c = true at hac
  simp [hbc, hac] at hc

'''.replace('MASKS', ', '.join(map(str, masks)))
for i in range(46):
    out += f'theorem bound_{i} : rowCheck {i} = false := by decide +kernel\n'
    out += f'theorem tri_{i} : tfCheck {i} = true := by decide +kernel\n'
for thm, statement, prefix in [('rows','rowCheck a = false','bound'), ('triangles','tfCheck a = true','tri')]:
    out += f'\ntheorem {thm} (a : Fin 46) : {statement} := by\n'
    out += f'  exact Fin.cases ' + ''.join(f'{prefix}_{i} (Fin.cases ' for i in range(45))
    out += f'{prefix}_45 (fun t : Fin 0 => t.elim0)' + ''.join(') ' for _ in range(45)) + 'a\n'
out += '''
theorem graph_symmetric : ∀ a b, graph a b → graph b a := by
  decide +kernel

theorem graph_irreflexive : ∀ a, ¬ graph a a := by
  decide +kernel

theorem triangle_free : TriangleFree graph := tfCheck_sound triangles

theorem alpha_le_ten (S : Finset (Fin 46)) (h : Independent graph S) : S.card ≤ 10 :=
  bound_of_per_vertex adj 10 rows S h

theorem ramsey311_ge47 :
    ∃ R : Fin 46 → Fin 46 → Prop, (∀ a b, R a b → R b a) ∧ (∀ a, ¬ R a a) ∧
      TriangleFree R ∧ (∀ S : Finset (Fin 46), Independent R S → S.card ≤ 10) :=
  ⟨graph, graph_symmetric, graph_irreflexive, triangle_free, alpha_le_ten⟩

#print axioms ramsey311_ge47
end Erdos151Ramsey.Exoo
'''
print(out, end='')
