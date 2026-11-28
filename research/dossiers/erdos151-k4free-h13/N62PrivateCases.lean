import N62PrivateExact

namespace Erdos151N62

/-- The private demand and lone-row budgets confine the 16-edge row
to five singleton counts. P counts A+D and J counts A+B+C. -/
theorem tight16_private_cases
    (A B C D I L : Nat)
    (demand : 147≤I+A+B+C+(A+D))
    (privateCap : A+B+C≤12) (incidence : I≤100)
    (lone : A+2*D+C≤L) (loneCap : L≤62) :
    (A=8 ∧ D=27 ∧ B=4 ∧ C=0 ∧ L=62) ∨
    (A=9 ∧ D=26 ∧ B+C=3 ∧ C≤1) ∨
    (A=10 ∧ D=26 ∧ 1≤B ∧ C=0 ∧ L=62) ∨
    (A=10 ∧ D=25 ∧ B+C=2) ∨
    (A=11 ∧ 24≤D) ∨
    (A=12 ∧ 23≤D) := by omega

theorem marked_ten_star_degree
    (A D r n q : Nat)
    (special : 35≤A+D)
    (marks : A≤n+2)
    (omitted : q≤11)
    (sums : D≤10+q+r) :
    13≤1+n+r := by omega

theorem tight16_ghost_only_unmarked_numbers
    (t c u missG missQ : Nat)
    (big : 24≤t+c+u) (coreCap : t+2*c≤30)
    (pairCap : u≤1)
    (cross : t+missG+missQ=20)
    (pressure : u=1 → 21≤12+missG+(missG+missQ))
    (noPair : u=0 → c≤2*(missG+missQ)) :
    False := by
  by_cases h : u=1
  · have hh := pressure h
    omega
  · have hh := noPair (by omega)
    omega

theorem tight16_core_only_unmarked_numbers
    (t c u f z : Nat)
    (big : 24≤t+c+u) (coreCap : t+2*c≤31)
    (pairCap : u≤1)
    (cross : t+f=20)
    (pair : u=1 → t≤11)
    (sep : u=0 → 2*z≤f ∧ c≤2+f+z) :
    False := by
  by_cases h : u=1
  · have hh := pair h
    omega
  · have hh := sep (by omega)
    omega

theorem tight16_doubleB_numbers (t c u f fm fu z : Nat)
    (doubles : t+c+u=25) (coreCap : t+2*c≤32)
    (pairCap : u≤1)
    (cross : t+f=20) (miss : f=fm+fu)
    (pair : u=1 → t≤12)
    (sep : u=0 → 2*z≤fm ∧ c≤4+f+z)
    (noCommon : 1≤fu) : False := by
  by_cases h : u=1
  · have hh := pair h
    omega
  · have hh := sep (by omega)
    omega

#print axioms tight16_private_cases
#print axioms marked_ten_star_degree
#print axioms tight16_ghost_only_unmarked_numbers
#print axioms tight16_core_only_unmarked_numbers
#print axioms tight16_doubleB_numbers
end Erdos151N62
