import RibbonD3FieldDirectData0
import RibbonD3FieldDirectData1
import RibbonD3FieldDirectData2
import RibbonD3FieldDirectData3
import RibbonD3FieldDirectData4
import RibbonD3FieldDirectData5
import RibbonD3FieldDirectData6
import RibbonD3FieldDirectData7
import RibbonD3FieldDirectData8
import RibbonD3FieldDirectData9
import RibbonD3FieldDirectData10
import RibbonD3FieldDirectData11
import RibbonD3FieldDirectData12
namespace RibbonD3Field
variable {K : Type*} [Field K]
set_option maxRecDepth 30000
set_option maxHeartbeats 0
def exactBad : List Triple := [(11,1,3),(11,1,4),(11,1,5),(11,1,9),(11,3,1),(11,3,3),(11,3,4),(11,3,5),(11,3,9),(11,4,1),(11,4,3),(11,4,4),(11,4,5),(11,4,9),(11,5,1),(11,5,3),(11,5,4),(11,5,5),(11,5,9),(11,9,1),(11,9,3),(11,9,4),(11,9,5),(11,9,9),(23,1,3),(23,1,4),(23,1,6),(23,1,8),(23,1,9),(23,1,13),(23,1,16),(23,1,18),(23,3,1),(23,4,1),(23,6,1),(23,8,1),(23,9,1),(23,9,9),(23,9,18),(23,13,1),(23,16,1),(23,18,1),(23,18,9),(23,18,18),(29,1,7),(29,1,16),(29,1,20),(29,1,25),(29,7,1),(29,16,1),(29,20,1),(29,25,1)]
def directTable : Fin 101 → Nat × Nat × Nat × Count := ![(23,3,18,2),(23,4,6,0),(23,4,13,2),(23,4,16,3),(23,6,4,3),(23,6,9,2),(23,6,18,2),(23,8,16,1),(23,9,6,1),(23,13,4,3),(23,13,13,15),(23,13,16,14),(23,16,4,1),(23,16,8,3),(23,16,13,11),(23,18,3,0),(23,18,6,0),(29,7,20,3),(29,7,25,0),(29,20,7,0),(29,20,20,15),(29,20,24,3),(29,24,20,1),(29,25,7,2),(29,25,25,2),(41,10,1,9),(43,21,1,2),(47,4,18,1),(47,7,8,0),(47,8,7,2),(47,12,18,0),(47,18,4,2),(47,18,12,2),(47,21,42,2),(47,25,37,3),(47,34,42,1),(47,37,25,1),(47,42,21,1),(47,42,34,3),(53,13,1,2),(53,36,42,3),(53,42,36,1),(53,49,49,2),(59,21,36,0),(59,25,26,0),(59,26,25,3),(59,27,41,2),(59,36,21,2),(59,41,27,0),(61,20,1,2),(67,22,1,2),(71,12,60,0),(71,43,50,0),(71,50,43,2),(71,60,12,2),(83,7,51,2),(83,7,70,2),(83,12,49,1),(83,17,78,0),(83,41,1,2),(83,49,12,3),(83,51,7,1),(83,70,7,0),(83,78,17,2),(101,25,1,2),(101,52,79,3),(101,79,52,1),(107,10,76,2),(107,16,79,2),(107,42,49,0),(107,49,42,2),(107,76,10,0),(107,79,16,0),(137,34,1,2),(139,45,112,0),(139,112,45,2),(173,43,1,2),(191,117,121,0),(191,121,117,2),(191,134,135,0),(191,135,134,2),(239,11,187,0),(239,187,11,2),(251,164,175,2),(251,175,164,0),(367,200,225,0),(367,225,200,2),(419,69,300,0),(419,300,69,2),(443,86,272,2),(443,90,109,2),(443,109,90,0),(443,272,86,0),(1319,691,974,0),(1319,974,691,2),(1487,227,1034,2),(1487,1034,227,0),(2903,454,1225,0),(2903,1225,454,2),(4231,1218,2083,2),(4231,2083,1218,0)]
def directLabel (i : Fin 101) : Triple :=
  ((directTable i).1,(directTable i).2.1,(directTable i).2.2.1)

theorem classified (x : Triple) (X : x∈provisional) :
    x∈exactBad ∨ ∃ i : Fin 101, x=directLabel i := by
  have Z : (provisional.all fun x => decide (x∈exactBad ∨ ∃ i : Fin 101, x=directLabel i))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp Z x X)

theorem direct_to_ordered (a b : Kˣ) (i : Fin 101)
    (P : ((directTable i).1:K)=0) (A : (a:K)=((directTable i).2.1:K))
    (B : (b:K)=((directTable i).2.2.1:K)) :
    Ordered (chart (directTable i).2.2.2) a b := by
  fin_cases i
  · exact direct0 a b P A B
  · exact direct1 a b P A B
  · exact direct2 a b P A B
  · exact direct3 a b P A B
  · exact direct4 a b P A B
  · exact direct5 a b P A B
  · exact direct6 a b P A B
  · exact direct7 a b P A B
  · exact direct8 a b P A B
  · exact direct9 a b P A B
  · exact direct10 a b P A B
  · exact direct11 a b P A B
  · exact direct12 a b P A B
  · exact direct13 a b P A B
  · exact direct14 a b P A B
  · exact direct15 a b P A B
  · exact direct16 a b P A B
  · exact direct17 a b P A B
  · exact direct18 a b P A B
  · exact direct19 a b P A B
  · exact direct20 a b P A B
  · exact direct21 a b P A B
  · exact direct22 a b P A B
  · exact direct23 a b P A B
  · exact direct24 a b P A B
  · exact direct25 a b P A B
  · exact direct26 a b P A B
  · exact direct27 a b P A B
  · exact direct28 a b P A B
  · exact direct29 a b P A B
  · exact direct30 a b P A B
  · exact direct31 a b P A B
  · exact direct32 a b P A B
  · exact direct33 a b P A B
  · exact direct34 a b P A B
  · exact direct35 a b P A B
  · exact direct36 a b P A B
  · exact direct37 a b P A B
  · exact direct38 a b P A B
  · exact direct39 a b P A B
  · exact direct40 a b P A B
  · exact direct41 a b P A B
  · exact direct42 a b P A B
  · exact direct43 a b P A B
  · exact direct44 a b P A B
  · exact direct45 a b P A B
  · exact direct46 a b P A B
  · exact direct47 a b P A B
  · exact direct48 a b P A B
  · exact direct49 a b P A B
  · exact direct50 a b P A B
  · exact direct51 a b P A B
  · exact direct52 a b P A B
  · exact direct53 a b P A B
  · exact direct54 a b P A B
  · exact direct55 a b P A B
  · exact direct56 a b P A B
  · exact direct57 a b P A B
  · exact direct58 a b P A B
  · exact direct59 a b P A B
  · exact direct60 a b P A B
  · exact direct61 a b P A B
  · exact direct62 a b P A B
  · exact direct63 a b P A B
  · exact direct64 a b P A B
  · exact direct65 a b P A B
  · exact direct66 a b P A B
  · exact direct67 a b P A B
  · exact direct68 a b P A B
  · exact direct69 a b P A B
  · exact direct70 a b P A B
  · exact direct71 a b P A B
  · exact direct72 a b P A B
  · exact direct73 a b P A B
  · exact direct74 a b P A B
  · exact direct75 a b P A B
  · exact direct76 a b P A B
  · exact direct77 a b P A B
  · exact direct78 a b P A B
  · exact direct79 a b P A B
  · exact direct80 a b P A B
  · exact direct81 a b P A B
  · exact direct82 a b P A B
  · exact direct83 a b P A B
  · exact direct84 a b P A B
  · exact direct85 a b P A B
  · exact direct86 a b P A B
  · exact direct87 a b P A B
  · exact direct88 a b P A B
  · exact direct89 a b P A B
  · exact direct90 a b P A B
  · exact direct91 a b P A B
  · exact direct92 a b P A B
  · exact direct93 a b P A B
  · exact direct94 a b P A B
  · exact direct95 a b P A B
  · exact direct96 a b P A B
  · exact direct97 a b P A B
  · exact direct98 a b P A B
  · exact direct99 a b P A B
  · exact direct100 a b P A B
theorem scalar_cases (a b : Kˣ) (H : ScalarPair a b) :
    (∃ k, Ordered (chart k) a b) ∨
      ∃ p x y : Nat, p.Prime ∧ (p:K)=0 ∧ (a:K)=(x:K) ∧ (b:K)=(y:K) ∧ (p,x,y)∈exactBad := by
  obtain ⟨p,x,y,hp,P,A,B,E⟩ := H
  rcases classified _ E with Z|⟨i,Z⟩
  · exact Or.inr ⟨p,x,y,hp,P,A,B,Z⟩
  have ep : p=(directTable i).1 := congrArg Prod.fst Z
  have ex : x=(directTable i).2.1 := congrArg (fun q : Triple => q.2.1) Z
  have ey : y=(directTable i).2.2.1 := congrArg (fun q : Triple => q.2.2) Z
  exact Or.inl ⟨_,direct_to_ordered a b i (ep ▸ P)
    (A.trans (congrArg (fun z : Nat => (z:K)) ex))
    (B.trans (congrArg (fun z : Nat => (z:K)) ey))⟩

end RibbonD3Field
#print axioms RibbonD3Field.scalar_cases
