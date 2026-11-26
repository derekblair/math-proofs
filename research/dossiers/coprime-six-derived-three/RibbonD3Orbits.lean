import RibbonD3OrbitCheck0
import RibbonD3OrbitCheck1
import RibbonD3OrbitCheck2
import RibbonD3OrbitCheck3
import RibbonD3OrbitCheck4
import RibbonD3OrbitCheck5
import RibbonD3OrbitCheck6

namespace RibbonD3Finite
theorem all_orbits (i : B) : PairOrbit i ∧ JetOrbit i := by
  have lo := i.isLt
  have K (start : Nat) (hk : ∀ t : Fin 8, PairOrbit (pairChunk start t) ∧ JetOrbit (pairChunk start t))
      (l : start ≤ i.val) (h : i.val<start+8) : PairOrbit i ∧ JetOrbit i := by
    let t : Fin 8 := ⟨i.val-start,by omega⟩
    have e : pairChunk start t=i := Fin.ext (by
      change (start+(i.val-start))%52=i.val
      rw [show start+(i.val-start)=i.val by omega,Nat.mod_eq_of_lt lo])
    exact e ▸ hk t
  by_cases h0 : i.val<8
  · exact K 0 (fun n => ⟨pairOrbit0 n,jetOrbit0 n⟩) (by omega) h0
  by_cases h1 : i.val<16
  · exact K 8 (fun n => ⟨pairOrbit1 n,jetOrbit1 n⟩) (by omega) h1
  by_cases h2 : i.val<24
  · exact K 16 (fun n => ⟨pairOrbit2 n,jetOrbit2 n⟩) (by omega) h2
  by_cases h3 : i.val<32
  · exact K 24 (fun n => ⟨pairOrbit3 n,jetOrbit3 n⟩) (by omega) h3
  by_cases h4 : i.val<40
  · exact K 32 (fun n => ⟨pairOrbit4 n,jetOrbit4 n⟩) (by omega) h4
  by_cases h5 : i.val<48
  · exact K 40 (fun n => ⟨pairOrbit5 n,jetOrbit5 n⟩) (by omega) h5
  exact K 48 (fun n => ⟨pairOrbit6 n,jetOrbit6 n⟩) (by omega) (by omega)
end RibbonD3Finite
