import RibbonD3WideOrbitCheck0
import RibbonD3WideOrbitCheck1
import RibbonD3WideOrbitCheck2
import RibbonD3WideOrbitCheck3
import RibbonD3WideOrbitCheck4
import RibbonD3WideOrbitCheck5
import RibbonD3WideOrbitCheck6
import RibbonD3WideOrbitCheck7
import RibbonD3WideOrbitCheck8
import RibbonD3WideOrbitCheck9
import RibbonD3WideOrbitCheck10
import RibbonD3WideOrbitCheck11

namespace RibbonD3WideFinite
theorem all_orbits (i : B) : PairOrbit i ∧ JetOrbit i := by
  have lo := i.isLt
  have K (start : Nat) (hk : ∀ t : Fin 8, PairOrbit (pairChunk start t) ∧ JetOrbit (pairChunk start t))
      (l : start ≤ i.val) (h : i.val<start+8) : PairOrbit i ∧ JetOrbit i := by
    let t : Fin 8 := ⟨i.val-start,by omega⟩
    have e : pairChunk start t=i := Fin.ext (by
      change (start+(i.val-start))%96=i.val
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
  by_cases h6 : i.val<56
  · exact K 48 (fun n => ⟨pairOrbit6 n,jetOrbit6 n⟩) (by omega) h6
  by_cases h7 : i.val<64
  · exact K 56 (fun n => ⟨pairOrbit7 n,jetOrbit7 n⟩) (by omega) h7
  by_cases h8 : i.val<72
  · exact K 64 (fun n => ⟨pairOrbit8 n,jetOrbit8 n⟩) (by omega) h8
  by_cases h9 : i.val<80
  · exact K 72 (fun n => ⟨pairOrbit9 n,jetOrbit9 n⟩) (by omega) h9
  by_cases h10 : i.val<88
  · exact K 80 (fun n => ⟨pairOrbit10 n,jetOrbit10 n⟩) (by omega) h10
  exact K 88 (fun n => ⟨pairOrbit11 n,jetOrbit11 n⟩) (by omega) (by omega)
end RibbonD3WideFinite
