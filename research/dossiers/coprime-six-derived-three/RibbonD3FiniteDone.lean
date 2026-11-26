import RibbonD3FiniteCover
import RibbonD3Orbits
import RibbonD3PairCerts
import RibbonD3JetCerts

namespace RibbonD3Finite
universe u

theorem all_pairs : RibbonD3Stationary.PairCover.{u} Bad :=
  from_pair_orbits (fun i => (all_orbits i).1) pair_certs

theorem all_jets : RibbonD3Stationary.JetCover.{u} Bad :=
  from_jet_orbits (fun i => (all_orbits i).2) jet_certs

end RibbonD3Finite
#print axioms RibbonD3Finite.all_pairs
#print axioms RibbonD3Finite.all_jets
