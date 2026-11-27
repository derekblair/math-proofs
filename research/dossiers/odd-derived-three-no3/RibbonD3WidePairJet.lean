import RibbonD3WideCover
import RibbonD3WideOrbits
import RibbonD3WidePairCerts
import RibbonD3WideJetCerts
namespace RibbonD3WideFinite
universe u

theorem pair_cover : RibbonD3Odd.PairCover.{u} Bad :=
  from_pair_orbits (fun i => (all_orbits i).1) pair_certs

theorem jet_cover : RibbonD3Odd.JetCover.{u} Bad :=
  from_jet_orbits (fun i => (all_orbits i).2) jet_certs

#print axioms pair_cover
#print axioms jet_cover
end RibbonD3WideFinite
