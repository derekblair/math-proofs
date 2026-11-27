import Mathlib.Tactic

/-! Arithmetic supporting the cograph separator proof. The graph theorem itself is
proved in the dossier, not formalized in this file. -/

namespace BondyCographAudit

theorem ore_deficit (k s n head tail deg : ℤ)
    (hn : n = s + head + tail)
    (hdeg : deg ≤ (k + 1) * (s - 1) + head)
    (htail : k * (s - k) ≤ tail) :
    deg < n + k * (k - 1) := by
  nlinarith

theorem no_two_dominants (t ai aj pi pj outside : ℕ)
    (ht : 0 < t)
    (hi : pi = t + aj + outside) (hj : pj = t + ai + outside)
    (hpi : pi ≤ ai) (hpj : pj ≤ aj) : False := by
  omega

theorem donor_competitor_bound (t u retained competitorDemand : ℕ)
    (ht : 2 ≤ t) (hchildren : t + u - 1 ≤ retained)
    (hc : competitorDemand ≤ u) :
    competitorDemand ≤ t - 1 + retained := by
  omega

theorem splice_accounting (donor recipient donor' recipient' : ℕ)
    (hd : donor' + 1 ≤ donor) (hr : recipient' ≤ recipient + 1) :
    donor' + recipient' ≤ donor + recipient := by
  omega

#print axioms ore_deficit
#print axioms no_two_dominants
#print axioms donor_competitor_bound
#print axioms splice_accounting
end BondyCographAudit
