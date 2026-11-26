import HaarMatrixShards
import HaarOwnerCertificate

namespace HaarOwnerBind

theorem certify (l : List (List Nat)) (owner : Nat → Nat × Nat)
    (h : ∀ s < l.length, HaarOwnerCertificate.checkShard owner s 0 l[s]! = true) :
    l.flatten.Nodup := by
  apply HaarOwnerCertificate.of_checks l owner
  intro s chunk hs
  have bounded : s < l.length := by
    by_contra! H
    have none := List.getElem?_eq_none_iff.mpr H
    rw [hs] at none
    contradiction
  have e : l[s]! = chunk := List.getElem!_of_getElem? hs
  rw [← e]
  exact h s bounded

end HaarOwnerBind
#print axioms HaarOwnerBind.certify
