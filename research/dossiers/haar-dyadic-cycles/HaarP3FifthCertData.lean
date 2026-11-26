import HaarP3FifthCert01
import HaarP3FifthCert02
import HaarP3FifthCert10
import HaarP3FifthCert11
import HaarP3FifthCert12
import HaarP3FifthCert20
import HaarP3FifthCert21
import HaarP3FifthCert22
namespace HaarP3FifthCert
theorem coverage (p q a b c : Fin 3) (he : ¬ (p.val=0 ∧ q.val=0))
    (h12 : ¬ (p.val=1 ∧ q.val=2 ∧ a.val=2 ∧ b.val=2 ∧ c.val=2))
    (h21 : ¬ (p.val=2 ∧ q.val=1 ∧ a.val=1 ∧ b.val=1 ∧ c.val=1)) :
    ∃ C, Valid ⟨p.val,q.val,a.val,b.val,c.val⟩ C := by
  fin_cases p <;> fin_cases q
  · exact False.elim (he ⟨rfl,rfl⟩)
  · exact ⟨_,correct01 a b c⟩
  · exact ⟨_,correct02 a b c⟩
  · exact ⟨_,correct10 a b c⟩
  · exact ⟨_,correct11 a b c⟩
  · exact ⟨_,correct12 a b c (fun h => h12 ⟨rfl,rfl,h⟩)⟩
  · exact ⟨_,correct20 a b c⟩
  · exact ⟨_,correct21 a b c (fun h => h21 ⟨rfl,rfl,h⟩)⟩
  · exact ⟨_,correct22 a b c⟩
end HaarP3FifthCert
#print axioms HaarP3FifthCert.coverage
