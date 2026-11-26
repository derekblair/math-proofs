import HaarMatrix31NoShort
import HaarWordExtension

namespace HaarMatrix31ShortBound
open HaarAllNoncommuting HaarMatrix31Core HaarMatrix31Packed HaarMatrix31PackedSound

theorem halfDiameterBound (nd : (words zero true 3 17).Nodup) (k : ℕ) (lo : 2 ≤ k) (hi : k ≤ 17) :
    ¬ HasCycle x y (2*k) := by
  intro hc
  obtain ⟨L,R,hl,hr,gl,gr,hne,hend⟩ := HaarHalfCollision.exists_collision x y k lo hc
  obtain ⟨A,B,al,bl,ag,bg,ne,eq⟩ :=
    HaarWordExtension.extend x y (17-k) k L R hl hr gl gr hne hend
  apply ne
  apply HaarMatrix31WordsBridge.injective_keys 17 nd A B (by omega) (by omega) ag bg
  rw [← HaarMatrix31NoShort.link A, ← HaarMatrix31NoShort.link B, eq]

end HaarMatrix31ShortBound
#print axioms HaarMatrix31ShortBound.halfDiameterBound
