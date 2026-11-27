import HaarHoneyHaarGeometry
import HaarAbelCore

namespace HaarHoneyHaar
open HaarHoneyVoltage
variable {G Q : Type*} [Group G] [Group Q]
variable (f : G →* Q) (x y : G) (cm : Commute (f x) (f y))

def noShort (X Y : Q) : Prop :=
  ∀ a b : ℤ, a.natAbs≤3 → b.natAbs≤3 → X^a*Y^b=1 → a=0 ∧ b=0

include cm in
theorem grid_of_noShort (nh : noShort (f x) (f y)) :
    Function.Injective (fun t : Fin 16 => f (rep0 x y t)) := by
  intro i j e
  let a : ℤ := (↑(i.val/4 : ℕ) : ℤ)
  let b : ℤ := (↑(i.val%4 : ℕ) : ℤ)
  let c : ℤ := (↑(j.val/4 : ℕ) : ℤ)
  let d : ℤ := (↑(j.val%4 : ℕ) : ℤ)
  have eq : HaarAbelCore.image (f y) (f x) (b,a) =
      HaarAbelCore.image (f y) (f x) (d,c) := by
    simp only [HaarAbelCore.image,a,b,c,d,zpow_natCast]
    simpa only [rep0,map_mul,map_pow] using e
  have D := HaarAbelCore.diffR (f y) (f x) cm.symm (b,a) (d,c) eq
  have R : (f x)^(a-c)*(f y)^(b-d) = 1 := D
  have a3 : (a-c).natAbs≤3 := by
    have hi := i.isLt
    have hj := j.isLt
    dsimp [a,c]
    omega
  have b3 : (b-d).natAbs≤3 := by
    dsimp [b,d]
    omega
  obtain ⟨e0,e1⟩ := nh _ _ a3 b3 R
  apply Fin.ext
  have ia : i.val/4=j.val/4 := by dsimp [a,c] at e0; omega
  have ib : i.val%4=j.val%4 := by dsimp [b,d] at e1; omega
  omega

end HaarHoneyHaar
