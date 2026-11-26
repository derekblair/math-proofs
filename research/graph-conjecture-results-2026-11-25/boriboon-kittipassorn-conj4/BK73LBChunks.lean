import BK73LBCore
import BK73Sound1
namespace BK73

theorem eTTTT : allL lbp 9 13 [true, true, true, true] = true := by decide +kernel
theorem eTTTF : allL lbp 9 12 [false, true, true, true] = true := by decide +kernel
theorem eTTFT : allL lbp 9 12 [true, false, true, true] = true := by decide +kernel
theorem eTTFF : allL lbp 9 11 [false, false, true, true] = true := by decide +kernel
theorem eTFTT : allL lbp 9 12 [true, true, false, true] = true := by decide +kernel
theorem eTFTF : allL lbp 9 11 [false, true, false, true] = true := by decide +kernel
theorem eTFFT : allL lbp 9 11 [true, false, false, true] = true := by decide +kernel
theorem eTFFF : allL lbp 9 10 [false, false, false, true] = true := by decide +kernel
theorem eFTTT : allL lbp 9 12 [true, true, true, false] = true := by decide +kernel
theorem eFTTF : allL lbp 9 11 [false, true, true, false] = true := by decide +kernel
theorem eFTFT : allL lbp 9 11 [true, false, true, false] = true := by decide +kernel
theorem eFTFF : allL lbp 9 10 [false, false, true, false] = true := by decide +kernel
theorem eFFTT : allL lbp 9 11 [true, true, false, false] = true := by decide +kernel
theorem eFFTF : allL lbp 9 10 [false, true, false, false] = true := by decide +kernel
theorem eFFFT : allL lbp 9 10 [true, false, false, false] = true := by decide +kernel
theorem eFFFF : allL lbp 9 9 [false, false, false, false] = true := by decide +kernel

theorem lbS (p : List Bool → Bool) (n z : Nat) (acc : List Bool)
    (h1 : allL p n (z+1) (true :: acc) = true) (h2 : allL p n z (false :: acc) = true) :
    allL p (n+1) (z+1) acc = true :=
  allL_split p n (z+1) acc h1 (fun _ hz => by obtain rfl := Nat.succ.inj hz; exact h2)

/-- all 2^13 orientations of FCZnw fail diameter ≤ 3 (kernel-checked) -/
theorem lb_top : allL lbp 13 13 [] = true :=
  (lbS lbp 12 12 []
  (lbS lbp 11 12 [true]
   (lbS lbp 10 12 [true, true]
    (lbS lbp 9 12 [true, true, true]
     eTTTT
     eTTTF)
    (lbS lbp 9 11 [false, true, true]
     eTTFT
     eTTFF))
   (lbS lbp 10 11 [false, true]
    (lbS lbp 9 11 [true, false, true]
     eTFTT
     eTFTF)
    (lbS lbp 9 10 [false, false, true]
     eTFFT
     eTFFF)))
  (lbS lbp 11 11 [false]
   (lbS lbp 10 11 [true, false]
    (lbS lbp 9 11 [true, true, false]
     eFTTT
     eFTTF)
    (lbS lbp 9 10 [false, true, false]
     eFTFT
     eFTFF))
   (lbS lbp 10 10 [false, false]
    (lbS lbp 9 10 [true, false, false]
     eFFTT
     eFFTF)
    (lbS lbp 9 9 [false, false, false]
     eFFFT
     eFFFF))))

end BK73
