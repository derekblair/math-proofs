import BK73Sound1
import BK73Core4
import BK73C4_00
import BK73C4_01
import BK73C4_02
import BK73C4_03
import BK73C4_04
import BK73C4_05
import BK73C4_06
import BK73C4_07
import BK73C4_08
import BK73C4_09
import BK73C4_10
import BK73C4_11
import BK73C4_12
import BK73C4_13
import BK73C4_14
import BK73C4_15
import BK73C4_16
import BK73C4_17
import BK73C4_18
import BK73C4_19
import BK73C4_20
import BK73C4_21
import BK73C4_22
import BK73C4_23
import BK73C4_24
import BK73C4_25
import BK73C4_26
import BK73C4_27
import BK73C4_28
import BK73C4_29
import BK73C4_30
import BK73C4_31
import BK73C4_32
import BK73C4_33
import BK73C4_34
import BK73C4_35
import BK73C4_36
import BK73C4_37
import BK73C4_38
import BK73C4_39
import BK73C4_40
import BK73C4_41
import BK73C4_42
import BK73C4_43
import BK73C4_44
import BK73C4_45
import BK73C4_46
import BK73C4_47
import BK73C4_48
import BK73C4_49
import BK73C4_50
import BK73C4_51
import BK73C4_52
import BK73C4_53
import BK73C4_54
import BK73C4_55
import BK73C4_56
import BK73C4_57
import BK73C4_58
import BK73C4_59
import BK73C4_60
import BK73C4_61
import BK73C4_62
import BK73C4_63
namespace BK73

theorem s4S (p : List Bool → Bool) (n z : Nat) (acc : List Bool)
    (h1 : allL p n (z+1) (true :: acc) = true) (h2 : allL p n z (false :: acc) = true) :
    allL p (n+1) (z+1) acc = true :=
  allL_split p n (z+1) acc h1 (fun _ hz => by obtain rfl := Nat.succ.inj hz; exact h2)

theorem s40 (p : List Bool → Bool) (n : Nat) (acc : List Bool)
    (h1 : allL p n 0 (true :: acc) = true) : allL p (n+1) 0 acc = true :=
  allL_split p n 0 acc h1 (fun _ hz => nomatch hz)

/-- all 1,048,576 edge sets with ≥ 11 edges on 7 vertices pass `chk4`
(2,047 depth-11 subtrees kernel-checked in C4_00–C4_63) -/
theorem allL4_top : allL chk4 21 10 [] = true :=
  (s4S chk4 20 9 []
  (s4S chk4 19 9 [true]
   (s4S chk4 18 9 [true, true]
    (s4S chk4 17 9 [true, true, true]
     (s4S chk4 16 9 [true, true, true, true]
      (s4S chk4 15 9 [true, true, true, true, true]
       (s4S chk4 14 9 [true, true, true, true, true, true]
        (s4S chk4 13 9 [true, true, true, true, true, true, true]
         (s4S chk4 12 9 [true, true, true, true, true, true, true, true]
          (s4S chk4 11 9 [true, true, true, true, true, true, true, true, true]
           (s4S chk4 10 9 [true, true, true, true, true, true, true, true, true, true]
            dTTTTTTTTTTT
            dTTTTTTTTTTF)
           (s4S chk4 10 8 [false, true, true, true, true, true, true, true, true, true]
            dTTTTTTTTTFT
            dTTTTTTTTTFF))
          (s4S chk4 11 8 [false, true, true, true, true, true, true, true, true]
           (s4S chk4 10 8 [true, false, true, true, true, true, true, true, true, true]
            dTTTTTTTTFTT
            dTTTTTTTTFTF)
           (s4S chk4 10 7 [false, false, true, true, true, true, true, true, true, true]
            dTTTTTTTTFFT
            dTTTTTTTTFFF)))
         (s4S chk4 12 8 [false, true, true, true, true, true, true, true]
          (s4S chk4 11 8 [true, false, true, true, true, true, true, true, true]
           (s4S chk4 10 8 [true, true, false, true, true, true, true, true, true, true]
            dTTTTTTTFTTT
            dTTTTTTTFTTF)
           (s4S chk4 10 7 [false, true, false, true, true, true, true, true, true, true]
            dTTTTTTTFTFT
            dTTTTTTTFTFF))
          (s4S chk4 11 7 [false, false, true, true, true, true, true, true, true]
           (s4S chk4 10 7 [true, false, false, true, true, true, true, true, true, true]
            dTTTTTTTFFTT
            dTTTTTTTFFTF)
           (s4S chk4 10 6 [false, false, false, true, true, true, true, true, true, true]
            dTTTTTTTFFFT
            dTTTTTTTFFFF))))
        (s4S chk4 13 8 [false, true, true, true, true, true, true]
         (s4S chk4 12 8 [true, false, true, true, true, true, true, true]
          (s4S chk4 11 8 [true, true, false, true, true, true, true, true, true]
           (s4S chk4 10 8 [true, true, true, false, true, true, true, true, true, true]
            dTTTTTTFTTTT
            dTTTTTTFTTTF)
           (s4S chk4 10 7 [false, true, true, false, true, true, true, true, true, true]
            dTTTTTTFTTFT
            dTTTTTTFTTFF))
          (s4S chk4 11 7 [false, true, false, true, true, true, true, true, true]
           (s4S chk4 10 7 [true, false, true, false, true, true, true, true, true, true]
            dTTTTTTFTFTT
            dTTTTTTFTFTF)
           (s4S chk4 10 6 [false, false, true, false, true, true, true, true, true, true]
            dTTTTTTFTFFT
            dTTTTTTFTFFF)))
         (s4S chk4 12 7 [false, false, true, true, true, true, true, true]
          (s4S chk4 11 7 [true, false, false, true, true, true, true, true, true]
           (s4S chk4 10 7 [true, true, false, false, true, true, true, true, true, true]
            dTTTTTTFFTTT
            dTTTTTTFFTTF)
           (s4S chk4 10 6 [false, true, false, false, true, true, true, true, true, true]
            dTTTTTTFFTFT
            dTTTTTTFFTFF))
          (s4S chk4 11 6 [false, false, false, true, true, true, true, true, true]
           (s4S chk4 10 6 [true, false, false, false, true, true, true, true, true, true]
            dTTTTTTFFFTT
            dTTTTTTFFFTF)
           (s4S chk4 10 5 [false, false, false, false, true, true, true, true, true, true]
            dTTTTTTFFFFT
            dTTTTTTFFFFF)))))
       (s4S chk4 14 8 [false, true, true, true, true, true]
        (s4S chk4 13 8 [true, false, true, true, true, true, true]
         (s4S chk4 12 8 [true, true, false, true, true, true, true, true]
          (s4S chk4 11 8 [true, true, true, false, true, true, true, true, true]
           (s4S chk4 10 8 [true, true, true, true, false, true, true, true, true, true]
            dTTTTTFTTTTT
            dTTTTTFTTTTF)
           (s4S chk4 10 7 [false, true, true, true, false, true, true, true, true, true]
            dTTTTTFTTTFT
            dTTTTTFTTTFF))
          (s4S chk4 11 7 [false, true, true, false, true, true, true, true, true]
           (s4S chk4 10 7 [true, false, true, true, false, true, true, true, true, true]
            dTTTTTFTTFTT
            dTTTTTFTTFTF)
           (s4S chk4 10 6 [false, false, true, true, false, true, true, true, true, true]
            dTTTTTFTTFFT
            dTTTTTFTTFFF)))
         (s4S chk4 12 7 [false, true, false, true, true, true, true, true]
          (s4S chk4 11 7 [true, false, true, false, true, true, true, true, true]
           (s4S chk4 10 7 [true, true, false, true, false, true, true, true, true, true]
            dTTTTTFTFTTT
            dTTTTTFTFTTF)
           (s4S chk4 10 6 [false, true, false, true, false, true, true, true, true, true]
            dTTTTTFTFTFT
            dTTTTTFTFTFF))
          (s4S chk4 11 6 [false, false, true, false, true, true, true, true, true]
           (s4S chk4 10 6 [true, false, false, true, false, true, true, true, true, true]
            dTTTTTFTFFTT
            dTTTTTFTFFTF)
           (s4S chk4 10 5 [false, false, false, true, false, true, true, true, true, true]
            dTTTTTFTFFFT
            dTTTTTFTFFFF))))
        (s4S chk4 13 7 [false, false, true, true, true, true, true]
         (s4S chk4 12 7 [true, false, false, true, true, true, true, true]
          (s4S chk4 11 7 [true, true, false, false, true, true, true, true, true]
           (s4S chk4 10 7 [true, true, true, false, false, true, true, true, true, true]
            dTTTTTFFTTTT
            dTTTTTFFTTTF)
           (s4S chk4 10 6 [false, true, true, false, false, true, true, true, true, true]
            dTTTTTFFTTFT
            dTTTTTFFTTFF))
          (s4S chk4 11 6 [false, true, false, false, true, true, true, true, true]
           (s4S chk4 10 6 [true, false, true, false, false, true, true, true, true, true]
            dTTTTTFFTFTT
            dTTTTTFFTFTF)
           (s4S chk4 10 5 [false, false, true, false, false, true, true, true, true, true]
            dTTTTTFFTFFT
            dTTTTTFFTFFF)))
         (s4S chk4 12 6 [false, false, false, true, true, true, true, true]
          (s4S chk4 11 6 [true, false, false, false, true, true, true, true, true]
           (s4S chk4 10 6 [true, true, false, false, false, true, true, true, true, true]
            dTTTTTFFFTTT
            dTTTTTFFFTTF)
           (s4S chk4 10 5 [false, true, false, false, false, true, true, true, true, true]
            dTTTTTFFFTFT
            dTTTTTFFFTFF))
          (s4S chk4 11 5 [false, false, false, false, true, true, true, true, true]
           (s4S chk4 10 5 [true, false, false, false, false, true, true, true, true, true]
            dTTTTTFFFFTT
            dTTTTTFFFFTF)
           (s4S chk4 10 4 [false, false, false, false, false, true, true, true, true, true]
            dTTTTTFFFFFT
            dTTTTTFFFFFF))))))
      (s4S chk4 15 8 [false, true, true, true, true]
       (s4S chk4 14 8 [true, false, true, true, true, true]
        (s4S chk4 13 8 [true, true, false, true, true, true, true]
         (s4S chk4 12 8 [true, true, true, false, true, true, true, true]
          (s4S chk4 11 8 [true, true, true, true, false, true, true, true, true]
           (s4S chk4 10 8 [true, true, true, true, true, false, true, true, true, true]
            dTTTTFTTTTTT
            dTTTTFTTTTTF)
           (s4S chk4 10 7 [false, true, true, true, true, false, true, true, true, true]
            dTTTTFTTTTFT
            dTTTTFTTTTFF))
          (s4S chk4 11 7 [false, true, true, true, false, true, true, true, true]
           (s4S chk4 10 7 [true, false, true, true, true, false, true, true, true, true]
            dTTTTFTTTFTT
            dTTTTFTTTFTF)
           (s4S chk4 10 6 [false, false, true, true, true, false, true, true, true, true]
            dTTTTFTTTFFT
            dTTTTFTTTFFF)))
         (s4S chk4 12 7 [false, true, true, false, true, true, true, true]
          (s4S chk4 11 7 [true, false, true, true, false, true, true, true, true]
           (s4S chk4 10 7 [true, true, false, true, true, false, true, true, true, true]
            dTTTTFTTFTTT
            dTTTTFTTFTTF)
           (s4S chk4 10 6 [false, true, false, true, true, false, true, true, true, true]
            dTTTTFTTFTFT
            dTTTTFTTFTFF))
          (s4S chk4 11 6 [false, false, true, true, false, true, true, true, true]
           (s4S chk4 10 6 [true, false, false, true, true, false, true, true, true, true]
            dTTTTFTTFFTT
            dTTTTFTTFFTF)
           (s4S chk4 10 5 [false, false, false, true, true, false, true, true, true, true]
            dTTTTFTTFFFT
            dTTTTFTTFFFF))))
        (s4S chk4 13 7 [false, true, false, true, true, true, true]
         (s4S chk4 12 7 [true, false, true, false, true, true, true, true]
          (s4S chk4 11 7 [true, true, false, true, false, true, true, true, true]
           (s4S chk4 10 7 [true, true, true, false, true, false, true, true, true, true]
            dTTTTFTFTTTT
            dTTTTFTFTTTF)
           (s4S chk4 10 6 [false, true, true, false, true, false, true, true, true, true]
            dTTTTFTFTTFT
            dTTTTFTFTTFF))
          (s4S chk4 11 6 [false, true, false, true, false, true, true, true, true]
           (s4S chk4 10 6 [true, false, true, false, true, false, true, true, true, true]
            dTTTTFTFTFTT
            dTTTTFTFTFTF)
           (s4S chk4 10 5 [false, false, true, false, true, false, true, true, true, true]
            dTTTTFTFTFFT
            dTTTTFTFTFFF)))
         (s4S chk4 12 6 [false, false, true, false, true, true, true, true]
          (s4S chk4 11 6 [true, false, false, true, false, true, true, true, true]
           (s4S chk4 10 6 [true, true, false, false, true, false, true, true, true, true]
            dTTTTFTFFTTT
            dTTTTFTFFTTF)
           (s4S chk4 10 5 [false, true, false, false, true, false, true, true, true, true]
            dTTTTFTFFTFT
            dTTTTFTFFTFF))
          (s4S chk4 11 5 [false, false, false, true, false, true, true, true, true]
           (s4S chk4 10 5 [true, false, false, false, true, false, true, true, true, true]
            dTTTTFTFFFTT
            dTTTTFTFFFTF)
           (s4S chk4 10 4 [false, false, false, false, true, false, true, true, true, true]
            dTTTTFTFFFFT
            dTTTTFTFFFFF)))))
       (s4S chk4 14 7 [false, false, true, true, true, true]
        (s4S chk4 13 7 [true, false, false, true, true, true, true]
         (s4S chk4 12 7 [true, true, false, false, true, true, true, true]
          (s4S chk4 11 7 [true, true, true, false, false, true, true, true, true]
           (s4S chk4 10 7 [true, true, true, true, false, false, true, true, true, true]
            dTTTTFFTTTTT
            dTTTTFFTTTTF)
           (s4S chk4 10 6 [false, true, true, true, false, false, true, true, true, true]
            dTTTTFFTTTFT
            dTTTTFFTTTFF))
          (s4S chk4 11 6 [false, true, true, false, false, true, true, true, true]
           (s4S chk4 10 6 [true, false, true, true, false, false, true, true, true, true]
            dTTTTFFTTFTT
            dTTTTFFTTFTF)
           (s4S chk4 10 5 [false, false, true, true, false, false, true, true, true, true]
            dTTTTFFTTFFT
            dTTTTFFTTFFF)))
         (s4S chk4 12 6 [false, true, false, false, true, true, true, true]
          (s4S chk4 11 6 [true, false, true, false, false, true, true, true, true]
           (s4S chk4 10 6 [true, true, false, true, false, false, true, true, true, true]
            dTTTTFFTFTTT
            dTTTTFFTFTTF)
           (s4S chk4 10 5 [false, true, false, true, false, false, true, true, true, true]
            dTTTTFFTFTFT
            dTTTTFFTFTFF))
          (s4S chk4 11 5 [false, false, true, false, false, true, true, true, true]
           (s4S chk4 10 5 [true, false, false, true, false, false, true, true, true, true]
            dTTTTFFTFFTT
            dTTTTFFTFFTF)
           (s4S chk4 10 4 [false, false, false, true, false, false, true, true, true, true]
            dTTTTFFTFFFT
            dTTTTFFTFFFF))))
        (s4S chk4 13 6 [false, false, false, true, true, true, true]
         (s4S chk4 12 6 [true, false, false, false, true, true, true, true]
          (s4S chk4 11 6 [true, true, false, false, false, true, true, true, true]
           (s4S chk4 10 6 [true, true, true, false, false, false, true, true, true, true]
            dTTTTFFFTTTT
            dTTTTFFFTTTF)
           (s4S chk4 10 5 [false, true, true, false, false, false, true, true, true, true]
            dTTTTFFFTTFT
            dTTTTFFFTTFF))
          (s4S chk4 11 5 [false, true, false, false, false, true, true, true, true]
           (s4S chk4 10 5 [true, false, true, false, false, false, true, true, true, true]
            dTTTTFFFTFTT
            dTTTTFFFTFTF)
           (s4S chk4 10 4 [false, false, true, false, false, false, true, true, true, true]
            dTTTTFFFTFFT
            dTTTTFFFTFFF)))
         (s4S chk4 12 5 [false, false, false, false, true, true, true, true]
          (s4S chk4 11 5 [true, false, false, false, false, true, true, true, true]
           (s4S chk4 10 5 [true, true, false, false, false, false, true, true, true, true]
            dTTTTFFFFTTT
            dTTTTFFFFTTF)
           (s4S chk4 10 4 [false, true, false, false, false, false, true, true, true, true]
            dTTTTFFFFTFT
            dTTTTFFFFTFF))
          (s4S chk4 11 4 [false, false, false, false, false, true, true, true, true]
           (s4S chk4 10 4 [true, false, false, false, false, false, true, true, true, true]
            dTTTTFFFFFTT
            dTTTTFFFFFTF)
           (s4S chk4 10 3 [false, false, false, false, false, false, true, true, true, true]
            dTTTTFFFFFFT
            dTTTTFFFFFFF)))))))
     (s4S chk4 16 8 [false, true, true, true]
      (s4S chk4 15 8 [true, false, true, true, true]
       (s4S chk4 14 8 [true, true, false, true, true, true]
        (s4S chk4 13 8 [true, true, true, false, true, true, true]
         (s4S chk4 12 8 [true, true, true, true, false, true, true, true]
          (s4S chk4 11 8 [true, true, true, true, true, false, true, true, true]
           (s4S chk4 10 8 [true, true, true, true, true, true, false, true, true, true]
            dTTTFTTTTTTT
            dTTTFTTTTTTF)
           (s4S chk4 10 7 [false, true, true, true, true, true, false, true, true, true]
            dTTTFTTTTTFT
            dTTTFTTTTTFF))
          (s4S chk4 11 7 [false, true, true, true, true, false, true, true, true]
           (s4S chk4 10 7 [true, false, true, true, true, true, false, true, true, true]
            dTTTFTTTTFTT
            dTTTFTTTTFTF)
           (s4S chk4 10 6 [false, false, true, true, true, true, false, true, true, true]
            dTTTFTTTTFFT
            dTTTFTTTTFFF)))
         (s4S chk4 12 7 [false, true, true, true, false, true, true, true]
          (s4S chk4 11 7 [true, false, true, true, true, false, true, true, true]
           (s4S chk4 10 7 [true, true, false, true, true, true, false, true, true, true]
            dTTTFTTTFTTT
            dTTTFTTTFTTF)
           (s4S chk4 10 6 [false, true, false, true, true, true, false, true, true, true]
            dTTTFTTTFTFT
            dTTTFTTTFTFF))
          (s4S chk4 11 6 [false, false, true, true, true, false, true, true, true]
           (s4S chk4 10 6 [true, false, false, true, true, true, false, true, true, true]
            dTTTFTTTFFTT
            dTTTFTTTFFTF)
           (s4S chk4 10 5 [false, false, false, true, true, true, false, true, true, true]
            dTTTFTTTFFFT
            dTTTFTTTFFFF))))
        (s4S chk4 13 7 [false, true, true, false, true, true, true]
         (s4S chk4 12 7 [true, false, true, true, false, true, true, true]
          (s4S chk4 11 7 [true, true, false, true, true, false, true, true, true]
           (s4S chk4 10 7 [true, true, true, false, true, true, false, true, true, true]
            dTTTFTTFTTTT
            dTTTFTTFTTTF)
           (s4S chk4 10 6 [false, true, true, false, true, true, false, true, true, true]
            dTTTFTTFTTFT
            dTTTFTTFTTFF))
          (s4S chk4 11 6 [false, true, false, true, true, false, true, true, true]
           (s4S chk4 10 6 [true, false, true, false, true, true, false, true, true, true]
            dTTTFTTFTFTT
            dTTTFTTFTFTF)
           (s4S chk4 10 5 [false, false, true, false, true, true, false, true, true, true]
            dTTTFTTFTFFT
            dTTTFTTFTFFF)))
         (s4S chk4 12 6 [false, false, true, true, false, true, true, true]
          (s4S chk4 11 6 [true, false, false, true, true, false, true, true, true]
           (s4S chk4 10 6 [true, true, false, false, true, true, false, true, true, true]
            dTTTFTTFFTTT
            dTTTFTTFFTTF)
           (s4S chk4 10 5 [false, true, false, false, true, true, false, true, true, true]
            dTTTFTTFFTFT
            dTTTFTTFFTFF))
          (s4S chk4 11 5 [false, false, false, true, true, false, true, true, true]
           (s4S chk4 10 5 [true, false, false, false, true, true, false, true, true, true]
            dTTTFTTFFFTT
            dTTTFTTFFFTF)
           (s4S chk4 10 4 [false, false, false, false, true, true, false, true, true, true]
            dTTTFTTFFFFT
            dTTTFTTFFFFF)))))
       (s4S chk4 14 7 [false, true, false, true, true, true]
        (s4S chk4 13 7 [true, false, true, false, true, true, true]
         (s4S chk4 12 7 [true, true, false, true, false, true, true, true]
          (s4S chk4 11 7 [true, true, true, false, true, false, true, true, true]
           (s4S chk4 10 7 [true, true, true, true, false, true, false, true, true, true]
            dTTTFTFTTTTT
            dTTTFTFTTTTF)
           (s4S chk4 10 6 [false, true, true, true, false, true, false, true, true, true]
            dTTTFTFTTTFT
            dTTTFTFTTTFF))
          (s4S chk4 11 6 [false, true, true, false, true, false, true, true, true]
           (s4S chk4 10 6 [true, false, true, true, false, true, false, true, true, true]
            dTTTFTFTTFTT
            dTTTFTFTTFTF)
           (s4S chk4 10 5 [false, false, true, true, false, true, false, true, true, true]
            dTTTFTFTTFFT
            dTTTFTFTTFFF)))
         (s4S chk4 12 6 [false, true, false, true, false, true, true, true]
          (s4S chk4 11 6 [true, false, true, false, true, false, true, true, true]
           (s4S chk4 10 6 [true, true, false, true, false, true, false, true, true, true]
            dTTTFTFTFTTT
            dTTTFTFTFTTF)
           (s4S chk4 10 5 [false, true, false, true, false, true, false, true, true, true]
            dTTTFTFTFTFT
            dTTTFTFTFTFF))
          (s4S chk4 11 5 [false, false, true, false, true, false, true, true, true]
           (s4S chk4 10 5 [true, false, false, true, false, true, false, true, true, true]
            dTTTFTFTFFTT
            dTTTFTFTFFTF)
           (s4S chk4 10 4 [false, false, false, true, false, true, false, true, true, true]
            dTTTFTFTFFFT
            dTTTFTFTFFFF))))
        (s4S chk4 13 6 [false, false, true, false, true, true, true]
         (s4S chk4 12 6 [true, false, false, true, false, true, true, true]
          (s4S chk4 11 6 [true, true, false, false, true, false, true, true, true]
           (s4S chk4 10 6 [true, true, true, false, false, true, false, true, true, true]
            dTTTFTFFTTTT
            dTTTFTFFTTTF)
           (s4S chk4 10 5 [false, true, true, false, false, true, false, true, true, true]
            dTTTFTFFTTFT
            dTTTFTFFTTFF))
          (s4S chk4 11 5 [false, true, false, false, true, false, true, true, true]
           (s4S chk4 10 5 [true, false, true, false, false, true, false, true, true, true]
            dTTTFTFFTFTT
            dTTTFTFFTFTF)
           (s4S chk4 10 4 [false, false, true, false, false, true, false, true, true, true]
            dTTTFTFFTFFT
            dTTTFTFFTFFF)))
         (s4S chk4 12 5 [false, false, false, true, false, true, true, true]
          (s4S chk4 11 5 [true, false, false, false, true, false, true, true, true]
           (s4S chk4 10 5 [true, true, false, false, false, true, false, true, true, true]
            dTTTFTFFFTTT
            dTTTFTFFFTTF)
           (s4S chk4 10 4 [false, true, false, false, false, true, false, true, true, true]
            dTTTFTFFFTFT
            dTTTFTFFFTFF))
          (s4S chk4 11 4 [false, false, false, false, true, false, true, true, true]
           (s4S chk4 10 4 [true, false, false, false, false, true, false, true, true, true]
            dTTTFTFFFFTT
            dTTTFTFFFFTF)
           (s4S chk4 10 3 [false, false, false, false, false, true, false, true, true, true]
            dTTTFTFFFFFT
            dTTTFTFFFFFF))))))
      (s4S chk4 15 7 [false, false, true, true, true]
       (s4S chk4 14 7 [true, false, false, true, true, true]
        (s4S chk4 13 7 [true, true, false, false, true, true, true]
         (s4S chk4 12 7 [true, true, true, false, false, true, true, true]
          (s4S chk4 11 7 [true, true, true, true, false, false, true, true, true]
           (s4S chk4 10 7 [true, true, true, true, true, false, false, true, true, true]
            dTTTFFTTTTTT
            dTTTFFTTTTTF)
           (s4S chk4 10 6 [false, true, true, true, true, false, false, true, true, true]
            dTTTFFTTTTFT
            dTTTFFTTTTFF))
          (s4S chk4 11 6 [false, true, true, true, false, false, true, true, true]
           (s4S chk4 10 6 [true, false, true, true, true, false, false, true, true, true]
            dTTTFFTTTFTT
            dTTTFFTTTFTF)
           (s4S chk4 10 5 [false, false, true, true, true, false, false, true, true, true]
            dTTTFFTTTFFT
            dTTTFFTTTFFF)))
         (s4S chk4 12 6 [false, true, true, false, false, true, true, true]
          (s4S chk4 11 6 [true, false, true, true, false, false, true, true, true]
           (s4S chk4 10 6 [true, true, false, true, true, false, false, true, true, true]
            dTTTFFTTFTTT
            dTTTFFTTFTTF)
           (s4S chk4 10 5 [false, true, false, true, true, false, false, true, true, true]
            dTTTFFTTFTFT
            dTTTFFTTFTFF))
          (s4S chk4 11 5 [false, false, true, true, false, false, true, true, true]
           (s4S chk4 10 5 [true, false, false, true, true, false, false, true, true, true]
            dTTTFFTTFFTT
            dTTTFFTTFFTF)
           (s4S chk4 10 4 [false, false, false, true, true, false, false, true, true, true]
            dTTTFFTTFFFT
            dTTTFFTTFFFF))))
        (s4S chk4 13 6 [false, true, false, false, true, true, true]
         (s4S chk4 12 6 [true, false, true, false, false, true, true, true]
          (s4S chk4 11 6 [true, true, false, true, false, false, true, true, true]
           (s4S chk4 10 6 [true, true, true, false, true, false, false, true, true, true]
            dTTTFFTFTTTT
            dTTTFFTFTTTF)
           (s4S chk4 10 5 [false, true, true, false, true, false, false, true, true, true]
            dTTTFFTFTTFT
            dTTTFFTFTTFF))
          (s4S chk4 11 5 [false, true, false, true, false, false, true, true, true]
           (s4S chk4 10 5 [true, false, true, false, true, false, false, true, true, true]
            dTTTFFTFTFTT
            dTTTFFTFTFTF)
           (s4S chk4 10 4 [false, false, true, false, true, false, false, true, true, true]
            dTTTFFTFTFFT
            dTTTFFTFTFFF)))
         (s4S chk4 12 5 [false, false, true, false, false, true, true, true]
          (s4S chk4 11 5 [true, false, false, true, false, false, true, true, true]
           (s4S chk4 10 5 [true, true, false, false, true, false, false, true, true, true]
            dTTTFFTFFTTT
            dTTTFFTFFTTF)
           (s4S chk4 10 4 [false, true, false, false, true, false, false, true, true, true]
            dTTTFFTFFTFT
            dTTTFFTFFTFF))
          (s4S chk4 11 4 [false, false, false, true, false, false, true, true, true]
           (s4S chk4 10 4 [true, false, false, false, true, false, false, true, true, true]
            dTTTFFTFFFTT
            dTTTFFTFFFTF)
           (s4S chk4 10 3 [false, false, false, false, true, false, false, true, true, true]
            dTTTFFTFFFFT
            dTTTFFTFFFFF)))))
       (s4S chk4 14 6 [false, false, false, true, true, true]
        (s4S chk4 13 6 [true, false, false, false, true, true, true]
         (s4S chk4 12 6 [true, true, false, false, false, true, true, true]
          (s4S chk4 11 6 [true, true, true, false, false, false, true, true, true]
           (s4S chk4 10 6 [true, true, true, true, false, false, false, true, true, true]
            dTTTFFFTTTTT
            dTTTFFFTTTTF)
           (s4S chk4 10 5 [false, true, true, true, false, false, false, true, true, true]
            dTTTFFFTTTFT
            dTTTFFFTTTFF))
          (s4S chk4 11 5 [false, true, true, false, false, false, true, true, true]
           (s4S chk4 10 5 [true, false, true, true, false, false, false, true, true, true]
            dTTTFFFTTFTT
            dTTTFFFTTFTF)
           (s4S chk4 10 4 [false, false, true, true, false, false, false, true, true, true]
            dTTTFFFTTFFT
            dTTTFFFTTFFF)))
         (s4S chk4 12 5 [false, true, false, false, false, true, true, true]
          (s4S chk4 11 5 [true, false, true, false, false, false, true, true, true]
           (s4S chk4 10 5 [true, true, false, true, false, false, false, true, true, true]
            dTTTFFFTFTTT
            dTTTFFFTFTTF)
           (s4S chk4 10 4 [false, true, false, true, false, false, false, true, true, true]
            dTTTFFFTFTFT
            dTTTFFFTFTFF))
          (s4S chk4 11 4 [false, false, true, false, false, false, true, true, true]
           (s4S chk4 10 4 [true, false, false, true, false, false, false, true, true, true]
            dTTTFFFTFFTT
            dTTTFFFTFFTF)
           (s4S chk4 10 3 [false, false, false, true, false, false, false, true, true, true]
            dTTTFFFTFFFT
            dTTTFFFTFFFF))))
        (s4S chk4 13 5 [false, false, false, false, true, true, true]
         (s4S chk4 12 5 [true, false, false, false, false, true, true, true]
          (s4S chk4 11 5 [true, true, false, false, false, false, true, true, true]
           (s4S chk4 10 5 [true, true, true, false, false, false, false, true, true, true]
            dTTTFFFFTTTT
            dTTTFFFFTTTF)
           (s4S chk4 10 4 [false, true, true, false, false, false, false, true, true, true]
            dTTTFFFFTTFT
            dTTTFFFFTTFF))
          (s4S chk4 11 4 [false, true, false, false, false, false, true, true, true]
           (s4S chk4 10 4 [true, false, true, false, false, false, false, true, true, true]
            dTTTFFFFTFTT
            dTTTFFFFTFTF)
           (s4S chk4 10 3 [false, false, true, false, false, false, false, true, true, true]
            dTTTFFFFTFFT
            dTTTFFFFTFFF)))
         (s4S chk4 12 4 [false, false, false, false, false, true, true, true]
          (s4S chk4 11 4 [true, false, false, false, false, false, true, true, true]
           (s4S chk4 10 4 [true, true, false, false, false, false, false, true, true, true]
            dTTTFFFFFTTT
            dTTTFFFFFTTF)
           (s4S chk4 10 3 [false, true, false, false, false, false, false, true, true, true]
            dTTTFFFFFTFT
            dTTTFFFFFTFF))
          (s4S chk4 11 3 [false, false, false, false, false, false, true, true, true]
           (s4S chk4 10 3 [true, false, false, false, false, false, false, true, true, true]
            dTTTFFFFFFTT
            dTTTFFFFFFTF)
           (s4S chk4 10 2 [false, false, false, false, false, false, false, true, true, true]
            dTTTFFFFFFFT
            dTTTFFFFFFFF))))))))
    (s4S chk4 17 8 [false, true, true]
     (s4S chk4 16 8 [true, false, true, true]
      (s4S chk4 15 8 [true, true, false, true, true]
       (s4S chk4 14 8 [true, true, true, false, true, true]
        (s4S chk4 13 8 [true, true, true, true, false, true, true]
         (s4S chk4 12 8 [true, true, true, true, true, false, true, true]
          (s4S chk4 11 8 [true, true, true, true, true, true, false, true, true]
           (s4S chk4 10 8 [true, true, true, true, true, true, true, false, true, true]
            dTTFTTTTTTTT
            dTTFTTTTTTTF)
           (s4S chk4 10 7 [false, true, true, true, true, true, true, false, true, true]
            dTTFTTTTTTFT
            dTTFTTTTTTFF))
          (s4S chk4 11 7 [false, true, true, true, true, true, false, true, true]
           (s4S chk4 10 7 [true, false, true, true, true, true, true, false, true, true]
            dTTFTTTTTFTT
            dTTFTTTTTFTF)
           (s4S chk4 10 6 [false, false, true, true, true, true, true, false, true, true]
            dTTFTTTTTFFT
            dTTFTTTTTFFF)))
         (s4S chk4 12 7 [false, true, true, true, true, false, true, true]
          (s4S chk4 11 7 [true, false, true, true, true, true, false, true, true]
           (s4S chk4 10 7 [true, true, false, true, true, true, true, false, true, true]
            dTTFTTTTFTTT
            dTTFTTTTFTTF)
           (s4S chk4 10 6 [false, true, false, true, true, true, true, false, true, true]
            dTTFTTTTFTFT
            dTTFTTTTFTFF))
          (s4S chk4 11 6 [false, false, true, true, true, true, false, true, true]
           (s4S chk4 10 6 [true, false, false, true, true, true, true, false, true, true]
            dTTFTTTTFFTT
            dTTFTTTTFFTF)
           (s4S chk4 10 5 [false, false, false, true, true, true, true, false, true, true]
            dTTFTTTTFFFT
            dTTFTTTTFFFF))))
        (s4S chk4 13 7 [false, true, true, true, false, true, true]
         (s4S chk4 12 7 [true, false, true, true, true, false, true, true]
          (s4S chk4 11 7 [true, true, false, true, true, true, false, true, true]
           (s4S chk4 10 7 [true, true, true, false, true, true, true, false, true, true]
            dTTFTTTFTTTT
            dTTFTTTFTTTF)
           (s4S chk4 10 6 [false, true, true, false, true, true, true, false, true, true]
            dTTFTTTFTTFT
            dTTFTTTFTTFF))
          (s4S chk4 11 6 [false, true, false, true, true, true, false, true, true]
           (s4S chk4 10 6 [true, false, true, false, true, true, true, false, true, true]
            dTTFTTTFTFTT
            dTTFTTTFTFTF)
           (s4S chk4 10 5 [false, false, true, false, true, true, true, false, true, true]
            dTTFTTTFTFFT
            dTTFTTTFTFFF)))
         (s4S chk4 12 6 [false, false, true, true, true, false, true, true]
          (s4S chk4 11 6 [true, false, false, true, true, true, false, true, true]
           (s4S chk4 10 6 [true, true, false, false, true, true, true, false, true, true]
            dTTFTTTFFTTT
            dTTFTTTFFTTF)
           (s4S chk4 10 5 [false, true, false, false, true, true, true, false, true, true]
            dTTFTTTFFTFT
            dTTFTTTFFTFF))
          (s4S chk4 11 5 [false, false, false, true, true, true, false, true, true]
           (s4S chk4 10 5 [true, false, false, false, true, true, true, false, true, true]
            dTTFTTTFFFTT
            dTTFTTTFFFTF)
           (s4S chk4 10 4 [false, false, false, false, true, true, true, false, true, true]
            dTTFTTTFFFFT
            dTTFTTTFFFFF)))))
       (s4S chk4 14 7 [false, true, true, false, true, true]
        (s4S chk4 13 7 [true, false, true, true, false, true, true]
         (s4S chk4 12 7 [true, true, false, true, true, false, true, true]
          (s4S chk4 11 7 [true, true, true, false, true, true, false, true, true]
           (s4S chk4 10 7 [true, true, true, true, false, true, true, false, true, true]
            dTTFTTFTTTTT
            dTTFTTFTTTTF)
           (s4S chk4 10 6 [false, true, true, true, false, true, true, false, true, true]
            dTTFTTFTTTFT
            dTTFTTFTTTFF))
          (s4S chk4 11 6 [false, true, true, false, true, true, false, true, true]
           (s4S chk4 10 6 [true, false, true, true, false, true, true, false, true, true]
            dTTFTTFTTFTT
            dTTFTTFTTFTF)
           (s4S chk4 10 5 [false, false, true, true, false, true, true, false, true, true]
            dTTFTTFTTFFT
            dTTFTTFTTFFF)))
         (s4S chk4 12 6 [false, true, false, true, true, false, true, true]
          (s4S chk4 11 6 [true, false, true, false, true, true, false, true, true]
           (s4S chk4 10 6 [true, true, false, true, false, true, true, false, true, true]
            dTTFTTFTFTTT
            dTTFTTFTFTTF)
           (s4S chk4 10 5 [false, true, false, true, false, true, true, false, true, true]
            dTTFTTFTFTFT
            dTTFTTFTFTFF))
          (s4S chk4 11 5 [false, false, true, false, true, true, false, true, true]
           (s4S chk4 10 5 [true, false, false, true, false, true, true, false, true, true]
            dTTFTTFTFFTT
            dTTFTTFTFFTF)
           (s4S chk4 10 4 [false, false, false, true, false, true, true, false, true, true]
            dTTFTTFTFFFT
            dTTFTTFTFFFF))))
        (s4S chk4 13 6 [false, false, true, true, false, true, true]
         (s4S chk4 12 6 [true, false, false, true, true, false, true, true]
          (s4S chk4 11 6 [true, true, false, false, true, true, false, true, true]
           (s4S chk4 10 6 [true, true, true, false, false, true, true, false, true, true]
            dTTFTTFFTTTT
            dTTFTTFFTTTF)
           (s4S chk4 10 5 [false, true, true, false, false, true, true, false, true, true]
            dTTFTTFFTTFT
            dTTFTTFFTTFF))
          (s4S chk4 11 5 [false, true, false, false, true, true, false, true, true]
           (s4S chk4 10 5 [true, false, true, false, false, true, true, false, true, true]
            dTTFTTFFTFTT
            dTTFTTFFTFTF)
           (s4S chk4 10 4 [false, false, true, false, false, true, true, false, true, true]
            dTTFTTFFTFFT
            dTTFTTFFTFFF)))
         (s4S chk4 12 5 [false, false, false, true, true, false, true, true]
          (s4S chk4 11 5 [true, false, false, false, true, true, false, true, true]
           (s4S chk4 10 5 [true, true, false, false, false, true, true, false, true, true]
            dTTFTTFFFTTT
            dTTFTTFFFTTF)
           (s4S chk4 10 4 [false, true, false, false, false, true, true, false, true, true]
            dTTFTTFFFTFT
            dTTFTTFFFTFF))
          (s4S chk4 11 4 [false, false, false, false, true, true, false, true, true]
           (s4S chk4 10 4 [true, false, false, false, false, true, true, false, true, true]
            dTTFTTFFFFTT
            dTTFTTFFFFTF)
           (s4S chk4 10 3 [false, false, false, false, false, true, true, false, true, true]
            dTTFTTFFFFFT
            dTTFTTFFFFFF))))))
      (s4S chk4 15 7 [false, true, false, true, true]
       (s4S chk4 14 7 [true, false, true, false, true, true]
        (s4S chk4 13 7 [true, true, false, true, false, true, true]
         (s4S chk4 12 7 [true, true, true, false, true, false, true, true]
          (s4S chk4 11 7 [true, true, true, true, false, true, false, true, true]
           (s4S chk4 10 7 [true, true, true, true, true, false, true, false, true, true]
            dTTFTFTTTTTT
            dTTFTFTTTTTF)
           (s4S chk4 10 6 [false, true, true, true, true, false, true, false, true, true]
            dTTFTFTTTTFT
            dTTFTFTTTTFF))
          (s4S chk4 11 6 [false, true, true, true, false, true, false, true, true]
           (s4S chk4 10 6 [true, false, true, true, true, false, true, false, true, true]
            dTTFTFTTTFTT
            dTTFTFTTTFTF)
           (s4S chk4 10 5 [false, false, true, true, true, false, true, false, true, true]
            dTTFTFTTTFFT
            dTTFTFTTTFFF)))
         (s4S chk4 12 6 [false, true, true, false, true, false, true, true]
          (s4S chk4 11 6 [true, false, true, true, false, true, false, true, true]
           (s4S chk4 10 6 [true, true, false, true, true, false, true, false, true, true]
            dTTFTFTTFTTT
            dTTFTFTTFTTF)
           (s4S chk4 10 5 [false, true, false, true, true, false, true, false, true, true]
            dTTFTFTTFTFT
            dTTFTFTTFTFF))
          (s4S chk4 11 5 [false, false, true, true, false, true, false, true, true]
           (s4S chk4 10 5 [true, false, false, true, true, false, true, false, true, true]
            dTTFTFTTFFTT
            dTTFTFTTFFTF)
           (s4S chk4 10 4 [false, false, false, true, true, false, true, false, true, true]
            dTTFTFTTFFFT
            dTTFTFTTFFFF))))
        (s4S chk4 13 6 [false, true, false, true, false, true, true]
         (s4S chk4 12 6 [true, false, true, false, true, false, true, true]
          (s4S chk4 11 6 [true, true, false, true, false, true, false, true, true]
           (s4S chk4 10 6 [true, true, true, false, true, false, true, false, true, true]
            dTTFTFTFTTTT
            dTTFTFTFTTTF)
           (s4S chk4 10 5 [false, true, true, false, true, false, true, false, true, true]
            dTTFTFTFTTFT
            dTTFTFTFTTFF))
          (s4S chk4 11 5 [false, true, false, true, false, true, false, true, true]
           (s4S chk4 10 5 [true, false, true, false, true, false, true, false, true, true]
            dTTFTFTFTFTT
            dTTFTFTFTFTF)
           (s4S chk4 10 4 [false, false, true, false, true, false, true, false, true, true]
            dTTFTFTFTFFT
            dTTFTFTFTFFF)))
         (s4S chk4 12 5 [false, false, true, false, true, false, true, true]
          (s4S chk4 11 5 [true, false, false, true, false, true, false, true, true]
           (s4S chk4 10 5 [true, true, false, false, true, false, true, false, true, true]
            dTTFTFTFFTTT
            dTTFTFTFFTTF)
           (s4S chk4 10 4 [false, true, false, false, true, false, true, false, true, true]
            dTTFTFTFFTFT
            dTTFTFTFFTFF))
          (s4S chk4 11 4 [false, false, false, true, false, true, false, true, true]
           (s4S chk4 10 4 [true, false, false, false, true, false, true, false, true, true]
            dTTFTFTFFFTT
            dTTFTFTFFFTF)
           (s4S chk4 10 3 [false, false, false, false, true, false, true, false, true, true]
            dTTFTFTFFFFT
            dTTFTFTFFFFF)))))
       (s4S chk4 14 6 [false, false, true, false, true, true]
        (s4S chk4 13 6 [true, false, false, true, false, true, true]
         (s4S chk4 12 6 [true, true, false, false, true, false, true, true]
          (s4S chk4 11 6 [true, true, true, false, false, true, false, true, true]
           (s4S chk4 10 6 [true, true, true, true, false, false, true, false, true, true]
            dTTFTFFTTTTT
            dTTFTFFTTTTF)
           (s4S chk4 10 5 [false, true, true, true, false, false, true, false, true, true]
            dTTFTFFTTTFT
            dTTFTFFTTTFF))
          (s4S chk4 11 5 [false, true, true, false, false, true, false, true, true]
           (s4S chk4 10 5 [true, false, true, true, false, false, true, false, true, true]
            dTTFTFFTTFTT
            dTTFTFFTTFTF)
           (s4S chk4 10 4 [false, false, true, true, false, false, true, false, true, true]
            dTTFTFFTTFFT
            dTTFTFFTTFFF)))
         (s4S chk4 12 5 [false, true, false, false, true, false, true, true]
          (s4S chk4 11 5 [true, false, true, false, false, true, false, true, true]
           (s4S chk4 10 5 [true, true, false, true, false, false, true, false, true, true]
            dTTFTFFTFTTT
            dTTFTFFTFTTF)
           (s4S chk4 10 4 [false, true, false, true, false, false, true, false, true, true]
            dTTFTFFTFTFT
            dTTFTFFTFTFF))
          (s4S chk4 11 4 [false, false, true, false, false, true, false, true, true]
           (s4S chk4 10 4 [true, false, false, true, false, false, true, false, true, true]
            dTTFTFFTFFTT
            dTTFTFFTFFTF)
           (s4S chk4 10 3 [false, false, false, true, false, false, true, false, true, true]
            dTTFTFFTFFFT
            dTTFTFFTFFFF))))
        (s4S chk4 13 5 [false, false, false, true, false, true, true]
         (s4S chk4 12 5 [true, false, false, false, true, false, true, true]
          (s4S chk4 11 5 [true, true, false, false, false, true, false, true, true]
           (s4S chk4 10 5 [true, true, true, false, false, false, true, false, true, true]
            dTTFTFFFTTTT
            dTTFTFFFTTTF)
           (s4S chk4 10 4 [false, true, true, false, false, false, true, false, true, true]
            dTTFTFFFTTFT
            dTTFTFFFTTFF))
          (s4S chk4 11 4 [false, true, false, false, false, true, false, true, true]
           (s4S chk4 10 4 [true, false, true, false, false, false, true, false, true, true]
            dTTFTFFFTFTT
            dTTFTFFFTFTF)
           (s4S chk4 10 3 [false, false, true, false, false, false, true, false, true, true]
            dTTFTFFFTFFT
            dTTFTFFFTFFF)))
         (s4S chk4 12 4 [false, false, false, false, true, false, true, true]
          (s4S chk4 11 4 [true, false, false, false, false, true, false, true, true]
           (s4S chk4 10 4 [true, true, false, false, false, false, true, false, true, true]
            dTTFTFFFFTTT
            dTTFTFFFFTTF)
           (s4S chk4 10 3 [false, true, false, false, false, false, true, false, true, true]
            dTTFTFFFFTFT
            dTTFTFFFFTFF))
          (s4S chk4 11 3 [false, false, false, false, false, true, false, true, true]
           (s4S chk4 10 3 [true, false, false, false, false, false, true, false, true, true]
            dTTFTFFFFFTT
            dTTFTFFFFFTF)
           (s4S chk4 10 2 [false, false, false, false, false, false, true, false, true, true]
            dTTFTFFFFFFT
            dTTFTFFFFFFF)))))))
     (s4S chk4 16 7 [false, false, true, true]
      (s4S chk4 15 7 [true, false, false, true, true]
       (s4S chk4 14 7 [true, true, false, false, true, true]
        (s4S chk4 13 7 [true, true, true, false, false, true, true]
         (s4S chk4 12 7 [true, true, true, true, false, false, true, true]
          (s4S chk4 11 7 [true, true, true, true, true, false, false, true, true]
           (s4S chk4 10 7 [true, true, true, true, true, true, false, false, true, true]
            dTTFFTTTTTTT
            dTTFFTTTTTTF)
           (s4S chk4 10 6 [false, true, true, true, true, true, false, false, true, true]
            dTTFFTTTTTFT
            dTTFFTTTTTFF))
          (s4S chk4 11 6 [false, true, true, true, true, false, false, true, true]
           (s4S chk4 10 6 [true, false, true, true, true, true, false, false, true, true]
            dTTFFTTTTFTT
            dTTFFTTTTFTF)
           (s4S chk4 10 5 [false, false, true, true, true, true, false, false, true, true]
            dTTFFTTTTFFT
            dTTFFTTTTFFF)))
         (s4S chk4 12 6 [false, true, true, true, false, false, true, true]
          (s4S chk4 11 6 [true, false, true, true, true, false, false, true, true]
           (s4S chk4 10 6 [true, true, false, true, true, true, false, false, true, true]
            dTTFFTTTFTTT
            dTTFFTTTFTTF)
           (s4S chk4 10 5 [false, true, false, true, true, true, false, false, true, true]
            dTTFFTTTFTFT
            dTTFFTTTFTFF))
          (s4S chk4 11 5 [false, false, true, true, true, false, false, true, true]
           (s4S chk4 10 5 [true, false, false, true, true, true, false, false, true, true]
            dTTFFTTTFFTT
            dTTFFTTTFFTF)
           (s4S chk4 10 4 [false, false, false, true, true, true, false, false, true, true]
            dTTFFTTTFFFT
            dTTFFTTTFFFF))))
        (s4S chk4 13 6 [false, true, true, false, false, true, true]
         (s4S chk4 12 6 [true, false, true, true, false, false, true, true]
          (s4S chk4 11 6 [true, true, false, true, true, false, false, true, true]
           (s4S chk4 10 6 [true, true, true, false, true, true, false, false, true, true]
            dTTFFTTFTTTT
            dTTFFTTFTTTF)
           (s4S chk4 10 5 [false, true, true, false, true, true, false, false, true, true]
            dTTFFTTFTTFT
            dTTFFTTFTTFF))
          (s4S chk4 11 5 [false, true, false, true, true, false, false, true, true]
           (s4S chk4 10 5 [true, false, true, false, true, true, false, false, true, true]
            dTTFFTTFTFTT
            dTTFFTTFTFTF)
           (s4S chk4 10 4 [false, false, true, false, true, true, false, false, true, true]
            dTTFFTTFTFFT
            dTTFFTTFTFFF)))
         (s4S chk4 12 5 [false, false, true, true, false, false, true, true]
          (s4S chk4 11 5 [true, false, false, true, true, false, false, true, true]
           (s4S chk4 10 5 [true, true, false, false, true, true, false, false, true, true]
            dTTFFTTFFTTT
            dTTFFTTFFTTF)
           (s4S chk4 10 4 [false, true, false, false, true, true, false, false, true, true]
            dTTFFTTFFTFT
            dTTFFTTFFTFF))
          (s4S chk4 11 4 [false, false, false, true, true, false, false, true, true]
           (s4S chk4 10 4 [true, false, false, false, true, true, false, false, true, true]
            dTTFFTTFFFTT
            dTTFFTTFFFTF)
           (s4S chk4 10 3 [false, false, false, false, true, true, false, false, true, true]
            dTTFFTTFFFFT
            dTTFFTTFFFFF)))))
       (s4S chk4 14 6 [false, true, false, false, true, true]
        (s4S chk4 13 6 [true, false, true, false, false, true, true]
         (s4S chk4 12 6 [true, true, false, true, false, false, true, true]
          (s4S chk4 11 6 [true, true, true, false, true, false, false, true, true]
           (s4S chk4 10 6 [true, true, true, true, false, true, false, false, true, true]
            dTTFFTFTTTTT
            dTTFFTFTTTTF)
           (s4S chk4 10 5 [false, true, true, true, false, true, false, false, true, true]
            dTTFFTFTTTFT
            dTTFFTFTTTFF))
          (s4S chk4 11 5 [false, true, true, false, true, false, false, true, true]
           (s4S chk4 10 5 [true, false, true, true, false, true, false, false, true, true]
            dTTFFTFTTFTT
            dTTFFTFTTFTF)
           (s4S chk4 10 4 [false, false, true, true, false, true, false, false, true, true]
            dTTFFTFTTFFT
            dTTFFTFTTFFF)))
         (s4S chk4 12 5 [false, true, false, true, false, false, true, true]
          (s4S chk4 11 5 [true, false, true, false, true, false, false, true, true]
           (s4S chk4 10 5 [true, true, false, true, false, true, false, false, true, true]
            dTTFFTFTFTTT
            dTTFFTFTFTTF)
           (s4S chk4 10 4 [false, true, false, true, false, true, false, false, true, true]
            dTTFFTFTFTFT
            dTTFFTFTFTFF))
          (s4S chk4 11 4 [false, false, true, false, true, false, false, true, true]
           (s4S chk4 10 4 [true, false, false, true, false, true, false, false, true, true]
            dTTFFTFTFFTT
            dTTFFTFTFFTF)
           (s4S chk4 10 3 [false, false, false, true, false, true, false, false, true, true]
            dTTFFTFTFFFT
            dTTFFTFTFFFF))))
        (s4S chk4 13 5 [false, false, true, false, false, true, true]
         (s4S chk4 12 5 [true, false, false, true, false, false, true, true]
          (s4S chk4 11 5 [true, true, false, false, true, false, false, true, true]
           (s4S chk4 10 5 [true, true, true, false, false, true, false, false, true, true]
            dTTFFTFFTTTT
            dTTFFTFFTTTF)
           (s4S chk4 10 4 [false, true, true, false, false, true, false, false, true, true]
            dTTFFTFFTTFT
            dTTFFTFFTTFF))
          (s4S chk4 11 4 [false, true, false, false, true, false, false, true, true]
           (s4S chk4 10 4 [true, false, true, false, false, true, false, false, true, true]
            dTTFFTFFTFTT
            dTTFFTFFTFTF)
           (s4S chk4 10 3 [false, false, true, false, false, true, false, false, true, true]
            dTTFFTFFTFFT
            dTTFFTFFTFFF)))
         (s4S chk4 12 4 [false, false, false, true, false, false, true, true]
          (s4S chk4 11 4 [true, false, false, false, true, false, false, true, true]
           (s4S chk4 10 4 [true, true, false, false, false, true, false, false, true, true]
            dTTFFTFFFTTT
            dTTFFTFFFTTF)
           (s4S chk4 10 3 [false, true, false, false, false, true, false, false, true, true]
            dTTFFTFFFTFT
            dTTFFTFFFTFF))
          (s4S chk4 11 3 [false, false, false, false, true, false, false, true, true]
           (s4S chk4 10 3 [true, false, false, false, false, true, false, false, true, true]
            dTTFFTFFFFTT
            dTTFFTFFFFTF)
           (s4S chk4 10 2 [false, false, false, false, false, true, false, false, true, true]
            dTTFFTFFFFFT
            dTTFFTFFFFFF))))))
      (s4S chk4 15 6 [false, false, false, true, true]
       (s4S chk4 14 6 [true, false, false, false, true, true]
        (s4S chk4 13 6 [true, true, false, false, false, true, true]
         (s4S chk4 12 6 [true, true, true, false, false, false, true, true]
          (s4S chk4 11 6 [true, true, true, true, false, false, false, true, true]
           (s4S chk4 10 6 [true, true, true, true, true, false, false, false, true, true]
            dTTFFFTTTTTT
            dTTFFFTTTTTF)
           (s4S chk4 10 5 [false, true, true, true, true, false, false, false, true, true]
            dTTFFFTTTTFT
            dTTFFFTTTTFF))
          (s4S chk4 11 5 [false, true, true, true, false, false, false, true, true]
           (s4S chk4 10 5 [true, false, true, true, true, false, false, false, true, true]
            dTTFFFTTTFTT
            dTTFFFTTTFTF)
           (s4S chk4 10 4 [false, false, true, true, true, false, false, false, true, true]
            dTTFFFTTTFFT
            dTTFFFTTTFFF)))
         (s4S chk4 12 5 [false, true, true, false, false, false, true, true]
          (s4S chk4 11 5 [true, false, true, true, false, false, false, true, true]
           (s4S chk4 10 5 [true, true, false, true, true, false, false, false, true, true]
            dTTFFFTTFTTT
            dTTFFFTTFTTF)
           (s4S chk4 10 4 [false, true, false, true, true, false, false, false, true, true]
            dTTFFFTTFTFT
            dTTFFFTTFTFF))
          (s4S chk4 11 4 [false, false, true, true, false, false, false, true, true]
           (s4S chk4 10 4 [true, false, false, true, true, false, false, false, true, true]
            dTTFFFTTFFTT
            dTTFFFTTFFTF)
           (s4S chk4 10 3 [false, false, false, true, true, false, false, false, true, true]
            dTTFFFTTFFFT
            dTTFFFTTFFFF))))
        (s4S chk4 13 5 [false, true, false, false, false, true, true]
         (s4S chk4 12 5 [true, false, true, false, false, false, true, true]
          (s4S chk4 11 5 [true, true, false, true, false, false, false, true, true]
           (s4S chk4 10 5 [true, true, true, false, true, false, false, false, true, true]
            dTTFFFTFTTTT
            dTTFFFTFTTTF)
           (s4S chk4 10 4 [false, true, true, false, true, false, false, false, true, true]
            dTTFFFTFTTFT
            dTTFFFTFTTFF))
          (s4S chk4 11 4 [false, true, false, true, false, false, false, true, true]
           (s4S chk4 10 4 [true, false, true, false, true, false, false, false, true, true]
            dTTFFFTFTFTT
            dTTFFFTFTFTF)
           (s4S chk4 10 3 [false, false, true, false, true, false, false, false, true, true]
            dTTFFFTFTFFT
            dTTFFFTFTFFF)))
         (s4S chk4 12 4 [false, false, true, false, false, false, true, true]
          (s4S chk4 11 4 [true, false, false, true, false, false, false, true, true]
           (s4S chk4 10 4 [true, true, false, false, true, false, false, false, true, true]
            dTTFFFTFFTTT
            dTTFFFTFFTTF)
           (s4S chk4 10 3 [false, true, false, false, true, false, false, false, true, true]
            dTTFFFTFFTFT
            dTTFFFTFFTFF))
          (s4S chk4 11 3 [false, false, false, true, false, false, false, true, true]
           (s4S chk4 10 3 [true, false, false, false, true, false, false, false, true, true]
            dTTFFFTFFFTT
            dTTFFFTFFFTF)
           (s4S chk4 10 2 [false, false, false, false, true, false, false, false, true, true]
            dTTFFFTFFFFT
            dTTFFFTFFFFF)))))
       (s4S chk4 14 5 [false, false, false, false, true, true]
        (s4S chk4 13 5 [true, false, false, false, false, true, true]
         (s4S chk4 12 5 [true, true, false, false, false, false, true, true]
          (s4S chk4 11 5 [true, true, true, false, false, false, false, true, true]
           (s4S chk4 10 5 [true, true, true, true, false, false, false, false, true, true]
            dTTFFFFTTTTT
            dTTFFFFTTTTF)
           (s4S chk4 10 4 [false, true, true, true, false, false, false, false, true, true]
            dTTFFFFTTTFT
            dTTFFFFTTTFF))
          (s4S chk4 11 4 [false, true, true, false, false, false, false, true, true]
           (s4S chk4 10 4 [true, false, true, true, false, false, false, false, true, true]
            dTTFFFFTTFTT
            dTTFFFFTTFTF)
           (s4S chk4 10 3 [false, false, true, true, false, false, false, false, true, true]
            dTTFFFFTTFFT
            dTTFFFFTTFFF)))
         (s4S chk4 12 4 [false, true, false, false, false, false, true, true]
          (s4S chk4 11 4 [true, false, true, false, false, false, false, true, true]
           (s4S chk4 10 4 [true, true, false, true, false, false, false, false, true, true]
            dTTFFFFTFTTT
            dTTFFFFTFTTF)
           (s4S chk4 10 3 [false, true, false, true, false, false, false, false, true, true]
            dTTFFFFTFTFT
            dTTFFFFTFTFF))
          (s4S chk4 11 3 [false, false, true, false, false, false, false, true, true]
           (s4S chk4 10 3 [true, false, false, true, false, false, false, false, true, true]
            dTTFFFFTFFTT
            dTTFFFFTFFTF)
           (s4S chk4 10 2 [false, false, false, true, false, false, false, false, true, true]
            dTTFFFFTFFFT
            dTTFFFFTFFFF))))
        (s4S chk4 13 4 [false, false, false, false, false, true, true]
         (s4S chk4 12 4 [true, false, false, false, false, false, true, true]
          (s4S chk4 11 4 [true, true, false, false, false, false, false, true, true]
           (s4S chk4 10 4 [true, true, true, false, false, false, false, false, true, true]
            dTTFFFFFTTTT
            dTTFFFFFTTTF)
           (s4S chk4 10 3 [false, true, true, false, false, false, false, false, true, true]
            dTTFFFFFTTFT
            dTTFFFFFTTFF))
          (s4S chk4 11 3 [false, true, false, false, false, false, false, true, true]
           (s4S chk4 10 3 [true, false, true, false, false, false, false, false, true, true]
            dTTFFFFFTFTT
            dTTFFFFFTFTF)
           (s4S chk4 10 2 [false, false, true, false, false, false, false, false, true, true]
            dTTFFFFFTFFT
            dTTFFFFFTFFF)))
         (s4S chk4 12 3 [false, false, false, false, false, false, true, true]
          (s4S chk4 11 3 [true, false, false, false, false, false, false, true, true]
           (s4S chk4 10 3 [true, true, false, false, false, false, false, false, true, true]
            dTTFFFFFFTTT
            dTTFFFFFFTTF)
           (s4S chk4 10 2 [false, true, false, false, false, false, false, false, true, true]
            dTTFFFFFFTFT
            dTTFFFFFFTFF))
          (s4S chk4 11 2 [false, false, false, false, false, false, false, true, true]
           (s4S chk4 10 2 [true, false, false, false, false, false, false, false, true, true]
            dTTFFFFFFFTT
            dTTFFFFFFFTF)
           (s4S chk4 10 1 [false, false, false, false, false, false, false, false, true, true]
            dTTFFFFFFFFT
            dTTFFFFFFFFF)))))))))
   (s4S chk4 18 8 [false, true]
    (s4S chk4 17 8 [true, false, true]
     (s4S chk4 16 8 [true, true, false, true]
      (s4S chk4 15 8 [true, true, true, false, true]
       (s4S chk4 14 8 [true, true, true, true, false, true]
        (s4S chk4 13 8 [true, true, true, true, true, false, true]
         (s4S chk4 12 8 [true, true, true, true, true, true, false, true]
          (s4S chk4 11 8 [true, true, true, true, true, true, true, false, true]
           (s4S chk4 10 8 [true, true, true, true, true, true, true, true, false, true]
            dTFTTTTTTTTT
            dTFTTTTTTTTF)
           (s4S chk4 10 7 [false, true, true, true, true, true, true, true, false, true]
            dTFTTTTTTTFT
            dTFTTTTTTTFF))
          (s4S chk4 11 7 [false, true, true, true, true, true, true, false, true]
           (s4S chk4 10 7 [true, false, true, true, true, true, true, true, false, true]
            dTFTTTTTTFTT
            dTFTTTTTTFTF)
           (s4S chk4 10 6 [false, false, true, true, true, true, true, true, false, true]
            dTFTTTTTTFFT
            dTFTTTTTTFFF)))
         (s4S chk4 12 7 [false, true, true, true, true, true, false, true]
          (s4S chk4 11 7 [true, false, true, true, true, true, true, false, true]
           (s4S chk4 10 7 [true, true, false, true, true, true, true, true, false, true]
            dTFTTTTTFTTT
            dTFTTTTTFTTF)
           (s4S chk4 10 6 [false, true, false, true, true, true, true, true, false, true]
            dTFTTTTTFTFT
            dTFTTTTTFTFF))
          (s4S chk4 11 6 [false, false, true, true, true, true, true, false, true]
           (s4S chk4 10 6 [true, false, false, true, true, true, true, true, false, true]
            dTFTTTTTFFTT
            dTFTTTTTFFTF)
           (s4S chk4 10 5 [false, false, false, true, true, true, true, true, false, true]
            dTFTTTTTFFFT
            dTFTTTTTFFFF))))
        (s4S chk4 13 7 [false, true, true, true, true, false, true]
         (s4S chk4 12 7 [true, false, true, true, true, true, false, true]
          (s4S chk4 11 7 [true, true, false, true, true, true, true, false, true]
           (s4S chk4 10 7 [true, true, true, false, true, true, true, true, false, true]
            dTFTTTTFTTTT
            dTFTTTTFTTTF)
           (s4S chk4 10 6 [false, true, true, false, true, true, true, true, false, true]
            dTFTTTTFTTFT
            dTFTTTTFTTFF))
          (s4S chk4 11 6 [false, true, false, true, true, true, true, false, true]
           (s4S chk4 10 6 [true, false, true, false, true, true, true, true, false, true]
            dTFTTTTFTFTT
            dTFTTTTFTFTF)
           (s4S chk4 10 5 [false, false, true, false, true, true, true, true, false, true]
            dTFTTTTFTFFT
            dTFTTTTFTFFF)))
         (s4S chk4 12 6 [false, false, true, true, true, true, false, true]
          (s4S chk4 11 6 [true, false, false, true, true, true, true, false, true]
           (s4S chk4 10 6 [true, true, false, false, true, true, true, true, false, true]
            dTFTTTTFFTTT
            dTFTTTTFFTTF)
           (s4S chk4 10 5 [false, true, false, false, true, true, true, true, false, true]
            dTFTTTTFFTFT
            dTFTTTTFFTFF))
          (s4S chk4 11 5 [false, false, false, true, true, true, true, false, true]
           (s4S chk4 10 5 [true, false, false, false, true, true, true, true, false, true]
            dTFTTTTFFFTT
            dTFTTTTFFFTF)
           (s4S chk4 10 4 [false, false, false, false, true, true, true, true, false, true]
            dTFTTTTFFFFT
            dTFTTTTFFFFF)))))
       (s4S chk4 14 7 [false, true, true, true, false, true]
        (s4S chk4 13 7 [true, false, true, true, true, false, true]
         (s4S chk4 12 7 [true, true, false, true, true, true, false, true]
          (s4S chk4 11 7 [true, true, true, false, true, true, true, false, true]
           (s4S chk4 10 7 [true, true, true, true, false, true, true, true, false, true]
            dTFTTTFTTTTT
            dTFTTTFTTTTF)
           (s4S chk4 10 6 [false, true, true, true, false, true, true, true, false, true]
            dTFTTTFTTTFT
            dTFTTTFTTTFF))
          (s4S chk4 11 6 [false, true, true, false, true, true, true, false, true]
           (s4S chk4 10 6 [true, false, true, true, false, true, true, true, false, true]
            dTFTTTFTTFTT
            dTFTTTFTTFTF)
           (s4S chk4 10 5 [false, false, true, true, false, true, true, true, false, true]
            dTFTTTFTTFFT
            dTFTTTFTTFFF)))
         (s4S chk4 12 6 [false, true, false, true, true, true, false, true]
          (s4S chk4 11 6 [true, false, true, false, true, true, true, false, true]
           (s4S chk4 10 6 [true, true, false, true, false, true, true, true, false, true]
            dTFTTTFTFTTT
            dTFTTTFTFTTF)
           (s4S chk4 10 5 [false, true, false, true, false, true, true, true, false, true]
            dTFTTTFTFTFT
            dTFTTTFTFTFF))
          (s4S chk4 11 5 [false, false, true, false, true, true, true, false, true]
           (s4S chk4 10 5 [true, false, false, true, false, true, true, true, false, true]
            dTFTTTFTFFTT
            dTFTTTFTFFTF)
           (s4S chk4 10 4 [false, false, false, true, false, true, true, true, false, true]
            dTFTTTFTFFFT
            dTFTTTFTFFFF))))
        (s4S chk4 13 6 [false, false, true, true, true, false, true]
         (s4S chk4 12 6 [true, false, false, true, true, true, false, true]
          (s4S chk4 11 6 [true, true, false, false, true, true, true, false, true]
           (s4S chk4 10 6 [true, true, true, false, false, true, true, true, false, true]
            dTFTTTFFTTTT
            dTFTTTFFTTTF)
           (s4S chk4 10 5 [false, true, true, false, false, true, true, true, false, true]
            dTFTTTFFTTFT
            dTFTTTFFTTFF))
          (s4S chk4 11 5 [false, true, false, false, true, true, true, false, true]
           (s4S chk4 10 5 [true, false, true, false, false, true, true, true, false, true]
            dTFTTTFFTFTT
            dTFTTTFFTFTF)
           (s4S chk4 10 4 [false, false, true, false, false, true, true, true, false, true]
            dTFTTTFFTFFT
            dTFTTTFFTFFF)))
         (s4S chk4 12 5 [false, false, false, true, true, true, false, true]
          (s4S chk4 11 5 [true, false, false, false, true, true, true, false, true]
           (s4S chk4 10 5 [true, true, false, false, false, true, true, true, false, true]
            dTFTTTFFFTTT
            dTFTTTFFFTTF)
           (s4S chk4 10 4 [false, true, false, false, false, true, true, true, false, true]
            dTFTTTFFFTFT
            dTFTTTFFFTFF))
          (s4S chk4 11 4 [false, false, false, false, true, true, true, false, true]
           (s4S chk4 10 4 [true, false, false, false, false, true, true, true, false, true]
            dTFTTTFFFFTT
            dTFTTTFFFFTF)
           (s4S chk4 10 3 [false, false, false, false, false, true, true, true, false, true]
            dTFTTTFFFFFT
            dTFTTTFFFFFF))))))
      (s4S chk4 15 7 [false, true, true, false, true]
       (s4S chk4 14 7 [true, false, true, true, false, true]
        (s4S chk4 13 7 [true, true, false, true, true, false, true]
         (s4S chk4 12 7 [true, true, true, false, true, true, false, true]
          (s4S chk4 11 7 [true, true, true, true, false, true, true, false, true]
           (s4S chk4 10 7 [true, true, true, true, true, false, true, true, false, true]
            dTFTTFTTTTTT
            dTFTTFTTTTTF)
           (s4S chk4 10 6 [false, true, true, true, true, false, true, true, false, true]
            dTFTTFTTTTFT
            dTFTTFTTTTFF))
          (s4S chk4 11 6 [false, true, true, true, false, true, true, false, true]
           (s4S chk4 10 6 [true, false, true, true, true, false, true, true, false, true]
            dTFTTFTTTFTT
            dTFTTFTTTFTF)
           (s4S chk4 10 5 [false, false, true, true, true, false, true, true, false, true]
            dTFTTFTTTFFT
            dTFTTFTTTFFF)))
         (s4S chk4 12 6 [false, true, true, false, true, true, false, true]
          (s4S chk4 11 6 [true, false, true, true, false, true, true, false, true]
           (s4S chk4 10 6 [true, true, false, true, true, false, true, true, false, true]
            dTFTTFTTFTTT
            dTFTTFTTFTTF)
           (s4S chk4 10 5 [false, true, false, true, true, false, true, true, false, true]
            dTFTTFTTFTFT
            dTFTTFTTFTFF))
          (s4S chk4 11 5 [false, false, true, true, false, true, true, false, true]
           (s4S chk4 10 5 [true, false, false, true, true, false, true, true, false, true]
            dTFTTFTTFFTT
            dTFTTFTTFFTF)
           (s4S chk4 10 4 [false, false, false, true, true, false, true, true, false, true]
            dTFTTFTTFFFT
            dTFTTFTTFFFF))))
        (s4S chk4 13 6 [false, true, false, true, true, false, true]
         (s4S chk4 12 6 [true, false, true, false, true, true, false, true]
          (s4S chk4 11 6 [true, true, false, true, false, true, true, false, true]
           (s4S chk4 10 6 [true, true, true, false, true, false, true, true, false, true]
            dTFTTFTFTTTT
            dTFTTFTFTTTF)
           (s4S chk4 10 5 [false, true, true, false, true, false, true, true, false, true]
            dTFTTFTFTTFT
            dTFTTFTFTTFF))
          (s4S chk4 11 5 [false, true, false, true, false, true, true, false, true]
           (s4S chk4 10 5 [true, false, true, false, true, false, true, true, false, true]
            dTFTTFTFTFTT
            dTFTTFTFTFTF)
           (s4S chk4 10 4 [false, false, true, false, true, false, true, true, false, true]
            dTFTTFTFTFFT
            dTFTTFTFTFFF)))
         (s4S chk4 12 5 [false, false, true, false, true, true, false, true]
          (s4S chk4 11 5 [true, false, false, true, false, true, true, false, true]
           (s4S chk4 10 5 [true, true, false, false, true, false, true, true, false, true]
            dTFTTFTFFTTT
            dTFTTFTFFTTF)
           (s4S chk4 10 4 [false, true, false, false, true, false, true, true, false, true]
            dTFTTFTFFTFT
            dTFTTFTFFTFF))
          (s4S chk4 11 4 [false, false, false, true, false, true, true, false, true]
           (s4S chk4 10 4 [true, false, false, false, true, false, true, true, false, true]
            dTFTTFTFFFTT
            dTFTTFTFFFTF)
           (s4S chk4 10 3 [false, false, false, false, true, false, true, true, false, true]
            dTFTTFTFFFFT
            dTFTTFTFFFFF)))))
       (s4S chk4 14 6 [false, false, true, true, false, true]
        (s4S chk4 13 6 [true, false, false, true, true, false, true]
         (s4S chk4 12 6 [true, true, false, false, true, true, false, true]
          (s4S chk4 11 6 [true, true, true, false, false, true, true, false, true]
           (s4S chk4 10 6 [true, true, true, true, false, false, true, true, false, true]
            dTFTTFFTTTTT
            dTFTTFFTTTTF)
           (s4S chk4 10 5 [false, true, true, true, false, false, true, true, false, true]
            dTFTTFFTTTFT
            dTFTTFFTTTFF))
          (s4S chk4 11 5 [false, true, true, false, false, true, true, false, true]
           (s4S chk4 10 5 [true, false, true, true, false, false, true, true, false, true]
            dTFTTFFTTFTT
            dTFTTFFTTFTF)
           (s4S chk4 10 4 [false, false, true, true, false, false, true, true, false, true]
            dTFTTFFTTFFT
            dTFTTFFTTFFF)))
         (s4S chk4 12 5 [false, true, false, false, true, true, false, true]
          (s4S chk4 11 5 [true, false, true, false, false, true, true, false, true]
           (s4S chk4 10 5 [true, true, false, true, false, false, true, true, false, true]
            dTFTTFFTFTTT
            dTFTTFFTFTTF)
           (s4S chk4 10 4 [false, true, false, true, false, false, true, true, false, true]
            dTFTTFFTFTFT
            dTFTTFFTFTFF))
          (s4S chk4 11 4 [false, false, true, false, false, true, true, false, true]
           (s4S chk4 10 4 [true, false, false, true, false, false, true, true, false, true]
            dTFTTFFTFFTT
            dTFTTFFTFFTF)
           (s4S chk4 10 3 [false, false, false, true, false, false, true, true, false, true]
            dTFTTFFTFFFT
            dTFTTFFTFFFF))))
        (s4S chk4 13 5 [false, false, false, true, true, false, true]
         (s4S chk4 12 5 [true, false, false, false, true, true, false, true]
          (s4S chk4 11 5 [true, true, false, false, false, true, true, false, true]
           (s4S chk4 10 5 [true, true, true, false, false, false, true, true, false, true]
            dTFTTFFFTTTT
            dTFTTFFFTTTF)
           (s4S chk4 10 4 [false, true, true, false, false, false, true, true, false, true]
            dTFTTFFFTTFT
            dTFTTFFFTTFF))
          (s4S chk4 11 4 [false, true, false, false, false, true, true, false, true]
           (s4S chk4 10 4 [true, false, true, false, false, false, true, true, false, true]
            dTFTTFFFTFTT
            dTFTTFFFTFTF)
           (s4S chk4 10 3 [false, false, true, false, false, false, true, true, false, true]
            dTFTTFFFTFFT
            dTFTTFFFTFFF)))
         (s4S chk4 12 4 [false, false, false, false, true, true, false, true]
          (s4S chk4 11 4 [true, false, false, false, false, true, true, false, true]
           (s4S chk4 10 4 [true, true, false, false, false, false, true, true, false, true]
            dTFTTFFFFTTT
            dTFTTFFFFTTF)
           (s4S chk4 10 3 [false, true, false, false, false, false, true, true, false, true]
            dTFTTFFFFTFT
            dTFTTFFFFTFF))
          (s4S chk4 11 3 [false, false, false, false, false, true, true, false, true]
           (s4S chk4 10 3 [true, false, false, false, false, false, true, true, false, true]
            dTFTTFFFFFTT
            dTFTTFFFFFTF)
           (s4S chk4 10 2 [false, false, false, false, false, false, true, true, false, true]
            dTFTTFFFFFFT
            dTFTTFFFFFFF)))))))
     (s4S chk4 16 7 [false, true, false, true]
      (s4S chk4 15 7 [true, false, true, false, true]
       (s4S chk4 14 7 [true, true, false, true, false, true]
        (s4S chk4 13 7 [true, true, true, false, true, false, true]
         (s4S chk4 12 7 [true, true, true, true, false, true, false, true]
          (s4S chk4 11 7 [true, true, true, true, true, false, true, false, true]
           (s4S chk4 10 7 [true, true, true, true, true, true, false, true, false, true]
            dTFTFTTTTTTT
            dTFTFTTTTTTF)
           (s4S chk4 10 6 [false, true, true, true, true, true, false, true, false, true]
            dTFTFTTTTTFT
            dTFTFTTTTTFF))
          (s4S chk4 11 6 [false, true, true, true, true, false, true, false, true]
           (s4S chk4 10 6 [true, false, true, true, true, true, false, true, false, true]
            dTFTFTTTTFTT
            dTFTFTTTTFTF)
           (s4S chk4 10 5 [false, false, true, true, true, true, false, true, false, true]
            dTFTFTTTTFFT
            dTFTFTTTTFFF)))
         (s4S chk4 12 6 [false, true, true, true, false, true, false, true]
          (s4S chk4 11 6 [true, false, true, true, true, false, true, false, true]
           (s4S chk4 10 6 [true, true, false, true, true, true, false, true, false, true]
            dTFTFTTTFTTT
            dTFTFTTTFTTF)
           (s4S chk4 10 5 [false, true, false, true, true, true, false, true, false, true]
            dTFTFTTTFTFT
            dTFTFTTTFTFF))
          (s4S chk4 11 5 [false, false, true, true, true, false, true, false, true]
           (s4S chk4 10 5 [true, false, false, true, true, true, false, true, false, true]
            dTFTFTTTFFTT
            dTFTFTTTFFTF)
           (s4S chk4 10 4 [false, false, false, true, true, true, false, true, false, true]
            dTFTFTTTFFFT
            dTFTFTTTFFFF))))
        (s4S chk4 13 6 [false, true, true, false, true, false, true]
         (s4S chk4 12 6 [true, false, true, true, false, true, false, true]
          (s4S chk4 11 6 [true, true, false, true, true, false, true, false, true]
           (s4S chk4 10 6 [true, true, true, false, true, true, false, true, false, true]
            dTFTFTTFTTTT
            dTFTFTTFTTTF)
           (s4S chk4 10 5 [false, true, true, false, true, true, false, true, false, true]
            dTFTFTTFTTFT
            dTFTFTTFTTFF))
          (s4S chk4 11 5 [false, true, false, true, true, false, true, false, true]
           (s4S chk4 10 5 [true, false, true, false, true, true, false, true, false, true]
            dTFTFTTFTFTT
            dTFTFTTFTFTF)
           (s4S chk4 10 4 [false, false, true, false, true, true, false, true, false, true]
            dTFTFTTFTFFT
            dTFTFTTFTFFF)))
         (s4S chk4 12 5 [false, false, true, true, false, true, false, true]
          (s4S chk4 11 5 [true, false, false, true, true, false, true, false, true]
           (s4S chk4 10 5 [true, true, false, false, true, true, false, true, false, true]
            dTFTFTTFFTTT
            dTFTFTTFFTTF)
           (s4S chk4 10 4 [false, true, false, false, true, true, false, true, false, true]
            dTFTFTTFFTFT
            dTFTFTTFFTFF))
          (s4S chk4 11 4 [false, false, false, true, true, false, true, false, true]
           (s4S chk4 10 4 [true, false, false, false, true, true, false, true, false, true]
            dTFTFTTFFFTT
            dTFTFTTFFFTF)
           (s4S chk4 10 3 [false, false, false, false, true, true, false, true, false, true]
            dTFTFTTFFFFT
            dTFTFTTFFFFF)))))
       (s4S chk4 14 6 [false, true, false, true, false, true]
        (s4S chk4 13 6 [true, false, true, false, true, false, true]
         (s4S chk4 12 6 [true, true, false, true, false, true, false, true]
          (s4S chk4 11 6 [true, true, true, false, true, false, true, false, true]
           (s4S chk4 10 6 [true, true, true, true, false, true, false, true, false, true]
            dTFTFTFTTTTT
            dTFTFTFTTTTF)
           (s4S chk4 10 5 [false, true, true, true, false, true, false, true, false, true]
            dTFTFTFTTTFT
            dTFTFTFTTTFF))
          (s4S chk4 11 5 [false, true, true, false, true, false, true, false, true]
           (s4S chk4 10 5 [true, false, true, true, false, true, false, true, false, true]
            dTFTFTFTTFTT
            dTFTFTFTTFTF)
           (s4S chk4 10 4 [false, false, true, true, false, true, false, true, false, true]
            dTFTFTFTTFFT
            dTFTFTFTTFFF)))
         (s4S chk4 12 5 [false, true, false, true, false, true, false, true]
          (s4S chk4 11 5 [true, false, true, false, true, false, true, false, true]
           (s4S chk4 10 5 [true, true, false, true, false, true, false, true, false, true]
            dTFTFTFTFTTT
            dTFTFTFTFTTF)
           (s4S chk4 10 4 [false, true, false, true, false, true, false, true, false, true]
            dTFTFTFTFTFT
            dTFTFTFTFTFF))
          (s4S chk4 11 4 [false, false, true, false, true, false, true, false, true]
           (s4S chk4 10 4 [true, false, false, true, false, true, false, true, false, true]
            dTFTFTFTFFTT
            dTFTFTFTFFTF)
           (s4S chk4 10 3 [false, false, false, true, false, true, false, true, false, true]
            dTFTFTFTFFFT
            dTFTFTFTFFFF))))
        (s4S chk4 13 5 [false, false, true, false, true, false, true]
         (s4S chk4 12 5 [true, false, false, true, false, true, false, true]
          (s4S chk4 11 5 [true, true, false, false, true, false, true, false, true]
           (s4S chk4 10 5 [true, true, true, false, false, true, false, true, false, true]
            dTFTFTFFTTTT
            dTFTFTFFTTTF)
           (s4S chk4 10 4 [false, true, true, false, false, true, false, true, false, true]
            dTFTFTFFTTFT
            dTFTFTFFTTFF))
          (s4S chk4 11 4 [false, true, false, false, true, false, true, false, true]
           (s4S chk4 10 4 [true, false, true, false, false, true, false, true, false, true]
            dTFTFTFFTFTT
            dTFTFTFFTFTF)
           (s4S chk4 10 3 [false, false, true, false, false, true, false, true, false, true]
            dTFTFTFFTFFT
            dTFTFTFFTFFF)))
         (s4S chk4 12 4 [false, false, false, true, false, true, false, true]
          (s4S chk4 11 4 [true, false, false, false, true, false, true, false, true]
           (s4S chk4 10 4 [true, true, false, false, false, true, false, true, false, true]
            dTFTFTFFFTTT
            dTFTFTFFFTTF)
           (s4S chk4 10 3 [false, true, false, false, false, true, false, true, false, true]
            dTFTFTFFFTFT
            dTFTFTFFFTFF))
          (s4S chk4 11 3 [false, false, false, false, true, false, true, false, true]
           (s4S chk4 10 3 [true, false, false, false, false, true, false, true, false, true]
            dTFTFTFFFFTT
            dTFTFTFFFFTF)
           (s4S chk4 10 2 [false, false, false, false, false, true, false, true, false, true]
            dTFTFTFFFFFT
            dTFTFTFFFFFF))))))
      (s4S chk4 15 6 [false, false, true, false, true]
       (s4S chk4 14 6 [true, false, false, true, false, true]
        (s4S chk4 13 6 [true, true, false, false, true, false, true]
         (s4S chk4 12 6 [true, true, true, false, false, true, false, true]
          (s4S chk4 11 6 [true, true, true, true, false, false, true, false, true]
           (s4S chk4 10 6 [true, true, true, true, true, false, false, true, false, true]
            dTFTFFTTTTTT
            dTFTFFTTTTTF)
           (s4S chk4 10 5 [false, true, true, true, true, false, false, true, false, true]
            dTFTFFTTTTFT
            dTFTFFTTTTFF))
          (s4S chk4 11 5 [false, true, true, true, false, false, true, false, true]
           (s4S chk4 10 5 [true, false, true, true, true, false, false, true, false, true]
            dTFTFFTTTFTT
            dTFTFFTTTFTF)
           (s4S chk4 10 4 [false, false, true, true, true, false, false, true, false, true]
            dTFTFFTTTFFT
            dTFTFFTTTFFF)))
         (s4S chk4 12 5 [false, true, true, false, false, true, false, true]
          (s4S chk4 11 5 [true, false, true, true, false, false, true, false, true]
           (s4S chk4 10 5 [true, true, false, true, true, false, false, true, false, true]
            dTFTFFTTFTTT
            dTFTFFTTFTTF)
           (s4S chk4 10 4 [false, true, false, true, true, false, false, true, false, true]
            dTFTFFTTFTFT
            dTFTFFTTFTFF))
          (s4S chk4 11 4 [false, false, true, true, false, false, true, false, true]
           (s4S chk4 10 4 [true, false, false, true, true, false, false, true, false, true]
            dTFTFFTTFFTT
            dTFTFFTTFFTF)
           (s4S chk4 10 3 [false, false, false, true, true, false, false, true, false, true]
            dTFTFFTTFFFT
            dTFTFFTTFFFF))))
        (s4S chk4 13 5 [false, true, false, false, true, false, true]
         (s4S chk4 12 5 [true, false, true, false, false, true, false, true]
          (s4S chk4 11 5 [true, true, false, true, false, false, true, false, true]
           (s4S chk4 10 5 [true, true, true, false, true, false, false, true, false, true]
            dTFTFFTFTTTT
            dTFTFFTFTTTF)
           (s4S chk4 10 4 [false, true, true, false, true, false, false, true, false, true]
            dTFTFFTFTTFT
            dTFTFFTFTTFF))
          (s4S chk4 11 4 [false, true, false, true, false, false, true, false, true]
           (s4S chk4 10 4 [true, false, true, false, true, false, false, true, false, true]
            dTFTFFTFTFTT
            dTFTFFTFTFTF)
           (s4S chk4 10 3 [false, false, true, false, true, false, false, true, false, true]
            dTFTFFTFTFFT
            dTFTFFTFTFFF)))
         (s4S chk4 12 4 [false, false, true, false, false, true, false, true]
          (s4S chk4 11 4 [true, false, false, true, false, false, true, false, true]
           (s4S chk4 10 4 [true, true, false, false, true, false, false, true, false, true]
            dTFTFFTFFTTT
            dTFTFFTFFTTF)
           (s4S chk4 10 3 [false, true, false, false, true, false, false, true, false, true]
            dTFTFFTFFTFT
            dTFTFFTFFTFF))
          (s4S chk4 11 3 [false, false, false, true, false, false, true, false, true]
           (s4S chk4 10 3 [true, false, false, false, true, false, false, true, false, true]
            dTFTFFTFFFTT
            dTFTFFTFFFTF)
           (s4S chk4 10 2 [false, false, false, false, true, false, false, true, false, true]
            dTFTFFTFFFFT
            dTFTFFTFFFFF)))))
       (s4S chk4 14 5 [false, false, false, true, false, true]
        (s4S chk4 13 5 [true, false, false, false, true, false, true]
         (s4S chk4 12 5 [true, true, false, false, false, true, false, true]
          (s4S chk4 11 5 [true, true, true, false, false, false, true, false, true]
           (s4S chk4 10 5 [true, true, true, true, false, false, false, true, false, true]
            dTFTFFFTTTTT
            dTFTFFFTTTTF)
           (s4S chk4 10 4 [false, true, true, true, false, false, false, true, false, true]
            dTFTFFFTTTFT
            dTFTFFFTTTFF))
          (s4S chk4 11 4 [false, true, true, false, false, false, true, false, true]
           (s4S chk4 10 4 [true, false, true, true, false, false, false, true, false, true]
            dTFTFFFTTFTT
            dTFTFFFTTFTF)
           (s4S chk4 10 3 [false, false, true, true, false, false, false, true, false, true]
            dTFTFFFTTFFT
            dTFTFFFTTFFF)))
         (s4S chk4 12 4 [false, true, false, false, false, true, false, true]
          (s4S chk4 11 4 [true, false, true, false, false, false, true, false, true]
           (s4S chk4 10 4 [true, true, false, true, false, false, false, true, false, true]
            dTFTFFFTFTTT
            dTFTFFFTFTTF)
           (s4S chk4 10 3 [false, true, false, true, false, false, false, true, false, true]
            dTFTFFFTFTFT
            dTFTFFFTFTFF))
          (s4S chk4 11 3 [false, false, true, false, false, false, true, false, true]
           (s4S chk4 10 3 [true, false, false, true, false, false, false, true, false, true]
            dTFTFFFTFFTT
            dTFTFFFTFFTF)
           (s4S chk4 10 2 [false, false, false, true, false, false, false, true, false, true]
            dTFTFFFTFFFT
            dTFTFFFTFFFF))))
        (s4S chk4 13 4 [false, false, false, false, true, false, true]
         (s4S chk4 12 4 [true, false, false, false, false, true, false, true]
          (s4S chk4 11 4 [true, true, false, false, false, false, true, false, true]
           (s4S chk4 10 4 [true, true, true, false, false, false, false, true, false, true]
            dTFTFFFFTTTT
            dTFTFFFFTTTF)
           (s4S chk4 10 3 [false, true, true, false, false, false, false, true, false, true]
            dTFTFFFFTTFT
            dTFTFFFFTTFF))
          (s4S chk4 11 3 [false, true, false, false, false, false, true, false, true]
           (s4S chk4 10 3 [true, false, true, false, false, false, false, true, false, true]
            dTFTFFFFTFTT
            dTFTFFFFTFTF)
           (s4S chk4 10 2 [false, false, true, false, false, false, false, true, false, true]
            dTFTFFFFTFFT
            dTFTFFFFTFFF)))
         (s4S chk4 12 3 [false, false, false, false, false, true, false, true]
          (s4S chk4 11 3 [true, false, false, false, false, false, true, false, true]
           (s4S chk4 10 3 [true, true, false, false, false, false, false, true, false, true]
            dTFTFFFFFTTT
            dTFTFFFFFTTF)
           (s4S chk4 10 2 [false, true, false, false, false, false, false, true, false, true]
            dTFTFFFFFTFT
            dTFTFFFFFTFF))
          (s4S chk4 11 2 [false, false, false, false, false, false, true, false, true]
           (s4S chk4 10 2 [true, false, false, false, false, false, false, true, false, true]
            dTFTFFFFFFTT
            dTFTFFFFFFTF)
           (s4S chk4 10 1 [false, false, false, false, false, false, false, true, false, true]
            dTFTFFFFFFFT
            dTFTFFFFFFFF))))))))
    (s4S chk4 17 7 [false, false, true]
     (s4S chk4 16 7 [true, false, false, true]
      (s4S chk4 15 7 [true, true, false, false, true]
       (s4S chk4 14 7 [true, true, true, false, false, true]
        (s4S chk4 13 7 [true, true, true, true, false, false, true]
         (s4S chk4 12 7 [true, true, true, true, true, false, false, true]
          (s4S chk4 11 7 [true, true, true, true, true, true, false, false, true]
           (s4S chk4 10 7 [true, true, true, true, true, true, true, false, false, true]
            dTFFTTTTTTTT
            dTFFTTTTTTTF)
           (s4S chk4 10 6 [false, true, true, true, true, true, true, false, false, true]
            dTFFTTTTTTFT
            dTFFTTTTTTFF))
          (s4S chk4 11 6 [false, true, true, true, true, true, false, false, true]
           (s4S chk4 10 6 [true, false, true, true, true, true, true, false, false, true]
            dTFFTTTTTFTT
            dTFFTTTTTFTF)
           (s4S chk4 10 5 [false, false, true, true, true, true, true, false, false, true]
            dTFFTTTTTFFT
            dTFFTTTTTFFF)))
         (s4S chk4 12 6 [false, true, true, true, true, false, false, true]
          (s4S chk4 11 6 [true, false, true, true, true, true, false, false, true]
           (s4S chk4 10 6 [true, true, false, true, true, true, true, false, false, true]
            dTFFTTTTFTTT
            dTFFTTTTFTTF)
           (s4S chk4 10 5 [false, true, false, true, true, true, true, false, false, true]
            dTFFTTTTFTFT
            dTFFTTTTFTFF))
          (s4S chk4 11 5 [false, false, true, true, true, true, false, false, true]
           (s4S chk4 10 5 [true, false, false, true, true, true, true, false, false, true]
            dTFFTTTTFFTT
            dTFFTTTTFFTF)
           (s4S chk4 10 4 [false, false, false, true, true, true, true, false, false, true]
            dTFFTTTTFFFT
            dTFFTTTTFFFF))))
        (s4S chk4 13 6 [false, true, true, true, false, false, true]
         (s4S chk4 12 6 [true, false, true, true, true, false, false, true]
          (s4S chk4 11 6 [true, true, false, true, true, true, false, false, true]
           (s4S chk4 10 6 [true, true, true, false, true, true, true, false, false, true]
            dTFFTTTFTTTT
            dTFFTTTFTTTF)
           (s4S chk4 10 5 [false, true, true, false, true, true, true, false, false, true]
            dTFFTTTFTTFT
            dTFFTTTFTTFF))
          (s4S chk4 11 5 [false, true, false, true, true, true, false, false, true]
           (s4S chk4 10 5 [true, false, true, false, true, true, true, false, false, true]
            dTFFTTTFTFTT
            dTFFTTTFTFTF)
           (s4S chk4 10 4 [false, false, true, false, true, true, true, false, false, true]
            dTFFTTTFTFFT
            dTFFTTTFTFFF)))
         (s4S chk4 12 5 [false, false, true, true, true, false, false, true]
          (s4S chk4 11 5 [true, false, false, true, true, true, false, false, true]
           (s4S chk4 10 5 [true, true, false, false, true, true, true, false, false, true]
            dTFFTTTFFTTT
            dTFFTTTFFTTF)
           (s4S chk4 10 4 [false, true, false, false, true, true, true, false, false, true]
            dTFFTTTFFTFT
            dTFFTTTFFTFF))
          (s4S chk4 11 4 [false, false, false, true, true, true, false, false, true]
           (s4S chk4 10 4 [true, false, false, false, true, true, true, false, false, true]
            dTFFTTTFFFTT
            dTFFTTTFFFTF)
           (s4S chk4 10 3 [false, false, false, false, true, true, true, false, false, true]
            dTFFTTTFFFFT
            dTFFTTTFFFFF)))))
       (s4S chk4 14 6 [false, true, true, false, false, true]
        (s4S chk4 13 6 [true, false, true, true, false, false, true]
         (s4S chk4 12 6 [true, true, false, true, true, false, false, true]
          (s4S chk4 11 6 [true, true, true, false, true, true, false, false, true]
           (s4S chk4 10 6 [true, true, true, true, false, true, true, false, false, true]
            dTFFTTFTTTTT
            dTFFTTFTTTTF)
           (s4S chk4 10 5 [false, true, true, true, false, true, true, false, false, true]
            dTFFTTFTTTFT
            dTFFTTFTTTFF))
          (s4S chk4 11 5 [false, true, true, false, true, true, false, false, true]
           (s4S chk4 10 5 [true, false, true, true, false, true, true, false, false, true]
            dTFFTTFTTFTT
            dTFFTTFTTFTF)
           (s4S chk4 10 4 [false, false, true, true, false, true, true, false, false, true]
            dTFFTTFTTFFT
            dTFFTTFTTFFF)))
         (s4S chk4 12 5 [false, true, false, true, true, false, false, true]
          (s4S chk4 11 5 [true, false, true, false, true, true, false, false, true]
           (s4S chk4 10 5 [true, true, false, true, false, true, true, false, false, true]
            dTFFTTFTFTTT
            dTFFTTFTFTTF)
           (s4S chk4 10 4 [false, true, false, true, false, true, true, false, false, true]
            dTFFTTFTFTFT
            dTFFTTFTFTFF))
          (s4S chk4 11 4 [false, false, true, false, true, true, false, false, true]
           (s4S chk4 10 4 [true, false, false, true, false, true, true, false, false, true]
            dTFFTTFTFFTT
            dTFFTTFTFFTF)
           (s4S chk4 10 3 [false, false, false, true, false, true, true, false, false, true]
            dTFFTTFTFFFT
            dTFFTTFTFFFF))))
        (s4S chk4 13 5 [false, false, true, true, false, false, true]
         (s4S chk4 12 5 [true, false, false, true, true, false, false, true]
          (s4S chk4 11 5 [true, true, false, false, true, true, false, false, true]
           (s4S chk4 10 5 [true, true, true, false, false, true, true, false, false, true]
            dTFFTTFFTTTT
            dTFFTTFFTTTF)
           (s4S chk4 10 4 [false, true, true, false, false, true, true, false, false, true]
            dTFFTTFFTTFT
            dTFFTTFFTTFF))
          (s4S chk4 11 4 [false, true, false, false, true, true, false, false, true]
           (s4S chk4 10 4 [true, false, true, false, false, true, true, false, false, true]
            dTFFTTFFTFTT
            dTFFTTFFTFTF)
           (s4S chk4 10 3 [false, false, true, false, false, true, true, false, false, true]
            dTFFTTFFTFFT
            dTFFTTFFTFFF)))
         (s4S chk4 12 4 [false, false, false, true, true, false, false, true]
          (s4S chk4 11 4 [true, false, false, false, true, true, false, false, true]
           (s4S chk4 10 4 [true, true, false, false, false, true, true, false, false, true]
            dTFFTTFFFTTT
            dTFFTTFFFTTF)
           (s4S chk4 10 3 [false, true, false, false, false, true, true, false, false, true]
            dTFFTTFFFTFT
            dTFFTTFFFTFF))
          (s4S chk4 11 3 [false, false, false, false, true, true, false, false, true]
           (s4S chk4 10 3 [true, false, false, false, false, true, true, false, false, true]
            dTFFTTFFFFTT
            dTFFTTFFFFTF)
           (s4S chk4 10 2 [false, false, false, false, false, true, true, false, false, true]
            dTFFTTFFFFFT
            dTFFTTFFFFFF))))))
      (s4S chk4 15 6 [false, true, false, false, true]
       (s4S chk4 14 6 [true, false, true, false, false, true]
        (s4S chk4 13 6 [true, true, false, true, false, false, true]
         (s4S chk4 12 6 [true, true, true, false, true, false, false, true]
          (s4S chk4 11 6 [true, true, true, true, false, true, false, false, true]
           (s4S chk4 10 6 [true, true, true, true, true, false, true, false, false, true]
            dTFFTFTTTTTT
            dTFFTFTTTTTF)
           (s4S chk4 10 5 [false, true, true, true, true, false, true, false, false, true]
            dTFFTFTTTTFT
            dTFFTFTTTTFF))
          (s4S chk4 11 5 [false, true, true, true, false, true, false, false, true]
           (s4S chk4 10 5 [true, false, true, true, true, false, true, false, false, true]
            dTFFTFTTTFTT
            dTFFTFTTTFTF)
           (s4S chk4 10 4 [false, false, true, true, true, false, true, false, false, true]
            dTFFTFTTTFFT
            dTFFTFTTTFFF)))
         (s4S chk4 12 5 [false, true, true, false, true, false, false, true]
          (s4S chk4 11 5 [true, false, true, true, false, true, false, false, true]
           (s4S chk4 10 5 [true, true, false, true, true, false, true, false, false, true]
            dTFFTFTTFTTT
            dTFFTFTTFTTF)
           (s4S chk4 10 4 [false, true, false, true, true, false, true, false, false, true]
            dTFFTFTTFTFT
            dTFFTFTTFTFF))
          (s4S chk4 11 4 [false, false, true, true, false, true, false, false, true]
           (s4S chk4 10 4 [true, false, false, true, true, false, true, false, false, true]
            dTFFTFTTFFTT
            dTFFTFTTFFTF)
           (s4S chk4 10 3 [false, false, false, true, true, false, true, false, false, true]
            dTFFTFTTFFFT
            dTFFTFTTFFFF))))
        (s4S chk4 13 5 [false, true, false, true, false, false, true]
         (s4S chk4 12 5 [true, false, true, false, true, false, false, true]
          (s4S chk4 11 5 [true, true, false, true, false, true, false, false, true]
           (s4S chk4 10 5 [true, true, true, false, true, false, true, false, false, true]
            dTFFTFTFTTTT
            dTFFTFTFTTTF)
           (s4S chk4 10 4 [false, true, true, false, true, false, true, false, false, true]
            dTFFTFTFTTFT
            dTFFTFTFTTFF))
          (s4S chk4 11 4 [false, true, false, true, false, true, false, false, true]
           (s4S chk4 10 4 [true, false, true, false, true, false, true, false, false, true]
            dTFFTFTFTFTT
            dTFFTFTFTFTF)
           (s4S chk4 10 3 [false, false, true, false, true, false, true, false, false, true]
            dTFFTFTFTFFT
            dTFFTFTFTFFF)))
         (s4S chk4 12 4 [false, false, true, false, true, false, false, true]
          (s4S chk4 11 4 [true, false, false, true, false, true, false, false, true]
           (s4S chk4 10 4 [true, true, false, false, true, false, true, false, false, true]
            dTFFTFTFFTTT
            dTFFTFTFFTTF)
           (s4S chk4 10 3 [false, true, false, false, true, false, true, false, false, true]
            dTFFTFTFFTFT
            dTFFTFTFFTFF))
          (s4S chk4 11 3 [false, false, false, true, false, true, false, false, true]
           (s4S chk4 10 3 [true, false, false, false, true, false, true, false, false, true]
            dTFFTFTFFFTT
            dTFFTFTFFFTF)
           (s4S chk4 10 2 [false, false, false, false, true, false, true, false, false, true]
            dTFFTFTFFFFT
            dTFFTFTFFFFF)))))
       (s4S chk4 14 5 [false, false, true, false, false, true]
        (s4S chk4 13 5 [true, false, false, true, false, false, true]
         (s4S chk4 12 5 [true, true, false, false, true, false, false, true]
          (s4S chk4 11 5 [true, true, true, false, false, true, false, false, true]
           (s4S chk4 10 5 [true, true, true, true, false, false, true, false, false, true]
            dTFFTFFTTTTT
            dTFFTFFTTTTF)
           (s4S chk4 10 4 [false, true, true, true, false, false, true, false, false, true]
            dTFFTFFTTTFT
            dTFFTFFTTTFF))
          (s4S chk4 11 4 [false, true, true, false, false, true, false, false, true]
           (s4S chk4 10 4 [true, false, true, true, false, false, true, false, false, true]
            dTFFTFFTTFTT
            dTFFTFFTTFTF)
           (s4S chk4 10 3 [false, false, true, true, false, false, true, false, false, true]
            dTFFTFFTTFFT
            dTFFTFFTTFFF)))
         (s4S chk4 12 4 [false, true, false, false, true, false, false, true]
          (s4S chk4 11 4 [true, false, true, false, false, true, false, false, true]
           (s4S chk4 10 4 [true, true, false, true, false, false, true, false, false, true]
            dTFFTFFTFTTT
            dTFFTFFTFTTF)
           (s4S chk4 10 3 [false, true, false, true, false, false, true, false, false, true]
            dTFFTFFTFTFT
            dTFFTFFTFTFF))
          (s4S chk4 11 3 [false, false, true, false, false, true, false, false, true]
           (s4S chk4 10 3 [true, false, false, true, false, false, true, false, false, true]
            dTFFTFFTFFTT
            dTFFTFFTFFTF)
           (s4S chk4 10 2 [false, false, false, true, false, false, true, false, false, true]
            dTFFTFFTFFFT
            dTFFTFFTFFFF))))
        (s4S chk4 13 4 [false, false, false, true, false, false, true]
         (s4S chk4 12 4 [true, false, false, false, true, false, false, true]
          (s4S chk4 11 4 [true, true, false, false, false, true, false, false, true]
           (s4S chk4 10 4 [true, true, true, false, false, false, true, false, false, true]
            dTFFTFFFTTTT
            dTFFTFFFTTTF)
           (s4S chk4 10 3 [false, true, true, false, false, false, true, false, false, true]
            dTFFTFFFTTFT
            dTFFTFFFTTFF))
          (s4S chk4 11 3 [false, true, false, false, false, true, false, false, true]
           (s4S chk4 10 3 [true, false, true, false, false, false, true, false, false, true]
            dTFFTFFFTFTT
            dTFFTFFFTFTF)
           (s4S chk4 10 2 [false, false, true, false, false, false, true, false, false, true]
            dTFFTFFFTFFT
            dTFFTFFFTFFF)))
         (s4S chk4 12 3 [false, false, false, false, true, false, false, true]
          (s4S chk4 11 3 [true, false, false, false, false, true, false, false, true]
           (s4S chk4 10 3 [true, true, false, false, false, false, true, false, false, true]
            dTFFTFFFFTTT
            dTFFTFFFFTTF)
           (s4S chk4 10 2 [false, true, false, false, false, false, true, false, false, true]
            dTFFTFFFFTFT
            dTFFTFFFFTFF))
          (s4S chk4 11 2 [false, false, false, false, false, true, false, false, true]
           (s4S chk4 10 2 [true, false, false, false, false, false, true, false, false, true]
            dTFFTFFFFFTT
            dTFFTFFFFFTF)
           (s4S chk4 10 1 [false, false, false, false, false, false, true, false, false, true]
            dTFFTFFFFFFT
            dTFFTFFFFFFF)))))))
     (s4S chk4 16 6 [false, false, false, true]
      (s4S chk4 15 6 [true, false, false, false, true]
       (s4S chk4 14 6 [true, true, false, false, false, true]
        (s4S chk4 13 6 [true, true, true, false, false, false, true]
         (s4S chk4 12 6 [true, true, true, true, false, false, false, true]
          (s4S chk4 11 6 [true, true, true, true, true, false, false, false, true]
           (s4S chk4 10 6 [true, true, true, true, true, true, false, false, false, true]
            dTFFFTTTTTTT
            dTFFFTTTTTTF)
           (s4S chk4 10 5 [false, true, true, true, true, true, false, false, false, true]
            dTFFFTTTTTFT
            dTFFFTTTTTFF))
          (s4S chk4 11 5 [false, true, true, true, true, false, false, false, true]
           (s4S chk4 10 5 [true, false, true, true, true, true, false, false, false, true]
            dTFFFTTTTFTT
            dTFFFTTTTFTF)
           (s4S chk4 10 4 [false, false, true, true, true, true, false, false, false, true]
            dTFFFTTTTFFT
            dTFFFTTTTFFF)))
         (s4S chk4 12 5 [false, true, true, true, false, false, false, true]
          (s4S chk4 11 5 [true, false, true, true, true, false, false, false, true]
           (s4S chk4 10 5 [true, true, false, true, true, true, false, false, false, true]
            dTFFFTTTFTTT
            dTFFFTTTFTTF)
           (s4S chk4 10 4 [false, true, false, true, true, true, false, false, false, true]
            dTFFFTTTFTFT
            dTFFFTTTFTFF))
          (s4S chk4 11 4 [false, false, true, true, true, false, false, false, true]
           (s4S chk4 10 4 [true, false, false, true, true, true, false, false, false, true]
            dTFFFTTTFFTT
            dTFFFTTTFFTF)
           (s4S chk4 10 3 [false, false, false, true, true, true, false, false, false, true]
            dTFFFTTTFFFT
            dTFFFTTTFFFF))))
        (s4S chk4 13 5 [false, true, true, false, false, false, true]
         (s4S chk4 12 5 [true, false, true, true, false, false, false, true]
          (s4S chk4 11 5 [true, true, false, true, true, false, false, false, true]
           (s4S chk4 10 5 [true, true, true, false, true, true, false, false, false, true]
            dTFFFTTFTTTT
            dTFFFTTFTTTF)
           (s4S chk4 10 4 [false, true, true, false, true, true, false, false, false, true]
            dTFFFTTFTTFT
            dTFFFTTFTTFF))
          (s4S chk4 11 4 [false, true, false, true, true, false, false, false, true]
           (s4S chk4 10 4 [true, false, true, false, true, true, false, false, false, true]
            dTFFFTTFTFTT
            dTFFFTTFTFTF)
           (s4S chk4 10 3 [false, false, true, false, true, true, false, false, false, true]
            dTFFFTTFTFFT
            dTFFFTTFTFFF)))
         (s4S chk4 12 4 [false, false, true, true, false, false, false, true]
          (s4S chk4 11 4 [true, false, false, true, true, false, false, false, true]
           (s4S chk4 10 4 [true, true, false, false, true, true, false, false, false, true]
            dTFFFTTFFTTT
            dTFFFTTFFTTF)
           (s4S chk4 10 3 [false, true, false, false, true, true, false, false, false, true]
            dTFFFTTFFTFT
            dTFFFTTFFTFF))
          (s4S chk4 11 3 [false, false, false, true, true, false, false, false, true]
           (s4S chk4 10 3 [true, false, false, false, true, true, false, false, false, true]
            dTFFFTTFFFTT
            dTFFFTTFFFTF)
           (s4S chk4 10 2 [false, false, false, false, true, true, false, false, false, true]
            dTFFFTTFFFFT
            dTFFFTTFFFFF)))))
       (s4S chk4 14 5 [false, true, false, false, false, true]
        (s4S chk4 13 5 [true, false, true, false, false, false, true]
         (s4S chk4 12 5 [true, true, false, true, false, false, false, true]
          (s4S chk4 11 5 [true, true, true, false, true, false, false, false, true]
           (s4S chk4 10 5 [true, true, true, true, false, true, false, false, false, true]
            dTFFFTFTTTTT
            dTFFFTFTTTTF)
           (s4S chk4 10 4 [false, true, true, true, false, true, false, false, false, true]
            dTFFFTFTTTFT
            dTFFFTFTTTFF))
          (s4S chk4 11 4 [false, true, true, false, true, false, false, false, true]
           (s4S chk4 10 4 [true, false, true, true, false, true, false, false, false, true]
            dTFFFTFTTFTT
            dTFFFTFTTFTF)
           (s4S chk4 10 3 [false, false, true, true, false, true, false, false, false, true]
            dTFFFTFTTFFT
            dTFFFTFTTFFF)))
         (s4S chk4 12 4 [false, true, false, true, false, false, false, true]
          (s4S chk4 11 4 [true, false, true, false, true, false, false, false, true]
           (s4S chk4 10 4 [true, true, false, true, false, true, false, false, false, true]
            dTFFFTFTFTTT
            dTFFFTFTFTTF)
           (s4S chk4 10 3 [false, true, false, true, false, true, false, false, false, true]
            dTFFFTFTFTFT
            dTFFFTFTFTFF))
          (s4S chk4 11 3 [false, false, true, false, true, false, false, false, true]
           (s4S chk4 10 3 [true, false, false, true, false, true, false, false, false, true]
            dTFFFTFTFFTT
            dTFFFTFTFFTF)
           (s4S chk4 10 2 [false, false, false, true, false, true, false, false, false, true]
            dTFFFTFTFFFT
            dTFFFTFTFFFF))))
        (s4S chk4 13 4 [false, false, true, false, false, false, true]
         (s4S chk4 12 4 [true, false, false, true, false, false, false, true]
          (s4S chk4 11 4 [true, true, false, false, true, false, false, false, true]
           (s4S chk4 10 4 [true, true, true, false, false, true, false, false, false, true]
            dTFFFTFFTTTT
            dTFFFTFFTTTF)
           (s4S chk4 10 3 [false, true, true, false, false, true, false, false, false, true]
            dTFFFTFFTTFT
            dTFFFTFFTTFF))
          (s4S chk4 11 3 [false, true, false, false, true, false, false, false, true]
           (s4S chk4 10 3 [true, false, true, false, false, true, false, false, false, true]
            dTFFFTFFTFTT
            dTFFFTFFTFTF)
           (s4S chk4 10 2 [false, false, true, false, false, true, false, false, false, true]
            dTFFFTFFTFFT
            dTFFFTFFTFFF)))
         (s4S chk4 12 3 [false, false, false, true, false, false, false, true]
          (s4S chk4 11 3 [true, false, false, false, true, false, false, false, true]
           (s4S chk4 10 3 [true, true, false, false, false, true, false, false, false, true]
            dTFFFTFFFTTT
            dTFFFTFFFTTF)
           (s4S chk4 10 2 [false, true, false, false, false, true, false, false, false, true]
            dTFFFTFFFTFT
            dTFFFTFFFTFF))
          (s4S chk4 11 2 [false, false, false, false, true, false, false, false, true]
           (s4S chk4 10 2 [true, false, false, false, false, true, false, false, false, true]
            dTFFFTFFFFTT
            dTFFFTFFFFTF)
           (s4S chk4 10 1 [false, false, false, false, false, true, false, false, false, true]
            dTFFFTFFFFFT
            dTFFFTFFFFFF))))))
      (s4S chk4 15 5 [false, false, false, false, true]
       (s4S chk4 14 5 [true, false, false, false, false, true]
        (s4S chk4 13 5 [true, true, false, false, false, false, true]
         (s4S chk4 12 5 [true, true, true, false, false, false, false, true]
          (s4S chk4 11 5 [true, true, true, true, false, false, false, false, true]
           (s4S chk4 10 5 [true, true, true, true, true, false, false, false, false, true]
            dTFFFFTTTTTT
            dTFFFFTTTTTF)
           (s4S chk4 10 4 [false, true, true, true, true, false, false, false, false, true]
            dTFFFFTTTTFT
            dTFFFFTTTTFF))
          (s4S chk4 11 4 [false, true, true, true, false, false, false, false, true]
           (s4S chk4 10 4 [true, false, true, true, true, false, false, false, false, true]
            dTFFFFTTTFTT
            dTFFFFTTTFTF)
           (s4S chk4 10 3 [false, false, true, true, true, false, false, false, false, true]
            dTFFFFTTTFFT
            dTFFFFTTTFFF)))
         (s4S chk4 12 4 [false, true, true, false, false, false, false, true]
          (s4S chk4 11 4 [true, false, true, true, false, false, false, false, true]
           (s4S chk4 10 4 [true, true, false, true, true, false, false, false, false, true]
            dTFFFFTTFTTT
            dTFFFFTTFTTF)
           (s4S chk4 10 3 [false, true, false, true, true, false, false, false, false, true]
            dTFFFFTTFTFT
            dTFFFFTTFTFF))
          (s4S chk4 11 3 [false, false, true, true, false, false, false, false, true]
           (s4S chk4 10 3 [true, false, false, true, true, false, false, false, false, true]
            dTFFFFTTFFTT
            dTFFFFTTFFTF)
           (s4S chk4 10 2 [false, false, false, true, true, false, false, false, false, true]
            dTFFFFTTFFFT
            dTFFFFTTFFFF))))
        (s4S chk4 13 4 [false, true, false, false, false, false, true]
         (s4S chk4 12 4 [true, false, true, false, false, false, false, true]
          (s4S chk4 11 4 [true, true, false, true, false, false, false, false, true]
           (s4S chk4 10 4 [true, true, true, false, true, false, false, false, false, true]
            dTFFFFTFTTTT
            dTFFFFTFTTTF)
           (s4S chk4 10 3 [false, true, true, false, true, false, false, false, false, true]
            dTFFFFTFTTFT
            dTFFFFTFTTFF))
          (s4S chk4 11 3 [false, true, false, true, false, false, false, false, true]
           (s4S chk4 10 3 [true, false, true, false, true, false, false, false, false, true]
            dTFFFFTFTFTT
            dTFFFFTFTFTF)
           (s4S chk4 10 2 [false, false, true, false, true, false, false, false, false, true]
            dTFFFFTFTFFT
            dTFFFFTFTFFF)))
         (s4S chk4 12 3 [false, false, true, false, false, false, false, true]
          (s4S chk4 11 3 [true, false, false, true, false, false, false, false, true]
           (s4S chk4 10 3 [true, true, false, false, true, false, false, false, false, true]
            dTFFFFTFFTTT
            dTFFFFTFFTTF)
           (s4S chk4 10 2 [false, true, false, false, true, false, false, false, false, true]
            dTFFFFTFFTFT
            dTFFFFTFFTFF))
          (s4S chk4 11 2 [false, false, false, true, false, false, false, false, true]
           (s4S chk4 10 2 [true, false, false, false, true, false, false, false, false, true]
            dTFFFFTFFFTT
            dTFFFFTFFFTF)
           (s4S chk4 10 1 [false, false, false, false, true, false, false, false, false, true]
            dTFFFFTFFFFT
            dTFFFFTFFFFF)))))
       (s4S chk4 14 4 [false, false, false, false, false, true]
        (s4S chk4 13 4 [true, false, false, false, false, false, true]
         (s4S chk4 12 4 [true, true, false, false, false, false, false, true]
          (s4S chk4 11 4 [true, true, true, false, false, false, false, false, true]
           (s4S chk4 10 4 [true, true, true, true, false, false, false, false, false, true]
            dTFFFFFTTTTT
            dTFFFFFTTTTF)
           (s4S chk4 10 3 [false, true, true, true, false, false, false, false, false, true]
            dTFFFFFTTTFT
            dTFFFFFTTTFF))
          (s4S chk4 11 3 [false, true, true, false, false, false, false, false, true]
           (s4S chk4 10 3 [true, false, true, true, false, false, false, false, false, true]
            dTFFFFFTTFTT
            dTFFFFFTTFTF)
           (s4S chk4 10 2 [false, false, true, true, false, false, false, false, false, true]
            dTFFFFFTTFFT
            dTFFFFFTTFFF)))
         (s4S chk4 12 3 [false, true, false, false, false, false, false, true]
          (s4S chk4 11 3 [true, false, true, false, false, false, false, false, true]
           (s4S chk4 10 3 [true, true, false, true, false, false, false, false, false, true]
            dTFFFFFTFTTT
            dTFFFFFTFTTF)
           (s4S chk4 10 2 [false, true, false, true, false, false, false, false, false, true]
            dTFFFFFTFTFT
            dTFFFFFTFTFF))
          (s4S chk4 11 2 [false, false, true, false, false, false, false, false, true]
           (s4S chk4 10 2 [true, false, false, true, false, false, false, false, false, true]
            dTFFFFFTFFTT
            dTFFFFFTFFTF)
           (s4S chk4 10 1 [false, false, false, true, false, false, false, false, false, true]
            dTFFFFFTFFFT
            dTFFFFFTFFFF))))
        (s4S chk4 13 3 [false, false, false, false, false, false, true]
         (s4S chk4 12 3 [true, false, false, false, false, false, false, true]
          (s4S chk4 11 3 [true, true, false, false, false, false, false, false, true]
           (s4S chk4 10 3 [true, true, true, false, false, false, false, false, false, true]
            dTFFFFFFTTTT
            dTFFFFFFTTTF)
           (s4S chk4 10 2 [false, true, true, false, false, false, false, false, false, true]
            dTFFFFFFTTFT
            dTFFFFFFTTFF))
          (s4S chk4 11 2 [false, true, false, false, false, false, false, false, true]
           (s4S chk4 10 2 [true, false, true, false, false, false, false, false, false, true]
            dTFFFFFFTFTT
            dTFFFFFFTFTF)
           (s4S chk4 10 1 [false, false, true, false, false, false, false, false, false, true]
            dTFFFFFFTFFT
            dTFFFFFFTFFF)))
         (s4S chk4 12 2 [false, false, false, false, false, false, false, true]
          (s4S chk4 11 2 [true, false, false, false, false, false, false, false, true]
           (s4S chk4 10 2 [true, true, false, false, false, false, false, false, false, true]
            dTFFFFFFFTTT
            dTFFFFFFFTTF)
           (s4S chk4 10 1 [false, true, false, false, false, false, false, false, false, true]
            dTFFFFFFFTFT
            dTFFFFFFFTFF))
          (s4S chk4 11 1 [false, false, false, false, false, false, false, false, true]
           (s4S chk4 10 1 [true, false, false, false, false, false, false, false, false, true]
            dTFFFFFFFFTT
            dTFFFFFFFFTF)
           (s4S chk4 10 0 [false, false, false, false, false, false, false, false, false, true]
            dTFFFFFFFFFT
            dTFFFFFFFFFF))))))))))
  (s4S chk4 19 8 [false]
   (s4S chk4 18 8 [true, false]
    (s4S chk4 17 8 [true, true, false]
     (s4S chk4 16 8 [true, true, true, false]
      (s4S chk4 15 8 [true, true, true, true, false]
       (s4S chk4 14 8 [true, true, true, true, true, false]
        (s4S chk4 13 8 [true, true, true, true, true, true, false]
         (s4S chk4 12 8 [true, true, true, true, true, true, true, false]
          (s4S chk4 11 8 [true, true, true, true, true, true, true, true, false]
           (s4S chk4 10 8 [true, true, true, true, true, true, true, true, true, false]
            dFTTTTTTTTTT
            dFTTTTTTTTTF)
           (s4S chk4 10 7 [false, true, true, true, true, true, true, true, true, false]
            dFTTTTTTTTFT
            dFTTTTTTTTFF))
          (s4S chk4 11 7 [false, true, true, true, true, true, true, true, false]
           (s4S chk4 10 7 [true, false, true, true, true, true, true, true, true, false]
            dFTTTTTTTFTT
            dFTTTTTTTFTF)
           (s4S chk4 10 6 [false, false, true, true, true, true, true, true, true, false]
            dFTTTTTTTFFT
            dFTTTTTTTFFF)))
         (s4S chk4 12 7 [false, true, true, true, true, true, true, false]
          (s4S chk4 11 7 [true, false, true, true, true, true, true, true, false]
           (s4S chk4 10 7 [true, true, false, true, true, true, true, true, true, false]
            dFTTTTTTFTTT
            dFTTTTTTFTTF)
           (s4S chk4 10 6 [false, true, false, true, true, true, true, true, true, false]
            dFTTTTTTFTFT
            dFTTTTTTFTFF))
          (s4S chk4 11 6 [false, false, true, true, true, true, true, true, false]
           (s4S chk4 10 6 [true, false, false, true, true, true, true, true, true, false]
            dFTTTTTTFFTT
            dFTTTTTTFFTF)
           (s4S chk4 10 5 [false, false, false, true, true, true, true, true, true, false]
            dFTTTTTTFFFT
            dFTTTTTTFFFF))))
        (s4S chk4 13 7 [false, true, true, true, true, true, false]
         (s4S chk4 12 7 [true, false, true, true, true, true, true, false]
          (s4S chk4 11 7 [true, true, false, true, true, true, true, true, false]
           (s4S chk4 10 7 [true, true, true, false, true, true, true, true, true, false]
            dFTTTTTFTTTT
            dFTTTTTFTTTF)
           (s4S chk4 10 6 [false, true, true, false, true, true, true, true, true, false]
            dFTTTTTFTTFT
            dFTTTTTFTTFF))
          (s4S chk4 11 6 [false, true, false, true, true, true, true, true, false]
           (s4S chk4 10 6 [true, false, true, false, true, true, true, true, true, false]
            dFTTTTTFTFTT
            dFTTTTTFTFTF)
           (s4S chk4 10 5 [false, false, true, false, true, true, true, true, true, false]
            dFTTTTTFTFFT
            dFTTTTTFTFFF)))
         (s4S chk4 12 6 [false, false, true, true, true, true, true, false]
          (s4S chk4 11 6 [true, false, false, true, true, true, true, true, false]
           (s4S chk4 10 6 [true, true, false, false, true, true, true, true, true, false]
            dFTTTTTFFTTT
            dFTTTTTFFTTF)
           (s4S chk4 10 5 [false, true, false, false, true, true, true, true, true, false]
            dFTTTTTFFTFT
            dFTTTTTFFTFF))
          (s4S chk4 11 5 [false, false, false, true, true, true, true, true, false]
           (s4S chk4 10 5 [true, false, false, false, true, true, true, true, true, false]
            dFTTTTTFFFTT
            dFTTTTTFFFTF)
           (s4S chk4 10 4 [false, false, false, false, true, true, true, true, true, false]
            dFTTTTTFFFFT
            dFTTTTTFFFFF)))))
       (s4S chk4 14 7 [false, true, true, true, true, false]
        (s4S chk4 13 7 [true, false, true, true, true, true, false]
         (s4S chk4 12 7 [true, true, false, true, true, true, true, false]
          (s4S chk4 11 7 [true, true, true, false, true, true, true, true, false]
           (s4S chk4 10 7 [true, true, true, true, false, true, true, true, true, false]
            dFTTTTFTTTTT
            dFTTTTFTTTTF)
           (s4S chk4 10 6 [false, true, true, true, false, true, true, true, true, false]
            dFTTTTFTTTFT
            dFTTTTFTTTFF))
          (s4S chk4 11 6 [false, true, true, false, true, true, true, true, false]
           (s4S chk4 10 6 [true, false, true, true, false, true, true, true, true, false]
            dFTTTTFTTFTT
            dFTTTTFTTFTF)
           (s4S chk4 10 5 [false, false, true, true, false, true, true, true, true, false]
            dFTTTTFTTFFT
            dFTTTTFTTFFF)))
         (s4S chk4 12 6 [false, true, false, true, true, true, true, false]
          (s4S chk4 11 6 [true, false, true, false, true, true, true, true, false]
           (s4S chk4 10 6 [true, true, false, true, false, true, true, true, true, false]
            dFTTTTFTFTTT
            dFTTTTFTFTTF)
           (s4S chk4 10 5 [false, true, false, true, false, true, true, true, true, false]
            dFTTTTFTFTFT
            dFTTTTFTFTFF))
          (s4S chk4 11 5 [false, false, true, false, true, true, true, true, false]
           (s4S chk4 10 5 [true, false, false, true, false, true, true, true, true, false]
            dFTTTTFTFFTT
            dFTTTTFTFFTF)
           (s4S chk4 10 4 [false, false, false, true, false, true, true, true, true, false]
            dFTTTTFTFFFT
            dFTTTTFTFFFF))))
        (s4S chk4 13 6 [false, false, true, true, true, true, false]
         (s4S chk4 12 6 [true, false, false, true, true, true, true, false]
          (s4S chk4 11 6 [true, true, false, false, true, true, true, true, false]
           (s4S chk4 10 6 [true, true, true, false, false, true, true, true, true, false]
            dFTTTTFFTTTT
            dFTTTTFFTTTF)
           (s4S chk4 10 5 [false, true, true, false, false, true, true, true, true, false]
            dFTTTTFFTTFT
            dFTTTTFFTTFF))
          (s4S chk4 11 5 [false, true, false, false, true, true, true, true, false]
           (s4S chk4 10 5 [true, false, true, false, false, true, true, true, true, false]
            dFTTTTFFTFTT
            dFTTTTFFTFTF)
           (s4S chk4 10 4 [false, false, true, false, false, true, true, true, true, false]
            dFTTTTFFTFFT
            dFTTTTFFTFFF)))
         (s4S chk4 12 5 [false, false, false, true, true, true, true, false]
          (s4S chk4 11 5 [true, false, false, false, true, true, true, true, false]
           (s4S chk4 10 5 [true, true, false, false, false, true, true, true, true, false]
            dFTTTTFFFTTT
            dFTTTTFFFTTF)
           (s4S chk4 10 4 [false, true, false, false, false, true, true, true, true, false]
            dFTTTTFFFTFT
            dFTTTTFFFTFF))
          (s4S chk4 11 4 [false, false, false, false, true, true, true, true, false]
           (s4S chk4 10 4 [true, false, false, false, false, true, true, true, true, false]
            dFTTTTFFFFTT
            dFTTTTFFFFTF)
           (s4S chk4 10 3 [false, false, false, false, false, true, true, true, true, false]
            dFTTTTFFFFFT
            dFTTTTFFFFFF))))))
      (s4S chk4 15 7 [false, true, true, true, false]
       (s4S chk4 14 7 [true, false, true, true, true, false]
        (s4S chk4 13 7 [true, true, false, true, true, true, false]
         (s4S chk4 12 7 [true, true, true, false, true, true, true, false]
          (s4S chk4 11 7 [true, true, true, true, false, true, true, true, false]
           (s4S chk4 10 7 [true, true, true, true, true, false, true, true, true, false]
            dFTTTFTTTTTT
            dFTTTFTTTTTF)
           (s4S chk4 10 6 [false, true, true, true, true, false, true, true, true, false]
            dFTTTFTTTTFT
            dFTTTFTTTTFF))
          (s4S chk4 11 6 [false, true, true, true, false, true, true, true, false]
           (s4S chk4 10 6 [true, false, true, true, true, false, true, true, true, false]
            dFTTTFTTTFTT
            dFTTTFTTTFTF)
           (s4S chk4 10 5 [false, false, true, true, true, false, true, true, true, false]
            dFTTTFTTTFFT
            dFTTTFTTTFFF)))
         (s4S chk4 12 6 [false, true, true, false, true, true, true, false]
          (s4S chk4 11 6 [true, false, true, true, false, true, true, true, false]
           (s4S chk4 10 6 [true, true, false, true, true, false, true, true, true, false]
            dFTTTFTTFTTT
            dFTTTFTTFTTF)
           (s4S chk4 10 5 [false, true, false, true, true, false, true, true, true, false]
            dFTTTFTTFTFT
            dFTTTFTTFTFF))
          (s4S chk4 11 5 [false, false, true, true, false, true, true, true, false]
           (s4S chk4 10 5 [true, false, false, true, true, false, true, true, true, false]
            dFTTTFTTFFTT
            dFTTTFTTFFTF)
           (s4S chk4 10 4 [false, false, false, true, true, false, true, true, true, false]
            dFTTTFTTFFFT
            dFTTTFTTFFFF))))
        (s4S chk4 13 6 [false, true, false, true, true, true, false]
         (s4S chk4 12 6 [true, false, true, false, true, true, true, false]
          (s4S chk4 11 6 [true, true, false, true, false, true, true, true, false]
           (s4S chk4 10 6 [true, true, true, false, true, false, true, true, true, false]
            dFTTTFTFTTTT
            dFTTTFTFTTTF)
           (s4S chk4 10 5 [false, true, true, false, true, false, true, true, true, false]
            dFTTTFTFTTFT
            dFTTTFTFTTFF))
          (s4S chk4 11 5 [false, true, false, true, false, true, true, true, false]
           (s4S chk4 10 5 [true, false, true, false, true, false, true, true, true, false]
            dFTTTFTFTFTT
            dFTTTFTFTFTF)
           (s4S chk4 10 4 [false, false, true, false, true, false, true, true, true, false]
            dFTTTFTFTFFT
            dFTTTFTFTFFF)))
         (s4S chk4 12 5 [false, false, true, false, true, true, true, false]
          (s4S chk4 11 5 [true, false, false, true, false, true, true, true, false]
           (s4S chk4 10 5 [true, true, false, false, true, false, true, true, true, false]
            dFTTTFTFFTTT
            dFTTTFTFFTTF)
           (s4S chk4 10 4 [false, true, false, false, true, false, true, true, true, false]
            dFTTTFTFFTFT
            dFTTTFTFFTFF))
          (s4S chk4 11 4 [false, false, false, true, false, true, true, true, false]
           (s4S chk4 10 4 [true, false, false, false, true, false, true, true, true, false]
            dFTTTFTFFFTT
            dFTTTFTFFFTF)
           (s4S chk4 10 3 [false, false, false, false, true, false, true, true, true, false]
            dFTTTFTFFFFT
            dFTTTFTFFFFF)))))
       (s4S chk4 14 6 [false, false, true, true, true, false]
        (s4S chk4 13 6 [true, false, false, true, true, true, false]
         (s4S chk4 12 6 [true, true, false, false, true, true, true, false]
          (s4S chk4 11 6 [true, true, true, false, false, true, true, true, false]
           (s4S chk4 10 6 [true, true, true, true, false, false, true, true, true, false]
            dFTTTFFTTTTT
            dFTTTFFTTTTF)
           (s4S chk4 10 5 [false, true, true, true, false, false, true, true, true, false]
            dFTTTFFTTTFT
            dFTTTFFTTTFF))
          (s4S chk4 11 5 [false, true, true, false, false, true, true, true, false]
           (s4S chk4 10 5 [true, false, true, true, false, false, true, true, true, false]
            dFTTTFFTTFTT
            dFTTTFFTTFTF)
           (s4S chk4 10 4 [false, false, true, true, false, false, true, true, true, false]
            dFTTTFFTTFFT
            dFTTTFFTTFFF)))
         (s4S chk4 12 5 [false, true, false, false, true, true, true, false]
          (s4S chk4 11 5 [true, false, true, false, false, true, true, true, false]
           (s4S chk4 10 5 [true, true, false, true, false, false, true, true, true, false]
            dFTTTFFTFTTT
            dFTTTFFTFTTF)
           (s4S chk4 10 4 [false, true, false, true, false, false, true, true, true, false]
            dFTTTFFTFTFT
            dFTTTFFTFTFF))
          (s4S chk4 11 4 [false, false, true, false, false, true, true, true, false]
           (s4S chk4 10 4 [true, false, false, true, false, false, true, true, true, false]
            dFTTTFFTFFTT
            dFTTTFFTFFTF)
           (s4S chk4 10 3 [false, false, false, true, false, false, true, true, true, false]
            dFTTTFFTFFFT
            dFTTTFFTFFFF))))
        (s4S chk4 13 5 [false, false, false, true, true, true, false]
         (s4S chk4 12 5 [true, false, false, false, true, true, true, false]
          (s4S chk4 11 5 [true, true, false, false, false, true, true, true, false]
           (s4S chk4 10 5 [true, true, true, false, false, false, true, true, true, false]
            dFTTTFFFTTTT
            dFTTTFFFTTTF)
           (s4S chk4 10 4 [false, true, true, false, false, false, true, true, true, false]
            dFTTTFFFTTFT
            dFTTTFFFTTFF))
          (s4S chk4 11 4 [false, true, false, false, false, true, true, true, false]
           (s4S chk4 10 4 [true, false, true, false, false, false, true, true, true, false]
            dFTTTFFFTFTT
            dFTTTFFFTFTF)
           (s4S chk4 10 3 [false, false, true, false, false, false, true, true, true, false]
            dFTTTFFFTFFT
            dFTTTFFFTFFF)))
         (s4S chk4 12 4 [false, false, false, false, true, true, true, false]
          (s4S chk4 11 4 [true, false, false, false, false, true, true, true, false]
           (s4S chk4 10 4 [true, true, false, false, false, false, true, true, true, false]
            dFTTTFFFFTTT
            dFTTTFFFFTTF)
           (s4S chk4 10 3 [false, true, false, false, false, false, true, true, true, false]
            dFTTTFFFFTFT
            dFTTTFFFFTFF))
          (s4S chk4 11 3 [false, false, false, false, false, true, true, true, false]
           (s4S chk4 10 3 [true, false, false, false, false, false, true, true, true, false]
            dFTTTFFFFFTT
            dFTTTFFFFFTF)
           (s4S chk4 10 2 [false, false, false, false, false, false, true, true, true, false]
            dFTTTFFFFFFT
            dFTTTFFFFFFF)))))))
     (s4S chk4 16 7 [false, true, true, false]
      (s4S chk4 15 7 [true, false, true, true, false]
       (s4S chk4 14 7 [true, true, false, true, true, false]
        (s4S chk4 13 7 [true, true, true, false, true, true, false]
         (s4S chk4 12 7 [true, true, true, true, false, true, true, false]
          (s4S chk4 11 7 [true, true, true, true, true, false, true, true, false]
           (s4S chk4 10 7 [true, true, true, true, true, true, false, true, true, false]
            dFTTFTTTTTTT
            dFTTFTTTTTTF)
           (s4S chk4 10 6 [false, true, true, true, true, true, false, true, true, false]
            dFTTFTTTTTFT
            dFTTFTTTTTFF))
          (s4S chk4 11 6 [false, true, true, true, true, false, true, true, false]
           (s4S chk4 10 6 [true, false, true, true, true, true, false, true, true, false]
            dFTTFTTTTFTT
            dFTTFTTTTFTF)
           (s4S chk4 10 5 [false, false, true, true, true, true, false, true, true, false]
            dFTTFTTTTFFT
            dFTTFTTTTFFF)))
         (s4S chk4 12 6 [false, true, true, true, false, true, true, false]
          (s4S chk4 11 6 [true, false, true, true, true, false, true, true, false]
           (s4S chk4 10 6 [true, true, false, true, true, true, false, true, true, false]
            dFTTFTTTFTTT
            dFTTFTTTFTTF)
           (s4S chk4 10 5 [false, true, false, true, true, true, false, true, true, false]
            dFTTFTTTFTFT
            dFTTFTTTFTFF))
          (s4S chk4 11 5 [false, false, true, true, true, false, true, true, false]
           (s4S chk4 10 5 [true, false, false, true, true, true, false, true, true, false]
            dFTTFTTTFFTT
            dFTTFTTTFFTF)
           (s4S chk4 10 4 [false, false, false, true, true, true, false, true, true, false]
            dFTTFTTTFFFT
            dFTTFTTTFFFF))))
        (s4S chk4 13 6 [false, true, true, false, true, true, false]
         (s4S chk4 12 6 [true, false, true, true, false, true, true, false]
          (s4S chk4 11 6 [true, true, false, true, true, false, true, true, false]
           (s4S chk4 10 6 [true, true, true, false, true, true, false, true, true, false]
            dFTTFTTFTTTT
            dFTTFTTFTTTF)
           (s4S chk4 10 5 [false, true, true, false, true, true, false, true, true, false]
            dFTTFTTFTTFT
            dFTTFTTFTTFF))
          (s4S chk4 11 5 [false, true, false, true, true, false, true, true, false]
           (s4S chk4 10 5 [true, false, true, false, true, true, false, true, true, false]
            dFTTFTTFTFTT
            dFTTFTTFTFTF)
           (s4S chk4 10 4 [false, false, true, false, true, true, false, true, true, false]
            dFTTFTTFTFFT
            dFTTFTTFTFFF)))
         (s4S chk4 12 5 [false, false, true, true, false, true, true, false]
          (s4S chk4 11 5 [true, false, false, true, true, false, true, true, false]
           (s4S chk4 10 5 [true, true, false, false, true, true, false, true, true, false]
            dFTTFTTFFTTT
            dFTTFTTFFTTF)
           (s4S chk4 10 4 [false, true, false, false, true, true, false, true, true, false]
            dFTTFTTFFTFT
            dFTTFTTFFTFF))
          (s4S chk4 11 4 [false, false, false, true, true, false, true, true, false]
           (s4S chk4 10 4 [true, false, false, false, true, true, false, true, true, false]
            dFTTFTTFFFTT
            dFTTFTTFFFTF)
           (s4S chk4 10 3 [false, false, false, false, true, true, false, true, true, false]
            dFTTFTTFFFFT
            dFTTFTTFFFFF)))))
       (s4S chk4 14 6 [false, true, false, true, true, false]
        (s4S chk4 13 6 [true, false, true, false, true, true, false]
         (s4S chk4 12 6 [true, true, false, true, false, true, true, false]
          (s4S chk4 11 6 [true, true, true, false, true, false, true, true, false]
           (s4S chk4 10 6 [true, true, true, true, false, true, false, true, true, false]
            dFTTFTFTTTTT
            dFTTFTFTTTTF)
           (s4S chk4 10 5 [false, true, true, true, false, true, false, true, true, false]
            dFTTFTFTTTFT
            dFTTFTFTTTFF))
          (s4S chk4 11 5 [false, true, true, false, true, false, true, true, false]
           (s4S chk4 10 5 [true, false, true, true, false, true, false, true, true, false]
            dFTTFTFTTFTT
            dFTTFTFTTFTF)
           (s4S chk4 10 4 [false, false, true, true, false, true, false, true, true, false]
            dFTTFTFTTFFT
            dFTTFTFTTFFF)))
         (s4S chk4 12 5 [false, true, false, true, false, true, true, false]
          (s4S chk4 11 5 [true, false, true, false, true, false, true, true, false]
           (s4S chk4 10 5 [true, true, false, true, false, true, false, true, true, false]
            dFTTFTFTFTTT
            dFTTFTFTFTTF)
           (s4S chk4 10 4 [false, true, false, true, false, true, false, true, true, false]
            dFTTFTFTFTFT
            dFTTFTFTFTFF))
          (s4S chk4 11 4 [false, false, true, false, true, false, true, true, false]
           (s4S chk4 10 4 [true, false, false, true, false, true, false, true, true, false]
            dFTTFTFTFFTT
            dFTTFTFTFFTF)
           (s4S chk4 10 3 [false, false, false, true, false, true, false, true, true, false]
            dFTTFTFTFFFT
            dFTTFTFTFFFF))))
        (s4S chk4 13 5 [false, false, true, false, true, true, false]
         (s4S chk4 12 5 [true, false, false, true, false, true, true, false]
          (s4S chk4 11 5 [true, true, false, false, true, false, true, true, false]
           (s4S chk4 10 5 [true, true, true, false, false, true, false, true, true, false]
            dFTTFTFFTTTT
            dFTTFTFFTTTF)
           (s4S chk4 10 4 [false, true, true, false, false, true, false, true, true, false]
            dFTTFTFFTTFT
            dFTTFTFFTTFF))
          (s4S chk4 11 4 [false, true, false, false, true, false, true, true, false]
           (s4S chk4 10 4 [true, false, true, false, false, true, false, true, true, false]
            dFTTFTFFTFTT
            dFTTFTFFTFTF)
           (s4S chk4 10 3 [false, false, true, false, false, true, false, true, true, false]
            dFTTFTFFTFFT
            dFTTFTFFTFFF)))
         (s4S chk4 12 4 [false, false, false, true, false, true, true, false]
          (s4S chk4 11 4 [true, false, false, false, true, false, true, true, false]
           (s4S chk4 10 4 [true, true, false, false, false, true, false, true, true, false]
            dFTTFTFFFTTT
            dFTTFTFFFTTF)
           (s4S chk4 10 3 [false, true, false, false, false, true, false, true, true, false]
            dFTTFTFFFTFT
            dFTTFTFFFTFF))
          (s4S chk4 11 3 [false, false, false, false, true, false, true, true, false]
           (s4S chk4 10 3 [true, false, false, false, false, true, false, true, true, false]
            dFTTFTFFFFTT
            dFTTFTFFFFTF)
           (s4S chk4 10 2 [false, false, false, false, false, true, false, true, true, false]
            dFTTFTFFFFFT
            dFTTFTFFFFFF))))))
      (s4S chk4 15 6 [false, false, true, true, false]
       (s4S chk4 14 6 [true, false, false, true, true, false]
        (s4S chk4 13 6 [true, true, false, false, true, true, false]
         (s4S chk4 12 6 [true, true, true, false, false, true, true, false]
          (s4S chk4 11 6 [true, true, true, true, false, false, true, true, false]
           (s4S chk4 10 6 [true, true, true, true, true, false, false, true, true, false]
            dFTTFFTTTTTT
            dFTTFFTTTTTF)
           (s4S chk4 10 5 [false, true, true, true, true, false, false, true, true, false]
            dFTTFFTTTTFT
            dFTTFFTTTTFF))
          (s4S chk4 11 5 [false, true, true, true, false, false, true, true, false]
           (s4S chk4 10 5 [true, false, true, true, true, false, false, true, true, false]
            dFTTFFTTTFTT
            dFTTFFTTTFTF)
           (s4S chk4 10 4 [false, false, true, true, true, false, false, true, true, false]
            dFTTFFTTTFFT
            dFTTFFTTTFFF)))
         (s4S chk4 12 5 [false, true, true, false, false, true, true, false]
          (s4S chk4 11 5 [true, false, true, true, false, false, true, true, false]
           (s4S chk4 10 5 [true, true, false, true, true, false, false, true, true, false]
            dFTTFFTTFTTT
            dFTTFFTTFTTF)
           (s4S chk4 10 4 [false, true, false, true, true, false, false, true, true, false]
            dFTTFFTTFTFT
            dFTTFFTTFTFF))
          (s4S chk4 11 4 [false, false, true, true, false, false, true, true, false]
           (s4S chk4 10 4 [true, false, false, true, true, false, false, true, true, false]
            dFTTFFTTFFTT
            dFTTFFTTFFTF)
           (s4S chk4 10 3 [false, false, false, true, true, false, false, true, true, false]
            dFTTFFTTFFFT
            dFTTFFTTFFFF))))
        (s4S chk4 13 5 [false, true, false, false, true, true, false]
         (s4S chk4 12 5 [true, false, true, false, false, true, true, false]
          (s4S chk4 11 5 [true, true, false, true, false, false, true, true, false]
           (s4S chk4 10 5 [true, true, true, false, true, false, false, true, true, false]
            dFTTFFTFTTTT
            dFTTFFTFTTTF)
           (s4S chk4 10 4 [false, true, true, false, true, false, false, true, true, false]
            dFTTFFTFTTFT
            dFTTFFTFTTFF))
          (s4S chk4 11 4 [false, true, false, true, false, false, true, true, false]
           (s4S chk4 10 4 [true, false, true, false, true, false, false, true, true, false]
            dFTTFFTFTFTT
            dFTTFFTFTFTF)
           (s4S chk4 10 3 [false, false, true, false, true, false, false, true, true, false]
            dFTTFFTFTFFT
            dFTTFFTFTFFF)))
         (s4S chk4 12 4 [false, false, true, false, false, true, true, false]
          (s4S chk4 11 4 [true, false, false, true, false, false, true, true, false]
           (s4S chk4 10 4 [true, true, false, false, true, false, false, true, true, false]
            dFTTFFTFFTTT
            dFTTFFTFFTTF)
           (s4S chk4 10 3 [false, true, false, false, true, false, false, true, true, false]
            dFTTFFTFFTFT
            dFTTFFTFFTFF))
          (s4S chk4 11 3 [false, false, false, true, false, false, true, true, false]
           (s4S chk4 10 3 [true, false, false, false, true, false, false, true, true, false]
            dFTTFFTFFFTT
            dFTTFFTFFFTF)
           (s4S chk4 10 2 [false, false, false, false, true, false, false, true, true, false]
            dFTTFFTFFFFT
            dFTTFFTFFFFF)))))
       (s4S chk4 14 5 [false, false, false, true, true, false]
        (s4S chk4 13 5 [true, false, false, false, true, true, false]
         (s4S chk4 12 5 [true, true, false, false, false, true, true, false]
          (s4S chk4 11 5 [true, true, true, false, false, false, true, true, false]
           (s4S chk4 10 5 [true, true, true, true, false, false, false, true, true, false]
            dFTTFFFTTTTT
            dFTTFFFTTTTF)
           (s4S chk4 10 4 [false, true, true, true, false, false, false, true, true, false]
            dFTTFFFTTTFT
            dFTTFFFTTTFF))
          (s4S chk4 11 4 [false, true, true, false, false, false, true, true, false]
           (s4S chk4 10 4 [true, false, true, true, false, false, false, true, true, false]
            dFTTFFFTTFTT
            dFTTFFFTTFTF)
           (s4S chk4 10 3 [false, false, true, true, false, false, false, true, true, false]
            dFTTFFFTTFFT
            dFTTFFFTTFFF)))
         (s4S chk4 12 4 [false, true, false, false, false, true, true, false]
          (s4S chk4 11 4 [true, false, true, false, false, false, true, true, false]
           (s4S chk4 10 4 [true, true, false, true, false, false, false, true, true, false]
            dFTTFFFTFTTT
            dFTTFFFTFTTF)
           (s4S chk4 10 3 [false, true, false, true, false, false, false, true, true, false]
            dFTTFFFTFTFT
            dFTTFFFTFTFF))
          (s4S chk4 11 3 [false, false, true, false, false, false, true, true, false]
           (s4S chk4 10 3 [true, false, false, true, false, false, false, true, true, false]
            dFTTFFFTFFTT
            dFTTFFFTFFTF)
           (s4S chk4 10 2 [false, false, false, true, false, false, false, true, true, false]
            dFTTFFFTFFFT
            dFTTFFFTFFFF))))
        (s4S chk4 13 4 [false, false, false, false, true, true, false]
         (s4S chk4 12 4 [true, false, false, false, false, true, true, false]
          (s4S chk4 11 4 [true, true, false, false, false, false, true, true, false]
           (s4S chk4 10 4 [true, true, true, false, false, false, false, true, true, false]
            dFTTFFFFTTTT
            dFTTFFFFTTTF)
           (s4S chk4 10 3 [false, true, true, false, false, false, false, true, true, false]
            dFTTFFFFTTFT
            dFTTFFFFTTFF))
          (s4S chk4 11 3 [false, true, false, false, false, false, true, true, false]
           (s4S chk4 10 3 [true, false, true, false, false, false, false, true, true, false]
            dFTTFFFFTFTT
            dFTTFFFFTFTF)
           (s4S chk4 10 2 [false, false, true, false, false, false, false, true, true, false]
            dFTTFFFFTFFT
            dFTTFFFFTFFF)))
         (s4S chk4 12 3 [false, false, false, false, false, true, true, false]
          (s4S chk4 11 3 [true, false, false, false, false, false, true, true, false]
           (s4S chk4 10 3 [true, true, false, false, false, false, false, true, true, false]
            dFTTFFFFFTTT
            dFTTFFFFFTTF)
           (s4S chk4 10 2 [false, true, false, false, false, false, false, true, true, false]
            dFTTFFFFFTFT
            dFTTFFFFFTFF))
          (s4S chk4 11 2 [false, false, false, false, false, false, true, true, false]
           (s4S chk4 10 2 [true, false, false, false, false, false, false, true, true, false]
            dFTTFFFFFFTT
            dFTTFFFFFFTF)
           (s4S chk4 10 1 [false, false, false, false, false, false, false, true, true, false]
            dFTTFFFFFFFT
            dFTTFFFFFFFF))))))))
    (s4S chk4 17 7 [false, true, false]
     (s4S chk4 16 7 [true, false, true, false]
      (s4S chk4 15 7 [true, true, false, true, false]
       (s4S chk4 14 7 [true, true, true, false, true, false]
        (s4S chk4 13 7 [true, true, true, true, false, true, false]
         (s4S chk4 12 7 [true, true, true, true, true, false, true, false]
          (s4S chk4 11 7 [true, true, true, true, true, true, false, true, false]
           (s4S chk4 10 7 [true, true, true, true, true, true, true, false, true, false]
            dFTFTTTTTTTT
            dFTFTTTTTTTF)
           (s4S chk4 10 6 [false, true, true, true, true, true, true, false, true, false]
            dFTFTTTTTTFT
            dFTFTTTTTTFF))
          (s4S chk4 11 6 [false, true, true, true, true, true, false, true, false]
           (s4S chk4 10 6 [true, false, true, true, true, true, true, false, true, false]
            dFTFTTTTTFTT
            dFTFTTTTTFTF)
           (s4S chk4 10 5 [false, false, true, true, true, true, true, false, true, false]
            dFTFTTTTTFFT
            dFTFTTTTTFFF)))
         (s4S chk4 12 6 [false, true, true, true, true, false, true, false]
          (s4S chk4 11 6 [true, false, true, true, true, true, false, true, false]
           (s4S chk4 10 6 [true, true, false, true, true, true, true, false, true, false]
            dFTFTTTTFTTT
            dFTFTTTTFTTF)
           (s4S chk4 10 5 [false, true, false, true, true, true, true, false, true, false]
            dFTFTTTTFTFT
            dFTFTTTTFTFF))
          (s4S chk4 11 5 [false, false, true, true, true, true, false, true, false]
           (s4S chk4 10 5 [true, false, false, true, true, true, true, false, true, false]
            dFTFTTTTFFTT
            dFTFTTTTFFTF)
           (s4S chk4 10 4 [false, false, false, true, true, true, true, false, true, false]
            dFTFTTTTFFFT
            dFTFTTTTFFFF))))
        (s4S chk4 13 6 [false, true, true, true, false, true, false]
         (s4S chk4 12 6 [true, false, true, true, true, false, true, false]
          (s4S chk4 11 6 [true, true, false, true, true, true, false, true, false]
           (s4S chk4 10 6 [true, true, true, false, true, true, true, false, true, false]
            dFTFTTTFTTTT
            dFTFTTTFTTTF)
           (s4S chk4 10 5 [false, true, true, false, true, true, true, false, true, false]
            dFTFTTTFTTFT
            dFTFTTTFTTFF))
          (s4S chk4 11 5 [false, true, false, true, true, true, false, true, false]
           (s4S chk4 10 5 [true, false, true, false, true, true, true, false, true, false]
            dFTFTTTFTFTT
            dFTFTTTFTFTF)
           (s4S chk4 10 4 [false, false, true, false, true, true, true, false, true, false]
            dFTFTTTFTFFT
            dFTFTTTFTFFF)))
         (s4S chk4 12 5 [false, false, true, true, true, false, true, false]
          (s4S chk4 11 5 [true, false, false, true, true, true, false, true, false]
           (s4S chk4 10 5 [true, true, false, false, true, true, true, false, true, false]
            dFTFTTTFFTTT
            dFTFTTTFFTTF)
           (s4S chk4 10 4 [false, true, false, false, true, true, true, false, true, false]
            dFTFTTTFFTFT
            dFTFTTTFFTFF))
          (s4S chk4 11 4 [false, false, false, true, true, true, false, true, false]
           (s4S chk4 10 4 [true, false, false, false, true, true, true, false, true, false]
            dFTFTTTFFFTT
            dFTFTTTFFFTF)
           (s4S chk4 10 3 [false, false, false, false, true, true, true, false, true, false]
            dFTFTTTFFFFT
            dFTFTTTFFFFF)))))
       (s4S chk4 14 6 [false, true, true, false, true, false]
        (s4S chk4 13 6 [true, false, true, true, false, true, false]
         (s4S chk4 12 6 [true, true, false, true, true, false, true, false]
          (s4S chk4 11 6 [true, true, true, false, true, true, false, true, false]
           (s4S chk4 10 6 [true, true, true, true, false, true, true, false, true, false]
            dFTFTTFTTTTT
            dFTFTTFTTTTF)
           (s4S chk4 10 5 [false, true, true, true, false, true, true, false, true, false]
            dFTFTTFTTTFT
            dFTFTTFTTTFF))
          (s4S chk4 11 5 [false, true, true, false, true, true, false, true, false]
           (s4S chk4 10 5 [true, false, true, true, false, true, true, false, true, false]
            dFTFTTFTTFTT
            dFTFTTFTTFTF)
           (s4S chk4 10 4 [false, false, true, true, false, true, true, false, true, false]
            dFTFTTFTTFFT
            dFTFTTFTTFFF)))
         (s4S chk4 12 5 [false, true, false, true, true, false, true, false]
          (s4S chk4 11 5 [true, false, true, false, true, true, false, true, false]
           (s4S chk4 10 5 [true, true, false, true, false, true, true, false, true, false]
            dFTFTTFTFTTT
            dFTFTTFTFTTF)
           (s4S chk4 10 4 [false, true, false, true, false, true, true, false, true, false]
            dFTFTTFTFTFT
            dFTFTTFTFTFF))
          (s4S chk4 11 4 [false, false, true, false, true, true, false, true, false]
           (s4S chk4 10 4 [true, false, false, true, false, true, true, false, true, false]
            dFTFTTFTFFTT
            dFTFTTFTFFTF)
           (s4S chk4 10 3 [false, false, false, true, false, true, true, false, true, false]
            dFTFTTFTFFFT
            dFTFTTFTFFFF))))
        (s4S chk4 13 5 [false, false, true, true, false, true, false]
         (s4S chk4 12 5 [true, false, false, true, true, false, true, false]
          (s4S chk4 11 5 [true, true, false, false, true, true, false, true, false]
           (s4S chk4 10 5 [true, true, true, false, false, true, true, false, true, false]
            dFTFTTFFTTTT
            dFTFTTFFTTTF)
           (s4S chk4 10 4 [false, true, true, false, false, true, true, false, true, false]
            dFTFTTFFTTFT
            dFTFTTFFTTFF))
          (s4S chk4 11 4 [false, true, false, false, true, true, false, true, false]
           (s4S chk4 10 4 [true, false, true, false, false, true, true, false, true, false]
            dFTFTTFFTFTT
            dFTFTTFFTFTF)
           (s4S chk4 10 3 [false, false, true, false, false, true, true, false, true, false]
            dFTFTTFFTFFT
            dFTFTTFFTFFF)))
         (s4S chk4 12 4 [false, false, false, true, true, false, true, false]
          (s4S chk4 11 4 [true, false, false, false, true, true, false, true, false]
           (s4S chk4 10 4 [true, true, false, false, false, true, true, false, true, false]
            dFTFTTFFFTTT
            dFTFTTFFFTTF)
           (s4S chk4 10 3 [false, true, false, false, false, true, true, false, true, false]
            dFTFTTFFFTFT
            dFTFTTFFFTFF))
          (s4S chk4 11 3 [false, false, false, false, true, true, false, true, false]
           (s4S chk4 10 3 [true, false, false, false, false, true, true, false, true, false]
            dFTFTTFFFFTT
            dFTFTTFFFFTF)
           (s4S chk4 10 2 [false, false, false, false, false, true, true, false, true, false]
            dFTFTTFFFFFT
            dFTFTTFFFFFF))))))
      (s4S chk4 15 6 [false, true, false, true, false]
       (s4S chk4 14 6 [true, false, true, false, true, false]
        (s4S chk4 13 6 [true, true, false, true, false, true, false]
         (s4S chk4 12 6 [true, true, true, false, true, false, true, false]
          (s4S chk4 11 6 [true, true, true, true, false, true, false, true, false]
           (s4S chk4 10 6 [true, true, true, true, true, false, true, false, true, false]
            dFTFTFTTTTTT
            dFTFTFTTTTTF)
           (s4S chk4 10 5 [false, true, true, true, true, false, true, false, true, false]
            dFTFTFTTTTFT
            dFTFTFTTTTFF))
          (s4S chk4 11 5 [false, true, true, true, false, true, false, true, false]
           (s4S chk4 10 5 [true, false, true, true, true, false, true, false, true, false]
            dFTFTFTTTFTT
            dFTFTFTTTFTF)
           (s4S chk4 10 4 [false, false, true, true, true, false, true, false, true, false]
            dFTFTFTTTFFT
            dFTFTFTTTFFF)))
         (s4S chk4 12 5 [false, true, true, false, true, false, true, false]
          (s4S chk4 11 5 [true, false, true, true, false, true, false, true, false]
           (s4S chk4 10 5 [true, true, false, true, true, false, true, false, true, false]
            dFTFTFTTFTTT
            dFTFTFTTFTTF)
           (s4S chk4 10 4 [false, true, false, true, true, false, true, false, true, false]
            dFTFTFTTFTFT
            dFTFTFTTFTFF))
          (s4S chk4 11 4 [false, false, true, true, false, true, false, true, false]
           (s4S chk4 10 4 [true, false, false, true, true, false, true, false, true, false]
            dFTFTFTTFFTT
            dFTFTFTTFFTF)
           (s4S chk4 10 3 [false, false, false, true, true, false, true, false, true, false]
            dFTFTFTTFFFT
            dFTFTFTTFFFF))))
        (s4S chk4 13 5 [false, true, false, true, false, true, false]
         (s4S chk4 12 5 [true, false, true, false, true, false, true, false]
          (s4S chk4 11 5 [true, true, false, true, false, true, false, true, false]
           (s4S chk4 10 5 [true, true, true, false, true, false, true, false, true, false]
            dFTFTFTFTTTT
            dFTFTFTFTTTF)
           (s4S chk4 10 4 [false, true, true, false, true, false, true, false, true, false]
            dFTFTFTFTTFT
            dFTFTFTFTTFF))
          (s4S chk4 11 4 [false, true, false, true, false, true, false, true, false]
           (s4S chk4 10 4 [true, false, true, false, true, false, true, false, true, false]
            dFTFTFTFTFTT
            dFTFTFTFTFTF)
           (s4S chk4 10 3 [false, false, true, false, true, false, true, false, true, false]
            dFTFTFTFTFFT
            dFTFTFTFTFFF)))
         (s4S chk4 12 4 [false, false, true, false, true, false, true, false]
          (s4S chk4 11 4 [true, false, false, true, false, true, false, true, false]
           (s4S chk4 10 4 [true, true, false, false, true, false, true, false, true, false]
            dFTFTFTFFTTT
            dFTFTFTFFTTF)
           (s4S chk4 10 3 [false, true, false, false, true, false, true, false, true, false]
            dFTFTFTFFTFT
            dFTFTFTFFTFF))
          (s4S chk4 11 3 [false, false, false, true, false, true, false, true, false]
           (s4S chk4 10 3 [true, false, false, false, true, false, true, false, true, false]
            dFTFTFTFFFTT
            dFTFTFTFFFTF)
           (s4S chk4 10 2 [false, false, false, false, true, false, true, false, true, false]
            dFTFTFTFFFFT
            dFTFTFTFFFFF)))))
       (s4S chk4 14 5 [false, false, true, false, true, false]
        (s4S chk4 13 5 [true, false, false, true, false, true, false]
         (s4S chk4 12 5 [true, true, false, false, true, false, true, false]
          (s4S chk4 11 5 [true, true, true, false, false, true, false, true, false]
           (s4S chk4 10 5 [true, true, true, true, false, false, true, false, true, false]
            dFTFTFFTTTTT
            dFTFTFFTTTTF)
           (s4S chk4 10 4 [false, true, true, true, false, false, true, false, true, false]
            dFTFTFFTTTFT
            dFTFTFFTTTFF))
          (s4S chk4 11 4 [false, true, true, false, false, true, false, true, false]
           (s4S chk4 10 4 [true, false, true, true, false, false, true, false, true, false]
            dFTFTFFTTFTT
            dFTFTFFTTFTF)
           (s4S chk4 10 3 [false, false, true, true, false, false, true, false, true, false]
            dFTFTFFTTFFT
            dFTFTFFTTFFF)))
         (s4S chk4 12 4 [false, true, false, false, true, false, true, false]
          (s4S chk4 11 4 [true, false, true, false, false, true, false, true, false]
           (s4S chk4 10 4 [true, true, false, true, false, false, true, false, true, false]
            dFTFTFFTFTTT
            dFTFTFFTFTTF)
           (s4S chk4 10 3 [false, true, false, true, false, false, true, false, true, false]
            dFTFTFFTFTFT
            dFTFTFFTFTFF))
          (s4S chk4 11 3 [false, false, true, false, false, true, false, true, false]
           (s4S chk4 10 3 [true, false, false, true, false, false, true, false, true, false]
            dFTFTFFTFFTT
            dFTFTFFTFFTF)
           (s4S chk4 10 2 [false, false, false, true, false, false, true, false, true, false]
            dFTFTFFTFFFT
            dFTFTFFTFFFF))))
        (s4S chk4 13 4 [false, false, false, true, false, true, false]
         (s4S chk4 12 4 [true, false, false, false, true, false, true, false]
          (s4S chk4 11 4 [true, true, false, false, false, true, false, true, false]
           (s4S chk4 10 4 [true, true, true, false, false, false, true, false, true, false]
            dFTFTFFFTTTT
            dFTFTFFFTTTF)
           (s4S chk4 10 3 [false, true, true, false, false, false, true, false, true, false]
            dFTFTFFFTTFT
            dFTFTFFFTTFF))
          (s4S chk4 11 3 [false, true, false, false, false, true, false, true, false]
           (s4S chk4 10 3 [true, false, true, false, false, false, true, false, true, false]
            dFTFTFFFTFTT
            dFTFTFFFTFTF)
           (s4S chk4 10 2 [false, false, true, false, false, false, true, false, true, false]
            dFTFTFFFTFFT
            dFTFTFFFTFFF)))
         (s4S chk4 12 3 [false, false, false, false, true, false, true, false]
          (s4S chk4 11 3 [true, false, false, false, false, true, false, true, false]
           (s4S chk4 10 3 [true, true, false, false, false, false, true, false, true, false]
            dFTFTFFFFTTT
            dFTFTFFFFTTF)
           (s4S chk4 10 2 [false, true, false, false, false, false, true, false, true, false]
            dFTFTFFFFTFT
            dFTFTFFFFTFF))
          (s4S chk4 11 2 [false, false, false, false, false, true, false, true, false]
           (s4S chk4 10 2 [true, false, false, false, false, false, true, false, true, false]
            dFTFTFFFFFTT
            dFTFTFFFFFTF)
           (s4S chk4 10 1 [false, false, false, false, false, false, true, false, true, false]
            dFTFTFFFFFFT
            dFTFTFFFFFFF)))))))
     (s4S chk4 16 6 [false, false, true, false]
      (s4S chk4 15 6 [true, false, false, true, false]
       (s4S chk4 14 6 [true, true, false, false, true, false]
        (s4S chk4 13 6 [true, true, true, false, false, true, false]
         (s4S chk4 12 6 [true, true, true, true, false, false, true, false]
          (s4S chk4 11 6 [true, true, true, true, true, false, false, true, false]
           (s4S chk4 10 6 [true, true, true, true, true, true, false, false, true, false]
            dFTFFTTTTTTT
            dFTFFTTTTTTF)
           (s4S chk4 10 5 [false, true, true, true, true, true, false, false, true, false]
            dFTFFTTTTTFT
            dFTFFTTTTTFF))
          (s4S chk4 11 5 [false, true, true, true, true, false, false, true, false]
           (s4S chk4 10 5 [true, false, true, true, true, true, false, false, true, false]
            dFTFFTTTTFTT
            dFTFFTTTTFTF)
           (s4S chk4 10 4 [false, false, true, true, true, true, false, false, true, false]
            dFTFFTTTTFFT
            dFTFFTTTTFFF)))
         (s4S chk4 12 5 [false, true, true, true, false, false, true, false]
          (s4S chk4 11 5 [true, false, true, true, true, false, false, true, false]
           (s4S chk4 10 5 [true, true, false, true, true, true, false, false, true, false]
            dFTFFTTTFTTT
            dFTFFTTTFTTF)
           (s4S chk4 10 4 [false, true, false, true, true, true, false, false, true, false]
            dFTFFTTTFTFT
            dFTFFTTTFTFF))
          (s4S chk4 11 4 [false, false, true, true, true, false, false, true, false]
           (s4S chk4 10 4 [true, false, false, true, true, true, false, false, true, false]
            dFTFFTTTFFTT
            dFTFFTTTFFTF)
           (s4S chk4 10 3 [false, false, false, true, true, true, false, false, true, false]
            dFTFFTTTFFFT
            dFTFFTTTFFFF))))
        (s4S chk4 13 5 [false, true, true, false, false, true, false]
         (s4S chk4 12 5 [true, false, true, true, false, false, true, false]
          (s4S chk4 11 5 [true, true, false, true, true, false, false, true, false]
           (s4S chk4 10 5 [true, true, true, false, true, true, false, false, true, false]
            dFTFFTTFTTTT
            dFTFFTTFTTTF)
           (s4S chk4 10 4 [false, true, true, false, true, true, false, false, true, false]
            dFTFFTTFTTFT
            dFTFFTTFTTFF))
          (s4S chk4 11 4 [false, true, false, true, true, false, false, true, false]
           (s4S chk4 10 4 [true, false, true, false, true, true, false, false, true, false]
            dFTFFTTFTFTT
            dFTFFTTFTFTF)
           (s4S chk4 10 3 [false, false, true, false, true, true, false, false, true, false]
            dFTFFTTFTFFT
            dFTFFTTFTFFF)))
         (s4S chk4 12 4 [false, false, true, true, false, false, true, false]
          (s4S chk4 11 4 [true, false, false, true, true, false, false, true, false]
           (s4S chk4 10 4 [true, true, false, false, true, true, false, false, true, false]
            dFTFFTTFFTTT
            dFTFFTTFFTTF)
           (s4S chk4 10 3 [false, true, false, false, true, true, false, false, true, false]
            dFTFFTTFFTFT
            dFTFFTTFFTFF))
          (s4S chk4 11 3 [false, false, false, true, true, false, false, true, false]
           (s4S chk4 10 3 [true, false, false, false, true, true, false, false, true, false]
            dFTFFTTFFFTT
            dFTFFTTFFFTF)
           (s4S chk4 10 2 [false, false, false, false, true, true, false, false, true, false]
            dFTFFTTFFFFT
            dFTFFTTFFFFF)))))
       (s4S chk4 14 5 [false, true, false, false, true, false]
        (s4S chk4 13 5 [true, false, true, false, false, true, false]
         (s4S chk4 12 5 [true, true, false, true, false, false, true, false]
          (s4S chk4 11 5 [true, true, true, false, true, false, false, true, false]
           (s4S chk4 10 5 [true, true, true, true, false, true, false, false, true, false]
            dFTFFTFTTTTT
            dFTFFTFTTTTF)
           (s4S chk4 10 4 [false, true, true, true, false, true, false, false, true, false]
            dFTFFTFTTTFT
            dFTFFTFTTTFF))
          (s4S chk4 11 4 [false, true, true, false, true, false, false, true, false]
           (s4S chk4 10 4 [true, false, true, true, false, true, false, false, true, false]
            dFTFFTFTTFTT
            dFTFFTFTTFTF)
           (s4S chk4 10 3 [false, false, true, true, false, true, false, false, true, false]
            dFTFFTFTTFFT
            dFTFFTFTTFFF)))
         (s4S chk4 12 4 [false, true, false, true, false, false, true, false]
          (s4S chk4 11 4 [true, false, true, false, true, false, false, true, false]
           (s4S chk4 10 4 [true, true, false, true, false, true, false, false, true, false]
            dFTFFTFTFTTT
            dFTFFTFTFTTF)
           (s4S chk4 10 3 [false, true, false, true, false, true, false, false, true, false]
            dFTFFTFTFTFT
            dFTFFTFTFTFF))
          (s4S chk4 11 3 [false, false, true, false, true, false, false, true, false]
           (s4S chk4 10 3 [true, false, false, true, false, true, false, false, true, false]
            dFTFFTFTFFTT
            dFTFFTFTFFTF)
           (s4S chk4 10 2 [false, false, false, true, false, true, false, false, true, false]
            dFTFFTFTFFFT
            dFTFFTFTFFFF))))
        (s4S chk4 13 4 [false, false, true, false, false, true, false]
         (s4S chk4 12 4 [true, false, false, true, false, false, true, false]
          (s4S chk4 11 4 [true, true, false, false, true, false, false, true, false]
           (s4S chk4 10 4 [true, true, true, false, false, true, false, false, true, false]
            dFTFFTFFTTTT
            dFTFFTFFTTTF)
           (s4S chk4 10 3 [false, true, true, false, false, true, false, false, true, false]
            dFTFFTFFTTFT
            dFTFFTFFTTFF))
          (s4S chk4 11 3 [false, true, false, false, true, false, false, true, false]
           (s4S chk4 10 3 [true, false, true, false, false, true, false, false, true, false]
            dFTFFTFFTFTT
            dFTFFTFFTFTF)
           (s4S chk4 10 2 [false, false, true, false, false, true, false, false, true, false]
            dFTFFTFFTFFT
            dFTFFTFFTFFF)))
         (s4S chk4 12 3 [false, false, false, true, false, false, true, false]
          (s4S chk4 11 3 [true, false, false, false, true, false, false, true, false]
           (s4S chk4 10 3 [true, true, false, false, false, true, false, false, true, false]
            dFTFFTFFFTTT
            dFTFFTFFFTTF)
           (s4S chk4 10 2 [false, true, false, false, false, true, false, false, true, false]
            dFTFFTFFFTFT
            dFTFFTFFFTFF))
          (s4S chk4 11 2 [false, false, false, false, true, false, false, true, false]
           (s4S chk4 10 2 [true, false, false, false, false, true, false, false, true, false]
            dFTFFTFFFFTT
            dFTFFTFFFFTF)
           (s4S chk4 10 1 [false, false, false, false, false, true, false, false, true, false]
            dFTFFTFFFFFT
            dFTFFTFFFFFF))))))
      (s4S chk4 15 5 [false, false, false, true, false]
       (s4S chk4 14 5 [true, false, false, false, true, false]
        (s4S chk4 13 5 [true, true, false, false, false, true, false]
         (s4S chk4 12 5 [true, true, true, false, false, false, true, false]
          (s4S chk4 11 5 [true, true, true, true, false, false, false, true, false]
           (s4S chk4 10 5 [true, true, true, true, true, false, false, false, true, false]
            dFTFFFTTTTTT
            dFTFFFTTTTTF)
           (s4S chk4 10 4 [false, true, true, true, true, false, false, false, true, false]
            dFTFFFTTTTFT
            dFTFFFTTTTFF))
          (s4S chk4 11 4 [false, true, true, true, false, false, false, true, false]
           (s4S chk4 10 4 [true, false, true, true, true, false, false, false, true, false]
            dFTFFFTTTFTT
            dFTFFFTTTFTF)
           (s4S chk4 10 3 [false, false, true, true, true, false, false, false, true, false]
            dFTFFFTTTFFT
            dFTFFFTTTFFF)))
         (s4S chk4 12 4 [false, true, true, false, false, false, true, false]
          (s4S chk4 11 4 [true, false, true, true, false, false, false, true, false]
           (s4S chk4 10 4 [true, true, false, true, true, false, false, false, true, false]
            dFTFFFTTFTTT
            dFTFFFTTFTTF)
           (s4S chk4 10 3 [false, true, false, true, true, false, false, false, true, false]
            dFTFFFTTFTFT
            dFTFFFTTFTFF))
          (s4S chk4 11 3 [false, false, true, true, false, false, false, true, false]
           (s4S chk4 10 3 [true, false, false, true, true, false, false, false, true, false]
            dFTFFFTTFFTT
            dFTFFFTTFFTF)
           (s4S chk4 10 2 [false, false, false, true, true, false, false, false, true, false]
            dFTFFFTTFFFT
            dFTFFFTTFFFF))))
        (s4S chk4 13 4 [false, true, false, false, false, true, false]
         (s4S chk4 12 4 [true, false, true, false, false, false, true, false]
          (s4S chk4 11 4 [true, true, false, true, false, false, false, true, false]
           (s4S chk4 10 4 [true, true, true, false, true, false, false, false, true, false]
            dFTFFFTFTTTT
            dFTFFFTFTTTF)
           (s4S chk4 10 3 [false, true, true, false, true, false, false, false, true, false]
            dFTFFFTFTTFT
            dFTFFFTFTTFF))
          (s4S chk4 11 3 [false, true, false, true, false, false, false, true, false]
           (s4S chk4 10 3 [true, false, true, false, true, false, false, false, true, false]
            dFTFFFTFTFTT
            dFTFFFTFTFTF)
           (s4S chk4 10 2 [false, false, true, false, true, false, false, false, true, false]
            dFTFFFTFTFFT
            dFTFFFTFTFFF)))
         (s4S chk4 12 3 [false, false, true, false, false, false, true, false]
          (s4S chk4 11 3 [true, false, false, true, false, false, false, true, false]
           (s4S chk4 10 3 [true, true, false, false, true, false, false, false, true, false]
            dFTFFFTFFTTT
            dFTFFFTFFTTF)
           (s4S chk4 10 2 [false, true, false, false, true, false, false, false, true, false]
            dFTFFFTFFTFT
            dFTFFFTFFTFF))
          (s4S chk4 11 2 [false, false, false, true, false, false, false, true, false]
           (s4S chk4 10 2 [true, false, false, false, true, false, false, false, true, false]
            dFTFFFTFFFTT
            dFTFFFTFFFTF)
           (s4S chk4 10 1 [false, false, false, false, true, false, false, false, true, false]
            dFTFFFTFFFFT
            dFTFFFTFFFFF)))))
       (s4S chk4 14 4 [false, false, false, false, true, false]
        (s4S chk4 13 4 [true, false, false, false, false, true, false]
         (s4S chk4 12 4 [true, true, false, false, false, false, true, false]
          (s4S chk4 11 4 [true, true, true, false, false, false, false, true, false]
           (s4S chk4 10 4 [true, true, true, true, false, false, false, false, true, false]
            dFTFFFFTTTTT
            dFTFFFFTTTTF)
           (s4S chk4 10 3 [false, true, true, true, false, false, false, false, true, false]
            dFTFFFFTTTFT
            dFTFFFFTTTFF))
          (s4S chk4 11 3 [false, true, true, false, false, false, false, true, false]
           (s4S chk4 10 3 [true, false, true, true, false, false, false, false, true, false]
            dFTFFFFTTFTT
            dFTFFFFTTFTF)
           (s4S chk4 10 2 [false, false, true, true, false, false, false, false, true, false]
            dFTFFFFTTFFT
            dFTFFFFTTFFF)))
         (s4S chk4 12 3 [false, true, false, false, false, false, true, false]
          (s4S chk4 11 3 [true, false, true, false, false, false, false, true, false]
           (s4S chk4 10 3 [true, true, false, true, false, false, false, false, true, false]
            dFTFFFFTFTTT
            dFTFFFFTFTTF)
           (s4S chk4 10 2 [false, true, false, true, false, false, false, false, true, false]
            dFTFFFFTFTFT
            dFTFFFFTFTFF))
          (s4S chk4 11 2 [false, false, true, false, false, false, false, true, false]
           (s4S chk4 10 2 [true, false, false, true, false, false, false, false, true, false]
            dFTFFFFTFFTT
            dFTFFFFTFFTF)
           (s4S chk4 10 1 [false, false, false, true, false, false, false, false, true, false]
            dFTFFFFTFFFT
            dFTFFFFTFFFF))))
        (s4S chk4 13 3 [false, false, false, false, false, true, false]
         (s4S chk4 12 3 [true, false, false, false, false, false, true, false]
          (s4S chk4 11 3 [true, true, false, false, false, false, false, true, false]
           (s4S chk4 10 3 [true, true, true, false, false, false, false, false, true, false]
            dFTFFFFFTTTT
            dFTFFFFFTTTF)
           (s4S chk4 10 2 [false, true, true, false, false, false, false, false, true, false]
            dFTFFFFFTTFT
            dFTFFFFFTTFF))
          (s4S chk4 11 2 [false, true, false, false, false, false, false, true, false]
           (s4S chk4 10 2 [true, false, true, false, false, false, false, false, true, false]
            dFTFFFFFTFTT
            dFTFFFFFTFTF)
           (s4S chk4 10 1 [false, false, true, false, false, false, false, false, true, false]
            dFTFFFFFTFFT
            dFTFFFFFTFFF)))
         (s4S chk4 12 2 [false, false, false, false, false, false, true, false]
          (s4S chk4 11 2 [true, false, false, false, false, false, false, true, false]
           (s4S chk4 10 2 [true, true, false, false, false, false, false, false, true, false]
            dFTFFFFFFTTT
            dFTFFFFFFTTF)
           (s4S chk4 10 1 [false, true, false, false, false, false, false, false, true, false]
            dFTFFFFFFTFT
            dFTFFFFFFTFF))
          (s4S chk4 11 1 [false, false, false, false, false, false, false, true, false]
           (s4S chk4 10 1 [true, false, false, false, false, false, false, false, true, false]
            dFTFFFFFFFTT
            dFTFFFFFFFTF)
           (s4S chk4 10 0 [false, false, false, false, false, false, false, false, true, false]
            dFTFFFFFFFFT
            dFTFFFFFFFFF)))))))))
   (s4S chk4 18 7 [false, false]
    (s4S chk4 17 7 [true, false, false]
     (s4S chk4 16 7 [true, true, false, false]
      (s4S chk4 15 7 [true, true, true, false, false]
       (s4S chk4 14 7 [true, true, true, true, false, false]
        (s4S chk4 13 7 [true, true, true, true, true, false, false]
         (s4S chk4 12 7 [true, true, true, true, true, true, false, false]
          (s4S chk4 11 7 [true, true, true, true, true, true, true, false, false]
           (s4S chk4 10 7 [true, true, true, true, true, true, true, true, false, false]
            dFFTTTTTTTTT
            dFFTTTTTTTTF)
           (s4S chk4 10 6 [false, true, true, true, true, true, true, true, false, false]
            dFFTTTTTTTFT
            dFFTTTTTTTFF))
          (s4S chk4 11 6 [false, true, true, true, true, true, true, false, false]
           (s4S chk4 10 6 [true, false, true, true, true, true, true, true, false, false]
            dFFTTTTTTFTT
            dFFTTTTTTFTF)
           (s4S chk4 10 5 [false, false, true, true, true, true, true, true, false, false]
            dFFTTTTTTFFT
            dFFTTTTTTFFF)))
         (s4S chk4 12 6 [false, true, true, true, true, true, false, false]
          (s4S chk4 11 6 [true, false, true, true, true, true, true, false, false]
           (s4S chk4 10 6 [true, true, false, true, true, true, true, true, false, false]
            dFFTTTTTFTTT
            dFFTTTTTFTTF)
           (s4S chk4 10 5 [false, true, false, true, true, true, true, true, false, false]
            dFFTTTTTFTFT
            dFFTTTTTFTFF))
          (s4S chk4 11 5 [false, false, true, true, true, true, true, false, false]
           (s4S chk4 10 5 [true, false, false, true, true, true, true, true, false, false]
            dFFTTTTTFFTT
            dFFTTTTTFFTF)
           (s4S chk4 10 4 [false, false, false, true, true, true, true, true, false, false]
            dFFTTTTTFFFT
            dFFTTTTTFFFF))))
        (s4S chk4 13 6 [false, true, true, true, true, false, false]
         (s4S chk4 12 6 [true, false, true, true, true, true, false, false]
          (s4S chk4 11 6 [true, true, false, true, true, true, true, false, false]
           (s4S chk4 10 6 [true, true, true, false, true, true, true, true, false, false]
            dFFTTTTFTTTT
            dFFTTTTFTTTF)
           (s4S chk4 10 5 [false, true, true, false, true, true, true, true, false, false]
            dFFTTTTFTTFT
            dFFTTTTFTTFF))
          (s4S chk4 11 5 [false, true, false, true, true, true, true, false, false]
           (s4S chk4 10 5 [true, false, true, false, true, true, true, true, false, false]
            dFFTTTTFTFTT
            dFFTTTTFTFTF)
           (s4S chk4 10 4 [false, false, true, false, true, true, true, true, false, false]
            dFFTTTTFTFFT
            dFFTTTTFTFFF)))
         (s4S chk4 12 5 [false, false, true, true, true, true, false, false]
          (s4S chk4 11 5 [true, false, false, true, true, true, true, false, false]
           (s4S chk4 10 5 [true, true, false, false, true, true, true, true, false, false]
            dFFTTTTFFTTT
            dFFTTTTFFTTF)
           (s4S chk4 10 4 [false, true, false, false, true, true, true, true, false, false]
            dFFTTTTFFTFT
            dFFTTTTFFTFF))
          (s4S chk4 11 4 [false, false, false, true, true, true, true, false, false]
           (s4S chk4 10 4 [true, false, false, false, true, true, true, true, false, false]
            dFFTTTTFFFTT
            dFFTTTTFFFTF)
           (s4S chk4 10 3 [false, false, false, false, true, true, true, true, false, false]
            dFFTTTTFFFFT
            dFFTTTTFFFFF)))))
       (s4S chk4 14 6 [false, true, true, true, false, false]
        (s4S chk4 13 6 [true, false, true, true, true, false, false]
         (s4S chk4 12 6 [true, true, false, true, true, true, false, false]
          (s4S chk4 11 6 [true, true, true, false, true, true, true, false, false]
           (s4S chk4 10 6 [true, true, true, true, false, true, true, true, false, false]
            dFFTTTFTTTTT
            dFFTTTFTTTTF)
           (s4S chk4 10 5 [false, true, true, true, false, true, true, true, false, false]
            dFFTTTFTTTFT
            dFFTTTFTTTFF))
          (s4S chk4 11 5 [false, true, true, false, true, true, true, false, false]
           (s4S chk4 10 5 [true, false, true, true, false, true, true, true, false, false]
            dFFTTTFTTFTT
            dFFTTTFTTFTF)
           (s4S chk4 10 4 [false, false, true, true, false, true, true, true, false, false]
            dFFTTTFTTFFT
            dFFTTTFTTFFF)))
         (s4S chk4 12 5 [false, true, false, true, true, true, false, false]
          (s4S chk4 11 5 [true, false, true, false, true, true, true, false, false]
           (s4S chk4 10 5 [true, true, false, true, false, true, true, true, false, false]
            dFFTTTFTFTTT
            dFFTTTFTFTTF)
           (s4S chk4 10 4 [false, true, false, true, false, true, true, true, false, false]
            dFFTTTFTFTFT
            dFFTTTFTFTFF))
          (s4S chk4 11 4 [false, false, true, false, true, true, true, false, false]
           (s4S chk4 10 4 [true, false, false, true, false, true, true, true, false, false]
            dFFTTTFTFFTT
            dFFTTTFTFFTF)
           (s4S chk4 10 3 [false, false, false, true, false, true, true, true, false, false]
            dFFTTTFTFFFT
            dFFTTTFTFFFF))))
        (s4S chk4 13 5 [false, false, true, true, true, false, false]
         (s4S chk4 12 5 [true, false, false, true, true, true, false, false]
          (s4S chk4 11 5 [true, true, false, false, true, true, true, false, false]
           (s4S chk4 10 5 [true, true, true, false, false, true, true, true, false, false]
            dFFTTTFFTTTT
            dFFTTTFFTTTF)
           (s4S chk4 10 4 [false, true, true, false, false, true, true, true, false, false]
            dFFTTTFFTTFT
            dFFTTTFFTTFF))
          (s4S chk4 11 4 [false, true, false, false, true, true, true, false, false]
           (s4S chk4 10 4 [true, false, true, false, false, true, true, true, false, false]
            dFFTTTFFTFTT
            dFFTTTFFTFTF)
           (s4S chk4 10 3 [false, false, true, false, false, true, true, true, false, false]
            dFFTTTFFTFFT
            dFFTTTFFTFFF)))
         (s4S chk4 12 4 [false, false, false, true, true, true, false, false]
          (s4S chk4 11 4 [true, false, false, false, true, true, true, false, false]
           (s4S chk4 10 4 [true, true, false, false, false, true, true, true, false, false]
            dFFTTTFFFTTT
            dFFTTTFFFTTF)
           (s4S chk4 10 3 [false, true, false, false, false, true, true, true, false, false]
            dFFTTTFFFTFT
            dFFTTTFFFTFF))
          (s4S chk4 11 3 [false, false, false, false, true, true, true, false, false]
           (s4S chk4 10 3 [true, false, false, false, false, true, true, true, false, false]
            dFFTTTFFFFTT
            dFFTTTFFFFTF)
           (s4S chk4 10 2 [false, false, false, false, false, true, true, true, false, false]
            dFFTTTFFFFFT
            dFFTTTFFFFFF))))))
      (s4S chk4 15 6 [false, true, true, false, false]
       (s4S chk4 14 6 [true, false, true, true, false, false]
        (s4S chk4 13 6 [true, true, false, true, true, false, false]
         (s4S chk4 12 6 [true, true, true, false, true, true, false, false]
          (s4S chk4 11 6 [true, true, true, true, false, true, true, false, false]
           (s4S chk4 10 6 [true, true, true, true, true, false, true, true, false, false]
            dFFTTFTTTTTT
            dFFTTFTTTTTF)
           (s4S chk4 10 5 [false, true, true, true, true, false, true, true, false, false]
            dFFTTFTTTTFT
            dFFTTFTTTTFF))
          (s4S chk4 11 5 [false, true, true, true, false, true, true, false, false]
           (s4S chk4 10 5 [true, false, true, true, true, false, true, true, false, false]
            dFFTTFTTTFTT
            dFFTTFTTTFTF)
           (s4S chk4 10 4 [false, false, true, true, true, false, true, true, false, false]
            dFFTTFTTTFFT
            dFFTTFTTTFFF)))
         (s4S chk4 12 5 [false, true, true, false, true, true, false, false]
          (s4S chk4 11 5 [true, false, true, true, false, true, true, false, false]
           (s4S chk4 10 5 [true, true, false, true, true, false, true, true, false, false]
            dFFTTFTTFTTT
            dFFTTFTTFTTF)
           (s4S chk4 10 4 [false, true, false, true, true, false, true, true, false, false]
            dFFTTFTTFTFT
            dFFTTFTTFTFF))
          (s4S chk4 11 4 [false, false, true, true, false, true, true, false, false]
           (s4S chk4 10 4 [true, false, false, true, true, false, true, true, false, false]
            dFFTTFTTFFTT
            dFFTTFTTFFTF)
           (s4S chk4 10 3 [false, false, false, true, true, false, true, true, false, false]
            dFFTTFTTFFFT
            dFFTTFTTFFFF))))
        (s4S chk4 13 5 [false, true, false, true, true, false, false]
         (s4S chk4 12 5 [true, false, true, false, true, true, false, false]
          (s4S chk4 11 5 [true, true, false, true, false, true, true, false, false]
           (s4S chk4 10 5 [true, true, true, false, true, false, true, true, false, false]
            dFFTTFTFTTTT
            dFFTTFTFTTTF)
           (s4S chk4 10 4 [false, true, true, false, true, false, true, true, false, false]
            dFFTTFTFTTFT
            dFFTTFTFTTFF))
          (s4S chk4 11 4 [false, true, false, true, false, true, true, false, false]
           (s4S chk4 10 4 [true, false, true, false, true, false, true, true, false, false]
            dFFTTFTFTFTT
            dFFTTFTFTFTF)
           (s4S chk4 10 3 [false, false, true, false, true, false, true, true, false, false]
            dFFTTFTFTFFT
            dFFTTFTFTFFF)))
         (s4S chk4 12 4 [false, false, true, false, true, true, false, false]
          (s4S chk4 11 4 [true, false, false, true, false, true, true, false, false]
           (s4S chk4 10 4 [true, true, false, false, true, false, true, true, false, false]
            dFFTTFTFFTTT
            dFFTTFTFFTTF)
           (s4S chk4 10 3 [false, true, false, false, true, false, true, true, false, false]
            dFFTTFTFFTFT
            dFFTTFTFFTFF))
          (s4S chk4 11 3 [false, false, false, true, false, true, true, false, false]
           (s4S chk4 10 3 [true, false, false, false, true, false, true, true, false, false]
            dFFTTFTFFFTT
            dFFTTFTFFFTF)
           (s4S chk4 10 2 [false, false, false, false, true, false, true, true, false, false]
            dFFTTFTFFFFT
            dFFTTFTFFFFF)))))
       (s4S chk4 14 5 [false, false, true, true, false, false]
        (s4S chk4 13 5 [true, false, false, true, true, false, false]
         (s4S chk4 12 5 [true, true, false, false, true, true, false, false]
          (s4S chk4 11 5 [true, true, true, false, false, true, true, false, false]
           (s4S chk4 10 5 [true, true, true, true, false, false, true, true, false, false]
            dFFTTFFTTTTT
            dFFTTFFTTTTF)
           (s4S chk4 10 4 [false, true, true, true, false, false, true, true, false, false]
            dFFTTFFTTTFT
            dFFTTFFTTTFF))
          (s4S chk4 11 4 [false, true, true, false, false, true, true, false, false]
           (s4S chk4 10 4 [true, false, true, true, false, false, true, true, false, false]
            dFFTTFFTTFTT
            dFFTTFFTTFTF)
           (s4S chk4 10 3 [false, false, true, true, false, false, true, true, false, false]
            dFFTTFFTTFFT
            dFFTTFFTTFFF)))
         (s4S chk4 12 4 [false, true, false, false, true, true, false, false]
          (s4S chk4 11 4 [true, false, true, false, false, true, true, false, false]
           (s4S chk4 10 4 [true, true, false, true, false, false, true, true, false, false]
            dFFTTFFTFTTT
            dFFTTFFTFTTF)
           (s4S chk4 10 3 [false, true, false, true, false, false, true, true, false, false]
            dFFTTFFTFTFT
            dFFTTFFTFTFF))
          (s4S chk4 11 3 [false, false, true, false, false, true, true, false, false]
           (s4S chk4 10 3 [true, false, false, true, false, false, true, true, false, false]
            dFFTTFFTFFTT
            dFFTTFFTFFTF)
           (s4S chk4 10 2 [false, false, false, true, false, false, true, true, false, false]
            dFFTTFFTFFFT
            dFFTTFFTFFFF))))
        (s4S chk4 13 4 [false, false, false, true, true, false, false]
         (s4S chk4 12 4 [true, false, false, false, true, true, false, false]
          (s4S chk4 11 4 [true, true, false, false, false, true, true, false, false]
           (s4S chk4 10 4 [true, true, true, false, false, false, true, true, false, false]
            dFFTTFFFTTTT
            dFFTTFFFTTTF)
           (s4S chk4 10 3 [false, true, true, false, false, false, true, true, false, false]
            dFFTTFFFTTFT
            dFFTTFFFTTFF))
          (s4S chk4 11 3 [false, true, false, false, false, true, true, false, false]
           (s4S chk4 10 3 [true, false, true, false, false, false, true, true, false, false]
            dFFTTFFFTFTT
            dFFTTFFFTFTF)
           (s4S chk4 10 2 [false, false, true, false, false, false, true, true, false, false]
            dFFTTFFFTFFT
            dFFTTFFFTFFF)))
         (s4S chk4 12 3 [false, false, false, false, true, true, false, false]
          (s4S chk4 11 3 [true, false, false, false, false, true, true, false, false]
           (s4S chk4 10 3 [true, true, false, false, false, false, true, true, false, false]
            dFFTTFFFFTTT
            dFFTTFFFFTTF)
           (s4S chk4 10 2 [false, true, false, false, false, false, true, true, false, false]
            dFFTTFFFFTFT
            dFFTTFFFFTFF))
          (s4S chk4 11 2 [false, false, false, false, false, true, true, false, false]
           (s4S chk4 10 2 [true, false, false, false, false, false, true, true, false, false]
            dFFTTFFFFFTT
            dFFTTFFFFFTF)
           (s4S chk4 10 1 [false, false, false, false, false, false, true, true, false, false]
            dFFTTFFFFFFT
            dFFTTFFFFFFF)))))))
     (s4S chk4 16 6 [false, true, false, false]
      (s4S chk4 15 6 [true, false, true, false, false]
       (s4S chk4 14 6 [true, true, false, true, false, false]
        (s4S chk4 13 6 [true, true, true, false, true, false, false]
         (s4S chk4 12 6 [true, true, true, true, false, true, false, false]
          (s4S chk4 11 6 [true, true, true, true, true, false, true, false, false]
           (s4S chk4 10 6 [true, true, true, true, true, true, false, true, false, false]
            dFFTFTTTTTTT
            dFFTFTTTTTTF)
           (s4S chk4 10 5 [false, true, true, true, true, true, false, true, false, false]
            dFFTFTTTTTFT
            dFFTFTTTTTFF))
          (s4S chk4 11 5 [false, true, true, true, true, false, true, false, false]
           (s4S chk4 10 5 [true, false, true, true, true, true, false, true, false, false]
            dFFTFTTTTFTT
            dFFTFTTTTFTF)
           (s4S chk4 10 4 [false, false, true, true, true, true, false, true, false, false]
            dFFTFTTTTFFT
            dFFTFTTTTFFF)))
         (s4S chk4 12 5 [false, true, true, true, false, true, false, false]
          (s4S chk4 11 5 [true, false, true, true, true, false, true, false, false]
           (s4S chk4 10 5 [true, true, false, true, true, true, false, true, false, false]
            dFFTFTTTFTTT
            dFFTFTTTFTTF)
           (s4S chk4 10 4 [false, true, false, true, true, true, false, true, false, false]
            dFFTFTTTFTFT
            dFFTFTTTFTFF))
          (s4S chk4 11 4 [false, false, true, true, true, false, true, false, false]
           (s4S chk4 10 4 [true, false, false, true, true, true, false, true, false, false]
            dFFTFTTTFFTT
            dFFTFTTTFFTF)
           (s4S chk4 10 3 [false, false, false, true, true, true, false, true, false, false]
            dFFTFTTTFFFT
            dFFTFTTTFFFF))))
        (s4S chk4 13 5 [false, true, true, false, true, false, false]
         (s4S chk4 12 5 [true, false, true, true, false, true, false, false]
          (s4S chk4 11 5 [true, true, false, true, true, false, true, false, false]
           (s4S chk4 10 5 [true, true, true, false, true, true, false, true, false, false]
            dFFTFTTFTTTT
            dFFTFTTFTTTF)
           (s4S chk4 10 4 [false, true, true, false, true, true, false, true, false, false]
            dFFTFTTFTTFT
            dFFTFTTFTTFF))
          (s4S chk4 11 4 [false, true, false, true, true, false, true, false, false]
           (s4S chk4 10 4 [true, false, true, false, true, true, false, true, false, false]
            dFFTFTTFTFTT
            dFFTFTTFTFTF)
           (s4S chk4 10 3 [false, false, true, false, true, true, false, true, false, false]
            dFFTFTTFTFFT
            dFFTFTTFTFFF)))
         (s4S chk4 12 4 [false, false, true, true, false, true, false, false]
          (s4S chk4 11 4 [true, false, false, true, true, false, true, false, false]
           (s4S chk4 10 4 [true, true, false, false, true, true, false, true, false, false]
            dFFTFTTFFTTT
            dFFTFTTFFTTF)
           (s4S chk4 10 3 [false, true, false, false, true, true, false, true, false, false]
            dFFTFTTFFTFT
            dFFTFTTFFTFF))
          (s4S chk4 11 3 [false, false, false, true, true, false, true, false, false]
           (s4S chk4 10 3 [true, false, false, false, true, true, false, true, false, false]
            dFFTFTTFFFTT
            dFFTFTTFFFTF)
           (s4S chk4 10 2 [false, false, false, false, true, true, false, true, false, false]
            dFFTFTTFFFFT
            dFFTFTTFFFFF)))))
       (s4S chk4 14 5 [false, true, false, true, false, false]
        (s4S chk4 13 5 [true, false, true, false, true, false, false]
         (s4S chk4 12 5 [true, true, false, true, false, true, false, false]
          (s4S chk4 11 5 [true, true, true, false, true, false, true, false, false]
           (s4S chk4 10 5 [true, true, true, true, false, true, false, true, false, false]
            dFFTFTFTTTTT
            dFFTFTFTTTTF)
           (s4S chk4 10 4 [false, true, true, true, false, true, false, true, false, false]
            dFFTFTFTTTFT
            dFFTFTFTTTFF))
          (s4S chk4 11 4 [false, true, true, false, true, false, true, false, false]
           (s4S chk4 10 4 [true, false, true, true, false, true, false, true, false, false]
            dFFTFTFTTFTT
            dFFTFTFTTFTF)
           (s4S chk4 10 3 [false, false, true, true, false, true, false, true, false, false]
            dFFTFTFTTFFT
            dFFTFTFTTFFF)))
         (s4S chk4 12 4 [false, true, false, true, false, true, false, false]
          (s4S chk4 11 4 [true, false, true, false, true, false, true, false, false]
           (s4S chk4 10 4 [true, true, false, true, false, true, false, true, false, false]
            dFFTFTFTFTTT
            dFFTFTFTFTTF)
           (s4S chk4 10 3 [false, true, false, true, false, true, false, true, false, false]
            dFFTFTFTFTFT
            dFFTFTFTFTFF))
          (s4S chk4 11 3 [false, false, true, false, true, false, true, false, false]
           (s4S chk4 10 3 [true, false, false, true, false, true, false, true, false, false]
            dFFTFTFTFFTT
            dFFTFTFTFFTF)
           (s4S chk4 10 2 [false, false, false, true, false, true, false, true, false, false]
            dFFTFTFTFFFT
            dFFTFTFTFFFF))))
        (s4S chk4 13 4 [false, false, true, false, true, false, false]
         (s4S chk4 12 4 [true, false, false, true, false, true, false, false]
          (s4S chk4 11 4 [true, true, false, false, true, false, true, false, false]
           (s4S chk4 10 4 [true, true, true, false, false, true, false, true, false, false]
            dFFTFTFFTTTT
            dFFTFTFFTTTF)
           (s4S chk4 10 3 [false, true, true, false, false, true, false, true, false, false]
            dFFTFTFFTTFT
            dFFTFTFFTTFF))
          (s4S chk4 11 3 [false, true, false, false, true, false, true, false, false]
           (s4S chk4 10 3 [true, false, true, false, false, true, false, true, false, false]
            dFFTFTFFTFTT
            dFFTFTFFTFTF)
           (s4S chk4 10 2 [false, false, true, false, false, true, false, true, false, false]
            dFFTFTFFTFFT
            dFFTFTFFTFFF)))
         (s4S chk4 12 3 [false, false, false, true, false, true, false, false]
          (s4S chk4 11 3 [true, false, false, false, true, false, true, false, false]
           (s4S chk4 10 3 [true, true, false, false, false, true, false, true, false, false]
            dFFTFTFFFTTT
            dFFTFTFFFTTF)
           (s4S chk4 10 2 [false, true, false, false, false, true, false, true, false, false]
            dFFTFTFFFTFT
            dFFTFTFFFTFF))
          (s4S chk4 11 2 [false, false, false, false, true, false, true, false, false]
           (s4S chk4 10 2 [true, false, false, false, false, true, false, true, false, false]
            dFFTFTFFFFTT
            dFFTFTFFFFTF)
           (s4S chk4 10 1 [false, false, false, false, false, true, false, true, false, false]
            dFFTFTFFFFFT
            dFFTFTFFFFFF))))))
      (s4S chk4 15 5 [false, false, true, false, false]
       (s4S chk4 14 5 [true, false, false, true, false, false]
        (s4S chk4 13 5 [true, true, false, false, true, false, false]
         (s4S chk4 12 5 [true, true, true, false, false, true, false, false]
          (s4S chk4 11 5 [true, true, true, true, false, false, true, false, false]
           (s4S chk4 10 5 [true, true, true, true, true, false, false, true, false, false]
            dFFTFFTTTTTT
            dFFTFFTTTTTF)
           (s4S chk4 10 4 [false, true, true, true, true, false, false, true, false, false]
            dFFTFFTTTTFT
            dFFTFFTTTTFF))
          (s4S chk4 11 4 [false, true, true, true, false, false, true, false, false]
           (s4S chk4 10 4 [true, false, true, true, true, false, false, true, false, false]
            dFFTFFTTTFTT
            dFFTFFTTTFTF)
           (s4S chk4 10 3 [false, false, true, true, true, false, false, true, false, false]
            dFFTFFTTTFFT
            dFFTFFTTTFFF)))
         (s4S chk4 12 4 [false, true, true, false, false, true, false, false]
          (s4S chk4 11 4 [true, false, true, true, false, false, true, false, false]
           (s4S chk4 10 4 [true, true, false, true, true, false, false, true, false, false]
            dFFTFFTTFTTT
            dFFTFFTTFTTF)
           (s4S chk4 10 3 [false, true, false, true, true, false, false, true, false, false]
            dFFTFFTTFTFT
            dFFTFFTTFTFF))
          (s4S chk4 11 3 [false, false, true, true, false, false, true, false, false]
           (s4S chk4 10 3 [true, false, false, true, true, false, false, true, false, false]
            dFFTFFTTFFTT
            dFFTFFTTFFTF)
           (s4S chk4 10 2 [false, false, false, true, true, false, false, true, false, false]
            dFFTFFTTFFFT
            dFFTFFTTFFFF))))
        (s4S chk4 13 4 [false, true, false, false, true, false, false]
         (s4S chk4 12 4 [true, false, true, false, false, true, false, false]
          (s4S chk4 11 4 [true, true, false, true, false, false, true, false, false]
           (s4S chk4 10 4 [true, true, true, false, true, false, false, true, false, false]
            dFFTFFTFTTTT
            dFFTFFTFTTTF)
           (s4S chk4 10 3 [false, true, true, false, true, false, false, true, false, false]
            dFFTFFTFTTFT
            dFFTFFTFTTFF))
          (s4S chk4 11 3 [false, true, false, true, false, false, true, false, false]
           (s4S chk4 10 3 [true, false, true, false, true, false, false, true, false, false]
            dFFTFFTFTFTT
            dFFTFFTFTFTF)
           (s4S chk4 10 2 [false, false, true, false, true, false, false, true, false, false]
            dFFTFFTFTFFT
            dFFTFFTFTFFF)))
         (s4S chk4 12 3 [false, false, true, false, false, true, false, false]
          (s4S chk4 11 3 [true, false, false, true, false, false, true, false, false]
           (s4S chk4 10 3 [true, true, false, false, true, false, false, true, false, false]
            dFFTFFTFFTTT
            dFFTFFTFFTTF)
           (s4S chk4 10 2 [false, true, false, false, true, false, false, true, false, false]
            dFFTFFTFFTFT
            dFFTFFTFFTFF))
          (s4S chk4 11 2 [false, false, false, true, false, false, true, false, false]
           (s4S chk4 10 2 [true, false, false, false, true, false, false, true, false, false]
            dFFTFFTFFFTT
            dFFTFFTFFFTF)
           (s4S chk4 10 1 [false, false, false, false, true, false, false, true, false, false]
            dFFTFFTFFFFT
            dFFTFFTFFFFF)))))
       (s4S chk4 14 4 [false, false, false, true, false, false]
        (s4S chk4 13 4 [true, false, false, false, true, false, false]
         (s4S chk4 12 4 [true, true, false, false, false, true, false, false]
          (s4S chk4 11 4 [true, true, true, false, false, false, true, false, false]
           (s4S chk4 10 4 [true, true, true, true, false, false, false, true, false, false]
            dFFTFFFTTTTT
            dFFTFFFTTTTF)
           (s4S chk4 10 3 [false, true, true, true, false, false, false, true, false, false]
            dFFTFFFTTTFT
            dFFTFFFTTTFF))
          (s4S chk4 11 3 [false, true, true, false, false, false, true, false, false]
           (s4S chk4 10 3 [true, false, true, true, false, false, false, true, false, false]
            dFFTFFFTTFTT
            dFFTFFFTTFTF)
           (s4S chk4 10 2 [false, false, true, true, false, false, false, true, false, false]
            dFFTFFFTTFFT
            dFFTFFFTTFFF)))
         (s4S chk4 12 3 [false, true, false, false, false, true, false, false]
          (s4S chk4 11 3 [true, false, true, false, false, false, true, false, false]
           (s4S chk4 10 3 [true, true, false, true, false, false, false, true, false, false]
            dFFTFFFTFTTT
            dFFTFFFTFTTF)
           (s4S chk4 10 2 [false, true, false, true, false, false, false, true, false, false]
            dFFTFFFTFTFT
            dFFTFFFTFTFF))
          (s4S chk4 11 2 [false, false, true, false, false, false, true, false, false]
           (s4S chk4 10 2 [true, false, false, true, false, false, false, true, false, false]
            dFFTFFFTFFTT
            dFFTFFFTFFTF)
           (s4S chk4 10 1 [false, false, false, true, false, false, false, true, false, false]
            dFFTFFFTFFFT
            dFFTFFFTFFFF))))
        (s4S chk4 13 3 [false, false, false, false, true, false, false]
         (s4S chk4 12 3 [true, false, false, false, false, true, false, false]
          (s4S chk4 11 3 [true, true, false, false, false, false, true, false, false]
           (s4S chk4 10 3 [true, true, true, false, false, false, false, true, false, false]
            dFFTFFFFTTTT
            dFFTFFFFTTTF)
           (s4S chk4 10 2 [false, true, true, false, false, false, false, true, false, false]
            dFFTFFFFTTFT
            dFFTFFFFTTFF))
          (s4S chk4 11 2 [false, true, false, false, false, false, true, false, false]
           (s4S chk4 10 2 [true, false, true, false, false, false, false, true, false, false]
            dFFTFFFFTFTT
            dFFTFFFFTFTF)
           (s4S chk4 10 1 [false, false, true, false, false, false, false, true, false, false]
            dFFTFFFFTFFT
            dFFTFFFFTFFF)))
         (s4S chk4 12 2 [false, false, false, false, false, true, false, false]
          (s4S chk4 11 2 [true, false, false, false, false, false, true, false, false]
           (s4S chk4 10 2 [true, true, false, false, false, false, false, true, false, false]
            dFFTFFFFFTTT
            dFFTFFFFFTTF)
           (s4S chk4 10 1 [false, true, false, false, false, false, false, true, false, false]
            dFFTFFFFFTFT
            dFFTFFFFFTFF))
          (s4S chk4 11 1 [false, false, false, false, false, false, true, false, false]
           (s4S chk4 10 1 [true, false, false, false, false, false, false, true, false, false]
            dFFTFFFFFFTT
            dFFTFFFFFFTF)
           (s4S chk4 10 0 [false, false, false, false, false, false, false, true, false, false]
            dFFTFFFFFFFT
            dFFTFFFFFFFF))))))))
    (s4S chk4 17 6 [false, false, false]
     (s4S chk4 16 6 [true, false, false, false]
      (s4S chk4 15 6 [true, true, false, false, false]
       (s4S chk4 14 6 [true, true, true, false, false, false]
        (s4S chk4 13 6 [true, true, true, true, false, false, false]
         (s4S chk4 12 6 [true, true, true, true, true, false, false, false]
          (s4S chk4 11 6 [true, true, true, true, true, true, false, false, false]
           (s4S chk4 10 6 [true, true, true, true, true, true, true, false, false, false]
            dFFFTTTTTTTT
            dFFFTTTTTTTF)
           (s4S chk4 10 5 [false, true, true, true, true, true, true, false, false, false]
            dFFFTTTTTTFT
            dFFFTTTTTTFF))
          (s4S chk4 11 5 [false, true, true, true, true, true, false, false, false]
           (s4S chk4 10 5 [true, false, true, true, true, true, true, false, false, false]
            dFFFTTTTTFTT
            dFFFTTTTTFTF)
           (s4S chk4 10 4 [false, false, true, true, true, true, true, false, false, false]
            dFFFTTTTTFFT
            dFFFTTTTTFFF)))
         (s4S chk4 12 5 [false, true, true, true, true, false, false, false]
          (s4S chk4 11 5 [true, false, true, true, true, true, false, false, false]
           (s4S chk4 10 5 [true, true, false, true, true, true, true, false, false, false]
            dFFFTTTTFTTT
            dFFFTTTTFTTF)
           (s4S chk4 10 4 [false, true, false, true, true, true, true, false, false, false]
            dFFFTTTTFTFT
            dFFFTTTTFTFF))
          (s4S chk4 11 4 [false, false, true, true, true, true, false, false, false]
           (s4S chk4 10 4 [true, false, false, true, true, true, true, false, false, false]
            dFFFTTTTFFTT
            dFFFTTTTFFTF)
           (s4S chk4 10 3 [false, false, false, true, true, true, true, false, false, false]
            dFFFTTTTFFFT
            dFFFTTTTFFFF))))
        (s4S chk4 13 5 [false, true, true, true, false, false, false]
         (s4S chk4 12 5 [true, false, true, true, true, false, false, false]
          (s4S chk4 11 5 [true, true, false, true, true, true, false, false, false]
           (s4S chk4 10 5 [true, true, true, false, true, true, true, false, false, false]
            dFFFTTTFTTTT
            dFFFTTTFTTTF)
           (s4S chk4 10 4 [false, true, true, false, true, true, true, false, false, false]
            dFFFTTTFTTFT
            dFFFTTTFTTFF))
          (s4S chk4 11 4 [false, true, false, true, true, true, false, false, false]
           (s4S chk4 10 4 [true, false, true, false, true, true, true, false, false, false]
            dFFFTTTFTFTT
            dFFFTTTFTFTF)
           (s4S chk4 10 3 [false, false, true, false, true, true, true, false, false, false]
            dFFFTTTFTFFT
            dFFFTTTFTFFF)))
         (s4S chk4 12 4 [false, false, true, true, true, false, false, false]
          (s4S chk4 11 4 [true, false, false, true, true, true, false, false, false]
           (s4S chk4 10 4 [true, true, false, false, true, true, true, false, false, false]
            dFFFTTTFFTTT
            dFFFTTTFFTTF)
           (s4S chk4 10 3 [false, true, false, false, true, true, true, false, false, false]
            dFFFTTTFFTFT
            dFFFTTTFFTFF))
          (s4S chk4 11 3 [false, false, false, true, true, true, false, false, false]
           (s4S chk4 10 3 [true, false, false, false, true, true, true, false, false, false]
            dFFFTTTFFFTT
            dFFFTTTFFFTF)
           (s4S chk4 10 2 [false, false, false, false, true, true, true, false, false, false]
            dFFFTTTFFFFT
            dFFFTTTFFFFF)))))
       (s4S chk4 14 5 [false, true, true, false, false, false]
        (s4S chk4 13 5 [true, false, true, true, false, false, false]
         (s4S chk4 12 5 [true, true, false, true, true, false, false, false]
          (s4S chk4 11 5 [true, true, true, false, true, true, false, false, false]
           (s4S chk4 10 5 [true, true, true, true, false, true, true, false, false, false]
            dFFFTTFTTTTT
            dFFFTTFTTTTF)
           (s4S chk4 10 4 [false, true, true, true, false, true, true, false, false, false]
            dFFFTTFTTTFT
            dFFFTTFTTTFF))
          (s4S chk4 11 4 [false, true, true, false, true, true, false, false, false]
           (s4S chk4 10 4 [true, false, true, true, false, true, true, false, false, false]
            dFFFTTFTTFTT
            dFFFTTFTTFTF)
           (s4S chk4 10 3 [false, false, true, true, false, true, true, false, false, false]
            dFFFTTFTTFFT
            dFFFTTFTTFFF)))
         (s4S chk4 12 4 [false, true, false, true, true, false, false, false]
          (s4S chk4 11 4 [true, false, true, false, true, true, false, false, false]
           (s4S chk4 10 4 [true, true, false, true, false, true, true, false, false, false]
            dFFFTTFTFTTT
            dFFFTTFTFTTF)
           (s4S chk4 10 3 [false, true, false, true, false, true, true, false, false, false]
            dFFFTTFTFTFT
            dFFFTTFTFTFF))
          (s4S chk4 11 3 [false, false, true, false, true, true, false, false, false]
           (s4S chk4 10 3 [true, false, false, true, false, true, true, false, false, false]
            dFFFTTFTFFTT
            dFFFTTFTFFTF)
           (s4S chk4 10 2 [false, false, false, true, false, true, true, false, false, false]
            dFFFTTFTFFFT
            dFFFTTFTFFFF))))
        (s4S chk4 13 4 [false, false, true, true, false, false, false]
         (s4S chk4 12 4 [true, false, false, true, true, false, false, false]
          (s4S chk4 11 4 [true, true, false, false, true, true, false, false, false]
           (s4S chk4 10 4 [true, true, true, false, false, true, true, false, false, false]
            dFFFTTFFTTTT
            dFFFTTFFTTTF)
           (s4S chk4 10 3 [false, true, true, false, false, true, true, false, false, false]
            dFFFTTFFTTFT
            dFFFTTFFTTFF))
          (s4S chk4 11 3 [false, true, false, false, true, true, false, false, false]
           (s4S chk4 10 3 [true, false, true, false, false, true, true, false, false, false]
            dFFFTTFFTFTT
            dFFFTTFFTFTF)
           (s4S chk4 10 2 [false, false, true, false, false, true, true, false, false, false]
            dFFFTTFFTFFT
            dFFFTTFFTFFF)))
         (s4S chk4 12 3 [false, false, false, true, true, false, false, false]
          (s4S chk4 11 3 [true, false, false, false, true, true, false, false, false]
           (s4S chk4 10 3 [true, true, false, false, false, true, true, false, false, false]
            dFFFTTFFFTTT
            dFFFTTFFFTTF)
           (s4S chk4 10 2 [false, true, false, false, false, true, true, false, false, false]
            dFFFTTFFFTFT
            dFFFTTFFFTFF))
          (s4S chk4 11 2 [false, false, false, false, true, true, false, false, false]
           (s4S chk4 10 2 [true, false, false, false, false, true, true, false, false, false]
            dFFFTTFFFFTT
            dFFFTTFFFFTF)
           (s4S chk4 10 1 [false, false, false, false, false, true, true, false, false, false]
            dFFFTTFFFFFT
            dFFFTTFFFFFF))))))
      (s4S chk4 15 5 [false, true, false, false, false]
       (s4S chk4 14 5 [true, false, true, false, false, false]
        (s4S chk4 13 5 [true, true, false, true, false, false, false]
         (s4S chk4 12 5 [true, true, true, false, true, false, false, false]
          (s4S chk4 11 5 [true, true, true, true, false, true, false, false, false]
           (s4S chk4 10 5 [true, true, true, true, true, false, true, false, false, false]
            dFFFTFTTTTTT
            dFFFTFTTTTTF)
           (s4S chk4 10 4 [false, true, true, true, true, false, true, false, false, false]
            dFFFTFTTTTFT
            dFFFTFTTTTFF))
          (s4S chk4 11 4 [false, true, true, true, false, true, false, false, false]
           (s4S chk4 10 4 [true, false, true, true, true, false, true, false, false, false]
            dFFFTFTTTFTT
            dFFFTFTTTFTF)
           (s4S chk4 10 3 [false, false, true, true, true, false, true, false, false, false]
            dFFFTFTTTFFT
            dFFFTFTTTFFF)))
         (s4S chk4 12 4 [false, true, true, false, true, false, false, false]
          (s4S chk4 11 4 [true, false, true, true, false, true, false, false, false]
           (s4S chk4 10 4 [true, true, false, true, true, false, true, false, false, false]
            dFFFTFTTFTTT
            dFFFTFTTFTTF)
           (s4S chk4 10 3 [false, true, false, true, true, false, true, false, false, false]
            dFFFTFTTFTFT
            dFFFTFTTFTFF))
          (s4S chk4 11 3 [false, false, true, true, false, true, false, false, false]
           (s4S chk4 10 3 [true, false, false, true, true, false, true, false, false, false]
            dFFFTFTTFFTT
            dFFFTFTTFFTF)
           (s4S chk4 10 2 [false, false, false, true, true, false, true, false, false, false]
            dFFFTFTTFFFT
            dFFFTFTTFFFF))))
        (s4S chk4 13 4 [false, true, false, true, false, false, false]
         (s4S chk4 12 4 [true, false, true, false, true, false, false, false]
          (s4S chk4 11 4 [true, true, false, true, false, true, false, false, false]
           (s4S chk4 10 4 [true, true, true, false, true, false, true, false, false, false]
            dFFFTFTFTTTT
            dFFFTFTFTTTF)
           (s4S chk4 10 3 [false, true, true, false, true, false, true, false, false, false]
            dFFFTFTFTTFT
            dFFFTFTFTTFF))
          (s4S chk4 11 3 [false, true, false, true, false, true, false, false, false]
           (s4S chk4 10 3 [true, false, true, false, true, false, true, false, false, false]
            dFFFTFTFTFTT
            dFFFTFTFTFTF)
           (s4S chk4 10 2 [false, false, true, false, true, false, true, false, false, false]
            dFFFTFTFTFFT
            dFFFTFTFTFFF)))
         (s4S chk4 12 3 [false, false, true, false, true, false, false, false]
          (s4S chk4 11 3 [true, false, false, true, false, true, false, false, false]
           (s4S chk4 10 3 [true, true, false, false, true, false, true, false, false, false]
            dFFFTFTFFTTT
            dFFFTFTFFTTF)
           (s4S chk4 10 2 [false, true, false, false, true, false, true, false, false, false]
            dFFFTFTFFTFT
            dFFFTFTFFTFF))
          (s4S chk4 11 2 [false, false, false, true, false, true, false, false, false]
           (s4S chk4 10 2 [true, false, false, false, true, false, true, false, false, false]
            dFFFTFTFFFTT
            dFFFTFTFFFTF)
           (s4S chk4 10 1 [false, false, false, false, true, false, true, false, false, false]
            dFFFTFTFFFFT
            dFFFTFTFFFFF)))))
       (s4S chk4 14 4 [false, false, true, false, false, false]
        (s4S chk4 13 4 [true, false, false, true, false, false, false]
         (s4S chk4 12 4 [true, true, false, false, true, false, false, false]
          (s4S chk4 11 4 [true, true, true, false, false, true, false, false, false]
           (s4S chk4 10 4 [true, true, true, true, false, false, true, false, false, false]
            dFFFTFFTTTTT
            dFFFTFFTTTTF)
           (s4S chk4 10 3 [false, true, true, true, false, false, true, false, false, false]
            dFFFTFFTTTFT
            dFFFTFFTTTFF))
          (s4S chk4 11 3 [false, true, true, false, false, true, false, false, false]
           (s4S chk4 10 3 [true, false, true, true, false, false, true, false, false, false]
            dFFFTFFTTFTT
            dFFFTFFTTFTF)
           (s4S chk4 10 2 [false, false, true, true, false, false, true, false, false, false]
            dFFFTFFTTFFT
            dFFFTFFTTFFF)))
         (s4S chk4 12 3 [false, true, false, false, true, false, false, false]
          (s4S chk4 11 3 [true, false, true, false, false, true, false, false, false]
           (s4S chk4 10 3 [true, true, false, true, false, false, true, false, false, false]
            dFFFTFFTFTTT
            dFFFTFFTFTTF)
           (s4S chk4 10 2 [false, true, false, true, false, false, true, false, false, false]
            dFFFTFFTFTFT
            dFFFTFFTFTFF))
          (s4S chk4 11 2 [false, false, true, false, false, true, false, false, false]
           (s4S chk4 10 2 [true, false, false, true, false, false, true, false, false, false]
            dFFFTFFTFFTT
            dFFFTFFTFFTF)
           (s4S chk4 10 1 [false, false, false, true, false, false, true, false, false, false]
            dFFFTFFTFFFT
            dFFFTFFTFFFF))))
        (s4S chk4 13 3 [false, false, false, true, false, false, false]
         (s4S chk4 12 3 [true, false, false, false, true, false, false, false]
          (s4S chk4 11 3 [true, true, false, false, false, true, false, false, false]
           (s4S chk4 10 3 [true, true, true, false, false, false, true, false, false, false]
            dFFFTFFFTTTT
            dFFFTFFFTTTF)
           (s4S chk4 10 2 [false, true, true, false, false, false, true, false, false, false]
            dFFFTFFFTTFT
            dFFFTFFFTTFF))
          (s4S chk4 11 2 [false, true, false, false, false, true, false, false, false]
           (s4S chk4 10 2 [true, false, true, false, false, false, true, false, false, false]
            dFFFTFFFTFTT
            dFFFTFFFTFTF)
           (s4S chk4 10 1 [false, false, true, false, false, false, true, false, false, false]
            dFFFTFFFTFFT
            dFFFTFFFTFFF)))
         (s4S chk4 12 2 [false, false, false, false, true, false, false, false]
          (s4S chk4 11 2 [true, false, false, false, false, true, false, false, false]
           (s4S chk4 10 2 [true, true, false, false, false, false, true, false, false, false]
            dFFFTFFFFTTT
            dFFFTFFFFTTF)
           (s4S chk4 10 1 [false, true, false, false, false, false, true, false, false, false]
            dFFFTFFFFTFT
            dFFFTFFFFTFF))
          (s4S chk4 11 1 [false, false, false, false, false, true, false, false, false]
           (s4S chk4 10 1 [true, false, false, false, false, false, true, false, false, false]
            dFFFTFFFFFTT
            dFFFTFFFFFTF)
           (s4S chk4 10 0 [false, false, false, false, false, false, true, false, false, false]
            dFFFTFFFFFFT
            dFFFTFFFFFFF)))))))
     (s4S chk4 16 5 [false, false, false, false]
      (s4S chk4 15 5 [true, false, false, false, false]
       (s4S chk4 14 5 [true, true, false, false, false, false]
        (s4S chk4 13 5 [true, true, true, false, false, false, false]
         (s4S chk4 12 5 [true, true, true, true, false, false, false, false]
          (s4S chk4 11 5 [true, true, true, true, true, false, false, false, false]
           (s4S chk4 10 5 [true, true, true, true, true, true, false, false, false, false]
            dFFFFTTTTTTT
            dFFFFTTTTTTF)
           (s4S chk4 10 4 [false, true, true, true, true, true, false, false, false, false]
            dFFFFTTTTTFT
            dFFFFTTTTTFF))
          (s4S chk4 11 4 [false, true, true, true, true, false, false, false, false]
           (s4S chk4 10 4 [true, false, true, true, true, true, false, false, false, false]
            dFFFFTTTTFTT
            dFFFFTTTTFTF)
           (s4S chk4 10 3 [false, false, true, true, true, true, false, false, false, false]
            dFFFFTTTTFFT
            dFFFFTTTTFFF)))
         (s4S chk4 12 4 [false, true, true, true, false, false, false, false]
          (s4S chk4 11 4 [true, false, true, true, true, false, false, false, false]
           (s4S chk4 10 4 [true, true, false, true, true, true, false, false, false, false]
            dFFFFTTTFTTT
            dFFFFTTTFTTF)
           (s4S chk4 10 3 [false, true, false, true, true, true, false, false, false, false]
            dFFFFTTTFTFT
            dFFFFTTTFTFF))
          (s4S chk4 11 3 [false, false, true, true, true, false, false, false, false]
           (s4S chk4 10 3 [true, false, false, true, true, true, false, false, false, false]
            dFFFFTTTFFTT
            dFFFFTTTFFTF)
           (s4S chk4 10 2 [false, false, false, true, true, true, false, false, false, false]
            dFFFFTTTFFFT
            dFFFFTTTFFFF))))
        (s4S chk4 13 4 [false, true, true, false, false, false, false]
         (s4S chk4 12 4 [true, false, true, true, false, false, false, false]
          (s4S chk4 11 4 [true, true, false, true, true, false, false, false, false]
           (s4S chk4 10 4 [true, true, true, false, true, true, false, false, false, false]
            dFFFFTTFTTTT
            dFFFFTTFTTTF)
           (s4S chk4 10 3 [false, true, true, false, true, true, false, false, false, false]
            dFFFFTTFTTFT
            dFFFFTTFTTFF))
          (s4S chk4 11 3 [false, true, false, true, true, false, false, false, false]
           (s4S chk4 10 3 [true, false, true, false, true, true, false, false, false, false]
            dFFFFTTFTFTT
            dFFFFTTFTFTF)
           (s4S chk4 10 2 [false, false, true, false, true, true, false, false, false, false]
            dFFFFTTFTFFT
            dFFFFTTFTFFF)))
         (s4S chk4 12 3 [false, false, true, true, false, false, false, false]
          (s4S chk4 11 3 [true, false, false, true, true, false, false, false, false]
           (s4S chk4 10 3 [true, true, false, false, true, true, false, false, false, false]
            dFFFFTTFFTTT
            dFFFFTTFFTTF)
           (s4S chk4 10 2 [false, true, false, false, true, true, false, false, false, false]
            dFFFFTTFFTFT
            dFFFFTTFFTFF))
          (s4S chk4 11 2 [false, false, false, true, true, false, false, false, false]
           (s4S chk4 10 2 [true, false, false, false, true, true, false, false, false, false]
            dFFFFTTFFFTT
            dFFFFTTFFFTF)
           (s4S chk4 10 1 [false, false, false, false, true, true, false, false, false, false]
            dFFFFTTFFFFT
            dFFFFTTFFFFF)))))
       (s4S chk4 14 4 [false, true, false, false, false, false]
        (s4S chk4 13 4 [true, false, true, false, false, false, false]
         (s4S chk4 12 4 [true, true, false, true, false, false, false, false]
          (s4S chk4 11 4 [true, true, true, false, true, false, false, false, false]
           (s4S chk4 10 4 [true, true, true, true, false, true, false, false, false, false]
            dFFFFTFTTTTT
            dFFFFTFTTTTF)
           (s4S chk4 10 3 [false, true, true, true, false, true, false, false, false, false]
            dFFFFTFTTTFT
            dFFFFTFTTTFF))
          (s4S chk4 11 3 [false, true, true, false, true, false, false, false, false]
           (s4S chk4 10 3 [true, false, true, true, false, true, false, false, false, false]
            dFFFFTFTTFTT
            dFFFFTFTTFTF)
           (s4S chk4 10 2 [false, false, true, true, false, true, false, false, false, false]
            dFFFFTFTTFFT
            dFFFFTFTTFFF)))
         (s4S chk4 12 3 [false, true, false, true, false, false, false, false]
          (s4S chk4 11 3 [true, false, true, false, true, false, false, false, false]
           (s4S chk4 10 3 [true, true, false, true, false, true, false, false, false, false]
            dFFFFTFTFTTT
            dFFFFTFTFTTF)
           (s4S chk4 10 2 [false, true, false, true, false, true, false, false, false, false]
            dFFFFTFTFTFT
            dFFFFTFTFTFF))
          (s4S chk4 11 2 [false, false, true, false, true, false, false, false, false]
           (s4S chk4 10 2 [true, false, false, true, false, true, false, false, false, false]
            dFFFFTFTFFTT
            dFFFFTFTFFTF)
           (s4S chk4 10 1 [false, false, false, true, false, true, false, false, false, false]
            dFFFFTFTFFFT
            dFFFFTFTFFFF))))
        (s4S chk4 13 3 [false, false, true, false, false, false, false]
         (s4S chk4 12 3 [true, false, false, true, false, false, false, false]
          (s4S chk4 11 3 [true, true, false, false, true, false, false, false, false]
           (s4S chk4 10 3 [true, true, true, false, false, true, false, false, false, false]
            dFFFFTFFTTTT
            dFFFFTFFTTTF)
           (s4S chk4 10 2 [false, true, true, false, false, true, false, false, false, false]
            dFFFFTFFTTFT
            dFFFFTFFTTFF))
          (s4S chk4 11 2 [false, true, false, false, true, false, false, false, false]
           (s4S chk4 10 2 [true, false, true, false, false, true, false, false, false, false]
            dFFFFTFFTFTT
            dFFFFTFFTFTF)
           (s4S chk4 10 1 [false, false, true, false, false, true, false, false, false, false]
            dFFFFTFFTFFT
            dFFFFTFFTFFF)))
         (s4S chk4 12 2 [false, false, false, true, false, false, false, false]
          (s4S chk4 11 2 [true, false, false, false, true, false, false, false, false]
           (s4S chk4 10 2 [true, true, false, false, false, true, false, false, false, false]
            dFFFFTFFFTTT
            dFFFFTFFFTTF)
           (s4S chk4 10 1 [false, true, false, false, false, true, false, false, false, false]
            dFFFFTFFFTFT
            dFFFFTFFFTFF))
          (s4S chk4 11 1 [false, false, false, false, true, false, false, false, false]
           (s4S chk4 10 1 [true, false, false, false, false, true, false, false, false, false]
            dFFFFTFFFFTT
            dFFFFTFFFFTF)
           (s4S chk4 10 0 [false, false, false, false, false, true, false, false, false, false]
            dFFFFTFFFFFT
            dFFFFTFFFFFF))))))
      (s4S chk4 15 4 [false, false, false, false, false]
       (s4S chk4 14 4 [true, false, false, false, false, false]
        (s4S chk4 13 4 [true, true, false, false, false, false, false]
         (s4S chk4 12 4 [true, true, true, false, false, false, false, false]
          (s4S chk4 11 4 [true, true, true, true, false, false, false, false, false]
           (s4S chk4 10 4 [true, true, true, true, true, false, false, false, false, false]
            dFFFFFTTTTTT
            dFFFFFTTTTTF)
           (s4S chk4 10 3 [false, true, true, true, true, false, false, false, false, false]
            dFFFFFTTTTFT
            dFFFFFTTTTFF))
          (s4S chk4 11 3 [false, true, true, true, false, false, false, false, false]
           (s4S chk4 10 3 [true, false, true, true, true, false, false, false, false, false]
            dFFFFFTTTFTT
            dFFFFFTTTFTF)
           (s4S chk4 10 2 [false, false, true, true, true, false, false, false, false, false]
            dFFFFFTTTFFT
            dFFFFFTTTFFF)))
         (s4S chk4 12 3 [false, true, true, false, false, false, false, false]
          (s4S chk4 11 3 [true, false, true, true, false, false, false, false, false]
           (s4S chk4 10 3 [true, true, false, true, true, false, false, false, false, false]
            dFFFFFTTFTTT
            dFFFFFTTFTTF)
           (s4S chk4 10 2 [false, true, false, true, true, false, false, false, false, false]
            dFFFFFTTFTFT
            dFFFFFTTFTFF))
          (s4S chk4 11 2 [false, false, true, true, false, false, false, false, false]
           (s4S chk4 10 2 [true, false, false, true, true, false, false, false, false, false]
            dFFFFFTTFFTT
            dFFFFFTTFFTF)
           (s4S chk4 10 1 [false, false, false, true, true, false, false, false, false, false]
            dFFFFFTTFFFT
            dFFFFFTTFFFF))))
        (s4S chk4 13 3 [false, true, false, false, false, false, false]
         (s4S chk4 12 3 [true, false, true, false, false, false, false, false]
          (s4S chk4 11 3 [true, true, false, true, false, false, false, false, false]
           (s4S chk4 10 3 [true, true, true, false, true, false, false, false, false, false]
            dFFFFFTFTTTT
            dFFFFFTFTTTF)
           (s4S chk4 10 2 [false, true, true, false, true, false, false, false, false, false]
            dFFFFFTFTTFT
            dFFFFFTFTTFF))
          (s4S chk4 11 2 [false, true, false, true, false, false, false, false, false]
           (s4S chk4 10 2 [true, false, true, false, true, false, false, false, false, false]
            dFFFFFTFTFTT
            dFFFFFTFTFTF)
           (s4S chk4 10 1 [false, false, true, false, true, false, false, false, false, false]
            dFFFFFTFTFFT
            dFFFFFTFTFFF)))
         (s4S chk4 12 2 [false, false, true, false, false, false, false, false]
          (s4S chk4 11 2 [true, false, false, true, false, false, false, false, false]
           (s4S chk4 10 2 [true, true, false, false, true, false, false, false, false, false]
            dFFFFFTFFTTT
            dFFFFFTFFTTF)
           (s4S chk4 10 1 [false, true, false, false, true, false, false, false, false, false]
            dFFFFFTFFTFT
            dFFFFFTFFTFF))
          (s4S chk4 11 1 [false, false, false, true, false, false, false, false, false]
           (s4S chk4 10 1 [true, false, false, false, true, false, false, false, false, false]
            dFFFFFTFFFTT
            dFFFFFTFFFTF)
           (s4S chk4 10 0 [false, false, false, false, true, false, false, false, false, false]
            dFFFFFTFFFFT
            dFFFFFTFFFFF)))))
       (s4S chk4 14 3 [false, false, false, false, false, false]
        (s4S chk4 13 3 [true, false, false, false, false, false, false]
         (s4S chk4 12 3 [true, true, false, false, false, false, false, false]
          (s4S chk4 11 3 [true, true, true, false, false, false, false, false, false]
           (s4S chk4 10 3 [true, true, true, true, false, false, false, false, false, false]
            dFFFFFFTTTTT
            dFFFFFFTTTTF)
           (s4S chk4 10 2 [false, true, true, true, false, false, false, false, false, false]
            dFFFFFFTTTFT
            dFFFFFFTTTFF))
          (s4S chk4 11 2 [false, true, true, false, false, false, false, false, false]
           (s4S chk4 10 2 [true, false, true, true, false, false, false, false, false, false]
            dFFFFFFTTFTT
            dFFFFFFTTFTF)
           (s4S chk4 10 1 [false, false, true, true, false, false, false, false, false, false]
            dFFFFFFTTFFT
            dFFFFFFTTFFF)))
         (s4S chk4 12 2 [false, true, false, false, false, false, false, false]
          (s4S chk4 11 2 [true, false, true, false, false, false, false, false, false]
           (s4S chk4 10 2 [true, true, false, true, false, false, false, false, false, false]
            dFFFFFFTFTTT
            dFFFFFFTFTTF)
           (s4S chk4 10 1 [false, true, false, true, false, false, false, false, false, false]
            dFFFFFFTFTFT
            dFFFFFFTFTFF))
          (s4S chk4 11 1 [false, false, true, false, false, false, false, false, false]
           (s4S chk4 10 1 [true, false, false, true, false, false, false, false, false, false]
            dFFFFFFTFFTT
            dFFFFFFTFFTF)
           (s4S chk4 10 0 [false, false, false, true, false, false, false, false, false, false]
            dFFFFFFTFFFT
            dFFFFFFTFFFF))))
        (s4S chk4 13 2 [false, false, false, false, false, false, false]
         (s4S chk4 12 2 [true, false, false, false, false, false, false, false]
          (s4S chk4 11 2 [true, true, false, false, false, false, false, false, false]
           (s4S chk4 10 2 [true, true, true, false, false, false, false, false, false, false]
            dFFFFFFFTTTT
            dFFFFFFFTTTF)
           (s4S chk4 10 1 [false, true, true, false, false, false, false, false, false, false]
            dFFFFFFFTTFT
            dFFFFFFFTTFF))
          (s4S chk4 11 1 [false, true, false, false, false, false, false, false, false]
           (s4S chk4 10 1 [true, false, true, false, false, false, false, false, false, false]
            dFFFFFFFTFTT
            dFFFFFFFTFTF)
           (s4S chk4 10 0 [false, false, true, false, false, false, false, false, false, false]
            dFFFFFFFTFFT
            dFFFFFFFTFFF)))
         (s4S chk4 12 1 [false, false, false, false, false, false, false, false]
          (s4S chk4 11 1 [true, false, false, false, false, false, false, false, false]
           (s4S chk4 10 1 [true, true, false, false, false, false, false, false, false, false]
            dFFFFFFFFTTT
            dFFFFFFFFTTF)
           (s4S chk4 10 0 [false, true, false, false, false, false, false, false, false, false]
            dFFFFFFFFTFT
            dFFFFFFFFTFF))
          (s4S chk4 11 0 [false, false, false, false, false, false, false, false, false]
           (s4S chk4 10 0 [true, false, false, false, false, false, false, false, false, false]
            dFFFFFFFFFTT
            dFFFFFFFFFTF)
           (s40 chk4 10 [false, false, false, false, false, false, false, false, false, false]
            dFFFFFFFFFFT)))))))))))

end BK73
