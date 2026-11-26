import BK73Sound1
import BK73Chunks0
import BK73Chunks1
import BK73Chunks2
import BK73Chunks3
import BK73Chunks4
import BK73Chunks5
import BK73Chunks6
import BK73Chunks7
namespace BK73

theorem splitS (p : List Bool → Bool) (n z : Nat) (acc : List Bool)
    (h1 : allL p n (z+1) (true :: acc) = true) (h2 : allL p n z (false :: acc) = true) :
    allL p (n+1) (z+1) acc = true :=
  allL_split p n (z+1) acc h1 (fun z' hz => by obtain rfl := Nat.succ.inj hz; exact h2)

theorem split0 (p : List Bool → Bool) (n : Nat) (acc : List Bool)
    (h1 : allL p n 0 (true :: acc) = true) : allL p (n+1) 0 acc = true :=
  allL_split p n 0 acc h1 (fun z' hz => nomatch hz)

/-- all 198,440 leaves (edge sets with ≥ 14 edges on 7 vertices) pass `chk`;
the 968 depth-10 subtrees are kernel-checked by `decide +kernel` in Chunks0–7 -/
theorem allL_top : allL chk 21 7 [] = true :=
  (splitS chk 20 6 []
  (splitS chk 19 6 [true]
   (splitS chk 18 6 [true, true]
    (splitS chk 17 6 [true, true, true]
     (splitS chk 16 6 [true, true, true, true]
      (splitS chk 15 6 [true, true, true, true, true]
       (splitS chk 14 6 [true, true, true, true, true, true]
        (splitS chk 13 6 [true, true, true, true, true, true, true]
         (splitS chk 12 6 [true, true, true, true, true, true, true, true]
          (splitS chk 11 6 [true, true, true, true, true, true, true, true, true]
           cTTTTTTTTTT
           cTTTTTTTTTF)
          (splitS chk 11 5 [false, true, true, true, true, true, true, true, true]
           cTTTTTTTTFT
           cTTTTTTTTFF))
         (splitS chk 12 5 [false, true, true, true, true, true, true, true]
          (splitS chk 11 5 [true, false, true, true, true, true, true, true, true]
           cTTTTTTTFTT
           cTTTTTTTFTF)
          (splitS chk 11 4 [false, false, true, true, true, true, true, true, true]
           cTTTTTTTFFT
           cTTTTTTTFFF)))
        (splitS chk 13 5 [false, true, true, true, true, true, true]
         (splitS chk 12 5 [true, false, true, true, true, true, true, true]
          (splitS chk 11 5 [true, true, false, true, true, true, true, true, true]
           cTTTTTTFTTT
           cTTTTTTFTTF)
          (splitS chk 11 4 [false, true, false, true, true, true, true, true, true]
           cTTTTTTFTFT
           cTTTTTTFTFF))
         (splitS chk 12 4 [false, false, true, true, true, true, true, true]
          (splitS chk 11 4 [true, false, false, true, true, true, true, true, true]
           cTTTTTTFFTT
           cTTTTTTFFTF)
          (splitS chk 11 3 [false, false, false, true, true, true, true, true, true]
           cTTTTTTFFFT
           cTTTTTTFFFF))))
       (splitS chk 14 5 [false, true, true, true, true, true]
        (splitS chk 13 5 [true, false, true, true, true, true, true]
         (splitS chk 12 5 [true, true, false, true, true, true, true, true]
          (splitS chk 11 5 [true, true, true, false, true, true, true, true, true]
           cTTTTTFTTTT
           cTTTTTFTTTF)
          (splitS chk 11 4 [false, true, true, false, true, true, true, true, true]
           cTTTTTFTTFT
           cTTTTTFTTFF))
         (splitS chk 12 4 [false, true, false, true, true, true, true, true]
          (splitS chk 11 4 [true, false, true, false, true, true, true, true, true]
           cTTTTTFTFTT
           cTTTTTFTFTF)
          (splitS chk 11 3 [false, false, true, false, true, true, true, true, true]
           cTTTTTFTFFT
           cTTTTTFTFFF)))
        (splitS chk 13 4 [false, false, true, true, true, true, true]
         (splitS chk 12 4 [true, false, false, true, true, true, true, true]
          (splitS chk 11 4 [true, true, false, false, true, true, true, true, true]
           cTTTTTFFTTT
           cTTTTTFFTTF)
          (splitS chk 11 3 [false, true, false, false, true, true, true, true, true]
           cTTTTTFFTFT
           cTTTTTFFTFF))
         (splitS chk 12 3 [false, false, false, true, true, true, true, true]
          (splitS chk 11 3 [true, false, false, false, true, true, true, true, true]
           cTTTTTFFFTT
           cTTTTTFFFTF)
          (splitS chk 11 2 [false, false, false, false, true, true, true, true, true]
           cTTTTTFFFFT
           cTTTTTFFFFF)))))
      (splitS chk 15 5 [false, true, true, true, true]
       (splitS chk 14 5 [true, false, true, true, true, true]
        (splitS chk 13 5 [true, true, false, true, true, true, true]
         (splitS chk 12 5 [true, true, true, false, true, true, true, true]
          (splitS chk 11 5 [true, true, true, true, false, true, true, true, true]
           cTTTTFTTTTT
           cTTTTFTTTTF)
          (splitS chk 11 4 [false, true, true, true, false, true, true, true, true]
           cTTTTFTTTFT
           cTTTTFTTTFF))
         (splitS chk 12 4 [false, true, true, false, true, true, true, true]
          (splitS chk 11 4 [true, false, true, true, false, true, true, true, true]
           cTTTTFTTFTT
           cTTTTFTTFTF)
          (splitS chk 11 3 [false, false, true, true, false, true, true, true, true]
           cTTTTFTTFFT
           cTTTTFTTFFF)))
        (splitS chk 13 4 [false, true, false, true, true, true, true]
         (splitS chk 12 4 [true, false, true, false, true, true, true, true]
          (splitS chk 11 4 [true, true, false, true, false, true, true, true, true]
           cTTTTFTFTTT
           cTTTTFTFTTF)
          (splitS chk 11 3 [false, true, false, true, false, true, true, true, true]
           cTTTTFTFTFT
           cTTTTFTFTFF))
         (splitS chk 12 3 [false, false, true, false, true, true, true, true]
          (splitS chk 11 3 [true, false, false, true, false, true, true, true, true]
           cTTTTFTFFTT
           cTTTTFTFFTF)
          (splitS chk 11 2 [false, false, false, true, false, true, true, true, true]
           cTTTTFTFFFT
           cTTTTFTFFFF))))
       (splitS chk 14 4 [false, false, true, true, true, true]
        (splitS chk 13 4 [true, false, false, true, true, true, true]
         (splitS chk 12 4 [true, true, false, false, true, true, true, true]
          (splitS chk 11 4 [true, true, true, false, false, true, true, true, true]
           cTTTTFFTTTT
           cTTTTFFTTTF)
          (splitS chk 11 3 [false, true, true, false, false, true, true, true, true]
           cTTTTFFTTFT
           cTTTTFFTTFF))
         (splitS chk 12 3 [false, true, false, false, true, true, true, true]
          (splitS chk 11 3 [true, false, true, false, false, true, true, true, true]
           cTTTTFFTFTT
           cTTTTFFTFTF)
          (splitS chk 11 2 [false, false, true, false, false, true, true, true, true]
           cTTTTFFTFFT
           cTTTTFFTFFF)))
        (splitS chk 13 3 [false, false, false, true, true, true, true]
         (splitS chk 12 3 [true, false, false, false, true, true, true, true]
          (splitS chk 11 3 [true, true, false, false, false, true, true, true, true]
           cTTTTFFFTTT
           cTTTTFFFTTF)
          (splitS chk 11 2 [false, true, false, false, false, true, true, true, true]
           cTTTTFFFTFT
           cTTTTFFFTFF))
         (splitS chk 12 2 [false, false, false, false, true, true, true, true]
          (splitS chk 11 2 [true, false, false, false, false, true, true, true, true]
           cTTTTFFFFTT
           cTTTTFFFFTF)
          (splitS chk 11 1 [false, false, false, false, false, true, true, true, true]
           cTTTTFFFFFT
           cTTTTFFFFFF))))))
     (splitS chk 16 5 [false, true, true, true]
      (splitS chk 15 5 [true, false, true, true, true]
       (splitS chk 14 5 [true, true, false, true, true, true]
        (splitS chk 13 5 [true, true, true, false, true, true, true]
         (splitS chk 12 5 [true, true, true, true, false, true, true, true]
          (splitS chk 11 5 [true, true, true, true, true, false, true, true, true]
           cTTTFTTTTTT
           cTTTFTTTTTF)
          (splitS chk 11 4 [false, true, true, true, true, false, true, true, true]
           cTTTFTTTTFT
           cTTTFTTTTFF))
         (splitS chk 12 4 [false, true, true, true, false, true, true, true]
          (splitS chk 11 4 [true, false, true, true, true, false, true, true, true]
           cTTTFTTTFTT
           cTTTFTTTFTF)
          (splitS chk 11 3 [false, false, true, true, true, false, true, true, true]
           cTTTFTTTFFT
           cTTTFTTTFFF)))
        (splitS chk 13 4 [false, true, true, false, true, true, true]
         (splitS chk 12 4 [true, false, true, true, false, true, true, true]
          (splitS chk 11 4 [true, true, false, true, true, false, true, true, true]
           cTTTFTTFTTT
           cTTTFTTFTTF)
          (splitS chk 11 3 [false, true, false, true, true, false, true, true, true]
           cTTTFTTFTFT
           cTTTFTTFTFF))
         (splitS chk 12 3 [false, false, true, true, false, true, true, true]
          (splitS chk 11 3 [true, false, false, true, true, false, true, true, true]
           cTTTFTTFFTT
           cTTTFTTFFTF)
          (splitS chk 11 2 [false, false, false, true, true, false, true, true, true]
           cTTTFTTFFFT
           cTTTFTTFFFF))))
       (splitS chk 14 4 [false, true, false, true, true, true]
        (splitS chk 13 4 [true, false, true, false, true, true, true]
         (splitS chk 12 4 [true, true, false, true, false, true, true, true]
          (splitS chk 11 4 [true, true, true, false, true, false, true, true, true]
           cTTTFTFTTTT
           cTTTFTFTTTF)
          (splitS chk 11 3 [false, true, true, false, true, false, true, true, true]
           cTTTFTFTTFT
           cTTTFTFTTFF))
         (splitS chk 12 3 [false, true, false, true, false, true, true, true]
          (splitS chk 11 3 [true, false, true, false, true, false, true, true, true]
           cTTTFTFTFTT
           cTTTFTFTFTF)
          (splitS chk 11 2 [false, false, true, false, true, false, true, true, true]
           cTTTFTFTFFT
           cTTTFTFTFFF)))
        (splitS chk 13 3 [false, false, true, false, true, true, true]
         (splitS chk 12 3 [true, false, false, true, false, true, true, true]
          (splitS chk 11 3 [true, true, false, false, true, false, true, true, true]
           cTTTFTFFTTT
           cTTTFTFFTTF)
          (splitS chk 11 2 [false, true, false, false, true, false, true, true, true]
           cTTTFTFFTFT
           cTTTFTFFTFF))
         (splitS chk 12 2 [false, false, false, true, false, true, true, true]
          (splitS chk 11 2 [true, false, false, false, true, false, true, true, true]
           cTTTFTFFFTT
           cTTTFTFFFTF)
          (splitS chk 11 1 [false, false, false, false, true, false, true, true, true]
           cTTTFTFFFFT
           cTTTFTFFFFF)))))
      (splitS chk 15 4 [false, false, true, true, true]
       (splitS chk 14 4 [true, false, false, true, true, true]
        (splitS chk 13 4 [true, true, false, false, true, true, true]
         (splitS chk 12 4 [true, true, true, false, false, true, true, true]
          (splitS chk 11 4 [true, true, true, true, false, false, true, true, true]
           cTTTFFTTTTT
           cTTTFFTTTTF)
          (splitS chk 11 3 [false, true, true, true, false, false, true, true, true]
           cTTTFFTTTFT
           cTTTFFTTTFF))
         (splitS chk 12 3 [false, true, true, false, false, true, true, true]
          (splitS chk 11 3 [true, false, true, true, false, false, true, true, true]
           cTTTFFTTFTT
           cTTTFFTTFTF)
          (splitS chk 11 2 [false, false, true, true, false, false, true, true, true]
           cTTTFFTTFFT
           cTTTFFTTFFF)))
        (splitS chk 13 3 [false, true, false, false, true, true, true]
         (splitS chk 12 3 [true, false, true, false, false, true, true, true]
          (splitS chk 11 3 [true, true, false, true, false, false, true, true, true]
           cTTTFFTFTTT
           cTTTFFTFTTF)
          (splitS chk 11 2 [false, true, false, true, false, false, true, true, true]
           cTTTFFTFTFT
           cTTTFFTFTFF))
         (splitS chk 12 2 [false, false, true, false, false, true, true, true]
          (splitS chk 11 2 [true, false, false, true, false, false, true, true, true]
           cTTTFFTFFTT
           cTTTFFTFFTF)
          (splitS chk 11 1 [false, false, false, true, false, false, true, true, true]
           cTTTFFTFFFT
           cTTTFFTFFFF))))
       (splitS chk 14 3 [false, false, false, true, true, true]
        (splitS chk 13 3 [true, false, false, false, true, true, true]
         (splitS chk 12 3 [true, true, false, false, false, true, true, true]
          (splitS chk 11 3 [true, true, true, false, false, false, true, true, true]
           cTTTFFFTTTT
           cTTTFFFTTTF)
          (splitS chk 11 2 [false, true, true, false, false, false, true, true, true]
           cTTTFFFTTFT
           cTTTFFFTTFF))
         (splitS chk 12 2 [false, true, false, false, false, true, true, true]
          (splitS chk 11 2 [true, false, true, false, false, false, true, true, true]
           cTTTFFFTFTT
           cTTTFFFTFTF)
          (splitS chk 11 1 [false, false, true, false, false, false, true, true, true]
           cTTTFFFTFFT
           cTTTFFFTFFF)))
        (splitS chk 13 2 [false, false, false, false, true, true, true]
         (splitS chk 12 2 [true, false, false, false, false, true, true, true]
          (splitS chk 11 2 [true, true, false, false, false, false, true, true, true]
           cTTTFFFFTTT
           cTTTFFFFTTF)
          (splitS chk 11 1 [false, true, false, false, false, false, true, true, true]
           cTTTFFFFTFT
           cTTTFFFFTFF))
         (splitS chk 12 1 [false, false, false, false, false, true, true, true]
          (splitS chk 11 1 [true, false, false, false, false, false, true, true, true]
           cTTTFFFFFTT
           cTTTFFFFFTF)
          (splitS chk 11 0 [false, false, false, false, false, false, true, true, true]
           cTTTFFFFFFT
           cTTTFFFFFFF)))))))
    (splitS chk 17 5 [false, true, true]
     (splitS chk 16 5 [true, false, true, true]
      (splitS chk 15 5 [true, true, false, true, true]
       (splitS chk 14 5 [true, true, true, false, true, true]
        (splitS chk 13 5 [true, true, true, true, false, true, true]
         (splitS chk 12 5 [true, true, true, true, true, false, true, true]
          (splitS chk 11 5 [true, true, true, true, true, true, false, true, true]
           cTTFTTTTTTT
           cTTFTTTTTTF)
          (splitS chk 11 4 [false, true, true, true, true, true, false, true, true]
           cTTFTTTTTFT
           cTTFTTTTTFF))
         (splitS chk 12 4 [false, true, true, true, true, false, true, true]
          (splitS chk 11 4 [true, false, true, true, true, true, false, true, true]
           cTTFTTTTFTT
           cTTFTTTTFTF)
          (splitS chk 11 3 [false, false, true, true, true, true, false, true, true]
           cTTFTTTTFFT
           cTTFTTTTFFF)))
        (splitS chk 13 4 [false, true, true, true, false, true, true]
         (splitS chk 12 4 [true, false, true, true, true, false, true, true]
          (splitS chk 11 4 [true, true, false, true, true, true, false, true, true]
           cTTFTTTFTTT
           cTTFTTTFTTF)
          (splitS chk 11 3 [false, true, false, true, true, true, false, true, true]
           cTTFTTTFTFT
           cTTFTTTFTFF))
         (splitS chk 12 3 [false, false, true, true, true, false, true, true]
          (splitS chk 11 3 [true, false, false, true, true, true, false, true, true]
           cTTFTTTFFTT
           cTTFTTTFFTF)
          (splitS chk 11 2 [false, false, false, true, true, true, false, true, true]
           cTTFTTTFFFT
           cTTFTTTFFFF))))
       (splitS chk 14 4 [false, true, true, false, true, true]
        (splitS chk 13 4 [true, false, true, true, false, true, true]
         (splitS chk 12 4 [true, true, false, true, true, false, true, true]
          (splitS chk 11 4 [true, true, true, false, true, true, false, true, true]
           cTTFTTFTTTT
           cTTFTTFTTTF)
          (splitS chk 11 3 [false, true, true, false, true, true, false, true, true]
           cTTFTTFTTFT
           cTTFTTFTTFF))
         (splitS chk 12 3 [false, true, false, true, true, false, true, true]
          (splitS chk 11 3 [true, false, true, false, true, true, false, true, true]
           cTTFTTFTFTT
           cTTFTTFTFTF)
          (splitS chk 11 2 [false, false, true, false, true, true, false, true, true]
           cTTFTTFTFFT
           cTTFTTFTFFF)))
        (splitS chk 13 3 [false, false, true, true, false, true, true]
         (splitS chk 12 3 [true, false, false, true, true, false, true, true]
          (splitS chk 11 3 [true, true, false, false, true, true, false, true, true]
           cTTFTTFFTTT
           cTTFTTFFTTF)
          (splitS chk 11 2 [false, true, false, false, true, true, false, true, true]
           cTTFTTFFTFT
           cTTFTTFFTFF))
         (splitS chk 12 2 [false, false, false, true, true, false, true, true]
          (splitS chk 11 2 [true, false, false, false, true, true, false, true, true]
           cTTFTTFFFTT
           cTTFTTFFFTF)
          (splitS chk 11 1 [false, false, false, false, true, true, false, true, true]
           cTTFTTFFFFT
           cTTFTTFFFFF)))))
      (splitS chk 15 4 [false, true, false, true, true]
       (splitS chk 14 4 [true, false, true, false, true, true]
        (splitS chk 13 4 [true, true, false, true, false, true, true]
         (splitS chk 12 4 [true, true, true, false, true, false, true, true]
          (splitS chk 11 4 [true, true, true, true, false, true, false, true, true]
           cTTFTFTTTTT
           cTTFTFTTTTF)
          (splitS chk 11 3 [false, true, true, true, false, true, false, true, true]
           cTTFTFTTTFT
           cTTFTFTTTFF))
         (splitS chk 12 3 [false, true, true, false, true, false, true, true]
          (splitS chk 11 3 [true, false, true, true, false, true, false, true, true]
           cTTFTFTTFTT
           cTTFTFTTFTF)
          (splitS chk 11 2 [false, false, true, true, false, true, false, true, true]
           cTTFTFTTFFT
           cTTFTFTTFFF)))
        (splitS chk 13 3 [false, true, false, true, false, true, true]
         (splitS chk 12 3 [true, false, true, false, true, false, true, true]
          (splitS chk 11 3 [true, true, false, true, false, true, false, true, true]
           cTTFTFTFTTT
           cTTFTFTFTTF)
          (splitS chk 11 2 [false, true, false, true, false, true, false, true, true]
           cTTFTFTFTFT
           cTTFTFTFTFF))
         (splitS chk 12 2 [false, false, true, false, true, false, true, true]
          (splitS chk 11 2 [true, false, false, true, false, true, false, true, true]
           cTTFTFTFFTT
           cTTFTFTFFTF)
          (splitS chk 11 1 [false, false, false, true, false, true, false, true, true]
           cTTFTFTFFFT
           cTTFTFTFFFF))))
       (splitS chk 14 3 [false, false, true, false, true, true]
        (splitS chk 13 3 [true, false, false, true, false, true, true]
         (splitS chk 12 3 [true, true, false, false, true, false, true, true]
          (splitS chk 11 3 [true, true, true, false, false, true, false, true, true]
           cTTFTFFTTTT
           cTTFTFFTTTF)
          (splitS chk 11 2 [false, true, true, false, false, true, false, true, true]
           cTTFTFFTTFT
           cTTFTFFTTFF))
         (splitS chk 12 2 [false, true, false, false, true, false, true, true]
          (splitS chk 11 2 [true, false, true, false, false, true, false, true, true]
           cTTFTFFTFTT
           cTTFTFFTFTF)
          (splitS chk 11 1 [false, false, true, false, false, true, false, true, true]
           cTTFTFFTFFT
           cTTFTFFTFFF)))
        (splitS chk 13 2 [false, false, false, true, false, true, true]
         (splitS chk 12 2 [true, false, false, false, true, false, true, true]
          (splitS chk 11 2 [true, true, false, false, false, true, false, true, true]
           cTTFTFFFTTT
           cTTFTFFFTTF)
          (splitS chk 11 1 [false, true, false, false, false, true, false, true, true]
           cTTFTFFFTFT
           cTTFTFFFTFF))
         (splitS chk 12 1 [false, false, false, false, true, false, true, true]
          (splitS chk 11 1 [true, false, false, false, false, true, false, true, true]
           cTTFTFFFFTT
           cTTFTFFFFTF)
          (splitS chk 11 0 [false, false, false, false, false, true, false, true, true]
           cTTFTFFFFFT
           cTTFTFFFFFF))))))
     (splitS chk 16 4 [false, false, true, true]
      (splitS chk 15 4 [true, false, false, true, true]
       (splitS chk 14 4 [true, true, false, false, true, true]
        (splitS chk 13 4 [true, true, true, false, false, true, true]
         (splitS chk 12 4 [true, true, true, true, false, false, true, true]
          (splitS chk 11 4 [true, true, true, true, true, false, false, true, true]
           cTTFFTTTTTT
           cTTFFTTTTTF)
          (splitS chk 11 3 [false, true, true, true, true, false, false, true, true]
           cTTFFTTTTFT
           cTTFFTTTTFF))
         (splitS chk 12 3 [false, true, true, true, false, false, true, true]
          (splitS chk 11 3 [true, false, true, true, true, false, false, true, true]
           cTTFFTTTFTT
           cTTFFTTTFTF)
          (splitS chk 11 2 [false, false, true, true, true, false, false, true, true]
           cTTFFTTTFFT
           cTTFFTTTFFF)))
        (splitS chk 13 3 [false, true, true, false, false, true, true]
         (splitS chk 12 3 [true, false, true, true, false, false, true, true]
          (splitS chk 11 3 [true, true, false, true, true, false, false, true, true]
           cTTFFTTFTTT
           cTTFFTTFTTF)
          (splitS chk 11 2 [false, true, false, true, true, false, false, true, true]
           cTTFFTTFTFT
           cTTFFTTFTFF))
         (splitS chk 12 2 [false, false, true, true, false, false, true, true]
          (splitS chk 11 2 [true, false, false, true, true, false, false, true, true]
           cTTFFTTFFTT
           cTTFFTTFFTF)
          (splitS chk 11 1 [false, false, false, true, true, false, false, true, true]
           cTTFFTTFFFT
           cTTFFTTFFFF))))
       (splitS chk 14 3 [false, true, false, false, true, true]
        (splitS chk 13 3 [true, false, true, false, false, true, true]
         (splitS chk 12 3 [true, true, false, true, false, false, true, true]
          (splitS chk 11 3 [true, true, true, false, true, false, false, true, true]
           cTTFFTFTTTT
           cTTFFTFTTTF)
          (splitS chk 11 2 [false, true, true, false, true, false, false, true, true]
           cTTFFTFTTFT
           cTTFFTFTTFF))
         (splitS chk 12 2 [false, true, false, true, false, false, true, true]
          (splitS chk 11 2 [true, false, true, false, true, false, false, true, true]
           cTTFFTFTFTT
           cTTFFTFTFTF)
          (splitS chk 11 1 [false, false, true, false, true, false, false, true, true]
           cTTFFTFTFFT
           cTTFFTFTFFF)))
        (splitS chk 13 2 [false, false, true, false, false, true, true]
         (splitS chk 12 2 [true, false, false, true, false, false, true, true]
          (splitS chk 11 2 [true, true, false, false, true, false, false, true, true]
           cTTFFTFFTTT
           cTTFFTFFTTF)
          (splitS chk 11 1 [false, true, false, false, true, false, false, true, true]
           cTTFFTFFTFT
           cTTFFTFFTFF))
         (splitS chk 12 1 [false, false, false, true, false, false, true, true]
          (splitS chk 11 1 [true, false, false, false, true, false, false, true, true]
           cTTFFTFFFTT
           cTTFFTFFFTF)
          (splitS chk 11 0 [false, false, false, false, true, false, false, true, true]
           cTTFFTFFFFT
           cTTFFTFFFFF)))))
      (splitS chk 15 3 [false, false, false, true, true]
       (splitS chk 14 3 [true, false, false, false, true, true]
        (splitS chk 13 3 [true, true, false, false, false, true, true]
         (splitS chk 12 3 [true, true, true, false, false, false, true, true]
          (splitS chk 11 3 [true, true, true, true, false, false, false, true, true]
           cTTFFFTTTTT
           cTTFFFTTTTF)
          (splitS chk 11 2 [false, true, true, true, false, false, false, true, true]
           cTTFFFTTTFT
           cTTFFFTTTFF))
         (splitS chk 12 2 [false, true, true, false, false, false, true, true]
          (splitS chk 11 2 [true, false, true, true, false, false, false, true, true]
           cTTFFFTTFTT
           cTTFFFTTFTF)
          (splitS chk 11 1 [false, false, true, true, false, false, false, true, true]
           cTTFFFTTFFT
           cTTFFFTTFFF)))
        (splitS chk 13 2 [false, true, false, false, false, true, true]
         (splitS chk 12 2 [true, false, true, false, false, false, true, true]
          (splitS chk 11 2 [true, true, false, true, false, false, false, true, true]
           cTTFFFTFTTT
           cTTFFFTFTTF)
          (splitS chk 11 1 [false, true, false, true, false, false, false, true, true]
           cTTFFFTFTFT
           cTTFFFTFTFF))
         (splitS chk 12 1 [false, false, true, false, false, false, true, true]
          (splitS chk 11 1 [true, false, false, true, false, false, false, true, true]
           cTTFFFTFFTT
           cTTFFFTFFTF)
          (splitS chk 11 0 [false, false, false, true, false, false, false, true, true]
           cTTFFFTFFFT
           cTTFFFTFFFF))))
       (splitS chk 14 2 [false, false, false, false, true, true]
        (splitS chk 13 2 [true, false, false, false, false, true, true]
         (splitS chk 12 2 [true, true, false, false, false, false, true, true]
          (splitS chk 11 2 [true, true, true, false, false, false, false, true, true]
           cTTFFFFTTTT
           cTTFFFFTTTF)
          (splitS chk 11 1 [false, true, true, false, false, false, false, true, true]
           cTTFFFFTTFT
           cTTFFFFTTFF))
         (splitS chk 12 1 [false, true, false, false, false, false, true, true]
          (splitS chk 11 1 [true, false, true, false, false, false, false, true, true]
           cTTFFFFTFTT
           cTTFFFFTFTF)
          (splitS chk 11 0 [false, false, true, false, false, false, false, true, true]
           cTTFFFFTFFT
           cTTFFFFTFFF)))
        (splitS chk 13 1 [false, false, false, false, false, true, true]
         (splitS chk 12 1 [true, false, false, false, false, false, true, true]
          (splitS chk 11 1 [true, true, false, false, false, false, false, true, true]
           cTTFFFFFTTT
           cTTFFFFFTTF)
          (splitS chk 11 0 [false, true, false, false, false, false, false, true, true]
           cTTFFFFFTFT
           cTTFFFFFTFF))
         (splitS chk 12 0 [false, false, false, false, false, false, true, true]
          (splitS chk 11 0 [true, false, false, false, false, false, false, true, true]
           cTTFFFFFFTT
           cTTFFFFFFTF)
          (split0 chk 11 [false, false, false, false, false, false, false, true, true]
           cTTFFFFFFFT))))))))
   (splitS chk 18 5 [false, true]
    (splitS chk 17 5 [true, false, true]
     (splitS chk 16 5 [true, true, false, true]
      (splitS chk 15 5 [true, true, true, false, true]
       (splitS chk 14 5 [true, true, true, true, false, true]
        (splitS chk 13 5 [true, true, true, true, true, false, true]
         (splitS chk 12 5 [true, true, true, true, true, true, false, true]
          (splitS chk 11 5 [true, true, true, true, true, true, true, false, true]
           cTFTTTTTTTT
           cTFTTTTTTTF)
          (splitS chk 11 4 [false, true, true, true, true, true, true, false, true]
           cTFTTTTTTFT
           cTFTTTTTTFF))
         (splitS chk 12 4 [false, true, true, true, true, true, false, true]
          (splitS chk 11 4 [true, false, true, true, true, true, true, false, true]
           cTFTTTTTFTT
           cTFTTTTTFTF)
          (splitS chk 11 3 [false, false, true, true, true, true, true, false, true]
           cTFTTTTTFFT
           cTFTTTTTFFF)))
        (splitS chk 13 4 [false, true, true, true, true, false, true]
         (splitS chk 12 4 [true, false, true, true, true, true, false, true]
          (splitS chk 11 4 [true, true, false, true, true, true, true, false, true]
           cTFTTTTFTTT
           cTFTTTTFTTF)
          (splitS chk 11 3 [false, true, false, true, true, true, true, false, true]
           cTFTTTTFTFT
           cTFTTTTFTFF))
         (splitS chk 12 3 [false, false, true, true, true, true, false, true]
          (splitS chk 11 3 [true, false, false, true, true, true, true, false, true]
           cTFTTTTFFTT
           cTFTTTTFFTF)
          (splitS chk 11 2 [false, false, false, true, true, true, true, false, true]
           cTFTTTTFFFT
           cTFTTTTFFFF))))
       (splitS chk 14 4 [false, true, true, true, false, true]
        (splitS chk 13 4 [true, false, true, true, true, false, true]
         (splitS chk 12 4 [true, true, false, true, true, true, false, true]
          (splitS chk 11 4 [true, true, true, false, true, true, true, false, true]
           cTFTTTFTTTT
           cTFTTTFTTTF)
          (splitS chk 11 3 [false, true, true, false, true, true, true, false, true]
           cTFTTTFTTFT
           cTFTTTFTTFF))
         (splitS chk 12 3 [false, true, false, true, true, true, false, true]
          (splitS chk 11 3 [true, false, true, false, true, true, true, false, true]
           cTFTTTFTFTT
           cTFTTTFTFTF)
          (splitS chk 11 2 [false, false, true, false, true, true, true, false, true]
           cTFTTTFTFFT
           cTFTTTFTFFF)))
        (splitS chk 13 3 [false, false, true, true, true, false, true]
         (splitS chk 12 3 [true, false, false, true, true, true, false, true]
          (splitS chk 11 3 [true, true, false, false, true, true, true, false, true]
           cTFTTTFFTTT
           cTFTTTFFTTF)
          (splitS chk 11 2 [false, true, false, false, true, true, true, false, true]
           cTFTTTFFTFT
           cTFTTTFFTFF))
         (splitS chk 12 2 [false, false, false, true, true, true, false, true]
          (splitS chk 11 2 [true, false, false, false, true, true, true, false, true]
           cTFTTTFFFTT
           cTFTTTFFFTF)
          (splitS chk 11 1 [false, false, false, false, true, true, true, false, true]
           cTFTTTFFFFT
           cTFTTTFFFFF)))))
      (splitS chk 15 4 [false, true, true, false, true]
       (splitS chk 14 4 [true, false, true, true, false, true]
        (splitS chk 13 4 [true, true, false, true, true, false, true]
         (splitS chk 12 4 [true, true, true, false, true, true, false, true]
          (splitS chk 11 4 [true, true, true, true, false, true, true, false, true]
           cTFTTFTTTTT
           cTFTTFTTTTF)
          (splitS chk 11 3 [false, true, true, true, false, true, true, false, true]
           cTFTTFTTTFT
           cTFTTFTTTFF))
         (splitS chk 12 3 [false, true, true, false, true, true, false, true]
          (splitS chk 11 3 [true, false, true, true, false, true, true, false, true]
           cTFTTFTTFTT
           cTFTTFTTFTF)
          (splitS chk 11 2 [false, false, true, true, false, true, true, false, true]
           cTFTTFTTFFT
           cTFTTFTTFFF)))
        (splitS chk 13 3 [false, true, false, true, true, false, true]
         (splitS chk 12 3 [true, false, true, false, true, true, false, true]
          (splitS chk 11 3 [true, true, false, true, false, true, true, false, true]
           cTFTTFTFTTT
           cTFTTFTFTTF)
          (splitS chk 11 2 [false, true, false, true, false, true, true, false, true]
           cTFTTFTFTFT
           cTFTTFTFTFF))
         (splitS chk 12 2 [false, false, true, false, true, true, false, true]
          (splitS chk 11 2 [true, false, false, true, false, true, true, false, true]
           cTFTTFTFFTT
           cTFTTFTFFTF)
          (splitS chk 11 1 [false, false, false, true, false, true, true, false, true]
           cTFTTFTFFFT
           cTFTTFTFFFF))))
       (splitS chk 14 3 [false, false, true, true, false, true]
        (splitS chk 13 3 [true, false, false, true, true, false, true]
         (splitS chk 12 3 [true, true, false, false, true, true, false, true]
          (splitS chk 11 3 [true, true, true, false, false, true, true, false, true]
           cTFTTFFTTTT
           cTFTTFFTTTF)
          (splitS chk 11 2 [false, true, true, false, false, true, true, false, true]
           cTFTTFFTTFT
           cTFTTFFTTFF))
         (splitS chk 12 2 [false, true, false, false, true, true, false, true]
          (splitS chk 11 2 [true, false, true, false, false, true, true, false, true]
           cTFTTFFTFTT
           cTFTTFFTFTF)
          (splitS chk 11 1 [false, false, true, false, false, true, true, false, true]
           cTFTTFFTFFT
           cTFTTFFTFFF)))
        (splitS chk 13 2 [false, false, false, true, true, false, true]
         (splitS chk 12 2 [true, false, false, false, true, true, false, true]
          (splitS chk 11 2 [true, true, false, false, false, true, true, false, true]
           cTFTTFFFTTT
           cTFTTFFFTTF)
          (splitS chk 11 1 [false, true, false, false, false, true, true, false, true]
           cTFTTFFFTFT
           cTFTTFFFTFF))
         (splitS chk 12 1 [false, false, false, false, true, true, false, true]
          (splitS chk 11 1 [true, false, false, false, false, true, true, false, true]
           cTFTTFFFFTT
           cTFTTFFFFTF)
          (splitS chk 11 0 [false, false, false, false, false, true, true, false, true]
           cTFTTFFFFFT
           cTFTTFFFFFF))))))
     (splitS chk 16 4 [false, true, false, true]
      (splitS chk 15 4 [true, false, true, false, true]
       (splitS chk 14 4 [true, true, false, true, false, true]
        (splitS chk 13 4 [true, true, true, false, true, false, true]
         (splitS chk 12 4 [true, true, true, true, false, true, false, true]
          (splitS chk 11 4 [true, true, true, true, true, false, true, false, true]
           cTFTFTTTTTT
           cTFTFTTTTTF)
          (splitS chk 11 3 [false, true, true, true, true, false, true, false, true]
           cTFTFTTTTFT
           cTFTFTTTTFF))
         (splitS chk 12 3 [false, true, true, true, false, true, false, true]
          (splitS chk 11 3 [true, false, true, true, true, false, true, false, true]
           cTFTFTTTFTT
           cTFTFTTTFTF)
          (splitS chk 11 2 [false, false, true, true, true, false, true, false, true]
           cTFTFTTTFFT
           cTFTFTTTFFF)))
        (splitS chk 13 3 [false, true, true, false, true, false, true]
         (splitS chk 12 3 [true, false, true, true, false, true, false, true]
          (splitS chk 11 3 [true, true, false, true, true, false, true, false, true]
           cTFTFTTFTTT
           cTFTFTTFTTF)
          (splitS chk 11 2 [false, true, false, true, true, false, true, false, true]
           cTFTFTTFTFT
           cTFTFTTFTFF))
         (splitS chk 12 2 [false, false, true, true, false, true, false, true]
          (splitS chk 11 2 [true, false, false, true, true, false, true, false, true]
           cTFTFTTFFTT
           cTFTFTTFFTF)
          (splitS chk 11 1 [false, false, false, true, true, false, true, false, true]
           cTFTFTTFFFT
           cTFTFTTFFFF))))
       (splitS chk 14 3 [false, true, false, true, false, true]
        (splitS chk 13 3 [true, false, true, false, true, false, true]
         (splitS chk 12 3 [true, true, false, true, false, true, false, true]
          (splitS chk 11 3 [true, true, true, false, true, false, true, false, true]
           cTFTFTFTTTT
           cTFTFTFTTTF)
          (splitS chk 11 2 [false, true, true, false, true, false, true, false, true]
           cTFTFTFTTFT
           cTFTFTFTTFF))
         (splitS chk 12 2 [false, true, false, true, false, true, false, true]
          (splitS chk 11 2 [true, false, true, false, true, false, true, false, true]
           cTFTFTFTFTT
           cTFTFTFTFTF)
          (splitS chk 11 1 [false, false, true, false, true, false, true, false, true]
           cTFTFTFTFFT
           cTFTFTFTFFF)))
        (splitS chk 13 2 [false, false, true, false, true, false, true]
         (splitS chk 12 2 [true, false, false, true, false, true, false, true]
          (splitS chk 11 2 [true, true, false, false, true, false, true, false, true]
           cTFTFTFFTTT
           cTFTFTFFTTF)
          (splitS chk 11 1 [false, true, false, false, true, false, true, false, true]
           cTFTFTFFTFT
           cTFTFTFFTFF))
         (splitS chk 12 1 [false, false, false, true, false, true, false, true]
          (splitS chk 11 1 [true, false, false, false, true, false, true, false, true]
           cTFTFTFFFTT
           cTFTFTFFFTF)
          (splitS chk 11 0 [false, false, false, false, true, false, true, false, true]
           cTFTFTFFFFT
           cTFTFTFFFFF)))))
      (splitS chk 15 3 [false, false, true, false, true]
       (splitS chk 14 3 [true, false, false, true, false, true]
        (splitS chk 13 3 [true, true, false, false, true, false, true]
         (splitS chk 12 3 [true, true, true, false, false, true, false, true]
          (splitS chk 11 3 [true, true, true, true, false, false, true, false, true]
           cTFTFFTTTTT
           cTFTFFTTTTF)
          (splitS chk 11 2 [false, true, true, true, false, false, true, false, true]
           cTFTFFTTTFT
           cTFTFFTTTFF))
         (splitS chk 12 2 [false, true, true, false, false, true, false, true]
          (splitS chk 11 2 [true, false, true, true, false, false, true, false, true]
           cTFTFFTTFTT
           cTFTFFTTFTF)
          (splitS chk 11 1 [false, false, true, true, false, false, true, false, true]
           cTFTFFTTFFT
           cTFTFFTTFFF)))
        (splitS chk 13 2 [false, true, false, false, true, false, true]
         (splitS chk 12 2 [true, false, true, false, false, true, false, true]
          (splitS chk 11 2 [true, true, false, true, false, false, true, false, true]
           cTFTFFTFTTT
           cTFTFFTFTTF)
          (splitS chk 11 1 [false, true, false, true, false, false, true, false, true]
           cTFTFFTFTFT
           cTFTFFTFTFF))
         (splitS chk 12 1 [false, false, true, false, false, true, false, true]
          (splitS chk 11 1 [true, false, false, true, false, false, true, false, true]
           cTFTFFTFFTT
           cTFTFFTFFTF)
          (splitS chk 11 0 [false, false, false, true, false, false, true, false, true]
           cTFTFFTFFFT
           cTFTFFTFFFF))))
       (splitS chk 14 2 [false, false, false, true, false, true]
        (splitS chk 13 2 [true, false, false, false, true, false, true]
         (splitS chk 12 2 [true, true, false, false, false, true, false, true]
          (splitS chk 11 2 [true, true, true, false, false, false, true, false, true]
           cTFTFFFTTTT
           cTFTFFFTTTF)
          (splitS chk 11 1 [false, true, true, false, false, false, true, false, true]
           cTFTFFFTTFT
           cTFTFFFTTFF))
         (splitS chk 12 1 [false, true, false, false, false, true, false, true]
          (splitS chk 11 1 [true, false, true, false, false, false, true, false, true]
           cTFTFFFTFTT
           cTFTFFFTFTF)
          (splitS chk 11 0 [false, false, true, false, false, false, true, false, true]
           cTFTFFFTFFT
           cTFTFFFTFFF)))
        (splitS chk 13 1 [false, false, false, false, true, false, true]
         (splitS chk 12 1 [true, false, false, false, false, true, false, true]
          (splitS chk 11 1 [true, true, false, false, false, false, true, false, true]
           cTFTFFFFTTT
           cTFTFFFFTTF)
          (splitS chk 11 0 [false, true, false, false, false, false, true, false, true]
           cTFTFFFFTFT
           cTFTFFFFTFF))
         (splitS chk 12 0 [false, false, false, false, false, true, false, true]
          (splitS chk 11 0 [true, false, false, false, false, false, true, false, true]
           cTFTFFFFFTT
           cTFTFFFFFTF)
          (split0 chk 11 [false, false, false, false, false, false, true, false, true]
           cTFTFFFFFFT)))))))
    (splitS chk 17 4 [false, false, true]
     (splitS chk 16 4 [true, false, false, true]
      (splitS chk 15 4 [true, true, false, false, true]
       (splitS chk 14 4 [true, true, true, false, false, true]
        (splitS chk 13 4 [true, true, true, true, false, false, true]
         (splitS chk 12 4 [true, true, true, true, true, false, false, true]
          (splitS chk 11 4 [true, true, true, true, true, true, false, false, true]
           cTFFTTTTTTT
           cTFFTTTTTTF)
          (splitS chk 11 3 [false, true, true, true, true, true, false, false, true]
           cTFFTTTTTFT
           cTFFTTTTTFF))
         (splitS chk 12 3 [false, true, true, true, true, false, false, true]
          (splitS chk 11 3 [true, false, true, true, true, true, false, false, true]
           cTFFTTTTFTT
           cTFFTTTTFTF)
          (splitS chk 11 2 [false, false, true, true, true, true, false, false, true]
           cTFFTTTTFFT
           cTFFTTTTFFF)))
        (splitS chk 13 3 [false, true, true, true, false, false, true]
         (splitS chk 12 3 [true, false, true, true, true, false, false, true]
          (splitS chk 11 3 [true, true, false, true, true, true, false, false, true]
           cTFFTTTFTTT
           cTFFTTTFTTF)
          (splitS chk 11 2 [false, true, false, true, true, true, false, false, true]
           cTFFTTTFTFT
           cTFFTTTFTFF))
         (splitS chk 12 2 [false, false, true, true, true, false, false, true]
          (splitS chk 11 2 [true, false, false, true, true, true, false, false, true]
           cTFFTTTFFTT
           cTFFTTTFFTF)
          (splitS chk 11 1 [false, false, false, true, true, true, false, false, true]
           cTFFTTTFFFT
           cTFFTTTFFFF))))
       (splitS chk 14 3 [false, true, true, false, false, true]
        (splitS chk 13 3 [true, false, true, true, false, false, true]
         (splitS chk 12 3 [true, true, false, true, true, false, false, true]
          (splitS chk 11 3 [true, true, true, false, true, true, false, false, true]
           cTFFTTFTTTT
           cTFFTTFTTTF)
          (splitS chk 11 2 [false, true, true, false, true, true, false, false, true]
           cTFFTTFTTFT
           cTFFTTFTTFF))
         (splitS chk 12 2 [false, true, false, true, true, false, false, true]
          (splitS chk 11 2 [true, false, true, false, true, true, false, false, true]
           cTFFTTFTFTT
           cTFFTTFTFTF)
          (splitS chk 11 1 [false, false, true, false, true, true, false, false, true]
           cTFFTTFTFFT
           cTFFTTFTFFF)))
        (splitS chk 13 2 [false, false, true, true, false, false, true]
         (splitS chk 12 2 [true, false, false, true, true, false, false, true]
          (splitS chk 11 2 [true, true, false, false, true, true, false, false, true]
           cTFFTTFFTTT
           cTFFTTFFTTF)
          (splitS chk 11 1 [false, true, false, false, true, true, false, false, true]
           cTFFTTFFTFT
           cTFFTTFFTFF))
         (splitS chk 12 1 [false, false, false, true, true, false, false, true]
          (splitS chk 11 1 [true, false, false, false, true, true, false, false, true]
           cTFFTTFFFTT
           cTFFTTFFFTF)
          (splitS chk 11 0 [false, false, false, false, true, true, false, false, true]
           cTFFTTFFFFT
           cTFFTTFFFFF)))))
      (splitS chk 15 3 [false, true, false, false, true]
       (splitS chk 14 3 [true, false, true, false, false, true]
        (splitS chk 13 3 [true, true, false, true, false, false, true]
         (splitS chk 12 3 [true, true, true, false, true, false, false, true]
          (splitS chk 11 3 [true, true, true, true, false, true, false, false, true]
           cTFFTFTTTTT
           cTFFTFTTTTF)
          (splitS chk 11 2 [false, true, true, true, false, true, false, false, true]
           cTFFTFTTTFT
           cTFFTFTTTFF))
         (splitS chk 12 2 [false, true, true, false, true, false, false, true]
          (splitS chk 11 2 [true, false, true, true, false, true, false, false, true]
           cTFFTFTTFTT
           cTFFTFTTFTF)
          (splitS chk 11 1 [false, false, true, true, false, true, false, false, true]
           cTFFTFTTFFT
           cTFFTFTTFFF)))
        (splitS chk 13 2 [false, true, false, true, false, false, true]
         (splitS chk 12 2 [true, false, true, false, true, false, false, true]
          (splitS chk 11 2 [true, true, false, true, false, true, false, false, true]
           cTFFTFTFTTT
           cTFFTFTFTTF)
          (splitS chk 11 1 [false, true, false, true, false, true, false, false, true]
           cTFFTFTFTFT
           cTFFTFTFTFF))
         (splitS chk 12 1 [false, false, true, false, true, false, false, true]
          (splitS chk 11 1 [true, false, false, true, false, true, false, false, true]
           cTFFTFTFFTT
           cTFFTFTFFTF)
          (splitS chk 11 0 [false, false, false, true, false, true, false, false, true]
           cTFFTFTFFFT
           cTFFTFTFFFF))))
       (splitS chk 14 2 [false, false, true, false, false, true]
        (splitS chk 13 2 [true, false, false, true, false, false, true]
         (splitS chk 12 2 [true, true, false, false, true, false, false, true]
          (splitS chk 11 2 [true, true, true, false, false, true, false, false, true]
           cTFFTFFTTTT
           cTFFTFFTTTF)
          (splitS chk 11 1 [false, true, true, false, false, true, false, false, true]
           cTFFTFFTTFT
           cTFFTFFTTFF))
         (splitS chk 12 1 [false, true, false, false, true, false, false, true]
          (splitS chk 11 1 [true, false, true, false, false, true, false, false, true]
           cTFFTFFTFTT
           cTFFTFFTFTF)
          (splitS chk 11 0 [false, false, true, false, false, true, false, false, true]
           cTFFTFFTFFT
           cTFFTFFTFFF)))
        (splitS chk 13 1 [false, false, false, true, false, false, true]
         (splitS chk 12 1 [true, false, false, false, true, false, false, true]
          (splitS chk 11 1 [true, true, false, false, false, true, false, false, true]
           cTFFTFFFTTT
           cTFFTFFFTTF)
          (splitS chk 11 0 [false, true, false, false, false, true, false, false, true]
           cTFFTFFFTFT
           cTFFTFFFTFF))
         (splitS chk 12 0 [false, false, false, false, true, false, false, true]
          (splitS chk 11 0 [true, false, false, false, false, true, false, false, true]
           cTFFTFFFFTT
           cTFFTFFFFTF)
          (split0 chk 11 [false, false, false, false, false, true, false, false, true]
           cTFFTFFFFFT))))))
     (splitS chk 16 3 [false, false, false, true]
      (splitS chk 15 3 [true, false, false, false, true]
       (splitS chk 14 3 [true, true, false, false, false, true]
        (splitS chk 13 3 [true, true, true, false, false, false, true]
         (splitS chk 12 3 [true, true, true, true, false, false, false, true]
          (splitS chk 11 3 [true, true, true, true, true, false, false, false, true]
           cTFFFTTTTTT
           cTFFFTTTTTF)
          (splitS chk 11 2 [false, true, true, true, true, false, false, false, true]
           cTFFFTTTTFT
           cTFFFTTTTFF))
         (splitS chk 12 2 [false, true, true, true, false, false, false, true]
          (splitS chk 11 2 [true, false, true, true, true, false, false, false, true]
           cTFFFTTTFTT
           cTFFFTTTFTF)
          (splitS chk 11 1 [false, false, true, true, true, false, false, false, true]
           cTFFFTTTFFT
           cTFFFTTTFFF)))
        (splitS chk 13 2 [false, true, true, false, false, false, true]
         (splitS chk 12 2 [true, false, true, true, false, false, false, true]
          (splitS chk 11 2 [true, true, false, true, true, false, false, false, true]
           cTFFFTTFTTT
           cTFFFTTFTTF)
          (splitS chk 11 1 [false, true, false, true, true, false, false, false, true]
           cTFFFTTFTFT
           cTFFFTTFTFF))
         (splitS chk 12 1 [false, false, true, true, false, false, false, true]
          (splitS chk 11 1 [true, false, false, true, true, false, false, false, true]
           cTFFFTTFFTT
           cTFFFTTFFTF)
          (splitS chk 11 0 [false, false, false, true, true, false, false, false, true]
           cTFFFTTFFFT
           cTFFFTTFFFF))))
       (splitS chk 14 2 [false, true, false, false, false, true]
        (splitS chk 13 2 [true, false, true, false, false, false, true]
         (splitS chk 12 2 [true, true, false, true, false, false, false, true]
          (splitS chk 11 2 [true, true, true, false, true, false, false, false, true]
           cTFFFTFTTTT
           cTFFFTFTTTF)
          (splitS chk 11 1 [false, true, true, false, true, false, false, false, true]
           cTFFFTFTTFT
           cTFFFTFTTFF))
         (splitS chk 12 1 [false, true, false, true, false, false, false, true]
          (splitS chk 11 1 [true, false, true, false, true, false, false, false, true]
           cTFFFTFTFTT
           cTFFFTFTFTF)
          (splitS chk 11 0 [false, false, true, false, true, false, false, false, true]
           cTFFFTFTFFT
           cTFFFTFTFFF)))
        (splitS chk 13 1 [false, false, true, false, false, false, true]
         (splitS chk 12 1 [true, false, false, true, false, false, false, true]
          (splitS chk 11 1 [true, true, false, false, true, false, false, false, true]
           cTFFFTFFTTT
           cTFFFTFFTTF)
          (splitS chk 11 0 [false, true, false, false, true, false, false, false, true]
           cTFFFTFFTFT
           cTFFFTFFTFF))
         (splitS chk 12 0 [false, false, false, true, false, false, false, true]
          (splitS chk 11 0 [true, false, false, false, true, false, false, false, true]
           cTFFFTFFFTT
           cTFFFTFFFTF)
          (split0 chk 11 [false, false, false, false, true, false, false, false, true]
           cTFFFTFFFFT)))))
      (splitS chk 15 2 [false, false, false, false, true]
       (splitS chk 14 2 [true, false, false, false, false, true]
        (splitS chk 13 2 [true, true, false, false, false, false, true]
         (splitS chk 12 2 [true, true, true, false, false, false, false, true]
          (splitS chk 11 2 [true, true, true, true, false, false, false, false, true]
           cTFFFFTTTTT
           cTFFFFTTTTF)
          (splitS chk 11 1 [false, true, true, true, false, false, false, false, true]
           cTFFFFTTTFT
           cTFFFFTTTFF))
         (splitS chk 12 1 [false, true, true, false, false, false, false, true]
          (splitS chk 11 1 [true, false, true, true, false, false, false, false, true]
           cTFFFFTTFTT
           cTFFFFTTFTF)
          (splitS chk 11 0 [false, false, true, true, false, false, false, false, true]
           cTFFFFTTFFT
           cTFFFFTTFFF)))
        (splitS chk 13 1 [false, true, false, false, false, false, true]
         (splitS chk 12 1 [true, false, true, false, false, false, false, true]
          (splitS chk 11 1 [true, true, false, true, false, false, false, false, true]
           cTFFFFTFTTT
           cTFFFFTFTTF)
          (splitS chk 11 0 [false, true, false, true, false, false, false, false, true]
           cTFFFFTFTFT
           cTFFFFTFTFF))
         (splitS chk 12 0 [false, false, true, false, false, false, false, true]
          (splitS chk 11 0 [true, false, false, true, false, false, false, false, true]
           cTFFFFTFFTT
           cTFFFFTFFTF)
          (split0 chk 11 [false, false, false, true, false, false, false, false, true]
           cTFFFFTFFFT))))
       (splitS chk 14 1 [false, false, false, false, false, true]
        (splitS chk 13 1 [true, false, false, false, false, false, true]
         (splitS chk 12 1 [true, true, false, false, false, false, false, true]
          (splitS chk 11 1 [true, true, true, false, false, false, false, false, true]
           cTFFFFFTTTT
           cTFFFFFTTTF)
          (splitS chk 11 0 [false, true, true, false, false, false, false, false, true]
           cTFFFFFTTFT
           cTFFFFFTTFF))
         (splitS chk 12 0 [false, true, false, false, false, false, false, true]
          (splitS chk 11 0 [true, false, true, false, false, false, false, false, true]
           cTFFFFFTFTT
           cTFFFFFTFTF)
          (split0 chk 11 [false, false, true, false, false, false, false, false, true]
           cTFFFFFTFFT)))
        (splitS chk 13 0 [false, false, false, false, false, false, true]
         (splitS chk 12 0 [true, false, false, false, false, false, false, true]
          (splitS chk 11 0 [true, true, false, false, false, false, false, false, true]
           cTFFFFFFTTT
           cTFFFFFFTTF)
          (split0 chk 11 [false, true, false, false, false, false, false, false, true]
           cTFFFFFFTFT))
         (split0 chk 12 [false, false, false, false, false, false, false, true]
          (split0 chk 11 [true, false, false, false, false, false, false, false, true]
           cTFFFFFFFTT)))))))))
  (splitS chk 19 5 [false]
   (splitS chk 18 5 [true, false]
    (splitS chk 17 5 [true, true, false]
     (splitS chk 16 5 [true, true, true, false]
      (splitS chk 15 5 [true, true, true, true, false]
       (splitS chk 14 5 [true, true, true, true, true, false]
        (splitS chk 13 5 [true, true, true, true, true, true, false]
         (splitS chk 12 5 [true, true, true, true, true, true, true, false]
          (splitS chk 11 5 [true, true, true, true, true, true, true, true, false]
           cFTTTTTTTTT
           cFTTTTTTTTF)
          (splitS chk 11 4 [false, true, true, true, true, true, true, true, false]
           cFTTTTTTTFT
           cFTTTTTTTFF))
         (splitS chk 12 4 [false, true, true, true, true, true, true, false]
          (splitS chk 11 4 [true, false, true, true, true, true, true, true, false]
           cFTTTTTTFTT
           cFTTTTTTFTF)
          (splitS chk 11 3 [false, false, true, true, true, true, true, true, false]
           cFTTTTTTFFT
           cFTTTTTTFFF)))
        (splitS chk 13 4 [false, true, true, true, true, true, false]
         (splitS chk 12 4 [true, false, true, true, true, true, true, false]
          (splitS chk 11 4 [true, true, false, true, true, true, true, true, false]
           cFTTTTTFTTT
           cFTTTTTFTTF)
          (splitS chk 11 3 [false, true, false, true, true, true, true, true, false]
           cFTTTTTFTFT
           cFTTTTTFTFF))
         (splitS chk 12 3 [false, false, true, true, true, true, true, false]
          (splitS chk 11 3 [true, false, false, true, true, true, true, true, false]
           cFTTTTTFFTT
           cFTTTTTFFTF)
          (splitS chk 11 2 [false, false, false, true, true, true, true, true, false]
           cFTTTTTFFFT
           cFTTTTTFFFF))))
       (splitS chk 14 4 [false, true, true, true, true, false]
        (splitS chk 13 4 [true, false, true, true, true, true, false]
         (splitS chk 12 4 [true, true, false, true, true, true, true, false]
          (splitS chk 11 4 [true, true, true, false, true, true, true, true, false]
           cFTTTTFTTTT
           cFTTTTFTTTF)
          (splitS chk 11 3 [false, true, true, false, true, true, true, true, false]
           cFTTTTFTTFT
           cFTTTTFTTFF))
         (splitS chk 12 3 [false, true, false, true, true, true, true, false]
          (splitS chk 11 3 [true, false, true, false, true, true, true, true, false]
           cFTTTTFTFTT
           cFTTTTFTFTF)
          (splitS chk 11 2 [false, false, true, false, true, true, true, true, false]
           cFTTTTFTFFT
           cFTTTTFTFFF)))
        (splitS chk 13 3 [false, false, true, true, true, true, false]
         (splitS chk 12 3 [true, false, false, true, true, true, true, false]
          (splitS chk 11 3 [true, true, false, false, true, true, true, true, false]
           cFTTTTFFTTT
           cFTTTTFFTTF)
          (splitS chk 11 2 [false, true, false, false, true, true, true, true, false]
           cFTTTTFFTFT
           cFTTTTFFTFF))
         (splitS chk 12 2 [false, false, false, true, true, true, true, false]
          (splitS chk 11 2 [true, false, false, false, true, true, true, true, false]
           cFTTTTFFFTT
           cFTTTTFFFTF)
          (splitS chk 11 1 [false, false, false, false, true, true, true, true, false]
           cFTTTTFFFFT
           cFTTTTFFFFF)))))
      (splitS chk 15 4 [false, true, true, true, false]
       (splitS chk 14 4 [true, false, true, true, true, false]
        (splitS chk 13 4 [true, true, false, true, true, true, false]
         (splitS chk 12 4 [true, true, true, false, true, true, true, false]
          (splitS chk 11 4 [true, true, true, true, false, true, true, true, false]
           cFTTTFTTTTT
           cFTTTFTTTTF)
          (splitS chk 11 3 [false, true, true, true, false, true, true, true, false]
           cFTTTFTTTFT
           cFTTTFTTTFF))
         (splitS chk 12 3 [false, true, true, false, true, true, true, false]
          (splitS chk 11 3 [true, false, true, true, false, true, true, true, false]
           cFTTTFTTFTT
           cFTTTFTTFTF)
          (splitS chk 11 2 [false, false, true, true, false, true, true, true, false]
           cFTTTFTTFFT
           cFTTTFTTFFF)))
        (splitS chk 13 3 [false, true, false, true, true, true, false]
         (splitS chk 12 3 [true, false, true, false, true, true, true, false]
          (splitS chk 11 3 [true, true, false, true, false, true, true, true, false]
           cFTTTFTFTTT
           cFTTTFTFTTF)
          (splitS chk 11 2 [false, true, false, true, false, true, true, true, false]
           cFTTTFTFTFT
           cFTTTFTFTFF))
         (splitS chk 12 2 [false, false, true, false, true, true, true, false]
          (splitS chk 11 2 [true, false, false, true, false, true, true, true, false]
           cFTTTFTFFTT
           cFTTTFTFFTF)
          (splitS chk 11 1 [false, false, false, true, false, true, true, true, false]
           cFTTTFTFFFT
           cFTTTFTFFFF))))
       (splitS chk 14 3 [false, false, true, true, true, false]
        (splitS chk 13 3 [true, false, false, true, true, true, false]
         (splitS chk 12 3 [true, true, false, false, true, true, true, false]
          (splitS chk 11 3 [true, true, true, false, false, true, true, true, false]
           cFTTTFFTTTT
           cFTTTFFTTTF)
          (splitS chk 11 2 [false, true, true, false, false, true, true, true, false]
           cFTTTFFTTFT
           cFTTTFFTTFF))
         (splitS chk 12 2 [false, true, false, false, true, true, true, false]
          (splitS chk 11 2 [true, false, true, false, false, true, true, true, false]
           cFTTTFFTFTT
           cFTTTFFTFTF)
          (splitS chk 11 1 [false, false, true, false, false, true, true, true, false]
           cFTTTFFTFFT
           cFTTTFFTFFF)))
        (splitS chk 13 2 [false, false, false, true, true, true, false]
         (splitS chk 12 2 [true, false, false, false, true, true, true, false]
          (splitS chk 11 2 [true, true, false, false, false, true, true, true, false]
           cFTTTFFFTTT
           cFTTTFFFTTF)
          (splitS chk 11 1 [false, true, false, false, false, true, true, true, false]
           cFTTTFFFTFT
           cFTTTFFFTFF))
         (splitS chk 12 1 [false, false, false, false, true, true, true, false]
          (splitS chk 11 1 [true, false, false, false, false, true, true, true, false]
           cFTTTFFFFTT
           cFTTTFFFFTF)
          (splitS chk 11 0 [false, false, false, false, false, true, true, true, false]
           cFTTTFFFFFT
           cFTTTFFFFFF))))))
     (splitS chk 16 4 [false, true, true, false]
      (splitS chk 15 4 [true, false, true, true, false]
       (splitS chk 14 4 [true, true, false, true, true, false]
        (splitS chk 13 4 [true, true, true, false, true, true, false]
         (splitS chk 12 4 [true, true, true, true, false, true, true, false]
          (splitS chk 11 4 [true, true, true, true, true, false, true, true, false]
           cFTTFTTTTTT
           cFTTFTTTTTF)
          (splitS chk 11 3 [false, true, true, true, true, false, true, true, false]
           cFTTFTTTTFT
           cFTTFTTTTFF))
         (splitS chk 12 3 [false, true, true, true, false, true, true, false]
          (splitS chk 11 3 [true, false, true, true, true, false, true, true, false]
           cFTTFTTTFTT
           cFTTFTTTFTF)
          (splitS chk 11 2 [false, false, true, true, true, false, true, true, false]
           cFTTFTTTFFT
           cFTTFTTTFFF)))
        (splitS chk 13 3 [false, true, true, false, true, true, false]
         (splitS chk 12 3 [true, false, true, true, false, true, true, false]
          (splitS chk 11 3 [true, true, false, true, true, false, true, true, false]
           cFTTFTTFTTT
           cFTTFTTFTTF)
          (splitS chk 11 2 [false, true, false, true, true, false, true, true, false]
           cFTTFTTFTFT
           cFTTFTTFTFF))
         (splitS chk 12 2 [false, false, true, true, false, true, true, false]
          (splitS chk 11 2 [true, false, false, true, true, false, true, true, false]
           cFTTFTTFFTT
           cFTTFTTFFTF)
          (splitS chk 11 1 [false, false, false, true, true, false, true, true, false]
           cFTTFTTFFFT
           cFTTFTTFFFF))))
       (splitS chk 14 3 [false, true, false, true, true, false]
        (splitS chk 13 3 [true, false, true, false, true, true, false]
         (splitS chk 12 3 [true, true, false, true, false, true, true, false]
          (splitS chk 11 3 [true, true, true, false, true, false, true, true, false]
           cFTTFTFTTTT
           cFTTFTFTTTF)
          (splitS chk 11 2 [false, true, true, false, true, false, true, true, false]
           cFTTFTFTTFT
           cFTTFTFTTFF))
         (splitS chk 12 2 [false, true, false, true, false, true, true, false]
          (splitS chk 11 2 [true, false, true, false, true, false, true, true, false]
           cFTTFTFTFTT
           cFTTFTFTFTF)
          (splitS chk 11 1 [false, false, true, false, true, false, true, true, false]
           cFTTFTFTFFT
           cFTTFTFTFFF)))
        (splitS chk 13 2 [false, false, true, false, true, true, false]
         (splitS chk 12 2 [true, false, false, true, false, true, true, false]
          (splitS chk 11 2 [true, true, false, false, true, false, true, true, false]
           cFTTFTFFTTT
           cFTTFTFFTTF)
          (splitS chk 11 1 [false, true, false, false, true, false, true, true, false]
           cFTTFTFFTFT
           cFTTFTFFTFF))
         (splitS chk 12 1 [false, false, false, true, false, true, true, false]
          (splitS chk 11 1 [true, false, false, false, true, false, true, true, false]
           cFTTFTFFFTT
           cFTTFTFFFTF)
          (splitS chk 11 0 [false, false, false, false, true, false, true, true, false]
           cFTTFTFFFFT
           cFTTFTFFFFF)))))
      (splitS chk 15 3 [false, false, true, true, false]
       (splitS chk 14 3 [true, false, false, true, true, false]
        (splitS chk 13 3 [true, true, false, false, true, true, false]
         (splitS chk 12 3 [true, true, true, false, false, true, true, false]
          (splitS chk 11 3 [true, true, true, true, false, false, true, true, false]
           cFTTFFTTTTT
           cFTTFFTTTTF)
          (splitS chk 11 2 [false, true, true, true, false, false, true, true, false]
           cFTTFFTTTFT
           cFTTFFTTTFF))
         (splitS chk 12 2 [false, true, true, false, false, true, true, false]
          (splitS chk 11 2 [true, false, true, true, false, false, true, true, false]
           cFTTFFTTFTT
           cFTTFFTTFTF)
          (splitS chk 11 1 [false, false, true, true, false, false, true, true, false]
           cFTTFFTTFFT
           cFTTFFTTFFF)))
        (splitS chk 13 2 [false, true, false, false, true, true, false]
         (splitS chk 12 2 [true, false, true, false, false, true, true, false]
          (splitS chk 11 2 [true, true, false, true, false, false, true, true, false]
           cFTTFFTFTTT
           cFTTFFTFTTF)
          (splitS chk 11 1 [false, true, false, true, false, false, true, true, false]
           cFTTFFTFTFT
           cFTTFFTFTFF))
         (splitS chk 12 1 [false, false, true, false, false, true, true, false]
          (splitS chk 11 1 [true, false, false, true, false, false, true, true, false]
           cFTTFFTFFTT
           cFTTFFTFFTF)
          (splitS chk 11 0 [false, false, false, true, false, false, true, true, false]
           cFTTFFTFFFT
           cFTTFFTFFFF))))
       (splitS chk 14 2 [false, false, false, true, true, false]
        (splitS chk 13 2 [true, false, false, false, true, true, false]
         (splitS chk 12 2 [true, true, false, false, false, true, true, false]
          (splitS chk 11 2 [true, true, true, false, false, false, true, true, false]
           cFTTFFFTTTT
           cFTTFFFTTTF)
          (splitS chk 11 1 [false, true, true, false, false, false, true, true, false]
           cFTTFFFTTFT
           cFTTFFFTTFF))
         (splitS chk 12 1 [false, true, false, false, false, true, true, false]
          (splitS chk 11 1 [true, false, true, false, false, false, true, true, false]
           cFTTFFFTFTT
           cFTTFFFTFTF)
          (splitS chk 11 0 [false, false, true, false, false, false, true, true, false]
           cFTTFFFTFFT
           cFTTFFFTFFF)))
        (splitS chk 13 1 [false, false, false, false, true, true, false]
         (splitS chk 12 1 [true, false, false, false, false, true, true, false]
          (splitS chk 11 1 [true, true, false, false, false, false, true, true, false]
           cFTTFFFFTTT
           cFTTFFFFTTF)
          (splitS chk 11 0 [false, true, false, false, false, false, true, true, false]
           cFTTFFFFTFT
           cFTTFFFFTFF))
         (splitS chk 12 0 [false, false, false, false, false, true, true, false]
          (splitS chk 11 0 [true, false, false, false, false, false, true, true, false]
           cFTTFFFFFTT
           cFTTFFFFFTF)
          (split0 chk 11 [false, false, false, false, false, false, true, true, false]
           cFTTFFFFFFT)))))))
    (splitS chk 17 4 [false, true, false]
     (splitS chk 16 4 [true, false, true, false]
      (splitS chk 15 4 [true, true, false, true, false]
       (splitS chk 14 4 [true, true, true, false, true, false]
        (splitS chk 13 4 [true, true, true, true, false, true, false]
         (splitS chk 12 4 [true, true, true, true, true, false, true, false]
          (splitS chk 11 4 [true, true, true, true, true, true, false, true, false]
           cFTFTTTTTTT
           cFTFTTTTTTF)
          (splitS chk 11 3 [false, true, true, true, true, true, false, true, false]
           cFTFTTTTTFT
           cFTFTTTTTFF))
         (splitS chk 12 3 [false, true, true, true, true, false, true, false]
          (splitS chk 11 3 [true, false, true, true, true, true, false, true, false]
           cFTFTTTTFTT
           cFTFTTTTFTF)
          (splitS chk 11 2 [false, false, true, true, true, true, false, true, false]
           cFTFTTTTFFT
           cFTFTTTTFFF)))
        (splitS chk 13 3 [false, true, true, true, false, true, false]
         (splitS chk 12 3 [true, false, true, true, true, false, true, false]
          (splitS chk 11 3 [true, true, false, true, true, true, false, true, false]
           cFTFTTTFTTT
           cFTFTTTFTTF)
          (splitS chk 11 2 [false, true, false, true, true, true, false, true, false]
           cFTFTTTFTFT
           cFTFTTTFTFF))
         (splitS chk 12 2 [false, false, true, true, true, false, true, false]
          (splitS chk 11 2 [true, false, false, true, true, true, false, true, false]
           cFTFTTTFFTT
           cFTFTTTFFTF)
          (splitS chk 11 1 [false, false, false, true, true, true, false, true, false]
           cFTFTTTFFFT
           cFTFTTTFFFF))))
       (splitS chk 14 3 [false, true, true, false, true, false]
        (splitS chk 13 3 [true, false, true, true, false, true, false]
         (splitS chk 12 3 [true, true, false, true, true, false, true, false]
          (splitS chk 11 3 [true, true, true, false, true, true, false, true, false]
           cFTFTTFTTTT
           cFTFTTFTTTF)
          (splitS chk 11 2 [false, true, true, false, true, true, false, true, false]
           cFTFTTFTTFT
           cFTFTTFTTFF))
         (splitS chk 12 2 [false, true, false, true, true, false, true, false]
          (splitS chk 11 2 [true, false, true, false, true, true, false, true, false]
           cFTFTTFTFTT
           cFTFTTFTFTF)
          (splitS chk 11 1 [false, false, true, false, true, true, false, true, false]
           cFTFTTFTFFT
           cFTFTTFTFFF)))
        (splitS chk 13 2 [false, false, true, true, false, true, false]
         (splitS chk 12 2 [true, false, false, true, true, false, true, false]
          (splitS chk 11 2 [true, true, false, false, true, true, false, true, false]
           cFTFTTFFTTT
           cFTFTTFFTTF)
          (splitS chk 11 1 [false, true, false, false, true, true, false, true, false]
           cFTFTTFFTFT
           cFTFTTFFTFF))
         (splitS chk 12 1 [false, false, false, true, true, false, true, false]
          (splitS chk 11 1 [true, false, false, false, true, true, false, true, false]
           cFTFTTFFFTT
           cFTFTTFFFTF)
          (splitS chk 11 0 [false, false, false, false, true, true, false, true, false]
           cFTFTTFFFFT
           cFTFTTFFFFF)))))
      (splitS chk 15 3 [false, true, false, true, false]
       (splitS chk 14 3 [true, false, true, false, true, false]
        (splitS chk 13 3 [true, true, false, true, false, true, false]
         (splitS chk 12 3 [true, true, true, false, true, false, true, false]
          (splitS chk 11 3 [true, true, true, true, false, true, false, true, false]
           cFTFTFTTTTT
           cFTFTFTTTTF)
          (splitS chk 11 2 [false, true, true, true, false, true, false, true, false]
           cFTFTFTTTFT
           cFTFTFTTTFF))
         (splitS chk 12 2 [false, true, true, false, true, false, true, false]
          (splitS chk 11 2 [true, false, true, true, false, true, false, true, false]
           cFTFTFTTFTT
           cFTFTFTTFTF)
          (splitS chk 11 1 [false, false, true, true, false, true, false, true, false]
           cFTFTFTTFFT
           cFTFTFTTFFF)))
        (splitS chk 13 2 [false, true, false, true, false, true, false]
         (splitS chk 12 2 [true, false, true, false, true, false, true, false]
          (splitS chk 11 2 [true, true, false, true, false, true, false, true, false]
           cFTFTFTFTTT
           cFTFTFTFTTF)
          (splitS chk 11 1 [false, true, false, true, false, true, false, true, false]
           cFTFTFTFTFT
           cFTFTFTFTFF))
         (splitS chk 12 1 [false, false, true, false, true, false, true, false]
          (splitS chk 11 1 [true, false, false, true, false, true, false, true, false]
           cFTFTFTFFTT
           cFTFTFTFFTF)
          (splitS chk 11 0 [false, false, false, true, false, true, false, true, false]
           cFTFTFTFFFT
           cFTFTFTFFFF))))
       (splitS chk 14 2 [false, false, true, false, true, false]
        (splitS chk 13 2 [true, false, false, true, false, true, false]
         (splitS chk 12 2 [true, true, false, false, true, false, true, false]
          (splitS chk 11 2 [true, true, true, false, false, true, false, true, false]
           cFTFTFFTTTT
           cFTFTFFTTTF)
          (splitS chk 11 1 [false, true, true, false, false, true, false, true, false]
           cFTFTFFTTFT
           cFTFTFFTTFF))
         (splitS chk 12 1 [false, true, false, false, true, false, true, false]
          (splitS chk 11 1 [true, false, true, false, false, true, false, true, false]
           cFTFTFFTFTT
           cFTFTFFTFTF)
          (splitS chk 11 0 [false, false, true, false, false, true, false, true, false]
           cFTFTFFTFFT
           cFTFTFFTFFF)))
        (splitS chk 13 1 [false, false, false, true, false, true, false]
         (splitS chk 12 1 [true, false, false, false, true, false, true, false]
          (splitS chk 11 1 [true, true, false, false, false, true, false, true, false]
           cFTFTFFFTTT
           cFTFTFFFTTF)
          (splitS chk 11 0 [false, true, false, false, false, true, false, true, false]
           cFTFTFFFTFT
           cFTFTFFFTFF))
         (splitS chk 12 0 [false, false, false, false, true, false, true, false]
          (splitS chk 11 0 [true, false, false, false, false, true, false, true, false]
           cFTFTFFFFTT
           cFTFTFFFFTF)
          (split0 chk 11 [false, false, false, false, false, true, false, true, false]
           cFTFTFFFFFT))))))
     (splitS chk 16 3 [false, false, true, false]
      (splitS chk 15 3 [true, false, false, true, false]
       (splitS chk 14 3 [true, true, false, false, true, false]
        (splitS chk 13 3 [true, true, true, false, false, true, false]
         (splitS chk 12 3 [true, true, true, true, false, false, true, false]
          (splitS chk 11 3 [true, true, true, true, true, false, false, true, false]
           cFTFFTTTTTT
           cFTFFTTTTTF)
          (splitS chk 11 2 [false, true, true, true, true, false, false, true, false]
           cFTFFTTTTFT
           cFTFFTTTTFF))
         (splitS chk 12 2 [false, true, true, true, false, false, true, false]
          (splitS chk 11 2 [true, false, true, true, true, false, false, true, false]
           cFTFFTTTFTT
           cFTFFTTTFTF)
          (splitS chk 11 1 [false, false, true, true, true, false, false, true, false]
           cFTFFTTTFFT
           cFTFFTTTFFF)))
        (splitS chk 13 2 [false, true, true, false, false, true, false]
         (splitS chk 12 2 [true, false, true, true, false, false, true, false]
          (splitS chk 11 2 [true, true, false, true, true, false, false, true, false]
           cFTFFTTFTTT
           cFTFFTTFTTF)
          (splitS chk 11 1 [false, true, false, true, true, false, false, true, false]
           cFTFFTTFTFT
           cFTFFTTFTFF))
         (splitS chk 12 1 [false, false, true, true, false, false, true, false]
          (splitS chk 11 1 [true, false, false, true, true, false, false, true, false]
           cFTFFTTFFTT
           cFTFFTTFFTF)
          (splitS chk 11 0 [false, false, false, true, true, false, false, true, false]
           cFTFFTTFFFT
           cFTFFTTFFFF))))
       (splitS chk 14 2 [false, true, false, false, true, false]
        (splitS chk 13 2 [true, false, true, false, false, true, false]
         (splitS chk 12 2 [true, true, false, true, false, false, true, false]
          (splitS chk 11 2 [true, true, true, false, true, false, false, true, false]
           cFTFFTFTTTT
           cFTFFTFTTTF)
          (splitS chk 11 1 [false, true, true, false, true, false, false, true, false]
           cFTFFTFTTFT
           cFTFFTFTTFF))
         (splitS chk 12 1 [false, true, false, true, false, false, true, false]
          (splitS chk 11 1 [true, false, true, false, true, false, false, true, false]
           cFTFFTFTFTT
           cFTFFTFTFTF)
          (splitS chk 11 0 [false, false, true, false, true, false, false, true, false]
           cFTFFTFTFFT
           cFTFFTFTFFF)))
        (splitS chk 13 1 [false, false, true, false, false, true, false]
         (splitS chk 12 1 [true, false, false, true, false, false, true, false]
          (splitS chk 11 1 [true, true, false, false, true, false, false, true, false]
           cFTFFTFFTTT
           cFTFFTFFTTF)
          (splitS chk 11 0 [false, true, false, false, true, false, false, true, false]
           cFTFFTFFTFT
           cFTFFTFFTFF))
         (splitS chk 12 0 [false, false, false, true, false, false, true, false]
          (splitS chk 11 0 [true, false, false, false, true, false, false, true, false]
           cFTFFTFFFTT
           cFTFFTFFFTF)
          (split0 chk 11 [false, false, false, false, true, false, false, true, false]
           cFTFFTFFFFT)))))
      (splitS chk 15 2 [false, false, false, true, false]
       (splitS chk 14 2 [true, false, false, false, true, false]
        (splitS chk 13 2 [true, true, false, false, false, true, false]
         (splitS chk 12 2 [true, true, true, false, false, false, true, false]
          (splitS chk 11 2 [true, true, true, true, false, false, false, true, false]
           cFTFFFTTTTT
           cFTFFFTTTTF)
          (splitS chk 11 1 [false, true, true, true, false, false, false, true, false]
           cFTFFFTTTFT
           cFTFFFTTTFF))
         (splitS chk 12 1 [false, true, true, false, false, false, true, false]
          (splitS chk 11 1 [true, false, true, true, false, false, false, true, false]
           cFTFFFTTFTT
           cFTFFFTTFTF)
          (splitS chk 11 0 [false, false, true, true, false, false, false, true, false]
           cFTFFFTTFFT
           cFTFFFTTFFF)))
        (splitS chk 13 1 [false, true, false, false, false, true, false]
         (splitS chk 12 1 [true, false, true, false, false, false, true, false]
          (splitS chk 11 1 [true, true, false, true, false, false, false, true, false]
           cFTFFFTFTTT
           cFTFFFTFTTF)
          (splitS chk 11 0 [false, true, false, true, false, false, false, true, false]
           cFTFFFTFTFT
           cFTFFFTFTFF))
         (splitS chk 12 0 [false, false, true, false, false, false, true, false]
          (splitS chk 11 0 [true, false, false, true, false, false, false, true, false]
           cFTFFFTFFTT
           cFTFFFTFFTF)
          (split0 chk 11 [false, false, false, true, false, false, false, true, false]
           cFTFFFTFFFT))))
       (splitS chk 14 1 [false, false, false, false, true, false]
        (splitS chk 13 1 [true, false, false, false, false, true, false]
         (splitS chk 12 1 [true, true, false, false, false, false, true, false]
          (splitS chk 11 1 [true, true, true, false, false, false, false, true, false]
           cFTFFFFTTTT
           cFTFFFFTTTF)
          (splitS chk 11 0 [false, true, true, false, false, false, false, true, false]
           cFTFFFFTTFT
           cFTFFFFTTFF))
         (splitS chk 12 0 [false, true, false, false, false, false, true, false]
          (splitS chk 11 0 [true, false, true, false, false, false, false, true, false]
           cFTFFFFTFTT
           cFTFFFFTFTF)
          (split0 chk 11 [false, false, true, false, false, false, false, true, false]
           cFTFFFFTFFT)))
        (splitS chk 13 0 [false, false, false, false, false, true, false]
         (splitS chk 12 0 [true, false, false, false, false, false, true, false]
          (splitS chk 11 0 [true, true, false, false, false, false, false, true, false]
           cFTFFFFFTTT
           cFTFFFFFTTF)
          (split0 chk 11 [false, true, false, false, false, false, false, true, false]
           cFTFFFFFTFT))
         (split0 chk 12 [false, false, false, false, false, false, true, false]
          (split0 chk 11 [true, false, false, false, false, false, false, true, false]
           cFTFFFFFFTT))))))))
   (splitS chk 18 4 [false, false]
    (splitS chk 17 4 [true, false, false]
     (splitS chk 16 4 [true, true, false, false]
      (splitS chk 15 4 [true, true, true, false, false]
       (splitS chk 14 4 [true, true, true, true, false, false]
        (splitS chk 13 4 [true, true, true, true, true, false, false]
         (splitS chk 12 4 [true, true, true, true, true, true, false, false]
          (splitS chk 11 4 [true, true, true, true, true, true, true, false, false]
           cFFTTTTTTTT
           cFFTTTTTTTF)
          (splitS chk 11 3 [false, true, true, true, true, true, true, false, false]
           cFFTTTTTTFT
           cFFTTTTTTFF))
         (splitS chk 12 3 [false, true, true, true, true, true, false, false]
          (splitS chk 11 3 [true, false, true, true, true, true, true, false, false]
           cFFTTTTTFTT
           cFFTTTTTFTF)
          (splitS chk 11 2 [false, false, true, true, true, true, true, false, false]
           cFFTTTTTFFT
           cFFTTTTTFFF)))
        (splitS chk 13 3 [false, true, true, true, true, false, false]
         (splitS chk 12 3 [true, false, true, true, true, true, false, false]
          (splitS chk 11 3 [true, true, false, true, true, true, true, false, false]
           cFFTTTTFTTT
           cFFTTTTFTTF)
          (splitS chk 11 2 [false, true, false, true, true, true, true, false, false]
           cFFTTTTFTFT
           cFFTTTTFTFF))
         (splitS chk 12 2 [false, false, true, true, true, true, false, false]
          (splitS chk 11 2 [true, false, false, true, true, true, true, false, false]
           cFFTTTTFFTT
           cFFTTTTFFTF)
          (splitS chk 11 1 [false, false, false, true, true, true, true, false, false]
           cFFTTTTFFFT
           cFFTTTTFFFF))))
       (splitS chk 14 3 [false, true, true, true, false, false]
        (splitS chk 13 3 [true, false, true, true, true, false, false]
         (splitS chk 12 3 [true, true, false, true, true, true, false, false]
          (splitS chk 11 3 [true, true, true, false, true, true, true, false, false]
           cFFTTTFTTTT
           cFFTTTFTTTF)
          (splitS chk 11 2 [false, true, true, false, true, true, true, false, false]
           cFFTTTFTTFT
           cFFTTTFTTFF))
         (splitS chk 12 2 [false, true, false, true, true, true, false, false]
          (splitS chk 11 2 [true, false, true, false, true, true, true, false, false]
           cFFTTTFTFTT
           cFFTTTFTFTF)
          (splitS chk 11 1 [false, false, true, false, true, true, true, false, false]
           cFFTTTFTFFT
           cFFTTTFTFFF)))
        (splitS chk 13 2 [false, false, true, true, true, false, false]
         (splitS chk 12 2 [true, false, false, true, true, true, false, false]
          (splitS chk 11 2 [true, true, false, false, true, true, true, false, false]
           cFFTTTFFTTT
           cFFTTTFFTTF)
          (splitS chk 11 1 [false, true, false, false, true, true, true, false, false]
           cFFTTTFFTFT
           cFFTTTFFTFF))
         (splitS chk 12 1 [false, false, false, true, true, true, false, false]
          (splitS chk 11 1 [true, false, false, false, true, true, true, false, false]
           cFFTTTFFFTT
           cFFTTTFFFTF)
          (splitS chk 11 0 [false, false, false, false, true, true, true, false, false]
           cFFTTTFFFFT
           cFFTTTFFFFF)))))
      (splitS chk 15 3 [false, true, true, false, false]
       (splitS chk 14 3 [true, false, true, true, false, false]
        (splitS chk 13 3 [true, true, false, true, true, false, false]
         (splitS chk 12 3 [true, true, true, false, true, true, false, false]
          (splitS chk 11 3 [true, true, true, true, false, true, true, false, false]
           cFFTTFTTTTT
           cFFTTFTTTTF)
          (splitS chk 11 2 [false, true, true, true, false, true, true, false, false]
           cFFTTFTTTFT
           cFFTTFTTTFF))
         (splitS chk 12 2 [false, true, true, false, true, true, false, false]
          (splitS chk 11 2 [true, false, true, true, false, true, true, false, false]
           cFFTTFTTFTT
           cFFTTFTTFTF)
          (splitS chk 11 1 [false, false, true, true, false, true, true, false, false]
           cFFTTFTTFFT
           cFFTTFTTFFF)))
        (splitS chk 13 2 [false, true, false, true, true, false, false]
         (splitS chk 12 2 [true, false, true, false, true, true, false, false]
          (splitS chk 11 2 [true, true, false, true, false, true, true, false, false]
           cFFTTFTFTTT
           cFFTTFTFTTF)
          (splitS chk 11 1 [false, true, false, true, false, true, true, false, false]
           cFFTTFTFTFT
           cFFTTFTFTFF))
         (splitS chk 12 1 [false, false, true, false, true, true, false, false]
          (splitS chk 11 1 [true, false, false, true, false, true, true, false, false]
           cFFTTFTFFTT
           cFFTTFTFFTF)
          (splitS chk 11 0 [false, false, false, true, false, true, true, false, false]
           cFFTTFTFFFT
           cFFTTFTFFFF))))
       (splitS chk 14 2 [false, false, true, true, false, false]
        (splitS chk 13 2 [true, false, false, true, true, false, false]
         (splitS chk 12 2 [true, true, false, false, true, true, false, false]
          (splitS chk 11 2 [true, true, true, false, false, true, true, false, false]
           cFFTTFFTTTT
           cFFTTFFTTTF)
          (splitS chk 11 1 [false, true, true, false, false, true, true, false, false]
           cFFTTFFTTFT
           cFFTTFFTTFF))
         (splitS chk 12 1 [false, true, false, false, true, true, false, false]
          (splitS chk 11 1 [true, false, true, false, false, true, true, false, false]
           cFFTTFFTFTT
           cFFTTFFTFTF)
          (splitS chk 11 0 [false, false, true, false, false, true, true, false, false]
           cFFTTFFTFFT
           cFFTTFFTFFF)))
        (splitS chk 13 1 [false, false, false, true, true, false, false]
         (splitS chk 12 1 [true, false, false, false, true, true, false, false]
          (splitS chk 11 1 [true, true, false, false, false, true, true, false, false]
           cFFTTFFFTTT
           cFFTTFFFTTF)
          (splitS chk 11 0 [false, true, false, false, false, true, true, false, false]
           cFFTTFFFTFT
           cFFTTFFFTFF))
         (splitS chk 12 0 [false, false, false, false, true, true, false, false]
          (splitS chk 11 0 [true, false, false, false, false, true, true, false, false]
           cFFTTFFFFTT
           cFFTTFFFFTF)
          (split0 chk 11 [false, false, false, false, false, true, true, false, false]
           cFFTTFFFFFT))))))
     (splitS chk 16 3 [false, true, false, false]
      (splitS chk 15 3 [true, false, true, false, false]
       (splitS chk 14 3 [true, true, false, true, false, false]
        (splitS chk 13 3 [true, true, true, false, true, false, false]
         (splitS chk 12 3 [true, true, true, true, false, true, false, false]
          (splitS chk 11 3 [true, true, true, true, true, false, true, false, false]
           cFFTFTTTTTT
           cFFTFTTTTTF)
          (splitS chk 11 2 [false, true, true, true, true, false, true, false, false]
           cFFTFTTTTFT
           cFFTFTTTTFF))
         (splitS chk 12 2 [false, true, true, true, false, true, false, false]
          (splitS chk 11 2 [true, false, true, true, true, false, true, false, false]
           cFFTFTTTFTT
           cFFTFTTTFTF)
          (splitS chk 11 1 [false, false, true, true, true, false, true, false, false]
           cFFTFTTTFFT
           cFFTFTTTFFF)))
        (splitS chk 13 2 [false, true, true, false, true, false, false]
         (splitS chk 12 2 [true, false, true, true, false, true, false, false]
          (splitS chk 11 2 [true, true, false, true, true, false, true, false, false]
           cFFTFTTFTTT
           cFFTFTTFTTF)
          (splitS chk 11 1 [false, true, false, true, true, false, true, false, false]
           cFFTFTTFTFT
           cFFTFTTFTFF))
         (splitS chk 12 1 [false, false, true, true, false, true, false, false]
          (splitS chk 11 1 [true, false, false, true, true, false, true, false, false]
           cFFTFTTFFTT
           cFFTFTTFFTF)
          (splitS chk 11 0 [false, false, false, true, true, false, true, false, false]
           cFFTFTTFFFT
           cFFTFTTFFFF))))
       (splitS chk 14 2 [false, true, false, true, false, false]
        (splitS chk 13 2 [true, false, true, false, true, false, false]
         (splitS chk 12 2 [true, true, false, true, false, true, false, false]
          (splitS chk 11 2 [true, true, true, false, true, false, true, false, false]
           cFFTFTFTTTT
           cFFTFTFTTTF)
          (splitS chk 11 1 [false, true, true, false, true, false, true, false, false]
           cFFTFTFTTFT
           cFFTFTFTTFF))
         (splitS chk 12 1 [false, true, false, true, false, true, false, false]
          (splitS chk 11 1 [true, false, true, false, true, false, true, false, false]
           cFFTFTFTFTT
           cFFTFTFTFTF)
          (splitS chk 11 0 [false, false, true, false, true, false, true, false, false]
           cFFTFTFTFFT
           cFFTFTFTFFF)))
        (splitS chk 13 1 [false, false, true, false, true, false, false]
         (splitS chk 12 1 [true, false, false, true, false, true, false, false]
          (splitS chk 11 1 [true, true, false, false, true, false, true, false, false]
           cFFTFTFFTTT
           cFFTFTFFTTF)
          (splitS chk 11 0 [false, true, false, false, true, false, true, false, false]
           cFFTFTFFTFT
           cFFTFTFFTFF))
         (splitS chk 12 0 [false, false, false, true, false, true, false, false]
          (splitS chk 11 0 [true, false, false, false, true, false, true, false, false]
           cFFTFTFFFTT
           cFFTFTFFFTF)
          (split0 chk 11 [false, false, false, false, true, false, true, false, false]
           cFFTFTFFFFT)))))
      (splitS chk 15 2 [false, false, true, false, false]
       (splitS chk 14 2 [true, false, false, true, false, false]
        (splitS chk 13 2 [true, true, false, false, true, false, false]
         (splitS chk 12 2 [true, true, true, false, false, true, false, false]
          (splitS chk 11 2 [true, true, true, true, false, false, true, false, false]
           cFFTFFTTTTT
           cFFTFFTTTTF)
          (splitS chk 11 1 [false, true, true, true, false, false, true, false, false]
           cFFTFFTTTFT
           cFFTFFTTTFF))
         (splitS chk 12 1 [false, true, true, false, false, true, false, false]
          (splitS chk 11 1 [true, false, true, true, false, false, true, false, false]
           cFFTFFTTFTT
           cFFTFFTTFTF)
          (splitS chk 11 0 [false, false, true, true, false, false, true, false, false]
           cFFTFFTTFFT
           cFFTFFTTFFF)))
        (splitS chk 13 1 [false, true, false, false, true, false, false]
         (splitS chk 12 1 [true, false, true, false, false, true, false, false]
          (splitS chk 11 1 [true, true, false, true, false, false, true, false, false]
           cFFTFFTFTTT
           cFFTFFTFTTF)
          (splitS chk 11 0 [false, true, false, true, false, false, true, false, false]
           cFFTFFTFTFT
           cFFTFFTFTFF))
         (splitS chk 12 0 [false, false, true, false, false, true, false, false]
          (splitS chk 11 0 [true, false, false, true, false, false, true, false, false]
           cFFTFFTFFTT
           cFFTFFTFFTF)
          (split0 chk 11 [false, false, false, true, false, false, true, false, false]
           cFFTFFTFFFT))))
       (splitS chk 14 1 [false, false, false, true, false, false]
        (splitS chk 13 1 [true, false, false, false, true, false, false]
         (splitS chk 12 1 [true, true, false, false, false, true, false, false]
          (splitS chk 11 1 [true, true, true, false, false, false, true, false, false]
           cFFTFFFTTTT
           cFFTFFFTTTF)
          (splitS chk 11 0 [false, true, true, false, false, false, true, false, false]
           cFFTFFFTTFT
           cFFTFFFTTFF))
         (splitS chk 12 0 [false, true, false, false, false, true, false, false]
          (splitS chk 11 0 [true, false, true, false, false, false, true, false, false]
           cFFTFFFTFTT
           cFFTFFFTFTF)
          (split0 chk 11 [false, false, true, false, false, false, true, false, false]
           cFFTFFFTFFT)))
        (splitS chk 13 0 [false, false, false, false, true, false, false]
         (splitS chk 12 0 [true, false, false, false, false, true, false, false]
          (splitS chk 11 0 [true, true, false, false, false, false, true, false, false]
           cFFTFFFFTTT
           cFFTFFFFTTF)
          (split0 chk 11 [false, true, false, false, false, false, true, false, false]
           cFFTFFFFTFT))
         (split0 chk 12 [false, false, false, false, false, true, false, false]
          (split0 chk 11 [true, false, false, false, false, false, true, false, false]
           cFFTFFFFFTT)))))))
    (splitS chk 17 3 [false, false, false]
     (splitS chk 16 3 [true, false, false, false]
      (splitS chk 15 3 [true, true, false, false, false]
       (splitS chk 14 3 [true, true, true, false, false, false]
        (splitS chk 13 3 [true, true, true, true, false, false, false]
         (splitS chk 12 3 [true, true, true, true, true, false, false, false]
          (splitS chk 11 3 [true, true, true, true, true, true, false, false, false]
           cFFFTTTTTTT
           cFFFTTTTTTF)
          (splitS chk 11 2 [false, true, true, true, true, true, false, false, false]
           cFFFTTTTTFT
           cFFFTTTTTFF))
         (splitS chk 12 2 [false, true, true, true, true, false, false, false]
          (splitS chk 11 2 [true, false, true, true, true, true, false, false, false]
           cFFFTTTTFTT
           cFFFTTTTFTF)
          (splitS chk 11 1 [false, false, true, true, true, true, false, false, false]
           cFFFTTTTFFT
           cFFFTTTTFFF)))
        (splitS chk 13 2 [false, true, true, true, false, false, false]
         (splitS chk 12 2 [true, false, true, true, true, false, false, false]
          (splitS chk 11 2 [true, true, false, true, true, true, false, false, false]
           cFFFTTTFTTT
           cFFFTTTFTTF)
          (splitS chk 11 1 [false, true, false, true, true, true, false, false, false]
           cFFFTTTFTFT
           cFFFTTTFTFF))
         (splitS chk 12 1 [false, false, true, true, true, false, false, false]
          (splitS chk 11 1 [true, false, false, true, true, true, false, false, false]
           cFFFTTTFFTT
           cFFFTTTFFTF)
          (splitS chk 11 0 [false, false, false, true, true, true, false, false, false]
           cFFFTTTFFFT
           cFFFTTTFFFF))))
       (splitS chk 14 2 [false, true, true, false, false, false]
        (splitS chk 13 2 [true, false, true, true, false, false, false]
         (splitS chk 12 2 [true, true, false, true, true, false, false, false]
          (splitS chk 11 2 [true, true, true, false, true, true, false, false, false]
           cFFFTTFTTTT
           cFFFTTFTTTF)
          (splitS chk 11 1 [false, true, true, false, true, true, false, false, false]
           cFFFTTFTTFT
           cFFFTTFTTFF))
         (splitS chk 12 1 [false, true, false, true, true, false, false, false]
          (splitS chk 11 1 [true, false, true, false, true, true, false, false, false]
           cFFFTTFTFTT
           cFFFTTFTFTF)
          (splitS chk 11 0 [false, false, true, false, true, true, false, false, false]
           cFFFTTFTFFT
           cFFFTTFTFFF)))
        (splitS chk 13 1 [false, false, true, true, false, false, false]
         (splitS chk 12 1 [true, false, false, true, true, false, false, false]
          (splitS chk 11 1 [true, true, false, false, true, true, false, false, false]
           cFFFTTFFTTT
           cFFFTTFFTTF)
          (splitS chk 11 0 [false, true, false, false, true, true, false, false, false]
           cFFFTTFFTFT
           cFFFTTFFTFF))
         (splitS chk 12 0 [false, false, false, true, true, false, false, false]
          (splitS chk 11 0 [true, false, false, false, true, true, false, false, false]
           cFFFTTFFFTT
           cFFFTTFFFTF)
          (split0 chk 11 [false, false, false, false, true, true, false, false, false]
           cFFFTTFFFFT)))))
      (splitS chk 15 2 [false, true, false, false, false]
       (splitS chk 14 2 [true, false, true, false, false, false]
        (splitS chk 13 2 [true, true, false, true, false, false, false]
         (splitS chk 12 2 [true, true, true, false, true, false, false, false]
          (splitS chk 11 2 [true, true, true, true, false, true, false, false, false]
           cFFFTFTTTTT
           cFFFTFTTTTF)
          (splitS chk 11 1 [false, true, true, true, false, true, false, false, false]
           cFFFTFTTTFT
           cFFFTFTTTFF))
         (splitS chk 12 1 [false, true, true, false, true, false, false, false]
          (splitS chk 11 1 [true, false, true, true, false, true, false, false, false]
           cFFFTFTTFTT
           cFFFTFTTFTF)
          (splitS chk 11 0 [false, false, true, true, false, true, false, false, false]
           cFFFTFTTFFT
           cFFFTFTTFFF)))
        (splitS chk 13 1 [false, true, false, true, false, false, false]
         (splitS chk 12 1 [true, false, true, false, true, false, false, false]
          (splitS chk 11 1 [true, true, false, true, false, true, false, false, false]
           cFFFTFTFTTT
           cFFFTFTFTTF)
          (splitS chk 11 0 [false, true, false, true, false, true, false, false, false]
           cFFFTFTFTFT
           cFFFTFTFTFF))
         (splitS chk 12 0 [false, false, true, false, true, false, false, false]
          (splitS chk 11 0 [true, false, false, true, false, true, false, false, false]
           cFFFTFTFFTT
           cFFFTFTFFTF)
          (split0 chk 11 [false, false, false, true, false, true, false, false, false]
           cFFFTFTFFFT))))
       (splitS chk 14 1 [false, false, true, false, false, false]
        (splitS chk 13 1 [true, false, false, true, false, false, false]
         (splitS chk 12 1 [true, true, false, false, true, false, false, false]
          (splitS chk 11 1 [true, true, true, false, false, true, false, false, false]
           cFFFTFFTTTT
           cFFFTFFTTTF)
          (splitS chk 11 0 [false, true, true, false, false, true, false, false, false]
           cFFFTFFTTFT
           cFFFTFFTTFF))
         (splitS chk 12 0 [false, true, false, false, true, false, false, false]
          (splitS chk 11 0 [true, false, true, false, false, true, false, false, false]
           cFFFTFFTFTT
           cFFFTFFTFTF)
          (split0 chk 11 [false, false, true, false, false, true, false, false, false]
           cFFFTFFTFFT)))
        (splitS chk 13 0 [false, false, false, true, false, false, false]
         (splitS chk 12 0 [true, false, false, false, true, false, false, false]
          (splitS chk 11 0 [true, true, false, false, false, true, false, false, false]
           cFFFTFFFTTT
           cFFFTFFFTTF)
          (split0 chk 11 [false, true, false, false, false, true, false, false, false]
           cFFFTFFFTFT))
         (split0 chk 12 [false, false, false, false, true, false, false, false]
          (split0 chk 11 [true, false, false, false, false, true, false, false, false]
           cFFFTFFFFTT))))))
     (splitS chk 16 2 [false, false, false, false]
      (splitS chk 15 2 [true, false, false, false, false]
       (splitS chk 14 2 [true, true, false, false, false, false]
        (splitS chk 13 2 [true, true, true, false, false, false, false]
         (splitS chk 12 2 [true, true, true, true, false, false, false, false]
          (splitS chk 11 2 [true, true, true, true, true, false, false, false, false]
           cFFFFTTTTTT
           cFFFFTTTTTF)
          (splitS chk 11 1 [false, true, true, true, true, false, false, false, false]
           cFFFFTTTTFT
           cFFFFTTTTFF))
         (splitS chk 12 1 [false, true, true, true, false, false, false, false]
          (splitS chk 11 1 [true, false, true, true, true, false, false, false, false]
           cFFFFTTTFTT
           cFFFFTTTFTF)
          (splitS chk 11 0 [false, false, true, true, true, false, false, false, false]
           cFFFFTTTFFT
           cFFFFTTTFFF)))
        (splitS chk 13 1 [false, true, true, false, false, false, false]
         (splitS chk 12 1 [true, false, true, true, false, false, false, false]
          (splitS chk 11 1 [true, true, false, true, true, false, false, false, false]
           cFFFFTTFTTT
           cFFFFTTFTTF)
          (splitS chk 11 0 [false, true, false, true, true, false, false, false, false]
           cFFFFTTFTFT
           cFFFFTTFTFF))
         (splitS chk 12 0 [false, false, true, true, false, false, false, false]
          (splitS chk 11 0 [true, false, false, true, true, false, false, false, false]
           cFFFFTTFFTT
           cFFFFTTFFTF)
          (split0 chk 11 [false, false, false, true, true, false, false, false, false]
           cFFFFTTFFFT))))
       (splitS chk 14 1 [false, true, false, false, false, false]
        (splitS chk 13 1 [true, false, true, false, false, false, false]
         (splitS chk 12 1 [true, true, false, true, false, false, false, false]
          (splitS chk 11 1 [true, true, true, false, true, false, false, false, false]
           cFFFFTFTTTT
           cFFFFTFTTTF)
          (splitS chk 11 0 [false, true, true, false, true, false, false, false, false]
           cFFFFTFTTFT
           cFFFFTFTTFF))
         (splitS chk 12 0 [false, true, false, true, false, false, false, false]
          (splitS chk 11 0 [true, false, true, false, true, false, false, false, false]
           cFFFFTFTFTT
           cFFFFTFTFTF)
          (split0 chk 11 [false, false, true, false, true, false, false, false, false]
           cFFFFTFTFFT)))
        (splitS chk 13 0 [false, false, true, false, false, false, false]
         (splitS chk 12 0 [true, false, false, true, false, false, false, false]
          (splitS chk 11 0 [true, true, false, false, true, false, false, false, false]
           cFFFFTFFTTT
           cFFFFTFFTTF)
          (split0 chk 11 [false, true, false, false, true, false, false, false, false]
           cFFFFTFFTFT))
         (split0 chk 12 [false, false, false, true, false, false, false, false]
          (split0 chk 11 [true, false, false, false, true, false, false, false, false]
           cFFFFTFFFTT)))))
      (splitS chk 15 1 [false, false, false, false, false]
       (splitS chk 14 1 [true, false, false, false, false, false]
        (splitS chk 13 1 [true, true, false, false, false, false, false]
         (splitS chk 12 1 [true, true, true, false, false, false, false, false]
          (splitS chk 11 1 [true, true, true, true, false, false, false, false, false]
           cFFFFFTTTTT
           cFFFFFTTTTF)
          (splitS chk 11 0 [false, true, true, true, false, false, false, false, false]
           cFFFFFTTTFT
           cFFFFFTTTFF))
         (splitS chk 12 0 [false, true, true, false, false, false, false, false]
          (splitS chk 11 0 [true, false, true, true, false, false, false, false, false]
           cFFFFFTTFTT
           cFFFFFTTFTF)
          (split0 chk 11 [false, false, true, true, false, false, false, false, false]
           cFFFFFTTFFT)))
        (splitS chk 13 0 [false, true, false, false, false, false, false]
         (splitS chk 12 0 [true, false, true, false, false, false, false, false]
          (splitS chk 11 0 [true, true, false, true, false, false, false, false, false]
           cFFFFFTFTTT
           cFFFFFTFTTF)
          (split0 chk 11 [false, true, false, true, false, false, false, false, false]
           cFFFFFTFTFT))
         (split0 chk 12 [false, false, true, false, false, false, false, false]
          (split0 chk 11 [true, false, false, true, false, false, false, false, false]
           cFFFFFTFFTT))))
       (splitS chk 14 0 [false, false, false, false, false, false]
        (splitS chk 13 0 [true, false, false, false, false, false, false]
         (splitS chk 12 0 [true, true, false, false, false, false, false, false]
          (splitS chk 11 0 [true, true, true, false, false, false, false, false, false]
           cFFFFFFTTTT
           cFFFFFFTTTF)
          (split0 chk 11 [false, true, true, false, false, false, false, false, false]
           cFFFFFFTTFT))
         (split0 chk 12 [false, true, false, false, false, false, false, false]
          (split0 chk 11 [true, false, true, false, false, false, false, false, false]
           cFFFFFFTFTT)))
        (split0 chk 13 [false, false, false, false, false, false, false]
         (split0 chk 12 [true, false, false, false, false, false, false, false]
          (split0 chk 11 [true, true, false, false, false, false, false, false, false]
           cFFFFFFFTTT))))))))))

end BK73
