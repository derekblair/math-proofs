import RibbonStationarySlopeStitch
import RibbonStationaryModData0
import RibbonStationaryModData1
import RibbonStationaryModData2
import RibbonStationaryModData3
import RibbonStationaryModData4
import RibbonStationaryModData5
import RibbonStationaryModData6
import RibbonStationaryModData7
import RibbonStationaryModData8
import RibbonStationaryModData9

namespace RibbonStationaryField
open RibbonStationaryWord
open RibbonAffine (pl)
variable {K : Type*} [Field K]

private theorem fromChunk0 : Chunk 0 8 := by
  intro s
  refine ⟨data0[s.val]!,valid0 s,geom0 s,?_⟩
  intro k
  exact ⟨mp0 s k.val,modProof0 s k⟩

private theorem fromChunk1 : Chunk 8 8 := by
  intro s
  refine ⟨data1[s.val]!,valid1 s,geom1 s,?_⟩
  intro k
  exact ⟨mp1 s k.val,modProof1 s k⟩

private theorem fromChunk2 : Chunk 16 8 := by
  intro s
  refine ⟨data2[s.val]!,valid2 s,geom2 s,?_⟩
  intro k
  exact ⟨mp2 s k.val,modProof2 s k⟩

private theorem fromChunk3 : Chunk 24 8 := by
  intro s
  refine ⟨data3[s.val]!,valid3 s,geom3 s,?_⟩
  intro k
  exact ⟨mp3 s k.val,modProof3 s k⟩

private theorem fromChunk4 : Chunk 32 8 := by
  intro s
  refine ⟨data4[s.val]!,valid4 s,geom4 s,?_⟩
  intro k
  exact ⟨mp4 s k.val,modProof4 s k⟩

private theorem fromChunk5 : Chunk 40 8 := by
  intro s
  refine ⟨data5[s.val]!,valid5 s,geom5 s,?_⟩
  intro k
  exact ⟨mp5 s k.val,modProof5 s k⟩

private theorem fromChunk6 : Chunk 48 8 := by
  intro s
  refine ⟨data6[s.val]!,valid6 s,geom6 s,?_⟩
  intro k
  exact ⟨mp6 s k.val,modProof6 s k⟩

private theorem fromChunk7 : Chunk 56 8 := by
  intro s
  refine ⟨data7[s.val]!,valid7 s,geom7 s,?_⟩
  intro k
  exact ⟨mp7 s k.val,modProof7 s k⟩

private theorem fromChunk8 : Chunk 64 8 := by
  intro s
  refine ⟨data8[s.val]!,valid8 s,geom8 s,?_⟩
  intro k
  exact ⟨mp8 s k.val,modProof8 s k⟩

private theorem fromChunk9 : Chunk 72 4 := by
  intro s
  refine ⟨data9[s.val]!,valid9 s,geom9 s,?_⟩
  intro k
  exact ⟨mp9 s k.val,modProof9 s k⟩

theorem slope_pack (r : Fin 76) : Verified (branch r.val) :=
  stitch fromChunk0 fromChunk1 fromChunk2 fromChunk3 fromChunk4 fromChunk5 fromChunk6 fromChunk7 fromChunk8 fromChunk9 r

theorem slope_full (r : Fin 76) (t : Kˣ) (n : Nat) (two : (2:K)≠0) (odd : Odd n) (no3 : ¬3∣n)
    (tn : t^n=1) (nt : t≠1) (F : pl t 1 (branch r.val).p=0) :
    (∃ k : Count, separates (t^(branch r.val).v) (t^(-(branch r.val).u)) k) ∨
      ((11:K)=0 ∧ ((t:K)=3 ∨ (t:K)=4 ∨ (t:K)=5 ∨ (t:K)=9)) := by
  obtain ⟨C,R,G,M⟩ := slope_pack r
  exact (slope_use _ C R G M t n two odd no3 tn nt F).imp_left (fun h => ⟨_,h⟩)

end RibbonStationaryField
#print axioms RibbonStationaryField.slope_full
