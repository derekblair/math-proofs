import RibbonD3WideSlopeData0
import RibbonD3WideSlopeData1
import RibbonD3WideSlopeData2
import RibbonD3WideSlopeData3
import RibbonD3WideSlopeData4
import RibbonD3WideSlopeData5
import RibbonD3WideSlopeData6
import RibbonD3WideSlopeData7
import RibbonD3WideSlopeData8
import RibbonD3WideSlopeData9
import RibbonD3WideSlopeData10
import RibbonD3WideSlopeData11
import RibbonD3WideSlopeData12
import RibbonD3WideSlopeData13
import RibbonD3WideSlopeData14
import RibbonD3WideSlopeData15
import RibbonD3WideSlopeData16
import RibbonD3WideSlopeData17
import RibbonD3WideSlopeData18
import RibbonD3WideSlopeData19
import RibbonD3WideSlopeData20
import RibbonD3WideSlopeData21
namespace RibbonD3Wide
open RibbonD3Field
open RibbonAffine (pl)
variable {K : Type*} [Field K]

structure GoodSlope where
  index : Nat
  certificate : SlopeCertificate
  sound : certificateValid bank (branch index) certificate

instance : Inhabited GoodSlope := ⟨⟨0,s0,s0_valid⟩⟩
def checkedSlopes : Array GoodSlope := #[
⟨0,s0,s0_valid⟩,
⟨1,s1,s1_valid⟩,
⟨2,s2,s2_valid⟩,
⟨3,s3,s3_valid⟩,
⟨4,s4,s4_valid⟩,
⟨5,s5,s5_valid⟩,
⟨6,s6,s6_valid⟩,
⟨7,s7,s7_valid⟩,
⟨8,s8,s8_valid⟩,
⟨9,s9,s9_valid⟩,
⟨10,s10,s10_valid⟩,
⟨11,s11,s11_valid⟩,
⟨12,s12,s12_valid⟩,
⟨13,s13,s13_valid⟩,
⟨14,s14,s14_valid⟩,
⟨15,s15,s15_valid⟩,
⟨16,s16,s16_valid⟩,
⟨17,s17,s17_valid⟩,
⟨18,s18,s18_valid⟩,
⟨19,s19,s19_valid⟩,
⟨20,s20,s20_valid⟩,
⟨21,s21,s21_valid⟩,
⟨22,s22,s22_valid⟩,
⟨23,s23,s23_valid⟩,
⟨24,s24,s24_valid⟩,
⟨25,s25,s25_valid⟩,
⟨26,s26,s26_valid⟩,
⟨27,s27,s27_valid⟩,
⟨28,s28,s28_valid⟩,
⟨29,s29,s29_valid⟩,
⟨30,s30,s30_valid⟩,
⟨31,s31,s31_valid⟩,
⟨32,s32,s32_valid⟩,
⟨33,s33,s33_valid⟩,
⟨34,s34,s34_valid⟩,
⟨35,s35,s35_valid⟩,
⟨36,s36,s36_valid⟩,
⟨37,s37,s37_valid⟩,
⟨38,s38,s38_valid⟩,
⟨39,s39,s39_valid⟩,
⟨40,s40,s40_valid⟩,
⟨41,s41,s41_valid⟩,
⟨42,s42,s42_valid⟩,
⟨43,s43,s43_valid⟩,
⟨44,s44,s44_valid⟩,
⟨45,s45,s45_valid⟩,
⟨46,s46,s46_valid⟩,
⟨47,s47,s47_valid⟩,
⟨48,s48,s48_valid⟩,
⟨49,s49,s49_valid⟩,
⟨50,s50,s50_valid⟩,
⟨51,s51,s51_valid⟩,
⟨52,s52,s52_valid⟩,
⟨53,s53,s53_valid⟩,
⟨54,s54,s54_valid⟩,
⟨55,s55,s55_valid⟩,
⟨56,s56,s56_valid⟩,
⟨57,s57,s57_valid⟩,
⟨58,s58,s58_valid⟩,
⟨59,s59,s59_valid⟩,
⟨60,s60,s60_valid⟩,
⟨61,s61,s61_valid⟩,
⟨62,s62,s62_valid⟩,
⟨63,s63,s63_valid⟩,
⟨64,s64,s64_valid⟩,
⟨65,s65,s65_valid⟩,
⟨66,s66,s66_valid⟩,
⟨67,s67,s67_valid⟩,
⟨68,s68,s68_valid⟩,
⟨69,s69,s69_valid⟩,
⟨70,s70,s70_valid⟩,
⟨71,s71,s71_valid⟩,
⟨72,s72,s72_valid⟩,
⟨73,s73,s73_valid⟩,
⟨74,s74,s74_valid⟩,
⟨75,s75,s75_valid⟩,
⟨76,s76,s76_valid⟩,
⟨77,s77,s77_valid⟩,
⟨78,s78,s78_valid⟩,
⟨79,s79,s79_valid⟩,
⟨80,s80,s80_valid⟩,
⟨81,s81,s81_valid⟩,
⟨82,s82,s82_valid⟩,
⟨83,s83,s83_valid⟩,
⟨84,s84,s84_valid⟩,
⟨85,s85,s85_valid⟩,
⟨86,s86,s86_valid⟩,
⟨87,s87,s87_valid⟩]
theorem checked_index : ∀ i : Fin 88, checkedSlopes[i.val]!.index=i.val := by decide +kernel

theorem slope_cases (i : Fin 88) (t : Kˣ) (n : Nat) (odd : Odd n)
    (tN : t^n=1) (t1 : t≠1) (a1 : t^(branch i.val).v≠1)
    (two : (2:K)≠0) (three : (3:K)≠0) (F : pl t 1 (branch i.val).p=0) :
    (∃ k, Ordered (chart k) (t^(branch i.val).v) (t^(-(branch i.val).u))) ∨
      ScalarPair (t^(branch i.val).v) (t^(-(branch i.val).u)) := by
  have S := checkedSlopes[i.val]!.sound
  rw [checked_index i] at S
  exact cert_sound bank bank_valid _ _ S t n odd tN t1 a1 two three F

end RibbonD3Wide
#print axioms RibbonD3Wide.slope_cases
