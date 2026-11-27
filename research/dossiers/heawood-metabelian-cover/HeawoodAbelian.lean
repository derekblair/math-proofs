import HeawoodRows0
import HeawoodRows1
import HeawoodRows2
import HeawoodRows3
import HeawoodRows4
import HeawoodRows5
import HeawoodRows6
namespace HeawoodCert
open HaarOrbitC7Voltage
open HaarOrbitC7DAG (Vanish)
variable {A : Type*} [AddCommGroup A]
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def h25 : V := ![1,0,0,0,0,0,0,0]
def h26 : V := ![1,0,2,0,0,0,0,0]
def h27 : V := ![0,0,-1,0,0,0,0,0]
def h28 : V := ![1,0,-1,0,0,0,0,0]
def h29 : V := ![0,0,-2,0,0,0,0,0]
def h32 : V := ![0,0,-1,0,1,-1,0,1]

theorem obstruction (φ : V →+ A) (F : NoCycles φ) : False := by
  let L : List V := []
  have Z : Vanish φ L := vanish_nil φ
  have sep1 : ∀ v ∈ row1.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row1,List.mem_cons,List.not_mem_nil,or_false] at hv
  have hn1 : φ row1.closing≠0 := force φ F row1 check1 sep1
  have sep2 : ∀ v ∈ row2.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row2,List.mem_cons,List.not_mem_nil,or_false] at hv
  have hn2 : φ row2.closing≠0 := force φ F row2 check2 sep2
  have sep3 : ∀ v ∈ row3.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row3,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl
    · exact via_deps φ L Z _ row2.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn2
    · exact via_deps φ L Z _ row1.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn1
  have hn3 : φ row3.closing≠0 := force φ F row3 check3 sep3
  have sep4 : ∀ v ∈ row4.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row4,List.mem_cons,List.not_mem_nil,or_false] at hv
  have hn4 : φ row4.closing≠0 := force φ F row4 check4 sep4
  have sep5 : ∀ v ∈ row5.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row5,List.mem_cons,List.not_mem_nil,or_false] at hv
  have hn5 : φ row5.closing≠0 := force φ F row5 check5 sep5
  have sep6 : ∀ v ∈ row6.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row6,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl
    · exact via_deps φ L Z _ row4.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn4
    · exact via_deps φ L Z _ row5.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn5
  have hn6 : φ row6.closing≠0 := force φ F row6 check6 sep6
  have sep7 : ∀ v ∈ row7.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row7,List.mem_cons,List.not_mem_nil,or_false] at hv
  have hn7 : φ row7.closing≠0 := force φ F row7 check7 sep7
  have sep8 : ∀ v ∈ row8.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row8,List.mem_cons,List.not_mem_nil,or_false] at hv
  have hn8 : φ row8.closing≠0 := force φ F row8 check8 sep8
  have sep9 : ∀ v ∈ row9.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row9,List.mem_cons,List.not_mem_nil,or_false] at hv
  have hn9 : φ row9.closing≠0 := force φ F row9 check9 sep9
  have sep10 : ∀ v ∈ row10.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row10,List.mem_cons,List.not_mem_nil,or_false] at hv
  have hn10 : φ row10.closing≠0 := force φ F row10 check10 sep10
  have sep11 : ∀ v ∈ row11.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row11,List.mem_cons,List.not_mem_nil,or_false] at hv
  have hn11 : φ row11.closing≠0 := force φ F row11 check11 sep11
  have sep12 : ∀ v ∈ row12.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row12,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl
    · exact via_deps φ L Z _ row10.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn10
    · exact via_deps φ L Z _ row11.closing (1:ℤ) (by decide) ([]) (by decide +kernel) hn11
  have hn12 : φ row12.closing≠0 := force φ F row12 check12 sep12
  have sep13 : ∀ v ∈ row13.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row13,List.mem_cons,List.not_mem_nil,or_false] at hv
    subst v
    exact via_deps φ L Z _ row9.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn9
  have hn13 : φ row13.closing≠0 := force φ F row13 check13 sep13
  have sep14 : ∀ v ∈ row14.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row14,List.mem_cons,List.not_mem_nil,or_false] at hv
    subst v
    exact via_deps φ L Z _ row9.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn9
  have hn14 : φ row14.closing≠0 := force φ F row14 check14 sep14
  have sep15 : ∀ v ∈ row15.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row15,List.mem_cons,List.not_mem_nil,or_false] at hv
  have hn15 : φ row15.closing≠0 := force φ F row15 check15 sep15
  have sep16 : ∀ v ∈ row16.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row16,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl
    · exact via_deps φ L Z _ row9.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn9
    · exact via_deps φ L Z _ row15.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn15
  have hn16 : φ row16.closing≠0 := force φ F row16 check16 sep16
  have sep17 : ∀ v ∈ row17.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row17,List.mem_cons,List.not_mem_nil,or_false] at hv
  have hn17 : φ row17.closing≠0 := force φ F row17 check17 sep17
  have sep18 : ∀ v ∈ row18.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row18,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl
    · exact via_deps φ L Z _ row9.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn9
    · exact via_deps φ L Z _ row17.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn17
  have hn18 : φ row18.closing≠0 := force φ F row18 check18 sep18
  have sep19 : ∀ v ∈ row19.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row19,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl
    · exact via_deps φ L Z _ row1.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn1
    · exact via_deps φ L Z _ row5.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn5
  have hn19 : φ row19.closing≠0 := force φ F row19 check19 sep19
  have sep20 : ∀ v ∈ row20.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row20,List.mem_cons,List.not_mem_nil,or_false] at hv
  have hn20 : φ row20.closing≠0 := force φ F row20 check20 sep20
  have sep21 : ∀ v ∈ row21.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row21,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl
    · exact via_deps φ L Z _ row8.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn8
    · exact via_deps φ L Z _ row20.closing (1:ℤ) (by decide) ([]) (by decide +kernel) hn20
  have hn21 : φ row21.closing≠0 := force φ F row21 check21 sep21
  have sep22 : ∀ v ∈ row22.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row22,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl
    · exact via_deps φ L Z _ row4.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn4
    · exact via_deps φ L Z _ row1.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn1
  have hn22 : φ row22.closing≠0 := force φ F row22 check22 sep22
  have sep23 : ∀ v ∈ row23.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row23,List.mem_cons,List.not_mem_nil,or_false] at hv
    subst v
    exact via_deps φ L Z _ row8.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn8
  have hn23 : φ row23.closing≠0 := force φ F row23 check23 sep23
  have sep24 : ∀ v ∈ row24.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row24,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl
    · exact via_deps φ L Z _ row7.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn7
    · exact via_deps φ L Z _ row8.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn8
  have hn24 : φ row24.closing≠0 := force φ F row24 check24 sep24
  have hn25 : φ h25≠0 := by
    intro zero
    let L := [h25]
    have Z : Vanish φ L := vanish_one φ h25 zero
    have sep25 : ∀ v ∈ row25.repeats, φ v ≠ 0 := by
      intro v hv
      simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact via_deps φ L Z _ row7.closing (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn7
      · exact via_deps φ L Z _ row10.closing (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn10
      · exact via_deps φ L Z _ row3.closing (1:ℤ) (by decide) ([-1]) (by decide +kernel) hn3
      · exact via_deps φ L Z _ row12.closing (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn12
      · exact via_deps φ L Z _ row9.closing (-1:ℤ) (by decide) ([1]) (by decide +kernel) hn9
      · exact via_deps φ L Z _ row6.closing (-1:ℤ) (by decide) ([1]) (by decide +kernel) hn6
      · exact via_deps φ L Z _ row1.closing (1:ℤ) (by decide) ([-1]) (by decide +kernel) hn1
      · exact via_deps φ L Z _ row8.closing (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn8
      · exact via_deps φ L Z _ row4.closing (-1:ℤ) (by decide) ([1]) (by decide +kernel) hn4
    exact force φ F row25 check25 sep25 (via_zero φ L Z _ [0] (by decide +kernel))
  have hn26 : φ h26≠0 := by
    intro zero
    let L := [h26]
    have Z : Vanish φ L := vanish_one φ h26 zero
    have sep26 : ∀ v ∈ row26.repeats, φ v ≠ 0 := by
      intro v hv
      simp only [row26,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact via_deps φ L Z _ row14.closing (1:ℤ) (by decide) ([0]) (by decide +kernel) hn14
      · exact via_deps φ L Z _ row9.closing (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn9
      · exact via_deps φ L Z _ row15.closing (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn15
      · exact via_deps φ L Z _ row13.closing (-1:ℤ) (by decide) ([1]) (by decide +kernel) hn13
      · exact via_deps φ L Z _ row14.closing (1:ℤ) (by decide) ([1]) (by decide +kernel) hn14
      · exact via_deps φ L Z _ row9.closing (1:ℤ) (by decide) ([-1]) (by decide +kernel) hn9
      · exact via_deps φ L Z _ row16.closing (-1:ℤ) (by decide) ([-1]) (by decide +kernel) hn16
    exact force φ F row26 check26 sep26 (via_zero φ L Z _ [-1] (by decide +kernel))
  have hn27 : φ h27≠0 := by
    intro zero
    let L := [h27]
    have Z : Vanish φ L := vanish_one φ h27 zero
    have sep27 : ∀ v ∈ row27.repeats, φ v ≠ 0 := by
      intro v hv
      simp only [row27,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact via_deps φ L Z _ row21.closing (1:ℤ) (by decide) ([0]) (by decide +kernel) hn21
      · exact via_deps φ L Z _ row1.closing (-1:ℤ) (by decide) ([1]) (by decide +kernel) hn1
      · exact via_deps φ L Z _ row19.closing (-1:ℤ) (by decide) ([1]) (by decide +kernel) hn19
      · exact via_deps φ L Z _ row9.closing (-1:ℤ) (by decide) ([-1]) (by decide +kernel) hn9
      · exact via_deps φ L Z _ row8.closing (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn8
      · exact via_deps φ L Z _ row5.closing (1:ℤ) (by decide) ([1]) (by decide +kernel) hn5
      · exact via_deps φ L Z _ row17.closing (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn17
      · exact via_deps φ L Z _ row18.closing (-1:ℤ) (by decide) ([1]) (by decide +kernel) hn18
      · exact via_deps φ L Z _ row20.closing (1:ℤ) (by decide) ([0]) (by decide +kernel) hn20
    exact force φ F row27 check27 sep27 (via_zero φ L Z _ [0] (by decide +kernel))
  have hn28 : φ h28≠0 := by
    intro zero
    let L := [h28]
    have Z : Vanish φ L := vanish_one φ h28 zero
    have sep28 : ∀ v ∈ row28.repeats, φ v ≠ 0 := by
      intro v hv
      simp only [row28,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact via_deps φ L Z _ row4.closing (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn4
      · exact via_deps φ L Z _ h25 (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn25
      · exact via_deps φ L Z _ row12.closing (1:ℤ) (by decide) ([-1]) (by decide +kernel) hn12
      · exact via_deps φ L Z _ row7.closing (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn7
      · exact via_deps φ L Z _ row10.closing (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn10
      · exact via_deps φ L Z _ row12.closing (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn12
      · exact via_deps φ L Z _ h25 (-1:ℤ) (by decide) ([1]) (by decide +kernel) hn25
      · exact via_deps φ L Z _ row22.closing (1:ℤ) (by decide) ([1]) (by decide +kernel) hn22
    exact force φ F row28 check28 sep28 (via_zero φ L Z _ [1] (by decide +kernel))
  have hn29 : φ h29≠0 := by
    intro zero
    by_cases hm : φ h32≠0
    · let L := [h29]
      have Z : Vanish φ L := vanish_one φ h29 zero
      have sep29 : ∀ v ∈ row29.repeats, φ v ≠ 0 := by
        intro v hv
        simp only [row29,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        · exact via_deps φ L Z _ h25 (-1:ℤ) (by decide) ([1]) (by decide +kernel) hn25
        · exact via_deps φ L Z _ row22.closing (1:ℤ) (by decide) ([1]) (by decide +kernel) hn22
        · exact via_deps φ L Z _ row9.closing (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn9
        · exact via_deps φ L Z _ row4.closing (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn4
        · exact via_deps φ L Z _ h25 (-1:ℤ) (by decide) ([0]) (by decide +kernel) hn25
        · exact via_deps φ L Z _ row22.closing (1:ℤ) (by decide) ([0]) (by decide +kernel) hn22
        · exact via_deps φ L Z _ h27 (1:ℤ) (by decide) ([0]) (by decide +kernel) hn27
        · exact via_deps φ L Z _ h32 (1:ℤ) (by decide) ([0]) (by decide +kernel) hm
      exact force φ F row29 check29 sep29 (via_zero φ L Z _ [1] (by decide +kernel))
    · let L := [h29,h32]
      have Z : Vanish φ L := vanish_two φ h29 h32 zero (not_not.mp hm)
      have sep30 : ∀ v ∈ row30.repeats, φ v ≠ 0 := by
        intro v hv
        simp only [row30,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        · exact via_deps φ L Z _ row24.closing (-1:ℤ) (by decide) ([0, 1]) (by decide +kernel) hn24
        · exact via_deps φ L Z _ row10.closing (-1:ℤ) (by decide) ([0, 0]) (by decide +kernel) hn10
        · exact via_deps φ L Z _ row10.closing (-1:ℤ) (by decide) ([0, -1]) (by decide +kernel) hn10
        · exact via_deps φ L Z _ row23.closing (-1:ℤ) (by decide) ([0, -1]) (by decide +kernel) hn23
        · exact via_deps φ L Z _ row12.closing (-1:ℤ) (by decide) ([0, -1]) (by decide +kernel) hn12
        · exact via_deps φ L Z _ row8.closing (-1:ℤ) (by decide) ([0, 1]) (by decide +kernel) hn8
        · exact via_deps φ L Z _ h27 (1:ℤ) (by decide) ([0, 0]) (by decide +kernel) hn27
        · exact via_deps φ L Z _ row8.closing (-1:ℤ) (by decide) ([0, 0]) (by decide +kernel) hn8
      exact force φ F row30 check30 sep30 (via_zero φ L Z _ [0, -1] (by decide +kernel))
  have sep31 : ∀ v ∈ row31.repeats, φ v ≠ 0 := by
    intro v hv
    simp only [row31,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl|rfl|rfl|rfl
    · exact via_deps φ L Z _ h26 (-1:ℤ) (by decide) ([]) (by decide +kernel) hn26
    · exact via_deps φ L Z _ row9.closing (-1:ℤ) (by decide) ([]) (by decide +kernel) hn9
    · exact via_deps φ L Z _ h25 (-1:ℤ) (by decide) ([]) (by decide +kernel) hn25
    · exact via_deps φ L Z _ h28 (-1:ℤ) (by decide) ([]) (by decide +kernel) hn28
    · exact via_deps φ L Z _ h29 (1:ℤ) (by decide) ([]) (by decide +kernel) hn29
    · exact via_deps φ L Z _ h27 (1:ℤ) (by decide) ([]) (by decide +kernel) hn27
  exact force φ F row31 check31 sep31 (via_zero φ L Z _ [] (by decide +kernel))

theorem any_voltage (φ : V →+ A) : ∃ n, n ∈ [8,16,32] ∧ HasCycle φ n := by
  classical
  by_contra! h
  exact obstruction φ h

theorem every_regular_abelian_voltage (W : B → B → A) (anti : ∀ u v, W v u = -W u v) :
    ∃ n, n ∈ [8,16,32] ∧ HaarOrbitC7RealCover.HasCycle W n := by
  obtain ⟨n,hn,cv⟩ := any_voltage (HaarOrbitC7Gauge.map W)
  refine ⟨n,hn,HaarOrbitC7RealCover.real (by simp at hn; omega) W ?_⟩
  exact HaarOrbitC7Gauge.ungauge W anti cv

end HeawoodCert
#print axioms HeawoodCert.every_regular_abelian_voltage
