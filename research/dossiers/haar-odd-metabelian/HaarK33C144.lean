import HaarK33Data
namespace HaarK33Data
open HaarK33DAG HaarK33Voltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok144 : valid D 144 := by decide +kernel
private theorem ok145 : valid D 145 := by decide +kernel
private theorem ok146 : valid D 146 := by decide +kernel
private theorem ok147 : valid D 147 := by decide +kernel
private theorem ok148 : valid D 148 := by decide +kernel
private theorem ok149 : valid D 149 := by decide +kernel
private theorem ok150 : valid D 150 := by decide +kernel
private theorem ok151 : valid D 151 := by decide +kernel
private theorem ok152 : valid D 152 := by decide +kernel
private theorem ok153 : valid D 153 := by decide +kernel
private theorem ok154 : valid D 154 := by decide +kernel
private theorem ok155 : valid D 155 := by decide +kernel
private theorem ok156 : valid D 156 := by decide +kernel
private theorem ok157 : valid D 157 := by decide +kernel
private theorem ok158 : valid D 158 := by decide +kernel
private theorem ok159 : valid D 159 := by decide +kernel
theorem C144valid (i : Nat) (_lo : 144 ≤ i) (_hi : i < 160) : valid D i := by
  by_cases h144_160 : i < 152
  · by_cases h144_152 : i < 148
    · by_cases h144_148 : i < 146
      · by_cases h144_146 : i < 145
        · have e : i = 144 := by omega
          subst i
          exact ok144
        · have e : i = 145 := by omega
          subst i
          exact ok145
      · by_cases h146_148 : i < 147
        · have e : i = 146 := by omega
          subst i
          exact ok146
        · have e : i = 147 := by omega
          subst i
          exact ok147
    · by_cases h148_152 : i < 150
      · by_cases h148_150 : i < 149
        · have e : i = 148 := by omega
          subst i
          exact ok148
        · have e : i = 149 := by omega
          subst i
          exact ok149
      · by_cases h150_152 : i < 151
        · have e : i = 150 := by omega
          subst i
          exact ok150
        · have e : i = 151 := by omega
          subst i
          exact ok151
  · by_cases h152_160 : i < 156
    · by_cases h152_156 : i < 154
      · by_cases h152_154 : i < 153
        · have e : i = 152 := by omega
          subst i
          exact ok152
        · have e : i = 153 := by omega
          subst i
          exact ok153
      · by_cases h154_156 : i < 155
        · have e : i = 154 := by omega
          subst i
          exact ok154
        · have e : i = 155 := by omega
          subst i
          exact ok155
    · by_cases h156_160 : i < 158
      · by_cases h156_158 : i < 157
        · have e : i = 156 := by omega
          subst i
          exact ok156
        · have e : i = 157 := by omega
          subst i
          exact ok157
      · by_cases h158_160 : i < 159
        · have e : i = 158 := by omega
          subst i
          exact ok158
        · have e : i = 159 := by omega
          subst i
          exact ok159
end HaarK33Data
