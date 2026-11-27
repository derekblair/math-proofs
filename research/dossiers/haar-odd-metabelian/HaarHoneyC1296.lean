import HaarHoneyData
namespace HaarHoneyData
open HaarHoneyDAG HaarHoneyVoltage
set_option maxRecDepth 24000
set_option maxHeartbeats 0
private theorem ok1296 : valid D 1296 := by decide +kernel
private theorem ok1297 : valid D 1297 := by decide +kernel
private theorem ok1298 : valid D 1298 := by decide +kernel
private theorem ok1299 : valid D 1299 := by decide +kernel
private theorem ok1300 : valid D 1300 := by decide +kernel
private theorem ok1301 : valid D 1301 := by decide +kernel
private theorem ok1302 : valid D 1302 := by decide +kernel
private theorem ok1303 : valid D 1303 := by decide +kernel
private theorem ok1304 : valid D 1304 := by decide +kernel
private theorem ok1305 : valid D 1305 := by decide +kernel
private theorem ok1306 : valid D 1306 := by decide +kernel
private theorem ok1307 : valid D 1307 := by decide +kernel
private theorem ok1308 : valid D 1308 := by decide +kernel
private theorem ok1309 : valid D 1309 := by decide +kernel
private theorem ok1310 : valid D 1310 := by decide +kernel
private theorem ok1311 : valid D 1311 := by decide +kernel
private theorem ok1312 : valid D 1312 := by decide +kernel
private theorem ok1313 : valid D 1313 := by decide +kernel
private theorem ok1314 : valid D 1314 := by decide +kernel
private theorem ok1315 : valid D 1315 := by decide +kernel
private theorem ok1316 : valid D 1316 := by decide +kernel
private theorem ok1317 : valid D 1317 := by decide +kernel
private theorem ok1318 : valid D 1318 := by decide +kernel
private theorem ok1319 : valid D 1319 := by decide +kernel
theorem C1296valid (i : Nat) (_lo : 1296 ≤ i) (_hi : i < 1320) : valid D i := by
  by_cases h1296_1320 : i < 1308
  · by_cases h1296_1308 : i < 1302
    · by_cases h1296_1302 : i < 1299
      · by_cases h1296_1299 : i < 1297
        · have e : i = 1296 := by omega
          subst i
          exact ok1296
        · by_cases h1297_1299 : i < 1298
          · have e : i = 1297 := by omega
            subst i
            exact ok1297
          · have e : i = 1298 := by omega
            subst i
            exact ok1298
      · by_cases h1299_1302 : i < 1300
        · have e : i = 1299 := by omega
          subst i
          exact ok1299
        · by_cases h1300_1302 : i < 1301
          · have e : i = 1300 := by omega
            subst i
            exact ok1300
          · have e : i = 1301 := by omega
            subst i
            exact ok1301
    · by_cases h1302_1308 : i < 1305
      · by_cases h1302_1305 : i < 1303
        · have e : i = 1302 := by omega
          subst i
          exact ok1302
        · by_cases h1303_1305 : i < 1304
          · have e : i = 1303 := by omega
            subst i
            exact ok1303
          · have e : i = 1304 := by omega
            subst i
            exact ok1304
      · by_cases h1305_1308 : i < 1306
        · have e : i = 1305 := by omega
          subst i
          exact ok1305
        · by_cases h1306_1308 : i < 1307
          · have e : i = 1306 := by omega
            subst i
            exact ok1306
          · have e : i = 1307 := by omega
            subst i
            exact ok1307
  · by_cases h1308_1320 : i < 1314
    · by_cases h1308_1314 : i < 1311
      · by_cases h1308_1311 : i < 1309
        · have e : i = 1308 := by omega
          subst i
          exact ok1308
        · by_cases h1309_1311 : i < 1310
          · have e : i = 1309 := by omega
            subst i
            exact ok1309
          · have e : i = 1310 := by omega
            subst i
            exact ok1310
      · by_cases h1311_1314 : i < 1312
        · have e : i = 1311 := by omega
          subst i
          exact ok1311
        · by_cases h1312_1314 : i < 1313
          · have e : i = 1312 := by omega
            subst i
            exact ok1312
          · have e : i = 1313 := by omega
            subst i
            exact ok1313
    · by_cases h1314_1320 : i < 1317
      · by_cases h1314_1317 : i < 1315
        · have e : i = 1314 := by omega
          subst i
          exact ok1314
        · by_cases h1315_1317 : i < 1316
          · have e : i = 1315 := by omega
            subst i
            exact ok1315
          · have e : i = 1316 := by omega
            subst i
            exact ok1316
      · by_cases h1317_1320 : i < 1318
        · have e : i = 1317 := by omega
          subst i
          exact ok1317
        · by_cases h1318_1320 : i < 1319
          · have e : i = 1318 := by omega
            subst i
            exact ok1318
          · have e : i = 1319 := by omega
            subst i
            exact ok1319
end HaarHoneyData
