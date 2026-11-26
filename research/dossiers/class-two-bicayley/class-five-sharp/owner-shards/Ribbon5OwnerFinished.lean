import Ribbon5OwnerShardR000000
import Ribbon5OwnerShardR000002
import Ribbon5OwnerShardR000020
import Ribbon5OwnerShardR000021
import Ribbon5OwnerShardR000200
import Ribbon5OwnerShardR000202
import Ribbon5OwnerShardR000211
import Ribbon5OwnerShardR000212
import Ribbon5OwnerShardR002000
import Ribbon5OwnerShardR002002
import Ribbon5OwnerShardR002020
import Ribbon5OwnerShardR002021
import Ribbon5OwnerShardR002111
import Ribbon5OwnerShardR002112
import Ribbon5OwnerShardR002120
import Ribbon5OwnerShardR002121
import Ribbon5OwnerShardR011111
import Ribbon5OwnerShardR011112
import Ribbon5OwnerShardR011120
import Ribbon5OwnerShardR011121
import Ribbon5OwnerShardR011200
import Ribbon5OwnerShardR011202
import Ribbon5OwnerShardR011211
import Ribbon5OwnerShardR011212
import Ribbon5OwnerShardR012000
import Ribbon5OwnerShardR012002
import Ribbon5OwnerShardR012020
import Ribbon5OwnerShardR012021
import Ribbon5OwnerShardR012111
import Ribbon5OwnerShardR012112
import Ribbon5OwnerShardR012120
import Ribbon5OwnerShardR012121
import Ribbon5OwnerShardR020000
import Ribbon5OwnerShardR020002
import Ribbon5OwnerShardR020020
import Ribbon5OwnerShardR020021
import Ribbon5OwnerShardR020200
import Ribbon5OwnerShardR020202
import Ribbon5OwnerShardR020211
import Ribbon5OwnerShardR020212
import Ribbon5OwnerShardR021111
import Ribbon5OwnerShardR021112
import Ribbon5OwnerShardR021120
import Ribbon5OwnerShardR021121
import Ribbon5OwnerShardR021200
import Ribbon5OwnerShardR021202
import Ribbon5OwnerShardR021211
import Ribbon5OwnerShardR021212
import Ribbon5OwnerShardR100000
import Ribbon5OwnerShardR100002
import Ribbon5OwnerShardR100020
import Ribbon5OwnerShardR100021
import Ribbon5OwnerShardR100200
import Ribbon5OwnerShardR100202
import Ribbon5OwnerShardR100211
import Ribbon5OwnerShardR100212
import Ribbon5OwnerShardR102000
import Ribbon5OwnerShardR102002
import Ribbon5OwnerShardR102020
import Ribbon5OwnerShardR102021
import Ribbon5OwnerShardR102111
import Ribbon5OwnerShardR102112
import Ribbon5OwnerShardR102120
import Ribbon5OwnerShardR102121
import Ribbon5OwnerShardR111111
import Ribbon5OwnerShardR111112
import Ribbon5OwnerShardR111120
import Ribbon5OwnerShardR111121
import Ribbon5OwnerShardR111200
import Ribbon5OwnerShardR111202
import Ribbon5OwnerShardR111211
import Ribbon5OwnerShardR111212
import Ribbon5OwnerShardR112000
import Ribbon5OwnerShardR112002
import Ribbon5OwnerShardR112020
import Ribbon5OwnerShardR112021
import Ribbon5OwnerShardR112111
import Ribbon5OwnerShardR112112
import Ribbon5OwnerShardR112120
import Ribbon5OwnerShardR112121
import Ribbon5OwnerShardR120000
import Ribbon5OwnerShardR120002
import Ribbon5OwnerShardR120020
import Ribbon5OwnerShardR120021
import Ribbon5OwnerShardR120200
import Ribbon5OwnerShardR120202
import Ribbon5OwnerShardR120211
import Ribbon5OwnerShardR120212
import Ribbon5OwnerShardR121111
import Ribbon5OwnerShardR121112
import Ribbon5OwnerShardR121120
import Ribbon5OwnerShardR121121
import Ribbon5OwnerShardR121200
import Ribbon5OwnerShardR121202
import Ribbon5OwnerShardR121211
import Ribbon5OwnerShardR121212

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R00000 : good false 0 (pref false [0,0,0,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R000000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R000002
theorem R00002 : good false 0 (pref false [0,0,0,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R000020
  · change good false 0 (step (pref false [0,0,0,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R000021
  · exact (hk (by decide)).elim
theorem R00020 : good false 0 (pref false [0,0,2,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R000200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R000202
theorem R00021 : good false 0 (pref false [0,0,2,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R000211
  · change good false 0 (step (pref false [0,0,2,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R000212
theorem R00200 : good false 0 (pref false [0,2,0,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R002000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R002002
theorem R00202 : good false 0 (pref false [0,2,0,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R002020
  · change good false 0 (step (pref false [0,2,0,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R002021
  · exact (hk (by decide)).elim
theorem R00211 : good false 0 (pref false [0,2,1,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R002111
  · change good false 0 (step (pref false [0,2,1,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R002112
theorem R00212 : good false 0 (pref false [0,2,1,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R002120
  · change good false 0 (step (pref false [0,2,1,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R002121
  · exact (hk (by decide)).elim
theorem R01111 : good false 1 (pref false [1,1,1,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R011111
  · change good false 1 (step (pref false [1,1,1,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R011112
theorem R01112 : good false 1 (pref false [1,1,1,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R011120
  · change good false 1 (step (pref false [1,1,1,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R011121
  · exact (hk (by decide)).elim
theorem R01120 : good false 1 (pref false [1,1,2,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R011200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R011202
theorem R01121 : good false 1 (pref false [1,1,2,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R011211
  · change good false 1 (step (pref false [1,1,2,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R011212
theorem R01200 : good false 1 (pref false [1,2,0,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R012000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R012002
theorem R01202 : good false 1 (pref false [1,2,0,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R012020
  · change good false 1 (step (pref false [1,2,0,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R012021
  · exact (hk (by decide)).elim
theorem R01211 : good false 1 (pref false [1,2,1,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R012111
  · change good false 1 (step (pref false [1,2,1,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R012112
theorem R01212 : good false 1 (pref false [1,2,1,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R012120
  · change good false 1 (step (pref false [1,2,1,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R012121
  · exact (hk (by decide)).elim
theorem R02000 : good false 2 (pref false [2,0,0,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R020000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R020002
theorem R02002 : good false 2 (pref false [2,0,0,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R020020
  · change good false 2 (step (pref false [2,0,0,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R020021
  · exact (hk (by decide)).elim
theorem R02020 : good false 2 (pref false [2,0,2,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R020200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R020202
theorem R02021 : good false 2 (pref false [2,0,2,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R020211
  · change good false 2 (step (pref false [2,0,2,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R020212
theorem R02111 : good false 2 (pref false [2,1,1,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R021111
  · change good false 2 (step (pref false [2,1,1,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R021112
theorem R02112 : good false 2 (pref false [2,1,1,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R021120
  · change good false 2 (step (pref false [2,1,1,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R021121
  · exact (hk (by decide)).elim
theorem R02120 : good false 2 (pref false [2,1,2,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R021200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R021202
theorem R02121 : good false 2 (pref false [2,1,2,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R021211
  · change good false 2 (step (pref false [2,1,2,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R021212
theorem R0000 : good false 0 (pref false [0,0,0]) 0 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R00000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R00002
theorem R0002 : good false 0 (pref false [0,0,2]) 2 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R00020
  · change good false 0 (step (pref false [0,0,2]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R00021
  · exact (hk (by decide)).elim
theorem R0020 : good false 0 (pref false [0,2,0]) 0 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R00200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R00202
theorem R0021 : good false 0 (pref false [0,2,1]) 1 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R00211
  · change good false 0 (step (pref false [0,2,1]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R00212
theorem R0111 : good false 1 (pref false [1,1,1]) 1 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R01111
  · change good false 1 (step (pref false [1,1,1]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R01112
theorem R0112 : good false 1 (pref false [1,1,2]) 2 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R01120
  · change good false 1 (step (pref false [1,1,2]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R01121
  · exact (hk (by decide)).elim
theorem R0120 : good false 1 (pref false [1,2,0]) 0 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R01200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R01202
theorem R0121 : good false 1 (pref false [1,2,1]) 1 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R01211
  · change good false 1 (step (pref false [1,2,1]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R01212
theorem R0200 : good false 2 (pref false [2,0,0]) 0 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R02000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R02002
theorem R0202 : good false 2 (pref false [2,0,2]) 2 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R02020
  · change good false 2 (step (pref false [2,0,2]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R02021
  · exact (hk (by decide)).elim
theorem R0211 : good false 2 (pref false [2,1,1]) 1 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R02111
  · change good false 2 (step (pref false [2,1,1]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R02112
theorem R0212 : good false 2 (pref false [2,1,2]) 2 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R02120
  · change good false 2 (step (pref false [2,1,2]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R02121
  · exact (hk (by decide)).elim
theorem R000 : good false 0 (pref false [0,0]) 0 14 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0]) 0) 0 13 = true
    rw [← pref_snoc]
    exact R0000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0]) 2) 2 13 = true
    rw [← pref_snoc]
    exact R0002
theorem R002 : good false 0 (pref false [0,2]) 2 14 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2]) 0) 0 13 = true
    rw [← pref_snoc]
    exact R0020
  · change good false 0 (step (pref false [0,2]) 1) 1 13 = true
    rw [← pref_snoc]
    exact R0021
  · exact (hk (by decide)).elim
theorem R011 : good false 1 (pref false [1,1]) 1 14 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1]) 1) 1 13 = true
    rw [← pref_snoc]
    exact R0111
  · change good false 1 (step (pref false [1,1]) 2) 2 13 = true
    rw [← pref_snoc]
    exact R0112
theorem R012 : good false 1 (pref false [1,2]) 2 14 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2]) 0) 0 13 = true
    rw [← pref_snoc]
    exact R0120
  · change good false 1 (step (pref false [1,2]) 1) 1 13 = true
    rw [← pref_snoc]
    exact R0121
  · exact (hk (by decide)).elim
theorem R020 : good false 2 (pref false [2,0]) 0 14 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0]) 0) 0 13 = true
    rw [← pref_snoc]
    exact R0200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0]) 2) 2 13 = true
    rw [← pref_snoc]
    exact R0202
theorem R021 : good false 2 (pref false [2,1]) 1 14 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1]) 1) 1 13 = true
    rw [← pref_snoc]
    exact R0211
  · change good false 2 (step (pref false [2,1]) 2) 2 13 = true
    rw [← pref_snoc]
    exact R0212
theorem R00 : good false 0 (pref false [0]) 0 15 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0]) 0) 0 14 = true
    rw [← pref_snoc]
    exact R000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0]) 2) 2 14 = true
    rw [← pref_snoc]
    exact R002
theorem R01 : good false 1 (pref false [1]) 1 15 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1]) 1) 1 14 = true
    rw [← pref_snoc]
    exact R011
  · change good false 1 (step (pref false [1]) 2) 2 14 = true
    rw [← pref_snoc]
    exact R012
theorem R02 : good false 2 (pref false [2]) 2 15 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2]) 0) 0 14 = true
    rw [← pref_snoc]
    exact R020
  · change good false 2 (step (pref false [2]) 1) 1 14 = true
    rw [← pref_snoc]
    exact R021
  · exact (hk (by decide)).elim
theorem R10000 : good true 0 (pref true [0,0,0,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R100000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R100002
theorem R10002 : good true 0 (pref true [0,0,0,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R100020
  · change good true 0 (step (pref true [0,0,0,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R100021
  · exact (hk (by decide)).elim
theorem R10020 : good true 0 (pref true [0,0,2,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R100200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R100202
theorem R10021 : good true 0 (pref true [0,0,2,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R100211
  · change good true 0 (step (pref true [0,0,2,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R100212
theorem R10200 : good true 0 (pref true [0,2,0,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R102000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R102002
theorem R10202 : good true 0 (pref true [0,2,0,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R102020
  · change good true 0 (step (pref true [0,2,0,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R102021
  · exact (hk (by decide)).elim
theorem R10211 : good true 0 (pref true [0,2,1,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R102111
  · change good true 0 (step (pref true [0,2,1,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R102112
theorem R10212 : good true 0 (pref true [0,2,1,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R102120
  · change good true 0 (step (pref true [0,2,1,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R102121
  · exact (hk (by decide)).elim
theorem R11111 : good true 1 (pref true [1,1,1,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R111111
  · change good true 1 (step (pref true [1,1,1,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R111112
theorem R11112 : good true 1 (pref true [1,1,1,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R111120
  · change good true 1 (step (pref true [1,1,1,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R111121
  · exact (hk (by decide)).elim
theorem R11120 : good true 1 (pref true [1,1,2,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R111200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R111202
theorem R11121 : good true 1 (pref true [1,1,2,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R111211
  · change good true 1 (step (pref true [1,1,2,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R111212
theorem R11200 : good true 1 (pref true [1,2,0,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R112000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R112002
theorem R11202 : good true 1 (pref true [1,2,0,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R112020
  · change good true 1 (step (pref true [1,2,0,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R112021
  · exact (hk (by decide)).elim
theorem R11211 : good true 1 (pref true [1,2,1,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R112111
  · change good true 1 (step (pref true [1,2,1,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R112112
theorem R11212 : good true 1 (pref true [1,2,1,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,1,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R112120
  · change good true 1 (step (pref true [1,2,1,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R112121
  · exact (hk (by decide)).elim
theorem R12000 : good true 2 (pref true [2,0,0,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R120000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R120002
theorem R12002 : good true 2 (pref true [2,0,0,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R120020
  · change good true 2 (step (pref true [2,0,0,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R120021
  · exact (hk (by decide)).elim
theorem R12020 : good true 2 (pref true [2,0,2,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R120200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R120202
theorem R12021 : good true 2 (pref true [2,0,2,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R120211
  · change good true 2 (step (pref true [2,0,2,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R120212
theorem R12111 : good true 2 (pref true [2,1,1,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R121111
  · change good true 2 (step (pref true [2,1,1,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R121112
theorem R12112 : good true 2 (pref true [2,1,1,2]) 2 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,2]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R121120
  · change good true 2 (step (pref true [2,1,1,2]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R121121
  · exact (hk (by decide)).elim
theorem R12120 : good true 2 (pref true [2,1,2,0]) 0 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,0]) 0) 0 11 = true
    rw [← pref_snoc]
    exact R121200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,0]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R121202
theorem R12121 : good true 2 (pref true [2,1,2,1]) 1 12 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,1]) 1) 1 11 = true
    rw [← pref_snoc]
    exact R121211
  · change good true 2 (step (pref true [2,1,2,1]) 2) 2 11 = true
    rw [← pref_snoc]
    exact R121212
theorem R1000 : good true 0 (pref true [0,0,0]) 0 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R10000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R10002
theorem R1002 : good true 0 (pref true [0,0,2]) 2 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R10020
  · change good true 0 (step (pref true [0,0,2]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R10021
  · exact (hk (by decide)).elim
theorem R1020 : good true 0 (pref true [0,2,0]) 0 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R10200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R10202
theorem R1021 : good true 0 (pref true [0,2,1]) 1 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R10211
  · change good true 0 (step (pref true [0,2,1]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R10212
theorem R1111 : good true 1 (pref true [1,1,1]) 1 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R11111
  · change good true 1 (step (pref true [1,1,1]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R11112
theorem R1112 : good true 1 (pref true [1,1,2]) 2 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R11120
  · change good true 1 (step (pref true [1,1,2]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R11121
  · exact (hk (by decide)).elim
theorem R1120 : good true 1 (pref true [1,2,0]) 0 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R11200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R11202
theorem R1121 : good true 1 (pref true [1,2,1]) 1 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R11211
  · change good true 1 (step (pref true [1,2,1]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R11212
theorem R1200 : good true 2 (pref true [2,0,0]) 0 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R12000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R12002
theorem R1202 : good true 2 (pref true [2,0,2]) 2 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R12020
  · change good true 2 (step (pref true [2,0,2]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R12021
  · exact (hk (by decide)).elim
theorem R1211 : good true 2 (pref true [2,1,1]) 1 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R12111
  · change good true 2 (step (pref true [2,1,1]) 2) 2 12 = true
    rw [← pref_snoc]
    exact R12112
theorem R1212 : good true 2 (pref true [2,1,2]) 2 13 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2]) 0) 0 12 = true
    rw [← pref_snoc]
    exact R12120
  · change good true 2 (step (pref true [2,1,2]) 1) 1 12 = true
    rw [← pref_snoc]
    exact R12121
  · exact (hk (by decide)).elim
theorem R100 : good true 0 (pref true [0,0]) 0 14 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0]) 0) 0 13 = true
    rw [← pref_snoc]
    exact R1000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0]) 2) 2 13 = true
    rw [← pref_snoc]
    exact R1002
theorem R102 : good true 0 (pref true [0,2]) 2 14 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2]) 0) 0 13 = true
    rw [← pref_snoc]
    exact R1020
  · change good true 0 (step (pref true [0,2]) 1) 1 13 = true
    rw [← pref_snoc]
    exact R1021
  · exact (hk (by decide)).elim
theorem R111 : good true 1 (pref true [1,1]) 1 14 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1]) 1) 1 13 = true
    rw [← pref_snoc]
    exact R1111
  · change good true 1 (step (pref true [1,1]) 2) 2 13 = true
    rw [← pref_snoc]
    exact R1112
theorem R112 : good true 1 (pref true [1,2]) 2 14 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2]) 0) 0 13 = true
    rw [← pref_snoc]
    exact R1120
  · change good true 1 (step (pref true [1,2]) 1) 1 13 = true
    rw [← pref_snoc]
    exact R1121
  · exact (hk (by decide)).elim
theorem R120 : good true 2 (pref true [2,0]) 0 14 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0]) 0) 0 13 = true
    rw [← pref_snoc]
    exact R1200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0]) 2) 2 13 = true
    rw [← pref_snoc]
    exact R1202
theorem R121 : good true 2 (pref true [2,1]) 1 14 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1]) 1) 1 13 = true
    rw [← pref_snoc]
    exact R1211
  · change good true 2 (step (pref true [2,1]) 2) 2 13 = true
    rw [← pref_snoc]
    exact R1212
theorem R10 : good true 0 (pref true [0]) 0 15 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0]) 0) 0 14 = true
    rw [← pref_snoc]
    exact R100
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0]) 2) 2 14 = true
    rw [← pref_snoc]
    exact R102
theorem R11 : good true 1 (pref true [1]) 1 15 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1]) 1) 1 14 = true
    rw [← pref_snoc]
    exact R111
  · change good true 1 (step (pref true [1]) 2) 2 14 = true
    rw [← pref_snoc]
    exact R112
theorem R12 : good true 2 (pref true [2]) 2 15 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2]) 0) 0 14 = true
    rw [← pref_snoc]
    exact R120
  · change good true 2 (step (pref true [2]) 1) 1 14 = true
    rw [← pref_snoc]
    exact R121
  · exact (hk (by decide)).elim
theorem allgood (s : Bool) (p : P) : good s p (step (zero s) p) p 15 = true := by
  cases s <;> fin_cases p
  · exact R00
  · exact R01
  · exact R02
  · exact R10
  · exact R11
  · exact R12
end Ribbon5Owner
