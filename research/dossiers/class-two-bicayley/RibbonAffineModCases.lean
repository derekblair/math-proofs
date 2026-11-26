import RibbonAffineModCore
namespace RibbonAffine
variable {K : Type*} [Field K]
set_option maxRecDepth 16000
set_option maxHeartbeats 0
theorem modcase_2_5 (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1)
    (two : (2:K)≠0) (hp : (5:K)=0) (root : pl t 1 (obstruction 2).2.2=0) :
    False := by
  have hc : ((1:ℤ):K)≠0 := by norm_num [two]
  obtain ⟨g,gm,gr⟩ := mod_factor t 5 (1) (by norm_num; exact hp) hc
    (obstruction 2).2.2 [[(0,0,-2),(1,0,1)],[(0,0,-2),(1,0,1)]] [(0,0,-1),(1,0,1)] (by decide +kernel) root
  have e : g=[(0,0,-2),(1,0,1)] := by simpa using gm
  rw [e] at gr
  exact mod_even_root t n 2 odd tn two 5 (by norm_num; exact hp) [(0,0,-2),(1,0,1)] [(0,0,2),(1,0,1)] [(0,0,1)] (by decide +kernel) gr

theorem modcase_3_5 (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1)
    (two : (2:K)≠0) (hp : (5:K)=0) (root : pl t 1 (obstruction 3).2.2=0) :
    False := by
  have hc : ((1:ℤ):K)≠0 := by norm_num [two]
  obtain ⟨g,gm,gr⟩ := mod_factor t 5 (1) (by norm_num; exact hp) hc
    (obstruction 3).2.2 [[(0,0,2),(1,0,1)],[(0,0,2),(1,0,1)]] [(0,0,-1),(1,0,-1)] (by decide +kernel) root
  have e : g=[(0,0,2),(1,0,1)] := by simpa using gm
  rw [e] at gr
  exact mod_even_root t n 2 odd tn two 5 (by norm_num; exact hp) [(0,0,2),(1,0,1)] [(0,0,-2),(1,0,1)] [(0,0,1)] (by decide +kernel) gr

theorem modcase_4_5 (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1)
    (two : (2:K)≠0) (hp : (5:K)=0) (root : pl t 1 (obstruction 4).2.2=0) :
    False := by
  have hc : ((1:ℤ):K)≠0 := by norm_num [two]
  obtain ⟨g,gm,gr⟩ := mod_factor t 5 (1) (by norm_num; exact hp) hc
    (obstruction 4).2.2 [[(0,0,2),(1,0,1)],[(0,0,2),(1,0,-1),(2,0,1)]] [(0,0,-1)] (by decide +kernel) root
  simp only [List.mem_cons,List.not_mem_nil,or_false] at gm
  rcases gm with e|e
  · rw [e] at gr
    exact mod_even_root t n 2 odd tn two 5 (by norm_num; exact hp) [(0,0,2),(1,0,1)] [(0,0,-2),(1,0,1)] [(0,0,1)] (by decide +kernel) gr
  · rw [e] at gr
    exact mod_even_root t n 12 odd tn two 5 (by norm_num; exact hp) [(0,0,2),(1,0,-1),(2,0,1)] [(0,0,-2),(1,0,-1),(2,0,-2),(3,0,2),(4,0,2),(6,0,-1),(7,0,2),(8,0,-1),(9,0,1),(10,0,1)] [(0,0,1),(2,0,1),(3,0,-1),(7,0,-1),(8,0,1),(9,0,-1)] (by decide +kernel) gr

theorem modcase_5_5 (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1)
    (two : (2:K)≠0) (hp : (5:K)=0) (root : pl t 1 (obstruction 5).2.2=0) :
    False := by
  have hc : ((1:ℤ):K)≠0 := by norm_num [two]
  obtain ⟨g,gm,gr⟩ := mod_factor t 5 (1) (by norm_num; exact hp) hc
    (obstruction 5).2.2 [[(0,0,-2),(1,0,1)],[(0,0,-2),(1,0,2),(2,0,1)]] [(0,0,-1),(1,0,1)] (by decide +kernel) root
  simp only [List.mem_cons,List.not_mem_nil,or_false] at gm
  rcases gm with e|e
  · rw [e] at gr
    exact mod_even_root t n 2 odd tn two 5 (by norm_num; exact hp) [(0,0,-2),(1,0,1)] [(0,0,2),(1,0,1)] [(0,0,1)] (by decide +kernel) gr
  · rw [e] at gr
    exact mod_even_root t n 12 odd tn two 5 (by norm_num; exact hp) [(0,0,-2),(1,0,2),(2,0,1)] [(0,0,2),(1,0,2),(2,0,-2),(3,0,-1),(4,0,-2),(6,0,-1),(7,0,-1),(8,0,1),(9,0,-2),(10,0,1)] [(0,0,1),(2,0,-2),(5,0,1),(8,0,1),(9,0,-1),(10,0,1)] (by decide +kernel) gr

theorem modcase_6_3 (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1)
    (two : (2:K)≠0) (hp : (3:K)=0) (root : pl t 1 (obstruction 6).2.2=0) :
    False := by
  have hc : ((-1:ℤ):K)≠0 := by norm_num [two]
  obtain ⟨g,gm,gr⟩ := mod_factor t 3 (-1) (by norm_num; exact hp) hc
    (obstruction 6).2.2 [[(0,0,1),(2,0,1)]] [(2,0,1)] (by decide +kernel) root
  have e : g=[(0,0,1),(2,0,1)] := by simpa using gm
  rw [e] at gr
  exact mod_even_root t n 2 odd tn two 3 (by norm_num; exact hp) [(0,0,1),(2,0,1)] [(0,0,1)] [] (by decide +kernel) gr

theorem modcase_6_7 (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1)
    (two : (2:K)≠0) (hp : (7:K)=0) (root : pl t 1 (obstruction 6).2.2=0) :
    ((t:K)=2 ∨ (t:K)=4) := by
  have hc : ((2:ℤ):K)≠0 := by norm_num [two]
  obtain ⟨g,gm,gr⟩ := mod_factor t 7 (2) (by norm_num; exact hp) hc
    (obstruction 6).2.2 [[(0,0,2),(1,0,1)],[(0,0,-2),(1,0,1)]] [(0,0,1)] (by decide +kernel) root
  simp only [List.mem_cons,List.not_mem_nil,or_false] at gm
  rcases gm with e|e
  · rw [e] at gr
    exfalso
    exact mod_even_root t n 3 odd tn two 7 (by norm_num; exact hp) [(0,0,2),(1,0,1)] [(0,0,-3),(1,0,-2),(2,0,1)] [(0,0,1),(1,0,1)] (by decide +kernel) gr
  · rw [e] at gr
    apply Or.inl
    simp [pl,mon] at gr
    linear_combination gr

theorem modcase_7_3 (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1)
    (two : (2:K)≠0) (hp : (3:K)=0) (root : pl t 1 (obstruction 7).2.2=0) :
    False := by
  have hc : ((1:ℤ):K)≠0 := by norm_num [two]
  obtain ⟨g,gm,gr⟩ := mod_factor t 3 (1) (by norm_num; exact hp) hc
    (obstruction 7).2.2 [[(0,0,1),(2,0,1)]] [(0,0,-1)] (by decide +kernel) root
  have e : g=[(0,0,1),(2,0,1)] := by simpa using gm
  rw [e] at gr
  exact mod_even_root t n 2 odd tn two 3 (by norm_num; exact hp) [(0,0,1),(2,0,1)] [(0,0,1)] [] (by decide +kernel) gr

theorem modcase_7_7 (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1)
    (two : (2:K)≠0) (hp : (7:K)=0) (root : pl t 1 (obstruction 7).2.2=0) :
    ((t:K)=2 ∨ (t:K)=4) := by
  have hc : ((1:ℤ):K)≠0 := by norm_num [two]
  obtain ⟨g,gm,gr⟩ := mod_factor t 7 (1) (by norm_num; exact hp) hc
    (obstruction 7).2.2 [[(0,0,3),(1,0,1)],[(0,0,-3),(1,0,1)]] [(0,0,1)] (by decide +kernel) root
  simp only [List.mem_cons,List.not_mem_nil,or_false] at gm
  rcases gm with e|e
  · rw [e] at gr
    apply Or.inr
    simp [pl,mon] at gr
    linear_combination gr - hp
  · rw [e] at gr
    exfalso
    exact mod_even_root t n 3 odd tn two 7 (by norm_num; exact hp) [(0,0,-3),(1,0,1)] [(0,0,2),(1,0,3),(2,0,1)] [(0,0,1),(1,0,1)] (by decide +kernel) gr

theorem modcase_8_5 (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1)
    (two : (2:K)≠0) (hp : (5:K)=0) (root : pl t 1 (obstruction 8).2.2=0) :
    False := by
  have hc : ((1:ℤ):K)≠0 := by norm_num [two]
  obtain ⟨g,gm,gr⟩ := mod_factor t 5 (1) (by norm_num; exact hp) hc
    (obstruction 8).2.2 [[(0,0,-2),(1,0,1)],[(0,0,-2),(1,0,1)]] [(0,0,-1),(1,0,1)] (by decide +kernel) root
  have e : g=[(0,0,-2),(1,0,1)] := by simpa using gm
  rw [e] at gr
  exact mod_even_root t n 2 odd tn two 5 (by norm_num; exact hp) [(0,0,-2),(1,0,1)] [(0,0,2),(1,0,1)] [(0,0,1)] (by decide +kernel) gr

theorem modcase_9_5 (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1)
    (two : (2:K)≠0) (hp : (5:K)=0) (root : pl t 1 (obstruction 9).2.2=0) :
    False := by
  have hc : ((1:ℤ):K)≠0 := by norm_num [two]
  obtain ⟨g,gm,gr⟩ := mod_factor t 5 (1) (by norm_num; exact hp) hc
    (obstruction 9).2.2 [[(0,0,2),(1,0,1)],[(0,0,2),(1,0,1)]] [(0,0,-1),(1,0,-1)] (by decide +kernel) root
  have e : g=[(0,0,2),(1,0,1)] := by simpa using gm
  rw [e] at gr
  exact mod_even_root t n 2 odd tn two 5 (by norm_num; exact hp) [(0,0,2),(1,0,1)] [(0,0,-2),(1,0,1)] [(0,0,1)] (by decide +kernel) gr

theorem modcase_10_5 (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1)
    (two : (2:K)≠0) (hp : (5:K)=0) (root : pl t 1 (obstruction 10).2.2=0) :
    False := by
  have hc : ((1:ℤ):K)≠0 := by norm_num [two]
  obtain ⟨g,gm,gr⟩ := mod_factor t 5 (1) (by norm_num; exact hp) hc
    (obstruction 10).2.2 [[(0,0,2),(1,0,1)],[(0,0,2),(1,0,-1),(2,0,1)]] [(0,0,-1)] (by decide +kernel) root
  simp only [List.mem_cons,List.not_mem_nil,or_false] at gm
  rcases gm with e|e
  · rw [e] at gr
    exact mod_even_root t n 2 odd tn two 5 (by norm_num; exact hp) [(0,0,2),(1,0,1)] [(0,0,-2),(1,0,1)] [(0,0,1)] (by decide +kernel) gr
  · rw [e] at gr
    exact mod_even_root t n 12 odd tn two 5 (by norm_num; exact hp) [(0,0,2),(1,0,-1),(2,0,1)] [(0,0,-2),(1,0,-1),(2,0,-2),(3,0,2),(4,0,2),(6,0,-1),(7,0,2),(8,0,-1),(9,0,1),(10,0,1)] [(0,0,1),(2,0,1),(3,0,-1),(7,0,-1),(8,0,1),(9,0,-1)] (by decide +kernel) gr

theorem modcase_11_5 (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1)
    (two : (2:K)≠0) (hp : (5:K)=0) (root : pl t 1 (obstruction 11).2.2=0) :
    False := by
  have hc : ((1:ℤ):K)≠0 := by norm_num [two]
  obtain ⟨g,gm,gr⟩ := mod_factor t 5 (1) (by norm_num; exact hp) hc
    (obstruction 11).2.2 [[(0,0,-2),(1,0,1)],[(0,0,-2),(1,0,2),(2,0,1)]] [(0,0,-1),(1,0,1)] (by decide +kernel) root
  simp only [List.mem_cons,List.not_mem_nil,or_false] at gm
  rcases gm with e|e
  · rw [e] at gr
    exact mod_even_root t n 2 odd tn two 5 (by norm_num; exact hp) [(0,0,-2),(1,0,1)] [(0,0,2),(1,0,1)] [(0,0,1)] (by decide +kernel) gr
  · rw [e] at gr
    exact mod_even_root t n 12 odd tn two 5 (by norm_num; exact hp) [(0,0,-2),(1,0,2),(2,0,1)] [(0,0,2),(1,0,2),(2,0,-2),(3,0,-1),(4,0,-2),(6,0,-1),(7,0,-1),(8,0,1),(9,0,-2),(10,0,1)] [(0,0,1),(2,0,-2),(5,0,1),(8,0,1),(9,0,-1),(10,0,1)] (by decide +kernel) gr

end RibbonAffine
