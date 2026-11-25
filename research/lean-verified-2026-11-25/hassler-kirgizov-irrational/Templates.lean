import Window
import Mathlib.Tactic

namespace Emerging

/-- Reverse every complete pair starting at positions of parity d. -/
def alt (n d i : Nat) : Nat :=
  if i % 2 = d ∧ i+1 < n then i+1
  else if 0 < i ∧ (i-1) % 2 = d then i-1
  else i

theorem alt_lt (n d i : Nat) (hi : i < n) : alt n d i < n := by
  unfold alt
  (try split_ifs) <;> omega

theorem alt_invol (n d i : Nat) (hd : d < 2) (hi : i < n) :
    alt n d (alt n d i) = i := by
  unfold alt
  (try split_ifs) <;> omega

theorem alt_close (n d i : Nat) (_hi : i+1 < n) :
    alt n d i  ≤  alt n d (i+1)+4 ∧ alt n d (i+1)  ≤  alt n d i+4 := by
  unfold alt
  (try split_ifs) <;> omega

def aidx (d i : Nat) : Fin 7 := if i % 2 = d then 5 else 6

set_option maxHeartbeats 4000000 in
theorem alt_matches (n d i : Nat) (hd : d < 2) (hi : i+4 < n) :
    matchWord (alt n d) i (w (aidx d i)) := by
  intro r s
  fin_cases r <;> fin_cases s <;>
   simp [alt,aidx,w] <;> (try split_ifs) <;> simp_all <;> omega

/-- The two possible nonconstant, nonalternating phase templates without the interior peak. -/
def peakLeft (n i : Nat) : Nat :=
  if i=0 then n-2 else if i=1 then n-1 else n-1-i
def peakLeftInv (n v : Nat) : Nat :=
  if n-2 ≤ v then v-(n-2) else n-1-v
def peakRight (n i : Nat) : Nat :=
  if i < n-3 then i else if i=n-1 then n-3 else i+1
def peakRightInv (n v : Nat) : Nat :=
  if v<n-3 then v else if v=n-3 then n-1 else v-1

theorem w0_cmp (r s : Fin 5) : w 0 r < w 0 s ↔ r.val < s.val := by decide +revert
theorem w4_cmp' (r s : Fin 5) : w 4 r < w 4 s ↔ s.val < r.val := by decide +revert

theorem peakLeft_match (n i : Nat) (hi : i+4 < n) :
    matchWord (peakLeft n) i (w (if i=0 then 3 else 4)) := by
  by_cases h0 : i=0
  · subst i
    intro r s
    fin_cases r <;> fin_cases s <;> simp [peakLeft,w] <;> omega
  · intro r s
    rw [if_neg h0,w4_cmp']
    unfold peakLeft
    (try split_ifs) <;> have := r.isLt <;> have := s.isLt <;> omega

theorem peakRight_match (n i : Nat) (hi : i+4 < n) :
    matchWord (peakRight n) i (w (if i+5=n then 1 else 0)) := by
  by_cases hl : i+5=n
  · subst n
    intro r s
    fin_cases r <;> fin_cases s <;> simp [peakRight,w] <;> (try split_ifs) <;> omega
  · intro r s
    rw [if_neg hl,w0_cmp]
    unfold peakRight
    (try split_ifs) <;> have := r.isLt <;> have := s.isLt <;> omega

/-- Given a valid permutation g on 0..n-1 with a short-step inverse, the
comparisons in its consecutive length-five windows uniquely determine g. -/
theorem from_short_rank_path (f g inv : Nat → Nat) (n : Nat) (hn : 5 ≤ n)
    (hf : ∀ i<n, f i < n)
    (hg : ∀ i<n, g i < n)
    (hi : ∀ i<n, inv i < n)
    (hgi : ∀ i<n, g (inv i)=i)
    (hig : ∀ i<n, inv (g i)=i)
    (close : ∀ i, i+1<n → inv i ≤ inv (i+1)+4 ∧ inv (i+1) ≤ inv i+4)
    (hw : ∀ j, j+4<n → ∃ u : Fin 7, matchWord f j (w u) ∧ matchWord g j (w u)) :
    ∀ i<n, f i=g i := by
  have hstep : ∀ i, i+1<n → f (inv i) < f (inv (i+1)) := by
    intro i h
    apply (compare_near f g n hn (inv i) (inv (i+1)) (hi i (by omega)) (hi (i+1) h) (close i h) hw).mpr
    rw [hgi i (by omega),hgi (i+1) h]
    omega
  intro i hi'
  have hh := unique_ranks (fun j => f (inv j)) n hstep (fun j hj => hf (inv j) (hi j hj)) (g i) (hg i hi')
  rw [hig i hi'] at hh
  exact hh

def tmpl (n : Nat) (c : Fin 6) (i : Nat) : Nat :=
  match c.val with
  | 0 => i
  | 1 => peakRight n i
  | 2 => peakLeft n i
  | 3 => n-1-i
  | 4 => alt n 0 i
  | _ => alt n 1 i

def invTmpl (n : Nat) (c : Fin 6) (i : Nat) : Nat :=
  match c.val with
  | 0 => i
  | 1 => peakRightInv n i
  | 2 => peakLeftInv n i
  | 3 => n-1-i
  | 4 => alt n 0 i
  | _ => alt n 1 i

def sig (m : Nat) (c : Fin 6) (i : Nat) : Fin 7 :=
  match c.val with
  | 0 => 0
  | 1 => if i+1=m then 1 else 0
  | 2 => if i=0 then 3 else 4
  | 3 => 4
  | 4 => aidx 0 i
  | _ => aidx 1 i

theorem tmpl_lt (n : Nat) (hn : 5 ≤ n) (c : Fin 6) (i : Nat) (hi : i < n) :
    tmpl n c i < n := by
  fin_cases c <;> simp [tmpl, peakLeft, peakRight] <;>
    first | exact alt_lt _ _ _ hi | ((try split_ifs) <;> omega)

theorem invTmpl_lt (n : Nat) (hn : 5 ≤ n) (c : Fin 6) (i : Nat) (hi : i < n) :
    invTmpl n c i < n := by
  fin_cases c <;> simp [invTmpl, peakLeftInv, peakRightInv] <;>
    first | exact alt_lt _ _ _ hi | ((try split_ifs) <;> omega)

theorem tmpl_inv (n : Nat) (hn : 5 ≤ n) (c : Fin 6) (i : Nat) (hi : i < n) :
    tmpl n c (invTmpl n c i) = i := by
  fin_cases c <;> simp [tmpl, invTmpl, peakLeft, peakRight, peakLeftInv, peakRightInv] <;>
    first | exact alt_invol _ _ _ (by omega) hi | ((try split_ifs) <;> omega)

theorem inv_tmpl (n : Nat) (hn : 5 ≤ n) (c : Fin 6) (i : Nat) (hi : i < n) :
    invTmpl n c (tmpl n c i) = i := by
  fin_cases c <;> simp [tmpl, invTmpl, peakLeft, peakRight, peakLeftInv, peakRightInv] <;>
    first | exact alt_invol _ _ _ (by omega) hi | ((try split_ifs) <;> omega)

theorem tmpl_close (n : Nat) (hn : 5 ≤ n) (c : Fin 6) (i : Nat) (hi : i+1 < n) :
    invTmpl n c i ≤ invTmpl n c (i+1)+4 ∧ invTmpl n c (i+1) ≤ invTmpl n c i+4 := by
  fin_cases c <;> simp [invTmpl, peakLeftInv, peakRightInv] <;>
    first | exact alt_close _ _ _ hi | ((try split_ifs) <;> omega)

theorem tmpl_match (n i : Nat) (c : Fin 6) (hi : i+4 < n) :
    matchWord (tmpl n c) i (w (sig (n-4) c i)) := by
  fin_cases c <;> simp [sig]
  · intro r s
    rw [w0_cmp]
    change i+r.val < i+s.val ↔ r.val < s.val
    omega
  · have h := peakRight_match n i hi
    have eq : (i+5=n) ↔ (i+1=n-4) := by omega
    change matchWord (peakRight n) i (w (if i+1=n-4 then 1 else 0))
    simpa only [eq] using h
  · exact peakLeft_match n i hi
  · intro r s
    rw [w4_cmp']
    have hr := r.isLt
    have hs := s.isLt
    change n-1-(i+r.val) < n-1-(i+s.val) ↔ s.val < r.val
    omega
  · exact alt_matches n 0 i (by omega) hi
  · exact alt_matches n 1 i (by omega) hi

theorem altClass (u : Nat → Fin 7) (m : Nat) (h : Path u m) (h0 : 5 ≤ (u 0).val) :
    ∃ c : Fin 2, ∀ i < m, u i = aidx c.val i := by
  have hlt := (u 0).isLt
  let c : Fin 2 := ⟨(u 0).val - 5, by omega⟩
  refine ⟨c,?_⟩
  intro i hi
  apply Fin.ext
  have hs := path_alt_signature u m i h h0 hi
  simp only [aidx,c]
  split <;> split at hs <;> (try simp only [Fin.val_ofNat] at *) <;> omega

theorem sig_noP (m i : Nat) (c : Fin 6) : (sig m c i).val ≠ 2 := by
  fin_cases c
  · change (0 : Nat) ≠ 2
    decide
  · change (if i+1=m then (1 : Fin 7) else 0).val ≠ 2
    split <;> decide
  · change (if i=0 then (3 : Fin 7) else 4).val ≠ 2
    split <;> decide
  · change (4 : Nat) ≠ 2
    decide
  · change (aidx 0 i).val ≠ 2
    unfold aidx
    split <;> decide
  · change (aidx 1 i).val ≠ 2
    unfold aidx
    split <;> decide

theorem BClass (u : Nat → Fin 7) (m : Nat) (hm : 2 ≤ m) (h : Path u m)
    (hn : ∀ j < m, (u j).val ≠ 2) :
    ∃ c : Fin 6, ∀ i < m, u i = sig m c i := by
  by_cases ha : 5 ≤ (u 0).val
  · obtain ⟨d,hd⟩ := altClass u m h ha
    fin_cases d
    · exact ⟨4,hd⟩
    · exact ⟨5,hd⟩
  have hz := hn 0 (by omega)
  have h1 := (B_edge_peak_start_last u m 0 h hn (by omega)).1
  have hcases : (u 0).val = 0 ∨ (u 0).val = 3 ∨ (u 0).val = 4 := by omega
  rcases hcases with hcases|hcases|hcases
  · have hp := B_from_zero u m _ h hn hcases (show m-2+1<m by omega)
    have he := h (m-2) (by omega)
    rw [show m-2+1=m-1 by omega] at he
    unfold allowedEdges at he
    by_cases hs : (u (m-1)).val = 1
    · refine ⟨1,?_⟩
      intro i hi
      apply Fin.ext
      change (u i).val = (if i+1=m then (1 : Fin 7) else 0).val
      split
      · have : i=m-1 := by omega
        rwa [this]
      · exact B_from_zero u m i h hn hcases (by omega)
    · refine ⟨0,?_⟩
      intro i hi
      apply Fin.ext
      change (u i).val = 0
      by_cases hh : i=m-1
      · rw [hh]
        omega
      · exact B_from_zero u m i h hn hcases (by omega)
  · have he := h 0 (by omega)
    unfold allowedEdges at he
    have h4 : (u 1).val = 4 := by simpa [hcases] using he
    refine ⟨2,?_⟩
    intro i hi
    apply Fin.ext
    change (u i).val = (if i=0 then (3 : Fin 7) else 4).val
    split
    · rwa [show i=0 by omega]
    · have hx := path_from_four u m 1 (i-1) h h4 (by omega)
      rwa [show 1+(i-1)=i by omega] at hx
  · refine ⟨3,?_⟩
    intro i hi
    apply Fin.ext
    have ht := path_from_four u m 0 i h hcases (by omega)
    simpa [sig] using ht

end Emerging
