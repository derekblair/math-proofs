import Answer

namespace PackingSeparator

theorem window_count_identity (K J : ℕ) (hk : 4≤K) (hj : 0<J) :
    nPos K J=K+(J-1)*(K-2) := by
  unfold nPos
  conv_lhs => arg 1; rw [show J=(J-1)+1 by omega,Nat.add_mul,one_mul]
  omega

/-- Source statement with one-based ranks: if the overlap-two prefix is
1,a and the suffix is b,c under the article's inequalities, the
K-th position of the occurrence poset is a separator. -/
theorem bks_section7_item5 (K J a b c : ℕ) (hk : 4≤K) (hJ : J>2)
    (p : Equiv.Perm (Fin K)) (a2 : 2<a) (ab : a<b) (bc : b<c-1)
    (cK : c-1<K-2)
    (P0 : (p ⟨0,by omega⟩).val+1=1)
    (P1 : (p ⟨1,by omega⟩).val+1=a)
    (S0 : (p ⟨K-2,by omega⟩).val+1=b)
    (S1 : (p ⟨K-1,by omega⟩).val+1=c) :
    ReachSeparator (stepEdges (J:=J) hk p)
      (atPos hk (⟨0,by omega⟩ : Fin J) ⟨K-1,by omega⟩) := by
  have result := last_first_window_separates (J:=J) hk p (a:=a-1) (b:=b-1) (c:=c-1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  simpa only [atPos,Nat.zero_mul,Nat.zero_add] using result

#print axioms bks_section7_item5
end PackingSeparator
