import Templates
import Witness
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology
namespace Emerging

theorem wdisjoint (u v : Fin 7) :
    (∀ r s : Fin 5, w u r < w u s ↔ w v r < w v s) → u = v := by decide +revert

theorem words_unique (f : Nat → Nat) (i : Nat) (u v : Fin 7)
    (hu : matchWord f i (w u)) (hv : matchWord f i (w v)) : u=v :=
  wdisjoint u v fun r s => (hu r s).symm.trans (hv r s)

abbrev Perm (n : Nat) := Equiv.Perm (Fin n)
def ext {n : Nat} (f : Perm n) (i : Nat) : Nat := if h : i<n then (f ⟨i,h⟩).val else 0

theorem ext_lt {n : Nat} (f : Perm n) {i : Nat} (hi : i<n) : ext f i < n := by simp [ext,hi]

theorem perm_ext {n : Nat} (f g : Perm n) (h : ∀ i<n, ext f i = ext g i) : f=g := by
  ext i
  exact (by simpa [ext,i.isLt] using h i.val i.isLt : (f i).val = (g i).val)

/-- Any injective endomorphism on a finite set is a permutation. -/
noncomputable def tallPerm (n : Nat) (hn : 6 ≤ n) (x : Fin (n-4)) : Perm n :=
  Equiv.ofBijective
    (fun i => ⟨tall n x.val i.val, tall_lt n x.val i.val hn x.isLt i.isLt⟩)
    ((Finite.injective_iff_bijective).mp (fun a b h => Fin.ext
      (tall_inj n x.val a.val b.val hn x.isLt a.isLt b.isLt (congrArg Fin.val h))))

noncomputable def tmplPerm (n : Nat) (hn : 5 ≤ n) (c : Fin 6) : Perm n where
  toFun i := ⟨tmpl n c i.val, tmpl_lt n hn c i.val i.isLt⟩
  invFun i := ⟨invTmpl n c i.val, invTmpl_lt n hn c i.val i.isLt⟩
  left_inv i := Fin.ext (inv_tmpl n hn c i.val i.isLt)
  right_inv i := Fin.ext (tmpl_inv n hn c i.val i.isLt)

theorem with_ext (n : Nat) (f : Perm n) (g : Nat → Nat) (i : Nat) (u : Fin 7)
    (h : i+4<n) (hf : ∀ j<n, ext f j = g j) :
    matchWord (ext f) i (w u) ↔ matchWord g i (w u) := by
  unfold matchWord
  apply forall_congr'
  intro r
  apply forall_congr'
  intro s
  have hr := r.isLt
  have hs := s.isLt
  rw [hf _ (by omega), hf _ (by omega)]

def Admis (n : Nat) (f : Perm n) : Prop :=
  ∀ i, i+4<n → ∃ u : Fin 7, matchWord (ext f) i (w u)

def BAdmis (n : Nat) (f : Perm n) : Prop :=
  Admis n f ∧ ∀ i, i+4<n → ¬ matchWord (ext f) i (w 2)

theorem tall_admis (n : Nat) (hn : 6 ≤ n) (x : Fin (n-4)) : Admis n (tallPerm n hn x) := by
  intro i hi
  obtain ⟨j,hj⟩ := tall_word n x.val i x.isLt hn hi
  exact ⟨j,(with_ext n _ _ i j hi (fun a ha => by simp [ext,ha,tallPerm])).mpr hj⟩

theorem tallPerm_inj (n : Nat) (hn : 6 ≤ n) : Function.Injective (tallPerm n hn) := by
  intro x y h
  have hh := congrArg (fun f : Perm n => ext f 0) h
  apply Fin.ext
  simpa [ext,show 0<n by omega,tallPerm,tall0] using hh

theorem tmpl_admis (n : Nat) (hn : 5 ≤ n) (c : Fin 6) (i : Nat) (hi : i+4<n) :
    matchWord (ext (tmplPerm n hn c)) i (w (sig (n-4) c i)) :=
  (with_ext n _ _ i _ hi (fun a ha => by simp [ext,ha,tmplPerm])).mpr (tmpl_match n i c hi)

theorem tmpl_B (n : Nat) (hn : 5 ≤ n) (c : Fin 6) : BAdmis n (tmplPerm n hn c) := by
  constructor
  · intro i hi
    exact ⟨_,tmpl_admis n hn c i hi⟩
  · intro i hi hp
    exact (sig_noP (n-4) i c) (congrArg Fin.val (words_unique _ i _ _ (tmpl_admis n hn c i hi) hp))

noncomputable def state (n : Nat) (f : Perm n) (hf : Admis n f) (i : Nat) : Fin 7 :=
  if h : i+4<n then Classical.choose (hf i h) else 0

theorem state_match (n : Nat) (f : Perm n) (hf : Admis n f) (i : Nat) (hi : i+4<n) :
    matchWord (ext f) i (w (state n f hf i)) := by
  simp only [state, dif_pos hi]
  exact Classical.choose_spec (hf i hi)

theorem state_path (n : Nat) (f : Perm n) (hf : Admis n f) :
    Path (state n f hf) (n-4) := by
  intro i hi
  exact step _ i _ _ (state_match n f hf i (by omega)) (state_match n f hf (i+1) (by omega))

theorem perm_of_sig (n : Nat) (hn : 5 ≤ n) (f : Perm n) (hf : Admis n f)
    (c : Fin 6) (hsig : ∀ i<n-4, state n f hf i = sig (n-4) c i) :
    f = tmplPerm n hn c := by
  apply perm_ext
  intro i hi
  rw [show ext (tmplPerm n hn c) i = tmpl n c i by simp [ext,hi,tmplPerm]]
  apply from_short_rank_path (ext f) (tmpl n c) (invTmpl n c) n hn
    (fun j hj => ext_lt f hj) (tmpl_lt n hn c) (invTmpl_lt n hn c) (tmpl_inv n hn c)
    (inv_tmpl n hn c) (tmpl_close n hn c) _ i hi
  intro j hj
  have hh := state_match n f hf j hj
  rw [hsig j (by omega)] at hh
  exact ⟨_,hh,tmpl_match n j c hj⟩

theorem B_tmpl (n : Nat) (hn : 6 ≤ n) (f : Perm n) (hf : BAdmis n f) :
    ∃ c : Fin 6, f=tmplPerm n (by omega) c := by
  obtain ⟨c,hc⟩ := BClass _ _ (by omega) (state_path n f hf.1) (by
    intro j hj he
    have hh := state_match n f hf.1 j (by omega)
    have hE : state n f hf.1 j = 2 := Fin.ext he
    rw [hE] at hh
    exact hf.2 j (by omega) hh)
  exact ⟨c,perm_of_sig n (by omega) f hf.1 c hc⟩

theorem A_hasQ_tmpl (n : Nat) (hn : 5 ≤ n) (f : Perm n) (hf : Admis n f)
    (i : Nat) (hi : i+4<n) (hq : matchWord (ext f) i (w 5)) :
    ∃ d : Fin 2, f=tmplPerm n hn ⟨4+d.val, by omega⟩ := by
  have hh := words_unique _ i _ _ (state_match n f hf i hi) hq
  have h0 := (path_alt_iff _ _ (state_path n f hf) i (by omega)).mp (by rw [hh]; decide)
  obtain ⟨d,hd⟩ := altClass _ _ (state_path n f hf) h0
  refine ⟨d,perm_of_sig n hn f hf _ ?_⟩
  fin_cases d <;> exact hd

noncomputable def aset (n : Nat) : Finset (Perm n) := by
  classical exact Finset.univ.filter (Admis n)
noncomputable def bset (n : Nat) : Finset (Perm n) := by
  classical exact Finset.univ.filter (BAdmis n)

@[simp] theorem mem_aset (n : Nat) (f : Perm n) : f ∈ aset n ↔ Admis n f := by
  classical
  simp [aset]
@[simp] theorem mem_bset (n : Nat) (f : Perm n) : f ∈ bset n ↔ BAdmis n f := by
  classical
  simp [bset]

noncomputable def occs (n : Nat) (S : Finset (Perm n)) (u : Fin 7) :
    Finset (Perm n × Fin (n-4)) := by
  classical exact Finset.univ.filter (fun a => a.1 ∈ S ∧ matchWord (ext a.1) a.2.val (w u))

@[simp] theorem mem_occs (n : Nat) (S : Finset (Perm n)) (u : Fin 7) (a : Perm n × Fin (n-4)) :
    a ∈ occs n S u ↔ a.1 ∈ S ∧ matchWord (ext a.1) a.2.val (w u) := by
  classical
  simp [occs]

theorem A_card_lower (n : Nat) (hn : 6 ≤ n) : n-4 ≤ (aset n).card := by
  classical
  have h := Finset.card_le_card_of_injOn (tallPerm n hn)
    (s := (Finset.univ : Finset (Fin (n-4)))) (t := aset n)
    (fun x _ => (mem_aset _ _).mpr (tall_admis n hn x))
    (tallPerm_inj n hn).injOn
  simpa using h

theorem A_P_card (n : Nat) : (occs n (aset n) 2).card ≤ (aset n).card := by
  classical
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro a ha
    exact ((mem_occs _ _ _ _).mp ha).1
  · intro a ha b hb e
    have ha' := (mem_occs _ _ _ _).mp ha
    have hb' := (mem_occs _ _ _ _).mp hb
    have hf := (mem_aset _ _).mp ha'.1
    have hx := a.2.isLt
    have hy := b.2.isLt
    have hpa := words_unique _ a.2.val _ _ (state_match n a.1 hf _ (by omega)) ha'.2
    have hpb := words_unique _ b.2.val _ _ (state_match n a.1 hf _ (by omega)) (by simpa [e] using hb'.2)
    have hab : a.2.val = b.2.val := by
      rcases Nat.lt_trichotomy a.2.val b.2.val with h|h|h
      · exfalso
        exact (path_unique_peak _ _ _ _ (state_path n a.1 hf) h hy (congrArg Fin.val hpa))
          (congrArg Fin.val hpb)
      · exact h
      · exfalso
        exact (path_unique_peak _ _ _ _ (state_path n a.1 hf) h hx (congrArg Fin.val hpb))
          (congrArg Fin.val hpa)
    exact Prod.ext e (Fin.ext hab)

theorem B_tmpl_image (n : Nat) (hn : 6 ≤ n) :
    bset n = Finset.univ.image (tmplPerm n (by omega)) := by
  classical
  ext f
  simp only [mem_bset,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · intro hf
    obtain ⟨c,hc⟩ := B_tmpl n hn f hf
    exact ⟨c,hc.symm⟩
  · rintro ⟨c,rfl⟩
    exact tmpl_B n (by omega) c

theorem sig_distinguish (m : Nat) (hm : 2 ≤ m) (c d : Fin 6)
    (h0 : sig m c 0 = sig m d 0) (h1 : sig m c (m-1) = sig m d (m-1)) : c=d := by
  have he : ¬ 0+1=m := by omega
  fin_cases c <;> fin_cases d <;>
    simp [sig,aidx,he,show m-1+1=m by omega] at * <;> omega

theorem tmplPerm_inj (n : Nat) (hn : 6 ≤ n) : Function.Injective (tmplPerm n (by omega)) := by
  intro c d h
  have hsig (i : Nat) (hi : i<n-4) : sig (n-4) c i = sig (n-4) d i :=
    words_unique _ i _ _ (tmpl_admis n (by omega) c i (by omega))
      (by simpa only [h] using tmpl_admis n (by omega) d i (by omega))
  exact sig_distinguish _ (by omega) c d (hsig 0 (by omega)) (hsig (n-4-1) (by omega))

theorem B_count (n : Nat) (hn : 6 ≤ n) : (bset n).card = 6 := by
  classical
  rw [B_tmpl_image n hn, Finset.card_image_of_injective _ (tmplPerm_inj n hn)]
  simp

theorem sig_altQ (m i : Nat) (d : Fin 2) :
    sig m ⟨4+d.val,by omega⟩ i = 5 ↔ i%2=d.val := by
  fin_cases d <;> change (if _ then (5 : Fin 7) else 6) = 5 ↔ _ <;> split <;> simp_all

noncomputable def qpair (n : Nat) (hn : 5 ≤ n) (i : Fin (n-4)) : Perm n × Fin (n-4) :=
  (tmplPerm n hn ⟨4+i.val%2,by omega⟩,i)

theorem qpair_memB (n : Nat) (hn : 5 ≤ n) (i : Fin (n-4)) : qpair n hn i ∈ occs n (bset n) 5 := by
  have hi := i.isLt
  let d : Fin 2 := ⟨i.val%2, by omega⟩
  have hq : sig (n-4) ⟨4+d.val,by omega⟩ i.val = 5 := (sig_altQ _ _ d).mpr rfl
  apply (mem_occs _ _ _ _).mpr
  refine ⟨(mem_bset _ _).mpr (tmpl_B n hn _),?_⟩
  change matchWord (ext (tmplPerm n hn ⟨4+d.val, by omega⟩)) i.val (w 5)
  rw [←hq]
  exact tmpl_admis n hn _ _ (by omega)

theorem qpair_memA (n : Nat) (hn : 5 ≤ n) (i : Fin (n-4)) : qpair n hn i ∈ occs n (aset n) 5 := by
  obtain ⟨hB,hq⟩ := (mem_occs _ _ _ _).mp (qpair_memB n hn i)
  exact (mem_occs _ _ _ _).mpr ⟨(mem_aset _ _).mpr ((mem_bset _ _).mp hB).1,hq⟩

theorem qpair_only (n : Nat) (hn : 5 ≤ n) (a : Perm n × Fin (n-4))
    (ha : a ∈ occs n (aset n) 5) : a = qpair n hn a.2 := by
  obtain ⟨ha,hqa⟩ := (mem_occs _ _ _ a).mp ha
  have hi := a.2.isLt
  obtain ⟨d,hd⟩ := A_hasQ_tmpl n hn a.1 ((mem_aset _ _).mp ha) _ (by omega) hqa
  have hm := tmpl_admis n hn ⟨4+d.val, by omega⟩ a.2.val (by omega)
  rw [←hd] at hm
  have hh : sig (n-4) ⟨4+d.val, by omega⟩ a.2.val = 5 := words_unique _ _ _ _ hm hqa
  have hp := (sig_altQ _ _ d).mp hh
  apply Prod.ext
  · apply hd.trans
    change tmplPerm n hn ⟨4+d.val,by omega⟩ = tmplPerm n hn ⟨4+a.2.val%2,by omega⟩
    apply congrArg (tmplPerm n hn)
    apply Fin.ext
    change 4+d.val = 4+a.2.val%2
    omega
  · rfl

theorem Q_sets (n : Nat) (hn : 5 ≤ n) :
    occs n (aset n) 5 = Finset.univ.image (qpair n hn) ∧
    occs n (bset n) 5 = Finset.univ.image (qpair n hn) := by
  classical
  constructor <;> ext a <;> simp only [Finset.mem_image,Finset.mem_univ,true_and] <;> constructor
  · intro ha
    exact ⟨a.2, (qpair_only n hn a ha).symm⟩
  · rintro ⟨i,rfl⟩
    exact qpair_memA n hn i
  · intro hb
    obtain ⟨hb,hq⟩ := (mem_occs _ _ _ a).mp hb
    have ha := (mem_occs _ _ _ a).mpr ⟨(mem_aset _ _).mpr ((mem_bset _ _).mp hb).1,hq⟩
    exact ⟨a.2,(qpair_only n hn a ha).symm⟩
  · rintro ⟨i,rfl⟩
    exact qpair_memB n hn i

theorem Q_counts (n : Nat) (hn : 5 ≤ n) :
    (occs n (aset n) 5).card = n-4 ∧ (occs n (bset n) 5).card = n-4 := by
  have hj : Function.Injective (qpair n hn) := fun i j h => congrArg Prod.snd h
  obtain ⟨h1,h2⟩ := Q_sets n hn
  rw [h1,h2,Finset.card_image_of_injective _ hj]
  simp

end Emerging
