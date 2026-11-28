import AtlasBits
import AtlasCycle
import AtlasSound

namespace BikovEight
open BikovLocal (cyclic)

private theorem coord (i : Fin 8) : Fin.ofNat 8 i.val=i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

private theorem decide_congr0 {P Q : Prop} [Decidable P] [Decidable Q] (h : P↔Q) :
    decide P=decide Q := by
  by_cases p : P
  · exact (decide_eq_true p).trans (decide_eq_true (h.mp p)).symm
  · exact (decide_eq_false p).trans (decide_eq_false (fun q=>p (h.mpr q))).symm

variable {G : Fin 8→Fin 8→Prop} [DecidableRel G]

def g (i j : Nat) : Bool := decide (G (Fin.ofNat 8 i) (Fin.ofNat 8 j))

theorem cycle_edge (k : Nat) (k5 : 0<k) (k8 : k≤8)
    (sym : ∀ a b,G a b→G b a)
    (geom : ∀ i j : Fin 8, i<j → j.val<k → (G i j ↔ cyclic k i.val j.val))
    (i : Nat) (hi : i<k) (k2 : 2≤k) :
    g (G:=G) i ((i+1)%k)=true := by
  have I : i<8 := by omega
  by_cases e:i+1<k
  · rw [Nat.mod_eq_of_lt e]
    let a : Fin 8 := ⟨i,I⟩
    let b : Fin 8 := ⟨i+1,by omega⟩
    have H := (geom a b (by change i<i+1; omega) (show b.val<k from e)).mpr
      (show cyclic k i (i+1) from Or.inl rfl)
    unfold g
    rw [show Fin.ofNat 8 i=a from coord a,show Fin.ofNat 8 (i+1)=b from coord b]
    exact decide_eq_true H
  · have E : i+1=k := by omega
    rw [E,Nat.mod_self]
    let a : Fin 8 := ⟨i,I⟩
    let b : Fin 8 := 0
    have H := (geom b a (by change 0<i; omega) (show a.val<k from hi)).mpr
      (show cyclic k 0 i from Or.inr ⟨rfl,E⟩)
    unfold g
    rw [show Fin.ofNat 8 i=a from coord a,show Fin.ofNat 8 0=b from rfl]
    exact decide_eq_true (sym b a H)

theorem local_attachment (k j : Nat) (h : ∀ i<k,g (G:=G) i ((i+1)%k)=true)
    (tri : ∀ a b c, G a b→G a c→G b c→False) :
    (List.range k).all (fun i=> !((packF (fun i=>g (G:=G) i j) k).testBit i &&
      (packF (fun i=>g (G:=G) i j) k).testBit ((i+1)%k)))=true := by
  apply List.all_eq_true.mpr
  intro i hi
  have ik := List.mem_range.mp hi
  have mk : (i+1)%k<k := Nat.mod_lt _ (by omega)
  rw [packF_bit _ _ _ ik,packF_bit _ _ _ mk]
  by_cases a : g (G:=G) i j=true <;> by_cases b : g (G:=G) ((i+1)%k) j=true <;> simp [a,b]
  exact False.elim (tri _ _ _ (of_decide_eq_true (h i ik)) (of_decide_eq_true a) (of_decide_eq_true b))

theorem pack_no_overlap (l j : Nat) (h : g (G:=G) l j=true)
    (tri : ∀ a b c,G a b→G a c→G b c→False) :
    (packF (fun i=>g (G:=G) i l) 5) &&& (packF (fun i=>g (G:=G) i j) 5)=0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases b : i<5
  · rw [packF_bit _ _ _ b,packF_bit _ _ _ b]
    by_cases p : g (G:=G) i l=true <;> by_cases q : g (G:=G) i j=true <;> simp [p,q]
    exact False.elim (tri _ _ _ (of_decide_eq_true p) (of_decide_eq_true q) (of_decide_eq_true h))
  · have hp : packF (fun i=>g (G:=G) i l) 5<2^i :=
      (packF_small _ 5).trans_le (Nat.pow_le_pow_right (n:=2) (by decide) (by omega))
    simp [Nat.testBit_lt_two_pow hp]

theorem normalized5 (sym : ∀ a b,G a b→G b a) (irr : ∀ a,¬G a a)
    (tri : ∀ a b c,G a b→G a c→G b c→False)
    (geom : ∀ i j : Fin 8, i<j → j.val<5 → (G i j ↔ cyclic 5 i.val j.val)) :
    ∃ h, h<10648 ∧ valid5 h=true ∧ (∀ i j,R (word5 h) i j ↔ G i j) := by
  let p := packF (fun i=>g (G:=G) i 5) 5
  let q := packF (fun i=>g (G:=G) i 6) 5
  let r := packF (fun i=>g (G:=G) i 7) 5
  let z (i : Nat) := if i=0 then g (G:=G) 5 6 else if i=1 then g (G:=G) 5 7 else g (G:=G) 6 7
  let e := packF z 3
  have pB : p<32 := packF_small _ 5
  have qB : q<32 := packF_small _ 5
  have rB : r<32 := packF_small _ 5
  have eB : e<8 := packF_small _ 3
  have H := cycle_edge 5 (by decide) (by decide) sym geom
  obtain ⟨a,ha⟩ := attachment5 p pB (local_attachment 5 5 (fun i hi=>H i hi (by decide)) tri)
  obtain ⟨b,hb⟩ := attachment5 q qB (local_attachment 5 6 (fun i hi=>H i hi (by decide)) tri)
  obtain ⟨c,hc⟩ := attachment5 r rB (local_attachment 5 7 (fun i hi=>H i hi (by decide)) tri)
  have E (u : Nat) (hu : u<3) : e.testBit u=z u := packF_bit z u 3 hu
  have E0 : e.testBit 0=g (G:=G) 5 6 := by rw [E 0 (by decide)]; rfl
  have E1 : e.testBit 1=g (G:=G) 5 7 := by rw [E 1 (by decide)]; rfl
  have E2 : e.testBit 2=g (G:=G) 6 7 := by rw [E 2 (by decide)]; rfl
  have not7 : e≠7 := by
    intro ee
    rw [ee] at E0 E1 E2
    exact tri _ _ _ (of_decide_eq_true E0.symm) (of_decide_eq_true E1.symm)
      (of_decide_eq_true E2.symm)
  have combo : good5 p q r e=true := by
    unfold good5
    have W : (e != 7)=true := bne_iff_ne.mpr not7
    rw [W,E0,E1,E2]
    have s (u v : Nat) : (!g (G:=G) u v ||
      (packF (fun i=>g (G:=G) i u) 5) &&& (packF (fun i=>g (G:=G) i v) 5)==0)=true := by
      by_cases t : g (G:=G) u v=true
      · have h := pack_no_overlap u v t tri
        simp [t,h]
      · simp [Bool.eq_false_iff.mpr t]
    have x := s 5 6
    have y := s 5 7
    have z := s 6 7
    change (!(g (G:=G) 5 6) || p &&& q == 0)=true at x
    change (!(g (G:=G) 5 7) || p &&& r == 0)=true at y
    change (!(g (G:=G) 6 7) || q &&& r == 0)=true at z
    simp [x,y,z]
  obtain ⟨hB,graph,valid⟩ := word_index a b c e eB
  rw [ha,hb,hc] at graph valid
  have ord (i j : Fin 8) (ij : i<j) :
      hasEdge (make5 p q r e) i.val j.val=g (G:=G) i.val j.val := by
    rw [bits5 p q r e pB qB rB i j ij]
    unfold pick5
    have i8 := i.isLt
    have j8 := j.isLt
    have ij' : i.val<j.val := ij
    by_cases j5 : j.val<5
    · rw [if_pos j5]
      unfold g
      rw [coord i,coord j]
      exact decide_congr0 (geom i j ij j5).symm
    · rw [if_neg j5]
      by_cases i5 : i.val<5
      · rw [if_pos i5]
        by_cases jE : j.val=5
        · simp only [if_pos jE,p]
          rw [packF_bit _ _ _ i5,jE]
        · rw [if_neg jE]
          by_cases jF : j.val=6
          · simp only [if_pos jF,q]
            rw [packF_bit _ _ _ i5,jF]
          · have jG : j.val=7 := by omega
            simp only [if_neg jF,r]
            rw [packF_bit _ _ _ i5,jG]
      · rw [if_neg i5]
        by_cases jF : j.val=6
        · have iE : i.val=5 := by omega
          simp [iE,jF,E0]
        · have jG : j.val=7 := by omega
          rw [if_neg jF]
          by_cases iE : i.val=5
          · simp [iE,jG,E1]
          · have iF : i.val=6 := by omega
            simp [iF,jG,E2]
  have sym_g (i j : Nat) : g (G:=G) i j=g (G:=G) j i :=
    decide_congr0 ⟨sym _ _,sym _ _⟩
  refine ⟨_,hB,valid.trans combo,?_⟩
  intro i j
  unfold R
  rw [graph]
  rcases lt_trichotomy i j with l|eq|rj
  · rw [ord i j l]
    simp only [g,coord,decide_eq_true_eq]
  · subst j
    simp [hasEdge,irr]
  · rw [has_sym (make5 p q r e) i.val j.val,ord j i rj,sym_g]
    simp only [g,coord,decide_eq_true_eq]

theorem normalized7 (sym : ∀ a b,G a b→G b a) (irr : ∀ a,¬G a a)
    (tri : ∀ a b c,G a b→G a c→G b c→False)
    (geom : ∀ i j : Fin 8, i<j → j.val<7 → (G i j ↔ cyclic 7 i.val j.val)) :
    ∃ p, p<128 ∧ good7 p=true ∧ (∀ i j,R (make7 p) i j ↔ G i j) := by
  let p := packF (fun i=>g (G:=G) i 7) 7
  have pB : p<128 := packF_small _ 7
  have H := cycle_edge 7 (by decide) (by decide) sym geom
  have v : good7 p=true := local_attachment 7 7 (fun i hi=>H i hi (by decide)) tri
  have ord (i j : Fin 8) (ij : i<j) :
      hasEdge (make7 p) i.val j.val=g (G:=G) i.val j.val := by
    rw [bits7 p i j ij]
    unfold pick7
    by_cases j7 : j.val<7
    · rw [if_pos j7]
      unfold g
      rw [coord i,coord j]
      exact decide_congr0 (geom i j ij j7).symm
    · have J : j.val=7 := by have := j.isLt; omega
      have I : i.val<7 := by have H : i.val<j.val := ij; omega
      rw [if_neg j7,packF_bit _ _ _ I,J]
  have sym_g (i j : Nat) : g (G:=G) i j=g (G:=G) j i :=
    decide_congr0 ⟨sym _ _,sym _ _⟩
  refine ⟨p,pB,v,?_⟩
  intro i j
  unfold R
  rcases lt_trichotomy i j with l|eq|rj
  · rw [ord i j l]
    simp only [g,coord,decide_eq_true_eq]
  · subst j
    simp [hasEdge,irr]
  · rw [has_sym (make7 p) i.val j.val,ord j i rj,sym_g]
    simp only [g,coord,decide_eq_true_eq]

#print axioms normalized5
#print axioms normalized7
end BikovEight
