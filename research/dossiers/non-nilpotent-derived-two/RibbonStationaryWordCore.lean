import RibbonStationaryLocal

namespace RibbonStationaryWord
open RibbonDerived3 Ribbon5Bridge Ribbon8Free
open scoped commutatorElement
variable {G : Type*} [Group G]

abbrev Schreier := Int × Int × Bool
inductive Form where
  | transport (x y : Ltr) (inverse : Bool) (conj : List Ltr)
  | single (a b : List Schreier)

structure Mate where
  i : Nat
  j : Nat
  inverse : Bool
  conj : List Ltr
  deriving Inhabited

structure Spec where
  id : Nat
  T : List P
  cut : Nat
  U : List Schreier
  R : Form
  mates : Array Mate

instance : Inhabited Spec := ⟨⟨0,[],0,[],.single [] [],#[]⟩⟩

def comm (a b : List Ltr) : List Ltr := a++b++rev a++rev b
def twist (a b : List Ltr) : List Ltr := a++b++rev a
def orient (z : Bool) (w : List Ltr) := if z then rev w else w
def powWord (pos : Ltr) (n : Int) := List.replicate n.natAbs (if n<0 then flip pos else pos)
def schr (i j : Int) : List Ltr := twist (powWord 0 i) (comm (powWord 2 j) [0])
def schrList (L : List Schreier) : List Ltr :=
  L.flatMap fun (i,j,d) => orient d (schr i j)
def sub (a b : Ltr) (w : List Ltr) := w.map (![a,flip a,b,flip b] : Ltr → Ltr)
def rw32 : List P := [2,1,2,0,0,2,1,2,1,2,0,2,1,2,0,2,0,0,2,1,2,1,2,1,2,0,2,0,0,2,1,1]
def form : Form → List Ltr
  | .transport a b d c => twist c (orient d (sub a b (encode false rw32)))
  | .single a b => comm (schrList a) (schrList b)
def head (s : Spec) := s.T.take 32
def pfx (s : Spec) := encode false (s.T.take s.cut)
def Rstr (s : Spec) := encode false (head s)
def Tstr (s : Spec) := encode false s.T
def Ustr (s : Spec) := schrList s.U
def rel (s : Spec) (m : Mate) : Prop :=
  reduce (rev (encode false (s.T.take m.i))++encode false (s.T.take m.j)) =
    reduce (twist m.conj (orient m.inverse (Rstr s)))
instance (s : Spec) (m : Mate) : Decidable (rel s m) := by unfold rel; infer_instance

def endSide : Bool → List P → Bool
  | s, [] => s
  | s, p::w => endSide (if p=2 then !s else s) w

def Valid (s : Spec) : Prop :=
  s.T.length=64 ∧ endSide false (head s)=false ∧ endSide false s.T=false ∧
  reduce (pfx s)=reduce (Ustr s) ∧ reduce (Rstr s)=reduce (form s.R) ∧
  reduce (Tstr s)=reduce (comm (Rstr s) (rev (Ustr s))) ∧
  ∀ m : Fin s.mates.size, rel s s.mates[m]
instance (s : Spec) : Decidable (Valid s) := by unfold Valid; infer_instance

theorem ev_comm (x y : G) (a b : List Ltr) :
    ev x y (comm a b)=⁅ev x y a,ev x y b⁆ := by
  simp only [comm,ev_append,ev_rev,commutatorElement_def]
theorem ev_twist (x y : G) (a b : List Ltr) :
    ev x y (twist a b)=ev x y a * ev x y b * (ev x y a)⁻¹ := by
  simp only [twist,ev_append,ev_rev]
theorem ev_orient (x y : G) (d : Bool) (a : List Ltr) :
    ev x y (orient d a)=if d then (ev x y a)⁻¹ else ev x y a := by cases d <;> simp [orient,ev_rev]

theorem shr_mem (x y : G) (i j : Int) : ev x y (schr i j) ∈ Derived G := by
  rw [schr,ev_twist,ev_comm]
  exact (inferInstance : (Derived G).Normal).conj_mem _ (Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _)) _

theorem shrs_mem (x y : G) (L : List Schreier) : ev x y (schrList L) ∈ Derived G := by
  induction L with
  | nil => simp [schrList,ev]
  | cons z zs ih =>
    obtain ⟨i,j,d⟩ := z
    simp only [schrList,List.flatMap_cons,ev_append,ev_orient]
    apply (Derived G).mul_mem _ ih
    cases d
    · exact shr_mem x y i j
    · exact (Derived G).inv_mem (shr_mem x y i j)

theorem ev_sub (x y : G) (a b : Ltr) (w : List Ltr) :
    ev x y (sub a b w)=ev (letter x y a) (letter x y b) w := by
  induction w with
  | nil => rfl
  | cons p ps ih =>
    simp only [sub,List.map_cons,ev]
    change letter x y (![a,flip a,b,flip b] p) * ev x y (sub a b ps) = _
    rw [ih]
    fin_cases p
    · rfl
    · exact congrArg (fun q => q*ev (letter x y a) (letter x y b) ps) (flip_letter x y a)
    · rfl
    · exact congrArg (fun q => q*ev (letter x y a) (letter x y b) ps) (flip_letter x y b)

theorem rw32_residue (x y : G) : ev x y (encode false rw32)=Ribbon6.residue x y := by
  norm_num [rw32,encode,ev,letter,Ribbon6.residue,Ribbon6.U,Ribbon6.V] <;> group

theorem form_mem (x y : G) (f : Form) : ev x y (form f) ∈ DLS G 1 := by
  cases f with
  | single a b =>
    rw [form,ev_comm]
    exact Subgroup.commutator_mem_commutator (shrs_mem x y a) (shrs_mem x y b)
  | transport a b d c =>
    rw [form,ev_twist,ev_orient,ev_sub,rw32_residue]
    apply (inferInstance : (DLS G 1).Normal).conj_mem
    cases d
    · exact residue_in_D2 _ _
    · exact (DLS G 1).inv_mem (residue_in_D2 _ _)

theorem path_sound (x y : G) (w : List P) (i : Nat) :
    (pathAt x y w.toArray i).2 = ev x y (encode false (w.take i)) := by
  simp only [pathAt,run_trace,start,one_mul,ev_encode,List.toList_toArray]

theorem endSide_sound (x y : G) (w : List P) (s : Bool) (g : G) :
    (run x y (s,g) w).1 = endSide s w := by
  induction w generalizing s g with
  | nil => rfl
  | cons p ps ih =>
    change (run x y (action x y (s,g) p) ps).1 = _
    by_cases h : p=2 <;> simpa only [endSide,action,h,if_true,if_false] using (ih _ _)

theorem complete_head (s : Spec) (V : Valid s) (x y : G) (R : ev x y (Rstr s)=1) :
    pathAt x y (head s).toArray 32 = pathAt x y (head s).toArray 0 := by
  have H : (head s).length = 32 := by simpa only [head,List.length_take,V.1,Nat.min_eq_left (by decide : 32≤64)]
  have S := V.2.1
  apply Prod.ext
  · simpa only [pathAt,List.toList_toArray,List.take_zero,start,
        List.take_of_length_le (Nat.le_of_eq H),endSide_sound, endSide] using S
  · rw [path_sound,path_sound,List.take_of_length_le (Nat.le_of_eq H)]
    exact R

theorem complete_all (s : Spec) (V : Valid s) (dnil : DLS G 2=⊥) (x y : G) :
    pathAt x y s.T.toArray 64 = pathAt x y s.T.toArray 0 := by
  have M : ev x y (Rstr s) ∈ DLS G 1 := by rw [sound x y _ _ V.2.2.2.2.1]; exact form_mem x y _
  have U := shrs_mem x y s.U
  have N : Commute (ev x y (Rstr s)) (ev x y (Ustr s)) := by
    apply commutatorElement_eq_one_iff_commute.mp
    exact Subgroup.mem_bot.mp (dnil ▸ Subgroup.commutator_mem_commutator M U :
      ⁅ev x y (Rstr s),ev x y (Ustr s)⁆ ∈ (⊥ : Subgroup G))
  apply Prod.ext
  · simpa only [pathAt,List.toList_toArray,List.take_zero,start,
        List.take_of_length_le (Nat.le_of_eq V.1),endSide_sound, endSide] using V.2.2.1
  · rw [path_sound,path_sound,List.take_of_length_le (Nat.le_of_eq V.1)]
    change ev x y (Tstr s) = 1
    rw [sound x y _ _ V.2.2.2.2.2.1,ev_comm,ev_rev,N.inv_right.commutator_eq]

theorem mate_ne (s : Spec) (V : Valid s) (x y : G) (N : ev x y (Rstr s)≠1)
    (m : Fin s.mates.size) :
    pathAt x y s.T.toArray s.mates[m].i ≠ pathAt x y s.T.toArray s.mates[m].j := by
  let b := s.mates[m]
  have C : rel s b := V.2.2.2.2.2.2 m
  unfold rel at C
  have E := sound x y _ _ C
  simp only [ev_append,ev_rev,ev_twist] at E
  intro eq
  have P := congrArg Prod.snd eq
  rw [path_sound,path_sound] at P
  change ev x y (encode false (s.T.take b.i)) = ev x y (encode false (s.T.take b.j)) at P
  rw [P,inv_mul_cancel] at E
  have Q : ev x y (orient b.inverse (Rstr s))=1 := by
    calc
      _ = (ev x y b.conj)⁻¹ * (ev x y b.conj * ev x y (orient b.inverse (Rstr s)) *
          (ev x y b.conj)⁻¹) * ev x y b.conj := by group
      _ = 1 := by rw [←E]; group
  apply N
  cases B : b.inverse <;> simpa [ev_orient,B] using Q

end RibbonStationaryWord
#print axioms RibbonStationaryWord.complete_all
#print axioms RibbonStationaryWord.mate_ne
