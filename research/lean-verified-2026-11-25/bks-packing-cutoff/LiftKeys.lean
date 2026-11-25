import AltRows

namespace CoverCutoff

def liftBase (h j : ℕ) := 3*(h+j)+3
def mainU {j : ℕ} (h : ℕ) (p : Equiv.Perm (Fin (SmallN j))) (i : ℕ) :=
  3*(liftBase h j + smallU (readRank p) i)
def mainV {j : ℕ} (h : ℕ) (p : Equiv.Perm (Fin (SmallN j))) (i : ℕ) :=
  3*(liftBase h j + smallV (readRank p) i)

def keyA {j : ℕ} (h : ℕ) (p : Equiv.Perm (Fin (SmallN j))) (i : ℕ) :=
  if i<h-1 then h+2*i else mainU h p (i-(h-1))

def keyC {j : ℕ} (h : ℕ) (p : Equiv.Perm (Fin (SmallN j))) (i : ℕ) :=
  if i≤j then mainV h p i else 3*(liftBase h j + SmallN j)+i

/-- Place each middle marker immediately before its right A neighbour.
    If `flip` is enabled and the marked index is h, put it just after its
    left A neighbour instead. -/
def betweenKey {j : ℕ} (h : ℕ) (p : Equiv.Perm (Fin (SmallN j))) (flip : Bool) (i : ℕ) :=
  if i+1<h-1 then h+2*i+1
  else if flip && i==h then mainU h p 1 + 1
  else mainU h p (i+1-(h-1))-1

def keyB {j : ℕ} (h : ℕ) (p : Equiv.Perm (Fin (SmallN j))) (flip : Bool) (i : ℕ) :=
  if i<h-1 then i else betweenKey h p flip (i-(h-1))

def bigKey {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) (flip : Bool) (v : ℕ) : ℕ :=
  match v%3 with
  | 0 => keyA h p (v/3)
  | 1 => keyB h p flip (v/3)
  | _ => keyC h p (v/3)

@[simp] lemma bigKey_A {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) (flip : Bool) (i : ℕ) :
    bigKey (h:=h) p flip (posA i)=keyA h p i := by
  simp [bigKey,posA,show 3*i/3=i by omega,show (3*i)%3=0 by omega]

@[simp] lemma bigKey_B {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) (flip : Bool) (i : ℕ) :
    bigKey (h:=h) p flip (posB i)=keyB h p flip i := by
  simp [bigKey,posB,show (3*i+1)/3=i by omega,show (3*i+1)%3=1 by omega]

@[simp] lemma bigKey_C {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) (flip : Bool) (i : ℕ) :
    bigKey (h:=h) p flip (posC i)=keyC h p i := by
  simp [bigKey,posC,show (3*i+2)/3=i by omega,show (3*i+2)%3=2 by omega]

lemma readRank_lt {n : ℕ} (r : Equiv.Perm (Fin n)) {x : ℕ} (hx : x<n) :
    readRank r x<n := by
  simp [readRank,hx,(r ⟨x,hx⟩).isLt]

lemma readRank_inj {n : ℕ} (r : Equiv.Perm (Fin n)) {x y : ℕ} (hx : x<n) (hy : y<n)
    (h : readRank r x=readRank r y) : x=y := by
  have he : r ⟨x,hx⟩=r ⟨y,hy⟩ := Fin.ext (by simpa [readRank,hx,hy] using h)
  exact congrArg Fin.val (r.injective he)

lemma mainU_bound {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) (hj : 1≤j)
    {i : ℕ} (hi : i≤j) :
    3*liftBase h j≤mainU h p i ∧ mainU h p i<3*(liftBase h j+SmallN j) := by
  have ht := readRank_lt p (x:=uPos i) (by rw [smallSize hj]; unfold uPos; omega)
  unfold mainU smallU
  omega

lemma mainV_bound {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j))) (hj : 1≤j)
    {i : ℕ} (hi : i≤j) :
    3*liftBase h j≤mainV h p i ∧ mainV h p i<3*(liftBase h j+SmallN j) := by
  have ht := readRank_lt p (x:=vPos i) (by rw [smallSize hj]; unfold vPos; omega)
  unfold mainV smallV
  omega

lemma mainU_step {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j)))
    (R : CatalanRows (readRank p) j) {i : ℕ} (hi : i<j) :
    mainU h p i+3≤mainU h p (i+1) := by
  have hU := R.1 i (Nat.zero_le _) (by omega)
  unfold mainU
  omega

lemma mainV_step {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j)))
    (R : CatalanRows (readRank p) j) {i : ℕ} (hi : i<j) :
    mainV h p i+3≤mainV h p (i+1) := by
  have hV := R.2.1 i (Nat.zero_le _) (by omega)
  unfold mainV
  omega

lemma mainCross {h j : ℕ} (p : Equiv.Perm (Fin (SmallN j)))
    (R : CatalanRows (readRank p) j) {i : ℕ} (hi : i<j) :
    mainU h p (i+1)+3≤mainV h p i := by
  have hX := R.2.2 i hi
  unfold mainU mainV
  omega

#print axioms mainCross
end CoverCutoff
