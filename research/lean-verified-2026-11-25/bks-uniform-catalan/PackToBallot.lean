import ActiveRanks

namespace FussCover
open Finset
variable {z h j : ℕ} (hj : 0<j) (hz : 0<z)
variable (r : Equiv.Perm (Fin (n z h j))) (P : packed r)

def upRanks : Finset (Fin (2*j)) := univ.image (U hj hz r P)
def downRanks : Finset (Fin (2*j)) := univ.image (D hj hz r P)

lemma up_card : (upRanks hj hz r P).card=j := by
  unfold upRanks
  rw [card_image_of_injective _ (U_mono hj hz r P).injective]
  exact Fintype.card_fin j

lemma down_eq_compl : downRanks hj hz r P = (upRanks hj hz r P)ᶜ := by
  ext x
  simp only [upRanks,downRanks,mem_image,mem_univ,true_and,mem_compl]
  constructor
  · intro ⟨d,dd⟩ ⟨u,uu⟩
    exact disjoint_core hj hz r P u d (uu.trans dd.symm)
  · intro ne
    exact (active_all hj hz r P x).resolve_left ne

lemma up_order :
    (fun i => (upRanks hj hz r P).orderEmbOfFin (up_card hj hz r P) i) = U hj hz r P := by
  apply StrictMono.eq_of_range_eq (Finset.orderEmbOfFin _ _).strictMono (U_mono hj hz r P)
  rw [range_orderEmbOfFin]
  ext x
  simp [upRanks,Set.mem_range]

lemma down_order :
    (fun i => ((upRanks hj hz r P)ᶜ : Finset _).orderEmbOfFin
      (comp_card _ (up_card hj hz r P)) i) = D hj hz r P := by
  apply StrictMono.eq_of_range_eq (Finset.orderEmbOfFin _ _).strictMono (D_mono hj hz r P)
  rw [range_orderEmbOfFin,←down_eq_compl hj hz r P]
  ext x
  simp [downRanks,Set.mem_range]

def packToBallot (c : {r : Equiv.Perm (Fin (n z h j)) // packed r}) : BallotSet j :=
  ⟨upRanks hj hz c.1 c.2, up_card hj hz c.1 c.2, by
    apply (ballot_iff_orders _ (up_card hj hz c.1 c.2)).2
    intro i
    rw [congrFun (up_order hj hz c.1 c.2) i,congrFun (down_order hj hz c.1 c.2) i]
    exact crossing hj hz c.1 c.2 i⟩

end FussCover
