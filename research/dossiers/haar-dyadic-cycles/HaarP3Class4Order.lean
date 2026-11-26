import HaarP3Class4Interpret
import HaarClass5TemplateClosure

namespace HaarP3Class4Order
open scoped commutatorElement
open HaarUniversal36 HaarClass4Generate HaarClass4Ports HaarClass5TemplateClosure
open HaarClass4Normal HaarP3Class4Interpret
variable {G : Type*} [Group G]

theorem c_order3 (c x : G) (hc : c∈L G 1)
    (h : orderOf ((QuotientGroup.mk' (L G 3)) ⁅c,x⁆)=3) :
    3 ∣ orderOf ((QuotientGroup.mk' (L G 2)) c) := by
  let T := L G 2
  let S := L G 3
  let f := QuotientGroup.mk' S
  let g := QuotientGroup.mk' T
  let n := orderOf (g c)
  change 3 ∣ n
  have e : c^n∈T := by
    apply (QuotientGroup.eq_one_iff (N:=T) _).mp
    change g (c^n)=1
    rw [map_pow]
    exact pow_orderOf_eq_one _
  have hm : T.map f=L (G ⧸ S) 2 := map_ls f (QuotientGroup.mk'_surjective S) 2
  have nil3 : L (G ⧸ S) 3=⊥ := quote_nil 3
  have mk (z:G) (hz:z∈T) : f z ∈ L (G ⧸ S) 2 := hm ▸ Subgroup.mem_map_of_mem f hz
  have ce : Commute ((f c)^n) (f x) := by
    rw [←map_pow]
    exact central_2 nil3 (mk (c^n) e) _
  have hc' : Commute (f c) ⁅f c,f x⁆ := by
    have ct := central_2 nil3 (mk _ (next hc x)) (f c)
    rw [map_commutatorElement] at ct
    exact ct.symm
  have de : (f ⁅c,x⁆)^n=1 := by
    rw [map_commutatorElement,hc'.commutatorElement_pow_left n,ce.commutator_eq]
  have m := orderOf_dvd_iff_pow_eq_one.mpr de
  change orderOf (f ⁅c,x⁆) = 3 at h
  rwa [h] at m

theorem pivot_order (nil : L G 4=⊥) (v x : G) (e : ℕ)
    (ord : orderOf ⁅v,x⁆=3) (hm : ⁅v,x⁆ ∈ L G 3) (hc : v^(3:ℕ)=⁅v,x⁆^e) :
    orderOf ((QuotientGroup.mk' (L G 3)) v)=3 := by
  let S := L G 3
  let f := QuotientGroup.mk' S
  have ea : f ⁅v,x⁆=1 := (QuotientGroup.eq_one_iff (N:=S) _).mpr hm
  change orderOf (f v)=3
  apply orderOf_eq_prime
  · simpa [map_pow,ea] using congrArg f hc
  · intro g
    have hv : v∈L G 3 := (QuotientGroup.eq_one_iff (N:=S) _).mp g
    have h := next hv x
    change ⁅v,x⁆∈L G 4 at h
    rw [nil] at h
    have e := Subgroup.mem_bot.mp h
    rw [e,orderOf_one] at ord
    omega

theorem small_projection (nil : L G 4=⊥) (x y : G) :
    HaarClass4Projection.KillsMid (make nil x y) (QuotientGroup.mk' (L G 2)) := by
  let φ := QuotientGroup.mk' (L G 2)
  obtain ⟨a,b,d⟩ := tail_layers nil x y
  have mid : L G 3 ≤ L G 2 := (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)) (by decide : 2 ≤ 3)
  exact ⟨⟨(QuotientGroup.eq_one_iff _).mpr (mid a),(QuotientGroup.eq_one_iff _).mpr (mid b),
      (QuotientGroup.eq_one_iff _).mpr (mid d)⟩,
      (QuotientGroup.eq_one_iff _).mpr (layer_u x y),(QuotientGroup.eq_one_iff _).mpr (layer_v x y)⟩

end HaarP3Class4Order
#print axioms HaarP3Class4Order.c_order3
#print axioms HaarP3Class4Order.pivot_order
