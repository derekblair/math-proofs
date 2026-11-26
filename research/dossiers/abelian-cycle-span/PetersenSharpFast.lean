import PetersenSharpCover

namespace PetersenSharp

def enc (u : V) : ℕ := 5*u.1.val+u.2.val

theorem enc_inj : Function.Injective enc := by
  intro a b e
  have s := ZMod.val_lt a.2
  have t := ZMod.val_lt b.2
  unfold enc at e
  exact Prod.ext (Fin.ext (by omega)) (ZMod.val_injective 5 (by omega))

def fast (u : ℕ) (p : P) : ℕ :=
  (#[
5,20,25,6,21,26,7,22,27,8,23,28,9,24,29,
10,0,30,11,1,31,12,2,32,13,3,33,14,4,34,
15,5,35,16,6,36,17,7,37,18,8,38,19,9,39,
20,10,41,21,11,42,22,12,43,23,13,44,24,14,40,
0,15,45,1,16,46,2,17,47,3,18,48,4,19,49,
35,40,0,36,41,1,37,42,2,38,43,3,39,44,4,
42,48,5,43,49,6,44,45,7,40,46,8,41,47,9,
49,25,10,45,26,11,46,27,12,47,28,13,48,29,14,
25,33,19,26,34,15,27,30,16,28,31,17,29,32,18,
32,36,20,33,37,21,34,38,22,30,39,23,31,35,24
  ] : Array ℕ)[3*u+p.val]?.getD 99

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem fast_ok (u : V) (p : P) : fast (enc u) p = enc (next u p) := by decide +revert

end PetersenSharp
