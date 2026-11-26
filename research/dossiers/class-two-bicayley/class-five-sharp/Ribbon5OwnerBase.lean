import Ribbon5OwnerCore

namespace Ribbon5Owner
open Ribbon5Packed

def pref (root : Bool) (w : List P) : State := w.foldl step (zero root)

theorem pref_snoc (root : Bool) (w : List P) (p : P) :
    pref root (w++[p]) = step (pref root w) p := by simp [pref]

end Ribbon5Owner
