import RamseySearch

namespace Erdos151Ramsey.Seed53
set_option maxHeartbeats 0
set_option maxRecDepth 4096

def masks : Array Nat := #[44017215603840, 90164472848640, 4400659583488, 290293904098304, 582788038264832, 1161177761715200, 2322356060299264, 145510543392769, 612571054082, 400508388356, 148030347018793, 2328164340858896, 152729039667236, 6409199550530, 1128889273417740, 658951196639496, 51267212673536, 384004989665312, 767460223486272, 1254544981889544, 2509227402731776, 2854343191581186, 3141304720557190, 1990667412703237, 2990783296831502, 3729685175607317, 2815033772425251, 1407941820317783, 1214995247464588, 175990923985232, 2322306005476024, 141012368949621, 1649302045418, 291370667345360, 582741296950184, 285873308455761, 290271623441056, 580543247899712, 1161086493702784, 2322172995532032, 140750646585344, 17189688338, 34362600580, 1125977221959689, 2251954710282258, 275439747105, 551133284418, 1408477097628800, 140849337991176, 154717683728, 149808904421408, 18143140382784]

def adj (a b : Fin 52) : Bool :=
  masks[a.val]!.testBit b.val

def graph (a b : Fin 52) : Prop := adj a b = true

instance : DecidableRel graph := fun a b => inferInstanceAs (Decidable (adj a b = true))

def rowCheck (a : Fin 52) : Bool :=
  findIndependent adj 11 ((List.finRange 52).filter
    (fun b => decide (a < b) && !adj a b))

def tfCheck (a : Fin 52) : Bool :=
  (List.finRange 52).all fun b =>
    if adj a b then (List.finRange 52).all (fun c => !(adj b c && adj a c)) else true

theorem tfCheck_sound (h : ∀ a, tfCheck a = true) : TriangleFree graph := by
  intro a b c hab hbc hac
  have hb := List.all_eq_true.mp (h a) b (List.mem_finRange b)
  change adj a b = true at hab
  rw [if_pos hab] at hb
  have hc := List.all_eq_true.mp hb c (List.mem_finRange c)
  change adj b c = true at hbc
  change adj a c = true at hac
  simp [hbc, hac] at hc

end Erdos151Ramsey.Seed53
