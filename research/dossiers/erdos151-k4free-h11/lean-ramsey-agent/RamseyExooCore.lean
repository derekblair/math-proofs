import RamseySearch

namespace Erdos151Ramsey.Exoo
set_option maxHeartbeats 0
set_option maxRecDepth 4096

def masks : Array Nat := #[2341092722982, 18702976712721, 18969798910081, 2766258843648, 2616778033282, 35547298996225, 2199333677440, 26461868116, 1925370351681, 215847432192, 64453476352, 23126255603793, 35184407251848, 38723388012, 35480798757376, 4591387152450, 29699703701536, 552775779840, 17741234831616, 4605278778370, 34084864668672, 8796764128316, 207233304714, 44256081217096, 65970731222920, 422735515712, 68761870353, 22027052253568, 44324197105737, 4436745650306, 35235949970196, 10999545858086, 71403955217, 4947836208770, 27488864486568, 11271739059200, 3852925927968, 1649306010129, 34670133556, 61787399651592, 35407711504646, 105227812953, 9279408128, 603739717632, 567088056326, 1650634805280]

def adj (a b : Fin 46) : Bool :=
  masks[a.val]!.testBit b.val

def graph (a b : Fin 46) : Prop := adj a b = true

instance : DecidableRel graph := fun a b => inferInstanceAs (Decidable (adj a b = true))

def rowCheck (a : Fin 46) : Bool :=
  findIndependent adj 10 ((List.finRange 46).filter
    (fun b => decide (a < b) && !adj a b))

def tfCheck (a : Fin 46) : Bool :=
  (List.finRange 46).all fun b =>
    if adj a b then (List.finRange 46).all (fun c => !(adj b c && adj a c)) else true

theorem tfCheck_sound (h : ∀ a, tfCheck a = true) : TriangleFree graph := by
  intro a b c hab hbc hac
  have hb := List.all_eq_true.mp (h a) b (List.mem_finRange b)
  change adj a b = true at hab
  rw [if_pos hab] at hb
  have hc := List.all_eq_true.mp hb c (List.mem_finRange c)
  change adj b c = true at hbc
  change adj a c = true at hac
  simp [hbc, hac] at hc

end Erdos151Ramsey.Exoo
