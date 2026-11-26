import RibbonOddJetCore
namespace RibbonOddFinite
open RibbonOrderThree RibbonStationaryWord
set_option maxHeartbeats 0
set_option maxRecDepth 30000
def jetTable : Array (Array Count) := #[#[2,0,0,0,0,0,0,0],#[0,0,0,2,0,0,0,0],#[0,3,0,0,0,0,0,2],#[0,0,0,0,0,0,0,0],#[0,0,0,0,2,0,0,0],#[0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,2,0],#[0,0,2,0,2,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,2,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,2,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,2,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,2,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,2],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
def pickJet (i : Fin 28) (d : Dir i) : Count := (jetTable[i.val]!)[d.val]!
def checkJet (i : Fin 28) (d : Dir i) : Prop :=
  let k := pickJet i d
  let row := jetRow i (direction i d).1 (direction i d).2 k
  RibbonP11Pair.checkRows row row (spec k)=true
instance (i : Fin 28) (d : Dir i) : Decidable (checkJet i d) := by unfold checkJet; infer_instance
end RibbonOddFinite
