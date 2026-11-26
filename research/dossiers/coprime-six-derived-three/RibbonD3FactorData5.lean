namespace RibbonD3Low
structure Factor5 where
  i : Nat
  j : Nat
  u : Int
  v : Int
  s : Int
  degree : Nat
  deriving Inhabited, DecidableEq

def factors5 : Array Factor5 := #[⟨17,35,0,0,1,2⟩, ⟨18,36,0,0,1,2⟩, ⟨19,37,0,0,1,2⟩, ⟨20,38,0,0,1,2⟩, ⟨21,39,0,0,1,2⟩, ⟨22,40,0,0,1,2⟩, ⟨23,41,0,0,1,2⟩, ⟨24,81,0,0,1,2⟩, ⟨25,80,0,0,1,2⟩, ⟨26,79,0,0,1,2⟩, ⟨27,78,0,0,1,2⟩, ⟨51,72,0,0,1,2⟩, ⟨52,73,0,0,1,2⟩, ⟨53,74,0,0,1,2⟩, ⟨54,75,0,0,1,2⟩, ⟨55,76,0,0,1,2⟩, ⟨56,77,0,0,1,2⟩]
end RibbonD3Low
