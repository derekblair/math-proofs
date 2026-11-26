import RibbonStationarySurfaceData0
import RibbonStationarySurfaceData1
import RibbonStationarySurfaceData2

namespace RibbonStationaryField
open RibbonAffine (mulP)
def commonN : Int := 1370250132213362400
def surfN : Int := 6075
def surfJoin : Id := ⟨[(0,3,-16),(0,2,-116),(0,1,-248),(0,0,-340)],[(0,3,32),(0,2,-8),(0,1,-44),(0,0,-340)],[(0,0,45)],[],[(0,1,6075),(0,0,6075)]⟩
def surf11Join : Id := ⟨[(0,0,1)],[],[],[],[(0,10,1),(0,0,-1)]⟩
def surf43Join : Id := ⟨[(0,2,13),(0,1,-7),(0,0,-20)],[(0,1,-13),(0,0,-21)],[],[(0,5,-6),(0,4,3),(0,3,10),(0,2,-8),(0,1,-2),(0,0,-1)],[(0,2,1),(0,1,-1),(0,0,-2)]⟩
def surf43target : Poly := [(0,2,1),(0,1,-1),(0,0,-2)]
def surfGcd : Poly := [(0,1,1),(0,0,1)]
theorem surfJoinOK : surfN∣commonN ∧ surfJoin.rhs=mulP (natConst surfN) surfGcd ∧
    surfJoin.valid surf0.normal surf1.normal surf2.normal 0 := by decide +kernel
theorem surf11JoinOK : surf11Join.rhs=surfaceBinom 10 ∧ surf11Join.valid surf0.mod11 [] [] 11 := by decide +kernel
theorem surf43JoinOK : surf43Join.rhs=surf43target ∧ surf43Join.valid surf0.mod43 surf1.mod43 [] 43 := by decide +kernel
end RibbonStationaryField
