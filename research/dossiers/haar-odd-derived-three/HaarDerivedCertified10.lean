import HaarDerivedKeys00
import HaarDerivedKeys01
import HaarDerivedKeys02
import HaarDerivedKeys03
import HaarDerivedKeys04
import HaarDerivedKeys05
import HaarDerivedKeys06
import HaarDerivedKeys07
import HaarDerivedKeys08
import HaarDerivedKeys09
import HaarDerivedKeys10
import HaarDerivedKeys11
import HaarDerivedKeys12
import HaarDerivedKeys13
import HaarDerivedKeys14
import HaarDerivedKeys15
import HaarDerivedKeys16
import HaarDerivedKeys17
import HaarDerivedKeys18
import HaarDerivedKeys19
import HaarDerivedKeys20
import HaarDerivedKeys21
import HaarDerivedKeys22
import HaarDerivedKeys23
import HaarDerivedKeys24
import HaarDerivedKeys25
import HaarDerivedKeys26
import HaarDerivedKeys27
import HaarDerivedKeys28
import HaarDerivedKeys29
import HaarDerivedKeys30
import HaarDerivedKeys31
import HaarDerivedKeys32
import HaarDerivedKeys33
import HaarDerivedKeys34
import HaarDerivedKeys35
import HaarDerivedKeys36
import HaarDerivedKeys37
import HaarDerivedKeys38
import HaarDerivedKeys39
import HaarDerivedKeys40
import HaarDerivedKeys41
import HaarDerivedKeys42
import HaarDerivedKeys43
import HaarDerivedKeys44
import HaarDerivedKeys45
import HaarDerivedKeys46
import HaarDerivedKeys47
namespace HaarDerivedGirth22
def expected : List (List Nat) := [expected00,expected01,expected02,expected03,expected04,expected05,expected06,expected07,expected08,expected09,expected10,expected11,expected12,expected13,expected14,expected15,expected16,expected17,expected18,expected19,expected20,expected21,expected22,expected23,expected24,expected25,expected26,expected27,expected28,expected29,expected30,expected31,expected32,expected33,expected34,expected35,expected36,expected37,expected38,expected39,expected40,expected41,expected42,expected43,expected44,expected45,expected46,expected47]

set_option maxRecDepth 25000 in
set_option maxHeartbeats 25000000 in
theorem keys_exact : keys10=expected.flatten := by
  have eq : portions 32 48 keys10=expected := by
    apply List.ext_getElem
    · rw [portion_count]; rfl
    · intro n hn hn'
      rw [portion_get]
      have h : n<48 := by simpa [portion_count] using hn
      have ih : ∀ i : Fin 48, (keys10.drop (i.val*32)).take 32 = expected[i.val]'(by change i.val<48; exact i.isLt) := by
        intro i
        fin_cases i
        · exact checked00
        · exact checked01
        · exact checked02
        · exact checked03
        · exact checked04
        · exact checked05
        · exact checked06
        · exact checked07
        · exact checked08
        · exact checked09
        · exact checked10
        · exact checked11
        · exact checked12
        · exact checked13
        · exact checked14
        · exact checked15
        · exact checked16
        · exact checked17
        · exact checked18
        · exact checked19
        · exact checked20
        · exact checked21
        · exact checked22
        · exact checked23
        · exact checked24
        · exact checked25
        · exact checked26
        · exact checked27
        · exact checked28
        · exact checked29
        · exact checked30
        · exact checked31
        · exact checked32
        · exact checked33
        · exact checked34
        · exact checked35
        · exact checked36
        · exact checked37
        · exact checked38
        · exact checked39
        · exact checked40
        · exact checked41
        · exact checked42
        · exact checked43
        · exact checked44
        · exact checked45
        · exact checked46
        · exact checked47
      exact ih ⟨n,h⟩
  exact (portion_flat 32 48 keys10 (by decide +kernel)).symm.trans (congrArg List.flatten eq)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
theorem unique_keys : expected.flatten.Nodup := by
  apply HaarDerivedTrie.nodup 68 .empty
  decide +kernel

theorem cert10 {u v : List (Fin 3)}
    (hu : u ∈ HaarSharpLamp.words 10 none) (hv : v ∈ HaarSharpLamp.words 10 none)
    (he : HaarSharpPortGeometry.value port true u = HaarSharpPortGeometry.value port true v) :
    u.head? = v.head? ∨ u.getLast? = v.getLast? :=
  cert_explicit keys_exact unique_keys hu hv he
#print axioms cert10
end HaarDerivedGirth22
