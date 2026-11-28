import New64Cert0
import New64Cert1
import New64Cert2
import New64Cert3
import New64Cert4
import New64Cert5
import New64Cert6
namespace Erdos151Ramsey.New64
set_option maxRecDepth 8192
set_option maxHeartbeats 0
def p9 : Plan := .step 32 p10 p11
theorem c9 : check p9 528769074535419327 12 = true := check_combine (v := 32) (l := p10) (r := p11) (m := 528769074535419327) (k := 12) (by decide +kernel) c10 c11
def p7 : Plan := .step 36 p8 p9
theorem c7 : check p7 528769143254896063 12 = true := check_combine (v := 36) (l := p8) (r := p9) (m := 528769143254896063) (k := 12) (by decide +kernel) c8 c9
def p5 : Plan := .step 43 p6 p7
theorem c5 : check p5 528777939347918271 12 = true := check_combine (v := 43) (l := p6) (r := p7) (m := 528777939347918271) (k := 12) (by decide +kernel) c6 c7
def p3 : Plan := .step 46 p4 p5
theorem c3 : check p3 528848308092095935 12 = true := check_combine (v := 46) (l := p4) (r := p5) (m := 528848308092095935) (k := 12) (by decide +kernel) c4 c5
def p1 : Plan := .step 53 p2 p3
theorem c1 : check p1 537855507346836927 12 = true := check_combine (v := 53) (l := p2) (r := p3) (m := 537855507346836927) (k := 12) (by decide +kernel) c2 c3
def p23 : Plan := .step 51 p24 p25
theorem c23 : check p23 2404557896385647405 12 = true := check_combine (v := 51) (l := p24) (r := p25) (m := 2404557896385647405) (k := 12) (by decide +kernel) c24 c25
def p21 : Plan := .step 1 p22 p23
theorem c21 : check p21 2404557896385647407 12 = true := check_combine (v := 1) (l := p22) (r := p23) (m := 2404557896385647407) (k := 12) (by decide +kernel) c22 c23
def p19 : Plan := .step 11 p20 p21
theorem c19 : check p19 2404557896385649455 12 = true := check_combine (v := 11) (l := p20) (r := p21) (m := 2404557896385649455) (k := 12) (by decide +kernel) c20 c21
def p17 : Plan := .step 30 p18 p19
theorem c17 : check p17 2404557897459391279 12 = true := check_combine (v := 30) (l := p18) (r := p19) (m := 2404557897459391279) (k := 12) (by decide +kernel) c18 c19
def p15 : Plan := .step 32 p16 p17
theorem c15 : check p15 2404557901754358575 12 = true := check_combine (v := 32) (l := p16) (r := p17) (m := 2404557901754358575) (k := 12) (by decide +kernel) c16 c17
def p13 : Plan := .step 53 p14 p15
theorem c13 : check p13 2413565101009099567 12 = true := check_combine (v := 53) (l := p14) (r := p15) (m := 2413565101009099567) (k := 12) (by decide +kernel) c14 c15
def p33 : Plan := .step 18 p34 p35
theorem c33 : check p33 3102677852050410139 12 = true := check_combine (v := 18) (l := p34) (r := p35) (m := 3102677852050410139) (k := 12) (by decide +kernel) c34 c35
def p31 : Plan := .step 29 p32 p33
theorem c31 : check p31 3102677852587281051 12 = true := check_combine (v := 29) (l := p32) (r := p33) (m := 3102677852587281051) (k := 12) (by decide +kernel) c32 c33
def p29 : Plan := .step 37 p30 p31
theorem c29 : check p29 3102677990026234523 12 = true := check_combine (v := 37) (l := p30) (r := p31) (m := 3102677990026234523) (k := 12) (by decide +kernel) c30 c31
def p27 : Plan := .step 39 p28 p29
theorem c27 : check p27 3102678539782048411 12 = true := check_combine (v := 39) (l := p28) (r := p29) (m := 3102678539782048411) (k := 12) (by decide +kernel) c28 c29
def p37 : Plan := .step 25 p38 p39
theorem c37 : check p37 2544812733227851035 12 = true := check_combine (v := 25) (l := p38) (r := p39) (m := 2544812733227851035) (k := 12) (by decide +kernel) c38 c39
def p41 : Plan := .step 25 p42 p43
theorem c41 : check p41 77401477018410943 12 = true := check_combine (v := 25) (l := p42) (r := p43) (m := 77401477018410943) (k := 12) (by decide +kernel) c42 c43
def p45 : Plan := .step 23 p46 p47
theorem c45 : check p45 2398374660638334911 12 = true := check_combine (v := 23) (l := p46) (r := p47) (m := 2398374660638334911) (k := 12) (by decide +kernel) c46 c47
def p74 : Plan := .step 57 p75 p76
theorem c74 : check p74 3119496299694185131 13 = true := check_combine (v := 57) (l := p75) (r := p76) (m := 3119496299694185131) (k := 13) (by decide +kernel) c75 c76
def p72 : Plan := .step 4 p73 p74
theorem c72 : check p72 3119496299694185147 13 = true := check_combine (v := 4) (l := p73) (r := p74) (m := 3119496299694185147) (k := 13) (by decide +kernel) c73 c74
def p70 : Plan := .step 10 p71 p72
theorem c70 : check p70 3119496299694186171 13 = true := check_combine (v := 10) (l := p71) (r := p72) (m := 3119496299694186171) (k := 13) (by decide +kernel) c71 c72
def p68 : Plan := .step 31 p69 p70
theorem c68 : check p68 3119496301841669819 13 = true := check_combine (v := 31) (l := p69) (r := p70) (m := 3119496301841669819) (k := 13) (by decide +kernel) c69 c70
def p66 : Plan := .step 2 p67 p68
theorem c66 : check p66 3119496301841669823 13 = true := check_combine (v := 2) (l := p67) (r := p68) (m := 3119496301841669823) (k := 13) (by decide +kernel) c67 c68
def p64 : Plan := .step 8 p65 p66
theorem c64 : check p64 3119496301841670079 13 = true := check_combine (v := 8) (l := p65) (r := p66) (m := 3119496301841670079) (k := 13) (by decide +kernel) c65 c66
def p62 : Plan := .step 25 p63 p64
theorem c62 : check p62 3119496301875224511 13 = true := check_combine (v := 25) (l := p63) (r := p64) (m := 3119496301875224511) (k := 13) (by decide +kernel) c63 c64
def p60 : Plan := .step 44 p61 p62
theorem c60 : check p60 3119513894061268927 13 = true := check_combine (v := 44) (l := p61) (r := p62) (m := 3119513894061268927) (k := 13) (by decide +kernel) c61 c62
def p58 : Plan := .step 46 p59 p60
theorem c58 : check p58 3119584262805446591 13 = true := check_combine (v := 46) (l := p59) (r := p60) (m := 3119584262805446591) (k := 13) (by decide +kernel) c59 c60
def p56 : Plan := .step 52 p57 p58
theorem c56 : check p56 3124087862432817087 13 = true := check_combine (v := 52) (l := p57) (r := p58) (m := 3124087862432817087) (k := 13) (by decide +kernel) c57 c58
def p54 : Plan := .step 16 p55 p56
theorem c54 : check p54 3124087862432882623 13 = true := check_combine (v := 16) (l := p55) (r := p56) (m := 3124087862432882623) (k := 13) (by decide +kernel) c55 c56
def p52 : Plan := .step 18 p53 p54
theorem c52 : check p52 3124087862433144767 13 = true := check_combine (v := 18) (l := p53) (r := p54) (m := 3124087862433144767) (k := 13) (by decide +kernel) c53 c54
def p50 : Plan := .step 23 p51 p52
theorem c50 : check p50 3124087862441533375 13 = true := check_combine (v := 23) (l := p51) (r := p52) (m := 3124087862441533375) (k := 13) (by decide +kernel) c51 c52
def p48 : Plan := .step 29 p49 p50
theorem c48 : check p48 3124087862978404287 13 = true := check_combine (v := 29) (l := p49) (r := p50) (m := 3124087862978404287) (k := 13) (by decide +kernel) c49 c50
def p44 : Plan := .step 37 p45 p48
theorem c44 : check p44 3124088000417357759 13 = true := check_combine (v := 37) (l := p45) (r := p48) (m := 3124088000417357759) (k := 13) (by decide +kernel) c45 c48
def p40 : Plan := .step 39 p41 p44
theorem c40 : check p40 3124088550173171647 13 = true := check_combine (v := 39) (l := p41) (r := p44) (m := 3124088550173171647) (k := 13) (by decide +kernel) c41 c44
def p36 : Plan := .step 50 p37 p40
theorem c36 : check p36 3125214450080014271 13 = true := check_combine (v := 50) (l := p37) (r := p40) (m := 3125214450080014271) (k := 13) (by decide +kernel) c37 c40
def p26 : Plan := .step 53 p27 p36
theorem c26 : check p26 3134221649334755263 13 = true := check_combine (v := 53) (l := p27) (r := p36) (m := 3134221649334755263) (k := 13) (by decide +kernel) c27 c36
def p12 : Plan := .step 58 p13 p26
theorem c12 : check p12 3422452025486467007 13 = true := check_combine (v := 58) (l := p13) (r := p26) (m := 3422452025486467007) (k := 13) (by decide +kernel) c13 c26
def p0 : Plan := .step 60 p1 p12
theorem c0 : check p0 4575373530093313983 13 = true := check_combine (v := 60) (l := p1) (r := p12) (m := 4575373530093313983) (k := 13) (by decide +kernel) c1 c12
theorem root_mask : checkRoot = 4575373530093313983 := by decide +kernel
theorem checked_root : check p0 checkRoot 13 = true := by rw [root_mask]; exact c0
end Erdos151Ramsey.New64
