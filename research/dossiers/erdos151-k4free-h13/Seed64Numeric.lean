import Seed64Cert0
import Seed64Cert1
import Seed64Cert2
import Seed64Cert3
import Seed64Cert4
import Seed64Cert5
import Seed64Cert6
import Seed64Cert7
import Seed64Cert8
import Seed64Cert9
import Seed64Cert10
import Seed64Cert11
import Seed64Cert12
import Seed64Cert13
import Seed64Cert14
import Seed64Cert15
import Seed64Cert16
import Seed64Cert17
import Seed64Cert18
import Seed64Cert19
import Seed64Cert20
import Seed64Cert21
import Seed64Cert22
import Seed64Cert23
import Seed64Cert24
import Seed64Cert25
import Seed64Cert26
import Seed64Cert27
import Seed64Cert28
import Seed64Cert29
import Seed64Cert30
import Seed64Cert31
import Seed64Cert32
import Seed64Cert33
import Seed64Cert34
import Seed64Cert35
import Seed64Cert36
import Seed64Cert37
import Seed64Cert38
import Seed64Cert39
import Seed64Cert40
import Seed64Cert41
import Seed64Cert42
import Seed64Cert43
import Seed64Cert44
import Seed64Cert45
import Seed64Cert46
import Seed64Cert47
import Seed64Cert48
import Seed64Cert49
import Seed64Cert50
import Seed64Cert51
import Seed64Cert52

namespace Erdos151Ramsey.Seed64
set_option maxHeartbeats 0
set_option maxRecDepth 8192
def p10 : Plan := .step 22 p11 p12
theorem c10 : check p10 186360645058573538 11 = true := check_combine (v := 22) (l := p11) (r := p12) (m := 186360645058573538) (k := 11) (by decide +kernel) c11 c12
def p8 : Plan := .step 43 p9 p10
theorem c8 : check p8 186369441151595746 11 = true := check_combine (v := 43) (l := p9) (r := p10) (m := 186369441151595746) (k := 11) (by decide +kernel) c9 c10
def p6 : Plan := .step 56 p7 p8
theorem c6 : check p6 258427035189523682 11 = true := check_combine (v := 56) (l := p7) (r := p8) (m := 258427035189523682) (k := 11) (by decide +kernel) c7 c8
def p4 : Plan := .step 26 p5 p6
theorem c4 : check p4 258427035256632546 11 = true := check_combine (v := 26) (l := p5) (r := p6) (m := 258427035256632546) (k := 11) (by decide +kernel) c5 c6
def p2 : Plan := .step 35 p3 p4
theorem c2 : check p2 258427069616370914 11 = true := check_combine (v := 35) (l := p3) (r := p4) (m := 258427069616370914) (k := 11) (by decide +kernel) c3 c4
def p20 : Plan := .step 5 p21 p22
theorem c20 : check p20 470094188319432930 11 = true := check_combine (v := 5) (l := p21) (r := p22) (m := 470094188319432930) (k := 11) (by decide +kernel) c21 c22
def p18 : Plan := .step 12 p19 p20
theorem c18 : check p18 470094188319437026 11 = true := check_combine (v := 12) (l := p19) (r := p20) (m := 470094188319437026) (k := 11) (by decide +kernel) c19 c20
def p16 : Plan := .step 26 p17 p18
theorem c16 : check p16 470094188386545890 11 = true := check_combine (v := 26) (l := p17) (r := p18) (m := 470094188386545890) (k := 11) (by decide +kernel) c17 c18
def p14 : Plan := .step 20 p15 p16
theorem c14 : check p14 470094188387594466 11 = true := check_combine (v := 20) (l := p15) (r := p16) (m := 470094188387594466) (k := 11) (by decide +kernel) c15 c16
def p28 : Plan := .step 20 p29 p30
theorem c28 : check p28 181857199798120902 11 = true := check_combine (v := 20) (l := p29) (r := p30) (m := 181857199798120902) (k := 11) (by decide +kernel) c29 c30
def p26 : Plan := .step 10 p27 p28
theorem c26 : check p26 181857199798121926 11 = true := check_combine (v := 10) (l := p27) (r := p28) (m := 181857199798121926) (k := 11) (by decide +kernel) c27 c28
def p24 : Plan := .step 16 p25 p26
theorem c24 : check p24 181857199798187462 11 = true := check_combine (v := 16) (l := p25) (r := p26) (m := 181857199798187462) (k := 11) (by decide +kernel) c25 c26
def p34 : Plan := .step 37 p35 p36
theorem c34 : check p34 469084802285400518 11 = true := check_combine (v := 37) (l := p35) (r := p36) (m := 469084802285400518) (k := 11) (by decide +kernel) c35 c36
def p32 : Plan := .step 5 p33 p34
theorem c32 : check p32 469084802285400550 11 = true := check_combine (v := 5) (l := p33) (r := p34) (m := 469084802285400550) (k := 11) (by decide +kernel) c33 c34
def p55 : Plan := .step 28 p56 p57
theorem c55 : check p55 474166746165880228 12 = true := check_combine (v := 28) (l := p56) (r := p57) (m := 474166746165880228) (k := 12) (by decide +kernel) c56 c57
def p53 : Plan := .step 49 p54 p55
theorem c53 : check p53 474729696119301540 12 = true := check_combine (v := 49) (l := p54) (r := p55) (m := 474729696119301540) (k := 12) (by decide +kernel) c54 c55
def p51 : Plan := .step 6 p52 p53
theorem c51 : check p51 474729696119301604 12 = true := check_combine (v := 6) (l := p52) (r := p53) (m := 474729696119301604) (k := 12) (by decide +kernel) c52 c53
def p49 : Plan := .step 12 p50 p51
theorem c49 : check p49 474729696119305700 12 = true := check_combine (v := 12) (l := p50) (r := p51) (m := 474729696119305700) (k := 12) (by decide +kernel) c50 c51
def p47 : Plan := .step 30 p48 p49
theorem c47 : check p47 474729697193047524 12 = true := check_combine (v := 30) (l := p48) (r := p49) (m := 474729697193047524) (k := 12) (by decide +kernel) c48 c49
def p45 : Plan := .step 14 p46 p47
theorem c45 : check p45 474729697193063908 12 = true := check_combine (v := 14) (l := p46) (r := p47) (m := 474729697193063908) (k := 12) (by decide +kernel) c46 c47
def p43 : Plan := .step 20 p44 p45
theorem c43 : check p43 474729697194112484 12 = true := check_combine (v := 20) (l := p44) (r := p45) (m := 474729697194112484) (k := 12) (by decide +kernel) c44 c45
def p41 : Plan := .step 41 p42 p43
theorem c41 : check p41 474731896217368036 12 = true := check_combine (v := 41) (l := p42) (r := p43) (m := 474731896217368036) (k := 12) (by decide +kernel) c42 c43
def p39 : Plan := .step 1 p40 p41
theorem c39 : check p39 474731896217368038 12 = true := check_combine (v := 1) (l := p40) (r := p41) (m := 474731896217368038) (k := 12) (by decide +kernel) c40 c41
def p37 : Plan := .step 22 p38 p39
theorem c37 : check p37 474731896221562342 12 = true := check_combine (v := 22) (l := p38) (r := p39) (m := 474731896221562342) (k := 12) (by decide +kernel) c38 c39
def p31 : Plan := .step 35 p32 p37
theorem c31 : check p31 474731930581300710 12 = true := check_combine (v := 35) (l := p32) (r := p37) (m := 474731930581300710) (k := 12) (by decide +kernel) c32 c37
def p23 : Plan := .step 43 p24 p31
theorem c23 : check p23 474740726674322918 12 = true := check_combine (v := 43) (l := p24) (r := p31) (m := 474740726674322918) (k := 12) (by decide +kernel) c24 c31
def p13 : Plan := .step 56 p14 p23
theorem c13 : check p13 546798320712250854 12 = true := check_combine (v := 56) (l := p14) (r := p23) (m := 546798320712250854) (k := 12) (by decide +kernel) c14 c23
def p1 : Plan := .step 62 p2 p13
theorem c1 : check p1 5158484339139638758 12 = true := check_combine (v := 62) (l := p2) (r := p13) (m := 5158484339139638758) (k := 12) (by decide +kernel) c2 c13
def p64 : Plan := .step 61 p65 p66
theorem c64 : check p64 2530494128456473794 11 = true := check_combine (v := 61) (l := p65) (r := p66) (m := 2530494128456473794) (k := 11) (by decide +kernel) c65 c66
def p62 : Plan := .step 32 p63 p64
theorem c62 : check p62 2530494132751441090 11 = true := check_combine (v := 32) (l := p63) (r := p64) (m := 2530494132751441090) (k := 11) (by decide +kernel) c63 c64
def p60 : Plan := .step 35 p61 p62
theorem c60 : check p60 2530494167111179458 11 = true := check_combine (v := 35) (l := p61) (r := p62) (m := 2530494167111179458) (k := 11) (by decide +kernel) c61 c62
def p70 : Plan := .step 28 p71 p72
theorem c70 : check p70 85022112562896192 11 = true := check_combine (v := 28) (l := p71) (r := p72) (m := 85022112562896192) (k := 11) (by decide +kernel) c71 c72
def p68 : Plan := .step 31 p69 p70
theorem c68 : check p68 85022114710379840 11 = true := check_combine (v := 31) (l := p69) (r := p70) (m := 85022114710379840) (k := 11) (by decide +kernel) c69 c70
def p95 : Plan := .step 6 p96 p97
theorem c95 : check p95 449264993603751238 12 = true := check_combine (v := 6) (l := p96) (r := p97) (m := 449264993603751238) (k := 12) (by decide +kernel) c96 c97
def p93 : Plan := .step 12 p94 p95
theorem c93 : check p93 449264993603755334 12 = true := check_combine (v := 12) (l := p94) (r := p95) (m := 449264993603755334) (k := 12) (by decide +kernel) c94 c95
def p91 : Plan := .step 7 p92 p93
theorem c91 : check p91 449264993603755462 12 = true := check_combine (v := 7) (l := p92) (r := p93) (m := 449264993603755462) (k := 12) (by decide +kernel) c92 c93
def p89 : Plan := .step 14 p90 p91
theorem c89 : check p89 449264993603771846 12 = true := check_combine (v := 14) (l := p90) (r := p91) (m := 449264993603771846) (k := 12) (by decide +kernel) c90 c91
def p87 : Plan := .step 19 p88 p89
theorem c87 : check p87 449264993604296134 12 = true := check_combine (v := 19) (l := p88) (r := p89) (m := 449264993604296134) (k := 12) (by decide +kernel) c88 c89
def p85 : Plan := .step 20 p86 p87
theorem c85 : check p85 449264993605344710 12 = true := check_combine (v := 20) (l := p86) (r := p87) (m := 449264993605344710) (k := 12) (by decide +kernel) c86 c87
def p83 : Plan := .step 40 p84 p85
theorem c83 : check p83 449266093116972486 12 = true := check_combine (v := 40) (l := p84) (r := p85) (m := 449266093116972486) (k := 12) (by decide +kernel) c84 c85
def p81 : Plan := .step 41 p82 p83
theorem c81 : check p81 449268292140228038 12 = true := check_combine (v := 41) (l := p82) (r := p83) (m := 449268292140228038) (k := 12) (by decide +kernel) c82 c83
def p79 : Plan := .step 28 p80 p81
theorem c79 : check p79 449268292408663494 12 = true := check_combine (v := 28) (l := p80) (r := p81) (m := 449268292408663494) (k := 12) (by decide +kernel) c80 c81
def p77 : Plan := .step 35 p78 p79
theorem c77 : check p77 449268326768401862 12 = true := check_combine (v := 35) (l := p78) (r := p79) (m := 449268326768401862) (k := 12) (by decide +kernel) c78 c79
def p75 : Plan := .step 49 p76 p77
theorem c75 : check p75 449831276721823174 12 = true := check_combine (v := 49) (l := p76) (r := p77) (m := 449831276721823174) (k := 12) (by decide +kernel) c76 c77
def p73 : Plan := .step 56 p74 p75
theorem c73 : check p73 521888870759751110 12 = true := check_combine (v := 56) (l := p74) (r := p75) (m := 521888870759751110) (k := 12) (by decide +kernel) c74 c75
def p67 : Plan := .step 61 p68 p73
theorem c67 : check p67 2827731879973445062 12 = true := check_combine (v := 61) (l := p68) (r := p73) (m := 2827731879973445062) (k := 12) (by decide +kernel) c68 c73
def p59 : Plan := .step 62 p60 p67
theorem c59 : check p59 7439417898400832966 12 = true := check_combine (v := 62) (l := p60) (r := p67) (m := 7439417898400832966) (k := 12) (by decide +kernel) c60 c67
def p104 : Plan := .step 40 p105 p106
theorem c104 : check p104 252781048485132514 11 = true := check_combine (v := 40) (l := p105) (r := p106) (m := 252781048485132514) (k := 11) (by decide +kernel) c105 c106
def p102 : Plan := .step 51 p103 p104
theorem c102 : check p102 255032848298817762 11 = true := check_combine (v := 51) (l := p103) (r := p104) (m := 255032848298817762) (k := 11) (by decide +kernel) c103 c104
def p100 : Plan := .step 61 p101 p102
theorem c100 : check p100 2560875857512511714 11 = true := check_combine (v := 61) (l := p101) (r := p102) (m := 2560875857512511714) (k := 11) (by decide +kernel) c101 c102
def p110 : Plan := .step 61 p111 p112
theorem c110 : check p110 2562009442995943618 11 = true := check_combine (v := 61) (l := p111) (r := p112) (m := 2562009442995943618) (k := 11) (by decide +kernel) c111 c112
def p108 : Plan := .step 10 p109 p110
theorem c108 : check p108 2562009442995944642 11 = true := check_combine (v := 10) (l := p109) (r := p110) (m := 2562009442995944642) (k := 11) (by decide +kernel) c109 c110
def p116 : Plan := .step 26 p117 p118
theorem c116 : check p116 2561989112961181922 11 = true := check_combine (v := 26) (l := p117) (r := p118) (m := 2561989112961181922) (k := 11) (by decide +kernel) c117 c118
def p114 : Plan := .step 32 p115 p116
theorem c114 : check p114 2561989117256149218 11 = true := check_combine (v := 32) (l := p115) (r := p116) (m := 2561989117256149218) (k := 11) (by decide +kernel) c115 c116
def p124 : Plan := .step 51 p125 p126
theorem c124 : check p124 2421834367106825312 11 = true := check_combine (v := 51) (l := p125) (r := p126) (m := 2421834367106825312) (k := 11) (by decide +kernel) c125 c126
def p141 : Plan := .step 29 p142 p143
theorem c141 : check p141 186361202395591840 12 = true := check_combine (v := 29) (l := p142) (r := p143) (m := 186361202395591840) (k := 12) (by decide +kernel) c142 c143
def p139 : Plan := .step 6 p140 p141
theorem c139 : check p139 186361202395591904 12 = true := check_combine (v := 6) (l := p140) (r := p141) (m := 186361202395591904) (k := 12) (by decide +kernel) c140 c141
def p137 : Plan := .step 11 p138 p139
theorem c137 : check p137 186361202395593952 12 = true := check_combine (v := 11) (l := p138) (r := p139) (m := 186361202395593952) (k := 12) (by decide +kernel) c138 c139
def p135 : Plan := .step 19 p136 p137
theorem c135 : check p135 186361202396118240 12 = true := check_combine (v := 19) (l := p136) (r := p137) (m := 186361202396118240) (k := 12) (by decide +kernel) c136 c137
def p133 : Plan := .step 40 p134 p135
theorem c133 : check p133 186362301907746016 12 = true := check_combine (v := 40) (l := p134) (r := p135) (m := 186362301907746016) (k := 12) (by decide +kernel) c134 c135
def p131 : Plan := .step 51 p132 p133
theorem c131 : check p131 188614101721431264 12 = true := check_combine (v := 51) (l := p132) (r := p133) (m := 188614101721431264) (k := 12) (by decide +kernel) c132 c133
def p129 : Plan := .step 56 p130 p131
theorem c129 : check p129 260671695759359200 12 = true := check_combine (v := 56) (l := p130) (r := p131) (m := 260671695759359200) (k := 12) (by decide +kernel) c130 c131
def p127 : Plan := .step 61 p128 p129
theorem c127 : check p127 2566514704973053152 12 = true := check_combine (v := 61) (l := p128) (r := p129) (m := 2566514704973053152) (k := 12) (by decide +kernel) c128 c129
def p123 : Plan := .step 32 p124 p127
theorem c123 : check p123 2566514709268020448 12 = true := check_combine (v := 32) (l := p124) (r := p127) (m := 2566514709268020448) (k := 12) (by decide +kernel) c124 c127
def p121 : Plan := .step 1 p122 p123
theorem c121 : check p121 2566514709268020450 12 = true := check_combine (v := 1) (l := p122) (r := p123) (m := 2566514709268020450) (k := 12) (by decide +kernel) c122 c123
def p119 : Plan := .step 22 p120 p121
theorem c119 : check p119 2566514709272214754 12 = true := check_combine (v := 22) (l := p120) (r := p121) (m := 2566514709272214754) (k := 12) (by decide +kernel) c120 c121
def p113 : Plan := .step 27 p114 p119
theorem c113 : check p113 2566514709406432482 12 = true := check_combine (v := 27) (l := p114) (r := p119) (m := 2566514709406432482) (k := 12) (by decide +kernel) c114 c119
def p107 : Plan := .step 43 p108 p113
theorem c107 : check p107 2566523505499454690 12 = true := check_combine (v := 43) (l := p108) (r := p113) (m := 2566523505499454690) (k := 12) (by decide +kernel) c108 c113
def p99 : Plan := .step 35 p100 p107
theorem c99 : check p99 2566523539859193058 12 = true := check_combine (v := 35) (l := p100) (r := p107) (m := 2566523539859193058) (k := 12) (by decide +kernel) c100 c107
def p146 : Plan := .step 61 p147 p148
theorem c146 : check p146 2489959560361046210 11 = true := check_combine (v := 61) (l := p147) (r := p148) (m := 2489959560361046210) (k := 11) (by decide +kernel) c147 c148
def p171 : Plan := .step 22 p172 p173
theorem c171 : check p171 2631268958189742178 12 = true := check_combine (v := 22) (l := p172) (r := p173) (m := 2631268958189742178) (k := 12) (by decide +kernel) c172 c173
def p169 : Plan := .step 43 p170 p171
theorem c169 : check p169 2631277754282764386 12 = true := check_combine (v := 43) (l := p170) (r := p171) (m := 2631277754282764386) (k := 12) (by decide +kernel) c170 c171
def p167 : Plan := .step 51 p168 p169
theorem c167 : check p167 2633529554096449634 12 = true := check_combine (v := 51) (l := p168) (r := p169) (m := 2633529554096449634) (k := 12) (by decide +kernel) c168 c169
def p165 : Plan := .step 57 p166 p167
theorem c165 : check p165 2777644742172305506 12 = true := check_combine (v := 57) (l := p166) (r := p167) (m := 2777644742172305506) (k := 12) (by decide +kernel) c166 c167
def p163 : Plan := .step 12 p164 p165
theorem c163 : check p163 2777644742172309602 12 = true := check_combine (v := 12) (l := p164) (r := p165) (m := 2777644742172309602) (k := 12) (by decide +kernel) c164 c165
def p161 : Plan := .step 23 p162 p163
theorem c161 : check p161 2777644742180698210 12 = true := check_combine (v := 23) (l := p162) (r := p163) (m := 2777644742180698210) (k := 12) (by decide +kernel) c162 c163
def p159 : Plan := .step 33 p160 p161
theorem c159 : check p159 2777644750770632802 12 = true := check_combine (v := 33) (l := p160) (r := p161) (m := 2777644750770632802) (k := 12) (by decide +kernel) c160 c161
def p157 : Plan := .step 44 p158 p159
theorem c157 : check p157 2777662342956677218 12 = true := check_combine (v := 44) (l := p158) (r := p159) (m := 2777662342956677218) (k := 12) (by decide +kernel) c158 c159
def p155 : Plan := .step 7 p156 p157
theorem c155 : check p155 2777662342956677346 12 = true := check_combine (v := 7) (l := p156) (r := p157) (m := 2777662342956677346) (k := 12) (by decide +kernel) c156 c157
def p153 : Plan := .step 26 p154 p155
theorem c153 : check p153 2777662343023786210 12 = true := check_combine (v := 26) (l := p154) (r := p155) (m := 2777662343023786210) (k := 12) (by decide +kernel) c154 c155
def p151 : Plan := .step 28 p152 p153
theorem c151 : check p151 2777662343292221666 12 = true := check_combine (v := 28) (l := p152) (r := p153) (m := 2777662343292221666) (k := 12) (by decide +kernel) c152 c153
def p149 : Plan := .step 49 p150 p151
theorem c149 : check p149 2778225293245642978 12 = true := check_combine (v := 49) (l := p150) (r := p151) (m := 2778225293245642978) (k := 12) (by decide +kernel) c150 c151
def p145 : Plan := .step 20 p146 p149
theorem c145 : check p145 2778225293246691554 12 = true := check_combine (v := 20) (l := p146) (r := p149) (m := 2778225293246691554) (k := 12) (by decide +kernel) c146 c149
def p195 : Plan := .step 12 p196 p197
theorem c195 : check p195 2487260918992090596 12 = true := check_combine (v := 12) (l := p196) (r := p197) (m := 2487260918992090596) (k := 12) (by decide +kernel) c196 c197
def p193 : Plan := .step 14 p194 p195
theorem c193 : check p193 2487260918992106980 12 = true := check_combine (v := 14) (l := p194) (r := p195) (m := 2487260918992106980) (k := 12) (by decide +kernel) c194 c195
def p191 : Plan := .step 27 p192 p193
theorem c191 : check p191 2487260919126324708 12 = true := check_combine (v := 27) (l := p192) (r := p193) (m := 2487260919126324708) (k := 12) (by decide +kernel) c192 c193
def p189 : Plan := .step 33 p190 p191
theorem c189 : check p189 2487260927716259300 12 = true := check_combine (v := 33) (l := p190) (r := p191) (m := 2487260927716259300) (k := 12) (by decide +kernel) c190 c191
def p187 : Plan := .step 43 p188 p189
theorem c187 : check p187 2487269723809281508 12 = true := check_combine (v := 43) (l := p188) (r := p189) (m := 2487269723809281508) (k := 12) (by decide +kernel) c188 c189
def p185 : Plan := .step 51 p186 p187
theorem c185 : check p185 2489521523622966756 12 = true := check_combine (v := 51) (l := p186) (r := p187) (m := 2489521523622966756) (k := 12) (by decide +kernel) c186 c187
def p183 : Plan := .step 35 p184 p185
theorem c183 : check p183 2489521557982705124 12 = true := check_combine (v := 35) (l := p184) (r := p185) (m := 2489521557982705124) (k := 12) (by decide +kernel) c184 c185
def p181 : Plan := .step 16 p182 p183
theorem c181 : check p181 2489521557982770660 12 = true := check_combine (v := 16) (l := p182) (r := p183) (m := 2489521557982770660) (k := 12) (by decide +kernel) c182 c183
def p179 : Plan := .step 23 p180 p181
theorem c179 : check p179 2489521557991159268 12 = true := check_combine (v := 23) (l := p180) (r := p181) (m := 2489521557991159268) (k := 12) (by decide +kernel) c180 c181
def p177 : Plan := .step 44 p178 p179
theorem c177 : check p177 2489539150177203684 12 = true := check_combine (v := 44) (l := p178) (r := p179) (m := 2489539150177203684) (k := 12) (by decide +kernel) c178 c179
def p175 : Plan := .step 22 p176 p177
theorem c175 : check p175 2489539150181397988 12 = true := check_combine (v := 22) (l := p176) (r := p177) (m := 2489539150181397988) (k := 12) (by decide +kernel) c176 c177
def p219 : Plan := .step 11 p220 p221
theorem c219 : check p219 474044154111143204 12 = true := check_combine (v := 11) (l := p220) (r := p221) (m := 474044154111143204) (k := 12) (by decide +kernel) c220 c221
def p217 : Plan := .step 12 p218 p219
theorem c217 : check p217 474044154111147300 12 = true := check_combine (v := 12) (l := p218) (r := p219) (m := 474044154111147300) (k := 12) (by decide +kernel) c218 c219
def p215 : Plan := .step 51 p216 p217
theorem c215 : check p215 476295953924832548 12 = true := check_combine (v := 51) (l := p216) (r := p217) (m := 476295953924832548) (k := 12) (by decide +kernel) c216 c217
def p213 : Plan := .step 1 p214 p215
theorem c213 : check p213 476295953924832550 12 = true := check_combine (v := 1) (l := p214) (r := p215) (m := 476295953924832550) (k := 12) (by decide +kernel) c214 c215
def p211 : Plan := .step 7 p212 p213
theorem c211 : check p211 476295953924832678 12 = true := check_combine (v := 7) (l := p212) (r := p213) (m := 476295953924832678) (k := 12) (by decide +kernel) c212 c213
def p209 : Plan := .step 28 p210 p211
theorem c209 : check p209 476295954193268134 12 = true := check_combine (v := 28) (l := p210) (r := p211) (m := 476295954193268134) (k := 12) (by decide +kernel) c210 c211
def p207 : Plan := .step 14 p208 p209
theorem c207 : check p207 476295954193284518 12 = true := check_combine (v := 14) (l := p208) (r := p209) (m := 476295954193284518) (k := 12) (by decide +kernel) c208 c209
def p205 : Plan := .step 20 p206 p207
theorem c205 : check p205 476295954194333094 12 = true := check_combine (v := 20) (l := p206) (r := p207) (m := 476295954194333094) (k := 12) (by decide +kernel) c206 c207
def p203 : Plan := .step 22 p204 p205
theorem c203 : check p203 476295954198527398 12 = true := check_combine (v := 22) (l := p204) (r := p205) (m := 476295954198527398) (k := 12) (by decide +kernel) c204 c205
def p201 : Plan := .step 33 p202 p203
theorem c201 : check p201 476295962788461990 12 = true := check_combine (v := 33) (l := p202) (r := p203) (m := 476295962788461990) (k := 12) (by decide +kernel) c202 c203
def p199 : Plan := .step 43 p200 p201
theorem c199 : check p199 476304758881484198 12 = true := check_combine (v := 43) (l := p200) (r := p201) (m := 476304758881484198) (k := 12) (by decide +kernel) c200 c201
def p237 : Plan := .step 33 p238 p239
theorem c237 : check p237 2353172774268729670 12 = true := check_combine (v := 33) (l := p238) (r := p239) (m := 2353172774268729670) (k := 12) (by decide +kernel) c238 c239
def p235 : Plan := .step 20 p236 p237
theorem c235 : check p235 2353172774269778246 12 = true := check_combine (v := 20) (l := p236) (r := p237) (m := 2353172774269778246) (k := 12) (by decide +kernel) c236 c237
def p233 : Plan := .step 50 p234 p235
theorem c233 : check p233 2354298674176620870 12 = true := check_combine (v := 50) (l := p234) (r := p235) (m := 2354298674176620870) (k := 12) (by decide +kernel) c234 c235
def p231 : Plan := .step 57 p232 p233
theorem c231 : check p231 2498413862252476742 12 = true := check_combine (v := 57) (l := p232) (r := p233) (m := 2498413862252476742) (k := 12) (by decide +kernel) c232 c233
def p229 : Plan := .step 10 p230 p231
theorem c229 : check p229 2498413862252477766 12 = true := check_combine (v := 10) (l := p230) (r := p231) (m := 2498413862252477766) (k := 12) (by decide +kernel) c230 c231
def p227 : Plan := .step 16 p228 p229
theorem c227 : check p227 2498413862252543302 12 = true := check_combine (v := 16) (l := p228) (r := p229) (m := 2498413862252543302) (k := 12) (by decide +kernel) c228 c229
def p225 : Plan := .step 23 p226 p227
theorem c225 : check p225 2498413862260931910 12 = true := check_combine (v := 23) (l := p226) (r := p227) (m := 2498413862260931910) (k := 12) (by decide +kernel) c226 c227
def p223 : Plan := .step 7 p224 p225
theorem c223 : check p223 2498413862260932038 12 = true := check_combine (v := 7) (l := p224) (r := p225) (m := 2498413862260932038) (k := 12) (by decide +kernel) c224 c225
def p257 : Plan := .step 35 p258 p259
theorem c257 : check p257 482066221473545252 12 = true := check_combine (v := 35) (l := p258) (r := p259) (m := 482066221473545252) (k := 12) (by decide +kernel) c258 c259
def p255 : Plan := .step 41 p256 p257
theorem c255 : check p255 482068420496800804 12 = true := check_combine (v := 41) (l := p256) (r := p257) (m := 482068420496800804) (k := 12) (by decide +kernel) c256 c257
def p253 : Plan := .step 50 p254 p255
theorem c253 : check p253 483194320403643428 12 = true := check_combine (v := 50) (l := p254) (r := p255) (m := 483194320403643428) (k := 12) (by decide +kernel) c254 c255
def p251 : Plan := .step 51 p252 p253
theorem c251 : check p251 485446120217328676 12 = true := check_combine (v := 51) (l := p252) (r := p253) (m := 485446120217328676) (k := 12) (by decide +kernel) c252 c253
def p249 : Plan := .step 1 p250 p251
theorem c249 : check p249 485446120217328678 12 = true := check_combine (v := 1) (l := p250) (r := p251) (m := 485446120217328678) (k := 12) (by decide +kernel) c250 c251
def p247 : Plan := .step 7 p248 p249
theorem c247 : check p247 485446120217328806 12 = true := check_combine (v := 7) (l := p248) (r := p249) (m := 485446120217328806) (k := 12) (by decide +kernel) c248 c249
def p245 : Plan := .step 28 p246 p247
theorem c245 : check p245 485446120485764262 12 = true := check_combine (v := 28) (l := p246) (r := p247) (m := 485446120485764262) (k := 12) (by decide +kernel) c246 c247
def p243 : Plan := .step 22 p244 p245
theorem c243 : check p243 485446120489958566 12 = true := check_combine (v := 22) (l := p244) (r := p245) (m := 485446120489958566) (k := 12) (by decide +kernel) c244 c245
def p241 : Plan := .step 33 p242 p243
theorem c241 : check p241 485446129079893158 12 = true := check_combine (v := 33) (l := p242) (r := p243) (m := 485446129079893158) (k := 12) (by decide +kernel) c242 c243
def p269 : Plan := .step 24 p270 p271
theorem c269 : check p269 2353173751638613318 12 = true := check_combine (v := 24) (l := p270) (r := p271) (m := 2353173751638613318) (k := 12) (by decide +kernel) c270 c271
def p267 : Plan := .step 50 p268 p269
theorem c267 : check p267 2354299651545455942 12 = true := check_combine (v := 50) (l := p268) (r := p269) (m := 2354299651545455942) (k := 12) (by decide +kernel) c268 c269
def p265 : Plan := .step 52 p266 p267
theorem c265 : check p265 2358803251172826438 12 = true := check_combine (v := 52) (l := p266) (r := p267) (m := 2358803251172826438) (k := 12) (by decide +kernel) c266 c267
def p263 : Plan := .step 57 p264 p265
theorem c263 : check p263 2502918439248682310 12 = true := check_combine (v := 57) (l := p264) (r := p265) (m := 2502918439248682310) (k := 12) (by decide +kernel) c264 c265
def p261 : Plan := .step 58 p262 p263
theorem c261 : check p261 2791148815400394054 12 = true := check_combine (v := 58) (l := p262) (r := p263) (m := 2791148815400394054) (k := 12) (by decide +kernel) c262 c263
def p285 : Plan := .step 51 p286 p287
theorem c285 : check p285 2641544955204036962 12 = true := check_combine (v := 51) (l := p286) (r := p287) (m := 2641544955204036962) (k := 12) (by decide +kernel) c286 c287
def p283 : Plan := .step 57 p284 p285
theorem c283 : check p283 2785660143279892834 12 = true := check_combine (v := 57) (l := p284) (r := p285) (m := 2785660143279892834) (k := 12) (by decide +kernel) c284 c285
def p281 : Plan := .step 2 p282 p283
theorem c281 : check p281 2785660143279892838 12 = true := check_combine (v := 2) (l := p282) (r := p283) (m := 2785660143279892838) (k := 12) (by decide +kernel) c282 c283
def p279 : Plan := .step 7 p280 p281
theorem c279 : check p279 2785660143279892966 12 = true := check_combine (v := 7) (l := p280) (r := p281) (m := 2785660143279892966) (k := 12) (by decide +kernel) c280 c281
def p277 : Plan := .step 12 p278 p279
theorem c277 : check p277 2785660143279897062 12 = true := check_combine (v := 12) (l := p278) (r := p279) (m := 2785660143279897062) (k := 12) (by decide +kernel) c278 c279
def p275 : Plan := .step 28 p276 p277
theorem c275 : check p275 2785660143548332518 12 = true := check_combine (v := 28) (l := p276) (r := p277) (m := 2785660143548332518) (k := 12) (by decide +kernel) c276 c277
def p273 : Plan := .step 33 p274 p275
theorem c273 : check p273 2785660152138267110 12 = true := check_combine (v := 33) (l := p274) (r := p275) (m := 2785660152138267110) (k := 12) (by decide +kernel) c274 c275
def p297 : Plan := .step 51 p298 p299
theorem c297 : check p297 2357814198906943714 12 = true := check_combine (v := 51) (l := p298) (r := p299) (m := 2357814198906943714) (k := 12) (by decide +kernel) c298 c299
def p295 : Plan := .step 57 p296 p297
theorem c295 : check p295 2501929386982799586 12 = true := check_combine (v := 57) (l := p296) (r := p297) (m := 2501929386982799586) (k := 12) (by decide +kernel) c296 c297
def p293 : Plan := .step 2 p294 p295
theorem c293 : check p293 2501929386982799590 12 = true := check_combine (v := 2) (l := p294) (r := p295) (m := 2501929386982799590) (k := 12) (by decide +kernel) c294 c295
def p291 : Plan := .step 10 p292 p293
theorem c291 : check p291 2501929386982800614 12 = true := check_combine (v := 10) (l := p292) (r := p293) (m := 2501929386982800614) (k := 12) (by decide +kernel) c292 c293
def p289 : Plan := .step 28 p290 p291
theorem c289 : check p289 2501929387251236070 12 = true := check_combine (v := 28) (l := p290) (r := p291) (m := 2501929387251236070) (k := 12) (by decide +kernel) c290 c291
def p309 : Plan := .step 2 p310 p311
theorem c309 : check p309 2779995871741543908 12 = true := check_combine (v := 2) (l := p310) (r := p311) (m := 2779995871741543908) (k := 12) (by decide +kernel) c310 c311
def p307 : Plan := .step 14 p308 p309
theorem c307 : check p307 2779995871741560292 12 = true := check_combine (v := 14) (l := p308) (r := p309) (m := 2779995871741560292) (k := 12) (by decide +kernel) c308 c309
def p305 : Plan := .step 51 p306 p307
theorem c305 : check p305 2782247671555245540 12 = true := check_combine (v := 51) (l := p306) (r := p307) (m := 2782247671555245540) (k := 12) (by decide +kernel) c306 c307
def p303 : Plan := .step 12 p304 p305
theorem c303 : check p303 2782247671555249636 12 = true := check_combine (v := 12) (l := p304) (r := p305) (m := 2782247671555249636) (k := 12) (by decide +kernel) c304 c305
def p301 : Plan := .step 1 p302 p303
theorem c301 : check p301 2782247671555249638 12 = true := check_combine (v := 1) (l := p302) (r := p303) (m := 2782247671555249638) (k := 12) (by decide +kernel) c302 c303
def p317 : Plan := .step 14 p318 p319
theorem c317 : check p317 438124205095805286 12 = true := check_combine (v := 14) (l := p318) (r := p319) (m := 438124205095805286) (k := 12) (by decide +kernel) c318 c319
def p315 : Plan := .step 51 p316 p317
theorem c315 : check p315 440376004909490534 12 = true := check_combine (v := 51) (l := p316) (r := p317) (m := 440376004909490534) (k := 12) (by decide +kernel) c316 c317
def p313 : Plan := .step 12 p314 p315
theorem c313 : check p313 440376004909494630 12 = true := check_combine (v := 12) (l := p314) (r := p315) (m := 440376004909494630) (k := 12) (by decide +kernel) c314 c315
def p323 : Plan := .step 14 p324 p325
theorem c323 : check p323 2501896397809024356 12 = true := check_combine (v := 14) (l := p324) (r := p325) (m := 2501896397809024356) (k := 12) (by decide +kernel) c324 c325
def p331 : Plan := .step 51 p332 p333
theorem c331 : check p331 2642664812008008032 12 = true := check_combine (v := 51) (l := p332) (r := p333) (m := 2642664812008008032) (k := 12) (by decide +kernel) c332 c333
def p329 : Plan := .step 57 p330 p331
theorem c329 : check p329 2786780000083863904 12 = true := check_combine (v := 57) (l := p330) (r := p331) (m := 2786780000083863904) (k := 12) (by decide +kernel) c330 c331
def p327 : Plan := .step 20 p328 p329
theorem c327 : check p327 2786780000084912480 12 = true := check_combine (v := 20) (l := p328) (r := p329) (m := 2786780000084912480) (k := 12) (by decide +kernel) c328 c329
def p354 : Plan := .step 61 p355 p356
theorem c354 : check p354 2640417410255759712 13 = true := check_combine (v := 61) (l := p355) (r := p356) (m := 2640417410255759712) (k := 13) (by decide +kernel) c355 c356
def p352 : Plan := .step 21 p353 p354
theorem c352 : check p352 2640417410257856864 13 = true := check_combine (v := 21) (l := p353) (r := p354) (m := 2640417410257856864) (k := 13) (by decide +kernel) c353 c354
def p350 : Plan := .step 10 p351 p352
theorem c350 : check p350 2640417410257857888 13 = true := check_combine (v := 10) (l := p351) (r := p352) (m := 2640417410257857888) (k := 13) (by decide +kernel) c351 c352
def p348 : Plan := .step 31 p349 p350
theorem c348 : check p348 2640417412405341536 13 = true := check_combine (v := 31) (l := p349) (r := p350) (m := 2640417412405341536) (k := 13) (by decide +kernel) c349 c350
def p346 : Plan := .step 52 p347 p348
theorem c346 : check p346 2644921012032712032 13 = true := check_combine (v := 52) (l := p347) (r := p348) (m := 2644921012032712032) (k := 13) (by decide +kernel) c347 c348
def p344 : Plan := .step 2 p345 p346
theorem c344 : check p344 2644921012032712036 13 = true := check_combine (v := 2) (l := p345) (r := p346) (m := 2644921012032712036) (k := 13) (by decide +kernel) c345 c346
def p342 : Plan := .step 12 p343 p344
theorem c342 : check p342 2644921012032716132 13 = true := check_combine (v := 12) (l := p343) (r := p344) (m := 2644921012032716132) (k := 13) (by decide +kernel) c343 c344
def p340 : Plan := .step 51 p341 p342
theorem c340 : check p340 2647172811846401380 13 = true := check_combine (v := 51) (l := p341) (r := p342) (m := 2647172811846401380) (k := 13) (by decide +kernel) c341 c342
def p338 : Plan := .step 57 p339 p340
theorem c338 : check p338 2791287999922257252 13 = true := check_combine (v := 57) (l := p339) (r := p340) (m := 2791287999922257252) (k := 13) (by decide +kernel) c339 c340
def p336 : Plan := .step 14 p337 p338
theorem c336 : check p336 2791287999922273636 13 = true := check_combine (v := 14) (l := p337) (r := p338) (m := 2791287999922273636) (k := 13) (by decide +kernel) c337 c338
def p334 : Plan := .step 20 p335 p336
theorem c334 : check p334 2791287999923322212 13 = true := check_combine (v := 20) (l := p335) (r := p336) (m := 2791287999923322212) (k := 13) (by decide +kernel) c335 c336
def p326 : Plan := .step 27 p327 p334
theorem c326 : check p326 2791288000057539940 13 = true := check_combine (v := 27) (l := p327) (r := p334) (m := 2791288000057539940) (k := 13) (by decide +kernel) c327 c334
def p322 : Plan := .step 41 p323 p326
theorem c322 : check p322 2791290199080795492 13 = true := check_combine (v := 41) (l := p323) (r := p326) (m := 2791290199080795492) (k := 13) (by decide +kernel) c323 c326
def p320 : Plan := .step 1 p321 p322
theorem c320 : check p320 2791290199080795494 13 = true := check_combine (v := 1) (l := p321) (r := p322) (m := 2791290199080795494) (k := 13) (by decide +kernel) c321 c322
def p312 : Plan := .step 7 p313 p320
theorem c312 : check p312 2791290199080795622 13 = true := check_combine (v := 7) (l := p313) (r := p320) (m := 2791290199080795622) (k := 13) (by decide +kernel) c313 c320
def p300 : Plan := .step 28 p301 p312
theorem c300 : check p300 2791290199349231078 13 = true := check_combine (v := 28) (l := p301) (r := p312) (m := 2791290199349231078) (k := 13) (by decide +kernel) c301 c312
def p288 : Plan := .step 33 p289 p300
theorem c288 : check p288 2791290207939165670 13 = true := check_combine (v := 33) (l := p289) (r := p300) (m := 2791290207939165670) (k := 13) (by decide +kernel) c289 c300
def p272 : Plan := .step 35 p273 p288
theorem c272 : check p272 2791290242298904038 13 = true := check_combine (v := 35) (l := p273) (r := p288) (m := 2791290242298904038) (k := 13) (by decide +kernel) c273 c288
def p260 : Plan := .step 22 p261 p272
theorem c260 : check p260 2791290242303098342 13 = true := check_combine (v := 22) (l := p261) (r := p272) (m := 2791290242303098342) (k := 13) (by decide +kernel) c261 c272
def p240 : Plan := .step 23 p241 p260
theorem c240 : check p240 2791290242311486950 13 = true := check_combine (v := 23) (l := p241) (r := p260) (m := 2791290242311486950) (k := 13) (by decide +kernel) c241 c260
def p222 : Plan := .step 43 p223 p240
theorem c222 : check p222 2791299038404509158 13 = true := check_combine (v := 43) (l := p223) (r := p240) (m := 2791299038404509158) (k := 13) (by decide +kernel) c223 c240
def p198 : Plan := .step 44 p199 p222
theorem c198 : check p198 2791316630590553574 13 = true := check_combine (v := 44) (l := p199) (r := p222) (m := 2791316630590553574) (k := 13) (by decide +kernel) c199 c222
def p174 : Plan := .step 49 p175 p198
theorem c174 : check p174 2791879580543974886 13 = true := check_combine (v := 49) (l := p175) (r := p198) (m := 2791879580543974886) (k := 13) (by decide +kernel) c175 c198
def p144 : Plan := .step 56 p145 p174
theorem c144 : check p144 2863937174581902822 13 = true := check_combine (v := 56) (l := p145) (r := p174) (m := 2863937174581902822) (k := 13) (by decide +kernel) c145 c174
def p98 : Plan := .step 62 p99 p144
theorem c98 : check p98 7475623193009290726 13 = true := check_combine (v := 62) (l := p99) (r := p144) (m := 7475623193009290726) (k := 13) (by decide +kernel) c99 c144
def p58 : Plan := .step 30 p59 p98
theorem c58 : check p58 7475623194083032550 13 = true := check_combine (v := 30) (l := p59) (r := p98) (m := 7475623194083032550) (k := 13) (by decide +kernel) c59 c98
def p0 : Plan := .step 36 p1 p58
theorem c0 : check p0 7475623262802509286 13 = true := check_combine (v := 36) (l := p1) (r := p58) (m := 7475623262802509286) (k := 13) (by decide +kernel) c1 c58
theorem root_mask : checkRoot = 7475623262802509286 := by decide +kernel
theorem checked_root : check p0 checkRoot 13 = true := by rw [root_mask]; exact c0
end Erdos151Ramsey.Seed64
