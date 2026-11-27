import Eliminate15TreeData7

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 30000
set_option maxHeartbeats 0
def p4089_4097 : PaintTree := .fork 4 (.fork 2 (.fork 1 (.leaf [13355,24824]) (.leaf [20724,26682])) (.fork 1 (.leaf [244,22571]) (.leaf [25654]))) (.fork 2 (.fork 1 (.leaf [14375]) (.leaf [11321])) (.fork 1 (.leaf [19499]) (.leaf [13370])))
def p4097_4106 : PaintTree := .fork 4 (.fork 2 (.fork 1 (.leaf [25660]) (.leaf [28717])) (.fork 1 (.leaf [19510]) (.leaf [28723]))) (.fork 2 (.fork 1 (.leaf [25646]) (.leaf [21550])) (.fork 1 (.leaf [21547]) (.fork 1 (.leaf [26681]) (.leaf [11324]))))
def p4073_4089 : PaintTree := .fork 8 (.fork 4 (.fork 2 (.fork 1 (.leaf [2296,13363]) (.leaf [8434,21557])) (.fork 1 (.leaf [8436,19507]) (.leaf [19502,24817]))) (.fork 2 (.fork 1 (.leaf [10484,13358]) (.leaf [18676,21543])) (.fork 1 (.leaf [24820,25658]) (.leaf [241,22579])))) (.fork 4 (.fork 2 (.fork 1 (.leaf [4338,13351]) (.leaf [2290,14396])) (.fork 1 (.leaf [11310,18673]) (.leaf [18674,25643]))) (.fork 2 (.fork 1 (.leaf [6388,28718]) (.leaf [16626,21562])) (.fork 1 (.leaf [248,28711]) (.leaf [10488,14387]))))
def p4089_4106 : PaintTree := .fork 8 p4089_4097 p4097_4106
def p4041_4073 : PaintTree := .fork 16 p4041_4057 p4057_4073
def p4073_4106 : PaintTree := .fork 16 p4073_4089 p4089_4106
def p3977_4041 : PaintTree := .fork 32 p3977_4009 p4009_4041
def p4041_4106 : PaintTree := .fork 32 p4041_4073 p4073_4106
def p3849_3977 : PaintTree := .fork 64 p3849_3913 p3913_3977
def p3977_4106 : PaintTree := .fork 64 p3977_4041 p4041_4106
def p3592_3849 : PaintTree := .fork 128 p3592_3720 p3720_3849
def p3849_4106 : PaintTree := .fork 128 p3849_3977 p3977_4106
def p3079_3592 : PaintTree := .fork 256 p3079_3335 p3335_3592
def p3592_4106 : PaintTree := .fork 257 p3592_3849 p3849_4106
def p2053_3079 : PaintTree := .fork 513 p2053_2566 p2566_3079
def p3079_4106 : PaintTree := .fork 513 p3079_3592 p3592_4106
def p0_2053 : PaintTree := .fork 1026 p0_1026 p1026_2053
def p2053_4106 : PaintTree := .fork 1026 p2053_3079 p3079_4106
def root : PaintTree := .fork 2053 p0_2053 p2053_4106
end IU.IU15Tree
