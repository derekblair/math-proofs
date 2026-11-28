import AtlasC5_0
import AtlasC5_1
import AtlasC5_2
import AtlasC5_3
import AtlasC5_4
import AtlasC5_5
import AtlasC5_6
import AtlasC5_7
import AtlasC5_8
import AtlasC5_9
import AtlasC5_10
import AtlasC5_11
import AtlasC5_12
import AtlasC5_13
import AtlasC5_14
import AtlasC5_15
import AtlasC5_16
import AtlasC5_17
import AtlasC5_18
import AtlasC5_19
import AtlasC5_20
import AtlasC5_21
import AtlasC5_22
import AtlasC5_23
import AtlasC5_24
import AtlasC5_25
import AtlasC5_26
import AtlasC5_27
import AtlasC5_28
import AtlasC5_29
import AtlasC5_30
import AtlasC5_31
import AtlasC5_32
import AtlasC5_33
import AtlasC5_34
import AtlasC5_35
import AtlasC5_36
import AtlasC5_37
import AtlasC5_38
import AtlasC5_39
import AtlasC5_40
import AtlasC5_41

import AtlasC7

namespace BikovEight
theorem cover5 (h : Nat) (hb : h<10648) (v : valid5 h=true) :
    ∃ s, check (word5 h) s=true := by
  by_cases t21 : h<5376
  ·
    by_cases t10 : h<2560
    ·
      by_cases t5 : h<1280
      ·
        by_cases t2 : h<512
        ·
          by_cases t1 : h<256
          ·
            exact portion0 h (by omega) (by omega) v
          ·
            exact portion1 h (by omega) (by omega) v
        ·
          by_cases t3 : h<768
          ·
            exact portion2 h (by omega) (by omega) v
          ·
            by_cases t4 : h<1024
            ·
              exact portion3 h (by omega) (by omega) v
            ·
              exact portion4 h (by omega) (by omega) v
      ·
        by_cases t7 : h<1792
        ·
          by_cases t6 : h<1536
          ·
            exact portion5 h (by omega) (by omega) v
          ·
            exact portion6 h (by omega) (by omega) v
        ·
          by_cases t8 : h<2048
          ·
            exact portion7 h (by omega) (by omega) v
          ·
            by_cases t9 : h<2304
            ·
              exact portion8 h (by omega) (by omega) v
            ·
              exact portion9 h (by omega) (by omega) v
    ·
      by_cases t15 : h<3840
      ·
        by_cases t12 : h<3072
        ·
          by_cases t11 : h<2816
          ·
            exact portion10 h (by omega) (by omega) v
          ·
            exact portion11 h (by omega) (by omega) v
        ·
          by_cases t13 : h<3328
          ·
            exact portion12 h (by omega) (by omega) v
          ·
            by_cases t14 : h<3584
            ·
              exact portion13 h (by omega) (by omega) v
            ·
              exact portion14 h (by omega) (by omega) v
      ·
        by_cases t18 : h<4608
        ·
          by_cases t16 : h<4096
          ·
            exact portion15 h (by omega) (by omega) v
          ·
            by_cases t17 : h<4352
            ·
              exact portion16 h (by omega) (by omega) v
            ·
              exact portion17 h (by omega) (by omega) v
        ·
          by_cases t19 : h<4864
          ·
            exact portion18 h (by omega) (by omega) v
          ·
            by_cases t20 : h<5120
            ·
              exact portion19 h (by omega) (by omega) v
            ·
              exact portion20 h (by omega) (by omega) v
  ·
    by_cases t31 : h<7936
    ·
      by_cases t26 : h<6656
      ·
        by_cases t23 : h<5888
        ·
          by_cases t22 : h<5632
          ·
            exact portion21 h (by omega) (by omega) v
          ·
            exact portion22 h (by omega) (by omega) v
        ·
          by_cases t24 : h<6144
          ·
            exact portion23 h (by omega) (by omega) v
          ·
            by_cases t25 : h<6400
            ·
              exact portion24 h (by omega) (by omega) v
            ·
              exact portion25 h (by omega) (by omega) v
      ·
        by_cases t28 : h<7168
        ·
          by_cases t27 : h<6912
          ·
            exact portion26 h (by omega) (by omega) v
          ·
            exact portion27 h (by omega) (by omega) v
        ·
          by_cases t29 : h<7424
          ·
            exact portion28 h (by omega) (by omega) v
          ·
            by_cases t30 : h<7680
            ·
              exact portion29 h (by omega) (by omega) v
            ·
              exact portion30 h (by omega) (by omega) v
    ·
      by_cases t36 : h<9216
      ·
        by_cases t33 : h<8448
        ·
          by_cases t32 : h<8192
          ·
            exact portion31 h (by omega) (by omega) v
          ·
            exact portion32 h (by omega) (by omega) v
        ·
          by_cases t34 : h<8704
          ·
            exact portion33 h (by omega) (by omega) v
          ·
            by_cases t35 : h<8960
            ·
              exact portion34 h (by omega) (by omega) v
            ·
              exact portion35 h (by omega) (by omega) v
      ·
        by_cases t39 : h<9984
        ·
          by_cases t37 : h<9472
          ·
            exact portion36 h (by omega) (by omega) v
          ·
            by_cases t38 : h<9728
            ·
              exact portion37 h (by omega) (by omega) v
            ·
              exact portion38 h (by omega) (by omega) v
        ·
          by_cases t40 : h<10240
          ·
            exact portion39 h (by omega) (by omega) v
          ·
            by_cases t41 : h<10496
            ·
              exact portion40 h (by omega) (by omega) v
            ·
              exact portion41 h (by omega) (by omega) v

theorem cover7 (p : Nat) (hb : p<128) (v : good7 p=true) :
    ∃ s, cutCheck (make7 p) s=true := by
  have h := blockC7 p (List.mem_range.mpr hb)
  exact ⟨_,by simpa [v] using h⟩

#print axioms cover5
#print axioms cover7
end BikovEight
