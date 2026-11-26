import Ribbon7Chart
namespace Ribbon7
open Ribbon5Bridge
open scoped commutatorElement
variable {G : Type*} [Group G]
set_option maxRecDepth 32000
set_option maxHeartbeats 0

theorem t_0_32 (x y : G) :
    ∃ k : G, (pathAt x y wt 0).2⁻¹*(pathAt x y wt 32).2=k*(R x y)*k⁻¹ := by
  refine ⟨1,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem w_0_32 (x y : G) :
    ∃ k : G, (pathAt x y ww 0).2⁻¹*(pathAt x y ww 32).2=k*(R x y)*k⁻¹ := by
  refine ⟨1,?_⟩
  norm_num [pathAt,run,start,action,ww,R,Z,U,V,commutatorElement_def] <;> group

theorem t_0_64 (x y : G) :
    ∃ k : G, (pathAt x y wt 0).2⁻¹*(pathAt x y wt 64).2=k*(Z x y)*k⁻¹ := by
  refine ⟨1,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem t_32_64 (x y : G) :
    ∃ k : G, (pathAt x y wt 32).2⁻¹*(pathAt x y wt 64).2=k*((R x y)⁻¹ * Z x y)*k⁻¹ := by
  refine ⟨1,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem t_1_33 (x y : G) :
    ∃ k : G, (pathAt x y wt 1).2⁻¹*(pathAt x y wt 33).2=k*(R x y)*k⁻¹ := by
  refine ⟨x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem w_1_33 (x y : G) :
    ∃ k : G, (pathAt x y ww 1).2⁻¹*(pathAt x y ww 33).2=k*(R x y)*k⁻¹ := by
  refine ⟨x,?_⟩
  norm_num [pathAt,run,start,action,ww,R,Z,U,V,commutatorElement_def] <;> group

theorem t_1_65 (x y : G) :
    ∃ k : G, (pathAt x y wt 1).2⁻¹*(pathAt x y wt 65).2=k*(Z x y)*k⁻¹ := by
  refine ⟨x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem t_33_65 (x y : G) :
    ∃ k : G, (pathAt x y wt 33).2⁻¹*(pathAt x y wt 65).2=k*((R x y)⁻¹ * Z x y)*k⁻¹ := by
  refine ⟨x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem t_2_34 (x y : G) :
    ∃ k : G, (pathAt x y wt 2).2⁻¹*(pathAt x y wt 34).2=k*(R x y)*k⁻¹ := by
  refine ⟨x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem w_2_34 (x y : G) :
    ∃ k : G, (pathAt x y ww 2).2⁻¹*(pathAt x y ww 34).2=k*(R x y)*k⁻¹ := by
  refine ⟨x,?_⟩
  norm_num [pathAt,run,start,action,ww,R,Z,U,V,commutatorElement_def] <;> group

theorem t_2_66 (x y : G) :
    ∃ k : G, (pathAt x y wt 2).2⁻¹*(pathAt x y wt 66).2=k*(Z x y)*k⁻¹ := by
  refine ⟨x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem t_34_66 (x y : G) :
    ∃ k : G, (pathAt x y wt 34).2⁻¹*(pathAt x y wt 66).2=k*((R x y)⁻¹ * Z x y)*k⁻¹ := by
  refine ⟨x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem t_3_35 (x y : G) :
    ∃ k : G, (pathAt x y wt 3).2⁻¹*(pathAt x y wt 35).2=k*(R x y)*k⁻¹ := by
  refine ⟨y*x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem w_3_35 (x y : G) :
    ∃ k : G, (pathAt x y ww 3).2⁻¹*(pathAt x y ww 35).2=k*(R x y)*k⁻¹ := by
  refine ⟨y*x,?_⟩
  norm_num [pathAt,run,start,action,ww,R,Z,U,V,commutatorElement_def] <;> group

theorem t_4_36 (x y : G) :
    ∃ k : G, (pathAt x y wt 4).2⁻¹*(pathAt x y wt 36).2=k*(R x y)*k⁻¹ := by
  refine ⟨y*x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem w_4_36 (x y : G) :
    ∃ k : G, (pathAt x y ww 4).2⁻¹*(pathAt x y ww 36).2=k*(R x y)*k⁻¹ := by
  refine ⟨y*x,?_⟩
  norm_num [pathAt,run,start,action,ww,R,Z,U,V,commutatorElement_def] <;> group

theorem t_5_37 (x y : G) :
    ∃ k : G, (pathAt x y wt 5).2⁻¹*(pathAt x y wt 37).2=k*(R x y)*k⁻¹ := by
  refine ⟨x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem w_5_37 (x y : G) :
    ∃ k : G, (pathAt x y ww 5).2⁻¹*(pathAt x y ww 37).2=k*(R x y)*k⁻¹ := by
  refine ⟨x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,ww,R,Z,U,V,commutatorElement_def] <;> group

theorem t_29_61 (x y : G) :
    ∃ k : G, (pathAt x y wt 29).2⁻¹*(pathAt x y wt 61).2=k*((R x y)⁻¹ * Z x y)*k⁻¹ := by
  refine ⟨x⁻¹*y⁻¹*x*y*y*x⁻¹*x⁻¹*y⁻¹*x*x*y⁻¹*x⁻¹*y*x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem w_29_61 (x y : G) :
    ∃ k : G, (pathAt x y ww 29).2⁻¹*(pathAt x y ww 61).2=k*((R x y)⁻¹ * Z x y)*k⁻¹ := by
  refine ⟨x⁻¹*y⁻¹*x*y*y*x⁻¹*x⁻¹*y⁻¹*x*x*y⁻¹*x⁻¹*y*x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,ww,R,Z,U,V,commutatorElement_def] <;> group

theorem t_30_62 (x y : G) :
    ∃ k : G, (pathAt x y wt 30).2⁻¹*(pathAt x y wt 62).2=k*((R x y)⁻¹ * Z x y)*k⁻¹ := by
  refine ⟨y⁻¹*x⁻¹*y⁻¹*x*y*y*x⁻¹*x⁻¹*y⁻¹*x*x*y⁻¹*x⁻¹*y*x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem w_30_62 (x y : G) :
    ∃ k : G, (pathAt x y ww 30).2⁻¹*(pathAt x y ww 62).2=k*((R x y)⁻¹ * Z x y)*k⁻¹ := by
  refine ⟨y⁻¹*x⁻¹*y⁻¹*x*y*y*x⁻¹*x⁻¹*y⁻¹*x*x*y⁻¹*x⁻¹*y*x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,ww,R,Z,U,V,commutatorElement_def] <;> group

theorem t_31_63 (x y : G) :
    ∃ k : G, (pathAt x y wt 31).2⁻¹*(pathAt x y wt 63).2=k*((R x y)⁻¹ * Z x y)*k⁻¹ := by
  refine ⟨y⁻¹*x⁻¹*y⁻¹*x*y*y*x⁻¹*x⁻¹*y⁻¹*x*x*y⁻¹*x⁻¹*y*x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem w_31_63 (x y : G) :
    ∃ k : G, (pathAt x y ww 31).2⁻¹*(pathAt x y ww 63).2=k*((R x y)⁻¹ * Z x y)*k⁻¹ := by
  refine ⟨y⁻¹*x⁻¹*y⁻¹*x*y*y*x⁻¹*x⁻¹*y⁻¹*x*x*y⁻¹*x⁻¹*y*x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,ww,R,Z,U,V,commutatorElement_def] <;> group

theorem t_86_118 (x y : G) :
    ∃ k : G, (pathAt x y wt 86).2⁻¹*(pathAt x y wt 118).2=k*(R x y)*k⁻¹ := by
  refine ⟨y⁻¹*x*y*x⁻¹*x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem t_87_119 (x y : G) :
    ∃ k : G, (pathAt x y wt 87).2⁻¹*(pathAt x y wt 119).2=k*(R x y)*k⁻¹ := by
  refine ⟨x*y⁻¹*x*y*x⁻¹*x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem t_88_120 (x y : G) :
    ∃ k : G, (pathAt x y wt 88).2⁻¹*(pathAt x y wt 120).2=k*(R x y)*k⁻¹ := by
  refine ⟨x*y⁻¹*x*y*x⁻¹*x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem t_89_121 (x y : G) :
    ∃ k : G, (pathAt x y wt 89).2⁻¹*(pathAt x y wt 121).2=k*(R x y)*k⁻¹ := by
  refine ⟨y⁻¹*x*y⁻¹*x*y*x⁻¹*x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem t_90_122 (x y : G) :
    ∃ k : G, (pathAt x y wt 90).2⁻¹*(pathAt x y wt 122).2=k*(R x y)*k⁻¹ := by
  refine ⟨y⁻¹*x*y⁻¹*x*y*x⁻¹*x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem t_91_123 (x y : G) :
    ∃ k : G, (pathAt x y wt 91).2⁻¹*(pathAt x y wt 123).2=k*(R x y)*k⁻¹ := by
  refine ⟨x⁻¹*y⁻¹*x*y⁻¹*x*y*x⁻¹*x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem t_92_124 (x y : G) :
    ∃ k : G, (pathAt x y wt 92).2⁻¹*(pathAt x y wt 124).2=k*(R x y)*k⁻¹ := by
  refine ⟨x⁻¹*x⁻¹*y⁻¹*x*y⁻¹*x*y*x⁻¹*x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem t_93_125 (x y : G) :
    ∃ k : G, (pathAt x y wt 93).2⁻¹*(pathAt x y wt 125).2=k*(R x y)*k⁻¹ := by
  refine ⟨x⁻¹*x⁻¹*y⁻¹*x*y⁻¹*x*y*x⁻¹*x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

theorem t_94_126 (x y : G) :
    ∃ k : G, (pathAt x y wt 94).2⁻¹*(pathAt x y wt 126).2=k*(R x y)*k⁻¹ := by
  refine ⟨y*x⁻¹*x⁻¹*y⁻¹*x*y⁻¹*x*y*x⁻¹*x⁻¹*y*x,?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group

end Ribbon7
