import Mathlib.Tactic

namespace TwoPencilChart

abbrev P := ℚ × ℚ

def det (a b c : P) : ℚ :=
  (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)

def scale (u : P) : ℚ := 1+u.1+u.2

/-- A change of projective chart taking the two pencil viewpoints to
(0,1) and (1,0). -/
def chart (u : P) : P := (u.1/scale u,u.2/scale u)

theorem detects_row (u v : P) (hu : scale u ≠ 0) (hv : scale v ≠ 0) :
    det (0,1) (chart u) (chart v) * (scale u * scale v) = v.1-u.1 := by
  simp only [det, chart, sub_zero]
  field_simp [hu,hv]
  dsimp [scale]
  ring

theorem detects_column (u v : P) (hu : scale u ≠ 0) (hv : scale v ≠ 0) :
    det (1,0) (chart u) (chart v) * (scale u * scale v) = u.2-v.2 := by
  simp only [det, chart, sub_zero]
  field_simp [hu,hv]
  dsimp [scale]
  ring

theorem preserves_three (u v w : P)
    (hu : scale u ≠ 0) (hv : scale v ≠ 0) (hw : scale w ≠ 0) :
    det (chart u) (chart v) (chart w) * (scale u * scale v * scale w) = det u v w := by
  simp only [det, chart]
  field_simp [hu,hv,hw]
  dsimp [scale]
  ring

theorem separates_anchors (u : P) (hu : scale u ≠ 0) :
    det (0,1) (1,0) (chart u) * scale u = -1 := by
  simp only [det, chart, sub_zero]
  field_simp [hu]
  dsimp [scale]
  ring

end TwoPencilChart

#print axioms TwoPencilChart.preserves_three
