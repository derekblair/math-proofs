import LinkCoverage
import Lean.Elab.Tactic.Omega

namespace BikovLocal
theorem covered (m : Nat) (hm : m<2048) : check m=true := by
  by_cases h0 : m<64
  · have h : m-0 ∈ List.range 64 := List.mem_range.mpr (by omega)
    have h' := cover0 (m-0) h
    simpa only [show 0+(m-0)=m by omega] using h'
  ·
    by_cases h1 : m<128
    · have h : m-64 ∈ List.range 64 := List.mem_range.mpr (by omega)
      have h' := cover1 (m-64) h
      simpa only [show 64+(m-64)=m by omega] using h'
    ·
      by_cases h2 : m<192
      · have h : m-128 ∈ List.range 64 := List.mem_range.mpr (by omega)
        have h' := cover2 (m-128) h
        simpa only [show 128+(m-128)=m by omega] using h'
      ·
        by_cases h3 : m<256
        · have h : m-192 ∈ List.range 64 := List.mem_range.mpr (by omega)
          have h' := cover3 (m-192) h
          simpa only [show 192+(m-192)=m by omega] using h'
        ·
          by_cases h4 : m<320
          · have h : m-256 ∈ List.range 64 := List.mem_range.mpr (by omega)
            have h' := cover4 (m-256) h
            simpa only [show 256+(m-256)=m by omega] using h'
          ·
            by_cases h5 : m<384
            · have h : m-320 ∈ List.range 64 := List.mem_range.mpr (by omega)
              have h' := cover5 (m-320) h
              simpa only [show 320+(m-320)=m by omega] using h'
            ·
              by_cases h6 : m<448
              · have h : m-384 ∈ List.range 64 := List.mem_range.mpr (by omega)
                have h' := cover6 (m-384) h
                simpa only [show 384+(m-384)=m by omega] using h'
              ·
                by_cases h7 : m<512
                · have h : m-448 ∈ List.range 64 := List.mem_range.mpr (by omega)
                  have h' := cover7 (m-448) h
                  simpa only [show 448+(m-448)=m by omega] using h'
                ·
                  by_cases h8 : m<576
                  · have h : m-512 ∈ List.range 64 := List.mem_range.mpr (by omega)
                    have h' := cover8 (m-512) h
                    simpa only [show 512+(m-512)=m by omega] using h'
                  ·
                    by_cases h9 : m<640
                    · have h : m-576 ∈ List.range 64 := List.mem_range.mpr (by omega)
                      have h' := cover9 (m-576) h
                      simpa only [show 576+(m-576)=m by omega] using h'
                    ·
                      by_cases h10 : m<704
                      · have h : m-640 ∈ List.range 64 := List.mem_range.mpr (by omega)
                        have h' := cover10 (m-640) h
                        simpa only [show 640+(m-640)=m by omega] using h'
                      ·
                        by_cases h11 : m<768
                        · have h : m-704 ∈ List.range 64 := List.mem_range.mpr (by omega)
                          have h' := cover11 (m-704) h
                          simpa only [show 704+(m-704)=m by omega] using h'
                        ·
                          by_cases h12 : m<832
                          · have h : m-768 ∈ List.range 64 := List.mem_range.mpr (by omega)
                            have h' := cover12 (m-768) h
                            simpa only [show 768+(m-768)=m by omega] using h'
                          ·
                            by_cases h13 : m<896
                            · have h : m-832 ∈ List.range 64 := List.mem_range.mpr (by omega)
                              have h' := cover13 (m-832) h
                              simpa only [show 832+(m-832)=m by omega] using h'
                            ·
                              by_cases h14 : m<960
                              · have h : m-896 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                have h' := cover14 (m-896) h
                                simpa only [show 896+(m-896)=m by omega] using h'
                              ·
                                by_cases h15 : m<1024
                                · have h : m-960 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                  have h' := cover15 (m-960) h
                                  simpa only [show 960+(m-960)=m by omega] using h'
                                ·
                                  by_cases h16 : m<1088
                                  · have h : m-1024 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                    have h' := cover16 (m-1024) h
                                    simpa only [show 1024+(m-1024)=m by omega] using h'
                                  ·
                                    by_cases h17 : m<1152
                                    · have h : m-1088 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                      have h' := cover17 (m-1088) h
                                      simpa only [show 1088+(m-1088)=m by omega] using h'
                                    ·
                                      by_cases h18 : m<1216
                                      · have h : m-1152 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                        have h' := cover18 (m-1152) h
                                        simpa only [show 1152+(m-1152)=m by omega] using h'
                                      ·
                                        by_cases h19 : m<1280
                                        · have h : m-1216 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                          have h' := cover19 (m-1216) h
                                          simpa only [show 1216+(m-1216)=m by omega] using h'
                                        ·
                                          by_cases h20 : m<1344
                                          · have h : m-1280 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                            have h' := cover20 (m-1280) h
                                            simpa only [show 1280+(m-1280)=m by omega] using h'
                                          ·
                                            by_cases h21 : m<1408
                                            · have h : m-1344 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                              have h' := cover21 (m-1344) h
                                              simpa only [show 1344+(m-1344)=m by omega] using h'
                                            ·
                                              by_cases h22 : m<1472
                                              · have h : m-1408 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                                have h' := cover22 (m-1408) h
                                                simpa only [show 1408+(m-1408)=m by omega] using h'
                                              ·
                                                by_cases h23 : m<1536
                                                · have h : m-1472 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                                  have h' := cover23 (m-1472) h
                                                  simpa only [show 1472+(m-1472)=m by omega] using h'
                                                ·
                                                  by_cases h24 : m<1600
                                                  · have h : m-1536 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                                    have h' := cover24 (m-1536) h
                                                    simpa only [show 1536+(m-1536)=m by omega] using h'
                                                  ·
                                                    by_cases h25 : m<1664
                                                    · have h : m-1600 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                                      have h' := cover25 (m-1600) h
                                                      simpa only [show 1600+(m-1600)=m by omega] using h'
                                                    ·
                                                      by_cases h26 : m<1728
                                                      · have h : m-1664 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                                        have h' := cover26 (m-1664) h
                                                        simpa only [show 1664+(m-1664)=m by omega] using h'
                                                      ·
                                                        by_cases h27 : m<1792
                                                        · have h : m-1728 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                                          have h' := cover27 (m-1728) h
                                                          simpa only [show 1728+(m-1728)=m by omega] using h'
                                                        ·
                                                          by_cases h28 : m<1856
                                                          · have h : m-1792 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                                            have h' := cover28 (m-1792) h
                                                            simpa only [show 1792+(m-1792)=m by omega] using h'
                                                          ·
                                                            by_cases h29 : m<1920
                                                            · have h : m-1856 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                                              have h' := cover29 (m-1856) h
                                                              simpa only [show 1856+(m-1856)=m by omega] using h'
                                                            ·
                                                              by_cases h30 : m<1984
                                                              · have h : m-1920 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                                                have h' := cover30 (m-1920) h
                                                                simpa only [show 1920+(m-1920)=m by omega] using h'
                                                              ·
                                                                have h : m-1984 ∈ List.range 64 := List.mem_range.mpr (by omega)
                                                                have h' := cover31 (m-1984) h
                                                                simpa only [show 1984+(m-1984)=m by omega] using h'
end BikovLocal

namespace BikovLocal

theorem edge_subset (m u : Nat) (h : m &&& u=m) : ∀ e∈edges m, e∈edges u := by
  intro e he
  simp only [edges,List.mem_append,List.mem_map,List.mem_filter] at he ⊢
  rcases he with he|⟨p,⟨he,bit⟩,ep⟩
  · exact Or.inl he
  · right
    refine ⟨p,⟨he,?_⟩,ep⟩
    have b := congrArg (fun n : Nat=>n.testBit p.2) h
    simpa [Nat.testBit_and,bit] using b

def Extends (es : List E) (lab : E→Bool) (f : Nat→Bool) : Prop :=
  ∀ e∈es, ¬ (f e.1 = lab e ∧ f e.2 = lab e)

lemma short_eq {α} (L : List α) (h : L.length≤1) (a b : α)
    (ha : a∈L) (hb : b∈L) : a=b := by
  cases L with
  | nil => simp at ha
  | cons c L =>
    cases L with
    | nil => simpa using (List.mem_singleton.mp ha).trans (List.mem_singleton.mp hb).symm
    | cons d L => simp at h

/-- A cut with at most one internal edge Extends all edge colorings on all
its subgraphs. Flip every spoke if necessary to avoid its sole bad edge. -/
theorem of_defect (E₀ E₁ : List E) (incl : ∀ e∈E₀,e∈E₁) (s : Nat)
    (small : (defect E₁ s).length≤1) (c : E→Bool) :
    ∃ f : Nat→Bool, Extends E₀ c f := by
  classical
  by_cases bad : ∃ e∈E₀, s.testBit e.1=c e ∧ s.testBit e.2=c e
  · obtain ⟨e,ee,h₁,h₂⟩ := bad
    refine ⟨fun n => !s.testBit n, ?_⟩
    intro a aa fail
    have eeq : s.testBit a.1=s.testBit a.2 := by
      have g := fail.1.trans fail.2.symm
      change (!s.testBit a.1) = (!s.testBit a.2) at g
      cases hA : s.testBit a.1 <;> cases hB : s.testBit a.2 <;> simp_all
    have ae : a∈defect E₁ s := List.mem_filter.mpr ⟨incl a aa,beq_iff_eq.mpr eeq⟩
    have ba : e∈defect E₁ s := List.mem_filter.mpr ⟨incl e ee,beq_iff_eq.mpr (h₁.trans h₂.symm)⟩
    have eq := short_eq _ small a e ae ba
    subst a
    have g := fail.1
    change (!s.testBit e.1)=c e at g
    rw [h₁] at g
    cases hc : c e <;> simp [hc] at g
  · exact ⟨fun n=>s.testBit n,fun e h e' => bad ⟨e,h,e'⟩⟩

theorem c5_bank_extends (m : Nat) (hm : m<2048) (tf : triFree (edges m)=true)
    (c : E→Bool) : ∃ f, Extends (edges m) c f := by
  have h := covered m hm
  simp only [check,tf,Bool.not_true,Bool.false_or] at h
  obtain ⟨⟨u,s⟩,rr,eq⟩ := List.any_eq_true.mp h
  have hh : m &&& u=m := beq_iff_eq.mp eq
  exact of_defect (edges m) (edges u) (edge_subset m u hh) s (rows_cut _ rr) c

theorem c7_extends (c : E→Bool) : ∃ f, Extends c7 c f :=
  of_defect c7 c7 (fun _ h=>h) 21 cycle7_cut c

#print axioms c5_bank_extends
#print axioms c7_extends
end BikovLocal
