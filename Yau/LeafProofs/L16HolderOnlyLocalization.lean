import Yau.LeafProofs.L16HolderOnlyEstimates

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def holderOnlyExteriorRate (n : ℕ) (α CH M N T E0 E1 E2 : ℝ) : ℝ :=
  lowerCutoffBudget n M E0 E1 E2*(CH*N*(T^(1/2:ℝ)+T^((1-α)/2)))

theorem exteriorHeatResidual_holder_only_refined_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ P CH : ℝ, 0 < P ∧ 0 < CH ∧
      ∀ (s : Finset (Space n)) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) →
      ∃ E0 E1 E2 : ℝ, 0 < E0 ∧ 0 < E1 ∧ 0 < E2 ∧
      ∀ (K : Set (Space n)) (T F S M N : ℝ) (a : Point n → Mat n)
        (b : Point n → Yau.RIdx n → ℝ) (B : Space n ≃L[ℝ] Space n) (f : Point n → ℝ),
      0 < T → T ≤ 1 → constantHeatNormFactor α B ≤ N →
      (∀ x ∈ K, 1 ≤ patchSum s r hr x) →
      HolderBound α (cylinder Set.univ 0 T) a M →
      (∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M) →
      (∀ p ∈ cylinder Set.univ 0 T, p.1 ∉ K → a p = 1) →
      HolderBound α (cylinder Set.univ 0 T) f F → 0 ≤ S →
      (∀ p ∈ cylinder Set.univ 0 T, |f p| ≤ S) →
      HolderBound α (cylinder Set.univ 0 T)
        (frozenPatchResidual (cylinder Set.univ 0 T) a b 1 (exteriorCutoff s r hr)
          (constantHeatDuhamel B (fun p => exteriorSourceCutoff s r hr p.1*f p)))
        (holderOnlyExteriorRate n α CH M N T E0 E1 E2*(F+(P*r⁻¹*r^(1-α))*S)) := by
  obtain ⟨P,hP,hSource⟩ := source_cutoffs_uniform_refined_holderBound (n := n) hα hα1
  obtain ⟨CH,hCH,hHeat⟩ := constantHeatDuhamel_controlled_bounds (n := n) hα hα1
  refine ⟨P,CH,hP,hCH,?_⟩
  intro s r hr hr1 hSep
  obtain ⟨E0,E1,E2,hE0,hE1,hE2,hφ0,hφD0,hφDD0⟩ := exteriorCutoff_holder_jets hα hα1 s hr
  refine ⟨E0,E1,E2,hE0,hE1,hE2,?_⟩
  intro K T F S M N a b B f hT hT1 hN hCover ha hb hExterior hf hS hSup
  let W : ℝ := F+(P*r⁻¹*r^(1-α))*S
  let G : ℝ := CH*N
  let w : Point n → ℝ := fun p => exteriorSourceCutoff s r hr p.1*f p
  let u : Point n → ℝ := constantHeatDuhamel B w
  have hWeighted : HolderBound α (cylinder Set.univ 0 T) w W :=
    (hSource s r hr hr1 hSep T F S f hf hS hSup).2
  have hHeatBounds := hHeat N B hN T W hT hT1 w hWeighted
  have hHeatScale : CH*W*N = G*W := by dsimp only [G]; ring
  rw [hHeatScale] at hHeatBounds
  have hφ := holderBound_mono hφ0 (cylinder_mono_time hT1)
  have hφD := holderBound_mono hφD0 (cylinder_mono_time hT1)
  have hφDD := holderBound_mono hφDD0 (cylinder_mono_time hT1)
  have hLower := lowerPatchResidual_holderBound ha hb hφ
    (fun i => holderBound_gradient_component hφD i)
    (fun i j => holderBound_hessian_component hφDD i j) hHeatBounds.2.2
  have hResidual := holderBound_congr_on (holderBound_neg hLower) (show
      Set.EqOn (fun p => -lowerPatchResidual a b (exteriorCutoff s r hr) u p)
        (frozenPatchResidual (cylinder Set.univ 0 T) a b 1 (exteriorCutoff s r hr) u)
        (cylinder Set.univ 0 T) from by
    intro p hp
    exact (exterior_frozenPatchResidual_eq_neg_lower b s hr hCover hExterior u hp).symm)
  change HolderBound α (cylinder Set.univ 0 T)
    (frozenPatchResidual (cylinder Set.univ 0 T) a b 1 (exteriorCutoff s r hr) u) _
  convert hResidual using 1
  dsimp only [holderOnlyExteriorRate,lowerCutoffBudget,G,W]
  ring

theorem frozenPatchResidual_outer_sum_sup_bound {n : ℕ} {H : ℝ}
    {Q : Set (Point n)} (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (A : Space n → Mat n) (v : Space n → Point n → ℝ)
    {r : ℝ} (hr : 0 < r) (s : Finset (Space n))
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) (hH : 0 ≤ H)
    (hResidual : ∀ c ∈ s, ∀ p ∈ Q,
      |frozenPatchResidual Q a b (A c) (outerPatchBump r hr c) (v c) p| ≤ H)
    {p : Point n} (hp : p ∈ Q) :
    |∑ c ∈ s, frozenPatchResidual Q a b (A c) (outerPatchBump r hr c) (v c) p| ≤
      ((5^(Module.finrank ℝ (Space n)) : ℕ) : ℝ)*H := by
  classical
  let f : Space n → ℝ := fun c =>
    frozenPatchResidual Q a b (A c) (outerPatchBump r hr c) (v c) p
  let sp := s.filter (fun c => f c ≠ 0)
  have hcard : sp.card ≤ 5^(Module.finrank ℝ (Space n)) := by
    apply (Finset.card_le_card (show sp ⊆ s.filter (fun c => ‖c-p.1‖ ≤ 2*r) from ?_)).trans
      (separated_centers_overlap_bound hr s hSep p.1)
    intro c hc
    obtain ⟨hcs,hNonzero⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨hcs,?_⟩
    rw [norm_sub_rev]
    by_contra hNorm
    exact hNonzero (frozenPatchResidual_outer_zero_of_norm_gt Q a b (A c) hr c (v c)
      (lt_of_not_ge hNorm))
  have hcardReal : (sp.card : ℝ) ≤ ((5^(Module.finrank ℝ (Space n)) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have heq : (∑ c ∈ sp, f c) = ∑ c ∈ s, f c := Finset.sum_filter_ne_zero s
  change |∑ c ∈ s, f c| ≤ _
  calc
    _ = |∑ c ∈ sp, f c| := congrArg abs heq.symm
    _ ≤ ∑ c ∈ sp, |f c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ sp, H := Finset.sum_le_sum (fun c hc =>
      hResidual c (Finset.mem_filter.mp hc).1 p hp)
    _ = (sp.card : ℝ)*H := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcardReal hH

def holderOnlyTotalHolderRate (n : ℕ)
    (α Cφ CHI CHE M N r T E0 E1 E2 : ℝ) : ℝ :=
  2*((5^(Module.finrank ℝ (Space n)) : ℕ) : ℝ)*
    holderOnlyInteriorHolderRate n α Cφ CHI M N r T+
      holderOnlyExteriorRate n α CHE M N T E0 E1 E2

def holderOnlyTotalSupRate (n : ℕ)
    (α Cφ CHI CHE M N r T E0 E1 E2 : ℝ) : ℝ :=
  ((5^(Module.finrank ℝ (Space n)) : ℕ) : ℝ)*
    holderOnlyInteriorSupRate n α Cφ CHI M N r T+
      holderOnlyExteriorRate n α CHE M N T E0 E1 E2

/-- Both estimates concern the actual finite localized heat error. The Holder
    estimate uses dimension-only overlap before the radius is selected. -/
theorem localizedHeatResidual_holder_only_refined_bounds {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ PI PE Cφ CHI CHE : ℝ, 0 < PI ∧ 0 < PE ∧ 0 < Cφ ∧ 0 < CHI ∧ 0 < CHE ∧
      ∀ (s : Finset (Space n)) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) →
      ∃ E0 E1 E2 : ℝ, 0 < E0 ∧ 0 < E1 ∧ 0 < E2 ∧
      ∀ (K : Set (Space n)) (T F S M N : ℝ) (a : Point n → Mat n)
        (b : Point n → Yau.RIdx n → ℝ) (B : Space n → Space n ≃L[ℝ] Space n)
        (Bext : Space n ≃L[ℝ] Space n) (f : Point n → ℝ),
      0 < T → T ≤ 1 →
      (∀ x ∈ K, 1 ≤ patchSum s r hr x) →
      HolderBound α (cylinder Set.univ 0 T) a M →
      (∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M) →
      (∀ p ∈ cylinder Set.univ 0 T, p.1 ∉ K → a p = 1) →
      (∀ c, constantHeatNormFactor α (B c) ≤ N) →
      constantHeatNormFactor α Bext ≤ N →
      HolderBound α (cylinder Set.univ 0 T) f F → 0 ≤ S →
      (∀ p ∈ cylinder Set.univ 0 T, |f p| ≤ S) →
      HolderBound α (cylinder Set.univ 0 T)
        (localizedHeatResidual T s r hr B Bext a b f)
        (holderOnlyTotalHolderRate n α Cφ CHI CHE M N r T E0 E1 E2*
          (F+((PI+PE)*r⁻¹*r^(1-α))*S)) ∧
      (∀ p ∈ cylinder Set.univ 0 T,
        |localizedHeatResidual T s r hr B Bext a b f p| ≤
        holderOnlyTotalSupRate n α Cφ CHI CHE M N r T E0 E1 E2*
          (F+((PI+PE)*r⁻¹*r^(1-α))*S)) := by
  obtain ⟨PI,Cφ,CHI,hPI,hCφ,hCHI,hInterior⟩ :=
    interiorHeatResidual_holder_only_refined_bounds (n := n) hα hα1
  obtain ⟨PE,CHE,hPE,hCHE,hExterior⟩ :=
    exteriorHeatResidual_holder_only_refined_bound (n := n) hα hα1
  refine ⟨PI,PE,Cφ,CHI,CHE,hPI,hPE,hCφ,hCHI,hCHE,?_⟩
  intro s r hr hr1 hSep
  obtain ⟨E0,E1,E2,hE0,hE1,hE2,hExt⟩ := hExterior s r hr hr1 hSep
  refine ⟨E0,E1,E2,hE0,hE1,hE2,?_⟩
  intro K T F S M N a b B Bext f hT hT1 hCover ha hb hExteriorCoeff hB hBext hf hS hSup
  let W : ℝ := F+((PI+PE)*r⁻¹*r^(1-α))*S
  let AI := holderOnlyInteriorHolderRate n α Cφ CHI M N r T
  let BI := holderOnlyInteriorSupRate n α Cφ CHI M N r T
  let AE := holderOnlyExteriorRate n α CHE M N T E0 E1 E2
  have hF : 0 ≤ F := hf.1
  have hM : 0 ≤ M := ha.1
  have hN : 0 ≤ N := (constantHeatNormFactor_pos α Bext).le.trans hBext
  have hAI : 0 ≤ AI := by
    dsimp only [AI,holderOnlyInteriorHolderRate,lowerCutoffBudget,cutoffJetBudget]
    positivity
  have hBI : 0 ≤ BI := by
    dsimp only [BI,holderOnlyInteriorSupRate,lowerCutoffBudget,cutoffJetBudget]
    positivity
  have hAE : 0 ≤ AE := by
    dsimp only [AE,holderOnlyExteriorRate,lowerCutoffBudget]
    positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hCmpI : F+(PI*r⁻¹*r^(1-α))*S ≤ W := by
    dsimp only [W]
    have hExtra : 0 ≤ PE*r⁻¹*r^(1-α)*S := by positivity
    nlinarith
  have hCmpE : F+(PE*r⁻¹*r^(1-α))*S ≤ W := by
    dsimp only [W]
    have hExtra : 0 ≤ PI*r⁻¹*r^(1-α)*S := by positivity
    nlinarith
  have hIntRaw (c : Space n) (hc : c ∈ s) :=
    hInterior s r hr hr1 hSep T F S M N a b (B c) c f hc hT hT1 (hB c) ha hb hf hS hSup
  have hExtRaw := hExt K T F S M N a b Bext f hT hT1 hBext hCover ha hb hExteriorCoeff hf hS hSup
  have hInt (c : Space n) (hc : c ∈ s) : HolderBound α (cylinder Set.univ 0 T)
      (frozenPatchResidual (cylinder Set.univ 0 T) a b (a (c,0)) (outerPatchBump r hr c)
        (constantHeatDuhamel (B c) (fun p => normalizedPatchCutoff s r hr c p.1*f p))) (AI*W) :=
    holderBound_mono_const (hIntRaw c hc).1 (mul_le_mul_of_nonneg_left hCmpI hAI)
  have hExt := holderBound_mono_const hExtRaw (mul_le_mul_of_nonneg_left hCmpE hAE)
  constructor
  · have hIntSum := frozenPatchResidual_outer_sum_holderBound a b (fun c => a (c,0))
      (fun c => constantHeatDuhamel (B c) (fun q => normalizedPatchCutoff s r hr c q.1*f q))
      hr s hSep (mul_nonneg hAI hW) hInt
    have hTotal := holderBound_add hIntSum hExt
    change HolderBound α (cylinder Set.univ 0 T)
      (localizedHeatResidual T s r hr B Bext a b f) _ at hTotal
    convert hTotal using 1
    dsimp only [holderOnlyTotalHolderRate,AI,AE]
    ring
  · intro p hp
    have hIntSup (c : Space n) (hc : c ∈ s) (q : Point n)
        (hq : q ∈ cylinder Set.univ 0 T) :
        |frozenPatchResidual (cylinder Set.univ 0 T) a b (a (c,0)) (outerPatchBump r hr c)
          (constantHeatDuhamel (B c) (fun z => normalizedPatchCutoff s r hr c z.1*f z)) q| ≤ BI*W :=
      ((hIntRaw c hc).2 q hq).trans (mul_le_mul_of_nonneg_left hCmpI hBI)
    have hIntSum := frozenPatchResidual_outer_sum_sup_bound a b (fun c => a (c,0))
      (fun c => constantHeatDuhamel (B c) (fun q => normalizedPatchCutoff s r hr c q.1*f q))
      hr s hSep (mul_nonneg hBI hW) hIntSup hp
    have hExtSup := hExt.2.1 p hp
    have hTotal := (abs_add_le _ _).trans (add_le_add hIntSum hExtSup)
    change |localizedHeatResidual T s r hr B Bext a b f p| ≤ _ at hTotal
    convert hTotal using 1
    dsimp only [holderOnlyTotalSupRate,BI,AE]
    ring

theorem holderOnlyExteriorRate_zero (n : ℕ) {α : ℝ}
    (hα1 : α < 1) (CH M N E0 E1 E2 : ℝ) :
    holderOnlyExteriorRate n α CH M N 0 E0 E1 E2 = 0 := by
  simp only [holderOnlyExteriorRate,Real.zero_rpow (by norm_num : (1/2 : ℝ) ≠ 0),
    Real.zero_rpow (by linarith : (1-α)/2 ≠ 0),add_zero,mul_zero]

theorem holderOnlyExteriorRate_continuous (n : ℕ) {α : ℝ}
    (hα1 : α ≤ 1) (CH M N E0 E1 E2 : ℝ) :
    Continuous (fun T => holderOnlyExteriorRate n α CH M N T E0 E1 E2) := by
  have hB : Continuous (fun T : ℝ => T^(1/2 : ℝ)) := Real.continuous_rpow_const (by positivity)
  have hC : Continuous (fun T : ℝ => T^((1-α)/2)) := Real.continuous_rpow_const (by linarith)
  dsimp only [holderOnlyExteriorRate]
  fun_prop

theorem holderOnlyTotalHolderRate_zero (n : ℕ) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (Cφ CHI CHE M N r E0 E1 E2 : ℝ) :
    holderOnlyTotalHolderRate n α Cφ CHI CHE M N r 0 E0 E1 E2 =
      2*((5^(Module.finrank ℝ (Space n)) : ℕ) : ℝ)*
        CHI*N*(Fintype.card (Yau.RIdx n) : ℝ)^2*M*(2*r)^α := by
  rw [holderOnlyTotalHolderRate,holderOnlyInteriorHolderRate_zero n hα hα1,
    holderOnlyExteriorRate_zero n hα1]
  ring

theorem holderOnlyTotalSupRate_zero (n : ℕ) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (Cφ CHI CHE M N r E0 E1 E2 : ℝ) :
    holderOnlyTotalSupRate n α Cφ CHI CHE M N r 0 E0 E1 E2 = 0 := by
  rw [holderOnlyTotalSupRate,holderOnlyInteriorSupRate_zero n hα hα1,
    holderOnlyExteriorRate_zero n hα1,mul_zero,zero_add]

theorem holderOnlyTotalHolderRate_continuous (n : ℕ) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (Cφ CHI CHE M N r E0 E1 E2 : ℝ) :
    Continuous (fun T => holderOnlyTotalHolderRate n α Cφ CHI CHE M N r T E0 E1 E2) := by
  exact (continuous_const.mul
    (holderOnlyInteriorHolderRate_continuous n hα hα1 Cφ CHI M N r)).add
      (holderOnlyExteriorRate_continuous n hα1 CHE M N E0 E1 E2)

theorem holderOnlyTotalSupRate_continuous (n : ℕ) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (Cφ CHI CHE M N r E0 E1 E2 : ℝ) :
    Continuous (fun T => holderOnlyTotalSupRate n α Cφ CHI CHE M N r T E0 E1 E2) := by
  exact (continuous_const.mul
    (holderOnlyInteriorSupRate_continuous n hα hα1 Cφ CHI M N r)).add
      (holderOnlyExteriorRate_continuous n hα1 CHE M N E0 E1 E2)

/-- The radius is selected before the finite exterior budgets. The weight is
    finite at that radius, and only then is the short time interval chosen. -/
theorem exists_holder_only_localization_scales (n : ℕ) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (PI PE Cφ CHI CHE M N : ℝ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ E0 E1 E2 : ℝ,
      ∃ β δ : ℝ, 0 < β ∧ (PI+PE)*r⁻¹*r^(1-α) ≤ β ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ T : ℝ, 0 ≤ T → T ≤ δ →
        holderOnlyTotalHolderRate n α Cφ CHI CHE M N r T E0 E1 E2 ≤ 1/4 ∧
        (1+(PI+PE)*r⁻¹*r^(1-α))*
          holderOnlyTotalSupRate n α Cφ CHI CHE M N r T E0 E1 E2 ≤ 1/(4*β) := by
  let A : ℝ := 2*((5^(Module.finrank ℝ (Space n)) : ℕ) : ℝ)*
    CHI*N*(Fintype.card (Yau.RIdx n) : ℝ)^2*M
  have hLead : ContinuousAt (fun r : ℝ => A*(2*r)^α) 0 := by
    have hPow : Continuous (fun r : ℝ => r^α) := Real.continuous_rpow_const hα.le
    fun_prop
  have hLead0 : A*(2*(0 : ℝ))^α < (1/8 : ℝ) := by
    rw [mul_zero,Real.zero_rpow hα.ne',mul_zero]
    norm_num
  obtain ⟨r,hr,hr1,hRadius⟩ := exists_small_positive_interval hLead hLead0
  refine ⟨r,hr,hr1,?_⟩
  intro E0 E1 E2
  let p : ℝ := (PI+PE)*r⁻¹*r^(1-α)
  let β : ℝ := max 1 p
  have hβ : 0 < β := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hZero : holderOnlyTotalHolderRate n α Cφ CHI CHE M N r 0 E0 E1 E2 < 1/4 := by
    rw [holderOnlyTotalHolderRate_zero n hα hα1]
    convert (hRadius r hr.le le_rfl).trans (by norm_num : (1/8 : ℝ) < 1/4) using 1
  obtain ⟨δ1,hδ1,hδ11,hTime1⟩ := exists_small_positive_interval
    (holderOnlyTotalHolderRate_continuous n hα.le hα1.le Cφ CHI CHE M N r E0 E1 E2).continuousAt
    hZero
  have hSmallSup : (1+p)*holderOnlyTotalSupRate n α Cφ CHI CHE M N r 0 E0 E1 E2 <
      1/(4*β) := by
    rw [holderOnlyTotalSupRate_zero n hα hα1,mul_zero]
    positivity
  obtain ⟨δ2,hδ2,hδ21,hTime2⟩ := exists_small_positive_interval
    (continuousAt_const.mul
      (holderOnlyTotalSupRate_continuous n hα.le hα1.le Cφ CHI CHE M N r E0 E1 E2).continuousAt)
    hSmallSup
  refine ⟨β,min δ1 δ2,hβ,le_max_right _ _,lt_min hδ1 hδ2,
    (min_le_left _ _).trans hδ11,?_⟩
  intro T hT hTδ
  exact ⟨(hTime1 T hT (hTδ.trans (min_le_left _ _))).le,
    (hTime2 T hT (hTδ.trans (min_le_right _ _))).le⟩

/-- Uniform scales for the genuine residual with Holder coefficients alone.
    All geometric and numeric choices precede coefficients and right-hand sides. -/
theorem exists_localizedHeatResidual_holder_only_weighted_bounds {n : ℕ}
    {α M N : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {K : Set (Space n)} (hK : IsCompact K) :
    ∃ (r : ℝ) (hr : 0 < r) (s : Finset (Space n)) (β δ : ℝ), r ≤ 1 ∧
      (∀ c ∈ s, c ∈ K) ∧ (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) ∧
      (∀ x ∈ K, 1 ≤ patchSum s r hr x) ∧ 0 < β ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (T : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
        (B : Space n → Space n ≃L[ℝ] Space n)
        (Bext : Space n ≃L[ℝ] Space n) (f : Point n → ℝ) (F S : ℝ),
      0 < T → T ≤ δ →
      HolderBound α (cylinder Set.univ 0 T) a M →
      (∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M) →
      (∀ p ∈ cylinder Set.univ 0 T, p.1 ∉ K → a p = 1) →
      (∀ c, constantHeatNormFactor α (B c) ≤ N) →
      constantHeatNormFactor α Bext ≤ N →
      HolderBound α (cylinder Set.univ 0 T) f F → 0 ≤ S → S ≤ F →
      (∀ p ∈ cylinder Set.univ 0 T, |f p| ≤ S) →
      HolderBound α (cylinder Set.univ 0 T)
        (localizedHeatResidual T s r hr B Bext a b f) (F/4+β*S/4) ∧
      (∀ p ∈ cylinder Set.univ 0 T,
        |localizedHeatResidual T s r hr B Bext a b f p| ≤ F/(4*β)) := by
  obtain ⟨PI,PE,Cφ,CHI,CHE,hPI,hPE,hCφ,hCHI,hCHE,hActual⟩ :=
    localizedHeatResidual_holder_only_refined_bounds (n := n) hα hα1
  obtain ⟨r,hr,hr1,hScales⟩ :=
    exists_holder_only_localization_scales n hα hα1 PI PE Cφ CHI CHE M N
  obtain ⟨s,hsK,hSep,hCover,_,_⟩ := compact_separated_patch_partition hK hr
  obtain ⟨E0,E1,E2,hE0,hE1,hE2,hBounds⟩ := hActual s r hr hr1 hSep
  obtain ⟨β,δ,hβ,hWeight,hδ,hδ1,hRate⟩ := hScales E0 E1 E2
  refine ⟨r,hr,s,β,δ,hr1,hsK,hSep,hCover,hβ,hδ,hδ1,?_⟩
  intro T a b B Bext f F S hT hTδ ha hb hExt hB hBext hf hS hSF hSup
  let p : ℝ := (PI+PE)*r⁻¹*r^(1-α)
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hF : 0 ≤ F := hf.1
  have hM : 0 ≤ M := ha.1
  have hN : 0 ≤ N := (constantHeatNormFactor_pos α Bext).le.trans hBext
  have hW : 0 ≤ F+p*S := by positivity
  have hRho : 0 ≤ holderOnlyTotalSupRate n α Cφ CHI CHE M N r T E0 E1 E2 := by
    dsimp only [holderOnlyTotalSupRate,holderOnlyInteriorSupRate,holderOnlyExteriorRate,
      lowerCutoffBudget,cutoffJetBudget]
    positivity
  have hFull := hBounds K T F S M N a b B Bext f hT (hTδ.trans hδ1) hCover
    ha hb hExt hB hBext hf hS hSup
  have hSmall := hRate T hT.le hTδ
  constructor
  · apply holderBound_mono_const hFull.1
    have h := mul_le_mul_of_nonneg_right hSmall.1 hW
    have hWeightS := mul_le_mul_of_nonneg_right hWeight hS
    change holderOnlyTotalHolderRate n α Cφ CHI CHE M N r T E0 E1 E2*(F+p*S) ≤ _
    change p*S ≤ β*S at hWeightS
    nlinarith
  · intro q hq
    have hWBound : F+p*S ≤ (1+p)*F := by nlinarith [mul_le_mul_of_nonneg_left hSF hp]
    calc
      _ ≤ holderOnlyTotalSupRate n α Cφ CHI CHE M N r T E0 E1 E2*(F+p*S) :=
        hFull.2 q hq
      _ ≤ holderOnlyTotalSupRate n α Cφ CHI CHE M N r T E0 E1 E2*((1+p)*F) :=
        mul_le_mul_of_nonneg_left hWBound hRho
      _ = ((1+p)*holderOnlyTotalSupRate n α Cφ CHI CHE M N r T E0 E1 E2)*F := by ring
      _ ≤ (1/(4*β))*F := mul_le_mul_of_nonneg_right hSmall.2 hF
      _ = F/(4*β) := by ring

end Yau.LeafProofs.L16Aux
