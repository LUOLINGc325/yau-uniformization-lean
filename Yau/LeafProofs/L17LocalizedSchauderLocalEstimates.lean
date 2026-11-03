import Yau.LeafProofs.L17LocalizedSchauderGlobalJetBounds

open Set Metric
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def LocalizedFourJetBounds (P : UniformChartPartition g) (T gamma B : ℝ)
    (v b : P.centers → ComplexVector n × Time T → ℝ) : Prop :=
  (∀ (p : P.centers) (q : M.Carrier) (t s : Time T) (z w : ComplexVector n),
    z ∈ ball 0 1 → w ∈ ball 0 1 → ∀ j, j ≤ 2 →
      ‖iteratedFDeriv ℝ j (unitLocalizedTerm P T p q (v p) t) z‖ ≤ B ∧
      ‖iteratedFDeriv ℝ j (unitLocalizedTerm P T p q (v p) t) z-
        iteratedFDeriv ℝ j (unitLocalizedTerm P T p q (v p) s) w‖ ≤
          B*(unitParabolicDistance P.radius (z,t) (w,s))^gamma) ∧
  ∀ (p : P.centers) (q : M.Carrier) (t s : Time T) (z w : ComplexVector n),
    z ∈ ball 0 1 → w ∈ ball 0 1 →
      |localizedTerm P T p (b p) (P.charts.chart q (P.radius • z),t)-
        localizedTerm P T p (b p) (P.charts.chart q (P.radius • w),s)| ≤
          B*(unitParabolicDistance P.radius (z,t) (w,s))^gamma

theorem cutoffUnitFamily_unitTime_eq (P : UniformChartPartition g) (hρone : P.radius ≤ 1)
    {T : ℝ} (b : P.centers → ComplexVector n × Time T → ℝ)
    (p : P.centers) (q : M.Carrier) (t : Time T) :
    cutoffUnitFamily P hρone (fun p t z => b p (P.radius • z,t)) p q t =
      (fun z => localizedTerm P T p (b p) (P.charts.chart q (P.radius • z),t)) := by
  funext z
  simp only [cutoffUnitFamily,unitCutoff,localizedTerm,BoundedChartFamily.scaledTransitionMap,
    BoundedChartFamily.transitionMap,smul_smul,mul_inv_cancel₀ P.radius_pos.ne',one_smul]

theorem exists_uniform_localized_four_jet_budget (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (C gamma : ℝ) (hC : 0 ≤ C) (hγ : 0 < gamma) (hγone : gamma ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : UniformChartPartition g), P.charts = A →
      ∀ (hρone : P.radius ≤ 1), 2*P.radius < A.radius → CutoffJetBounds P 2 C →
      ∀ (T F : ℝ) (hT : 0 ≤ T), 0 ≤ F →
      ∀ (v : P.centers → ComplexVector n × Time T → ℝ)
        (D : P.centers → ComplexVector n × Time T → D1 n)
        (H : P.centers → ComplexVector n × Time T → D2 n)
        (b : P.centers → ComplexVector n × Time T → ℝ),
      LocalTrueJets P T hT v D H b → LocalScaledJetBounds P T gamma F v D H b →
        LocalizedFourJetBounds P T gamma (K*F) v b := by
  obtain ⟨K₂,hK₂,hTwo⟩ := exists_uniform_cutoff_transport_budget A hg 2 (by norm_num) C gamma hC hγ hγone
  obtain ⟨K₀,hK₀,hZero⟩ := exists_uniform_cutoff_transport_budget A hg 0 (by norm_num) C gamma hC hγ hγone
  refine ⟨max K₂ K₀,hK₂.trans_le (le_max_left _ _),?_⟩
  intro P hPA hρone hρr hCut T F hT hF v D H b hTrue hBounds
  have hCut₀ : CutoffJetBounds P 0 C := fun p q z hz j hj => hCut p q z hz j (by omega)
  constructor
  · intro p q t s z w hz hw j hj
    have hh := hTwo P hPA hρone hρr hCut T F hF _
      (unitValueFamily_data P T hT v D H b hTrue hBounds) p q t s z w hz hw j hj
    rw [cutoffUnitFamily_unitValue_eq,cutoffUnitFamily_unitValue_eq] at hh
    exact ⟨hh.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hF),
      hh.2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hF)
        (Real.rpow_nonneg (unitParabolicDistance_nonneg P.radius_pos (z,t) (w,s)) _))⟩
  · intro p q t s z w hz hw
    have hh := (hZero P hPA hρone hρr hCut₀ T F hF _
      (unitTimeFamily_data P T hT v D H b hTrue hBounds) p q t s z w hz hw 0 (by norm_num)).2
    rw [cutoffUnitFamily_unitTime_eq,cutoffUnitFamily_unitTime_eq,norm_iteratedFDeriv_zero_sub,
      Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hF)
      (Real.rpow_nonneg (unitParabolicDistance_nonneg P.radius_pos (z,t) (w,s)) _))

end Yau.LeafProofs.L17LocalizedSchauderAux
