import Yau.LeafProofs.L17LocalizedSchauderAssembly

open Set Metric
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- Actual local four-jet data produce the unique original Schauder element
with the literal locally finite sum as its function. The norm constant is
selected before the partition, radius, time, and local functions. -/
theorem exists_uniform_localized_schauder_assembly (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (N : ℕ) (Ccut gamma : ℝ) (hCutNonneg : 0 ≤ Ccut) (hγ : 0 < gamma) (hγone : gamma ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : UniformChartPartition g), P.charts = A → P.overlapBudget ≤ N →
      ∀ (hρone : P.radius ≤ 1), 2*P.radius < A.radius → CutoffJetBounds P 2 Ccut →
      ∀ (T : ℝ) (hT : 0 < T) (F : ℝ), 0 ≤ F →
      ∀ (v : P.centers → ComplexVector n × Time T → ℝ)
        (D : P.centers → ComplexVector n × Time T → D1 n)
        (H : P.centers → ComplexVector n × Time T → D2 n)
        (b : P.centers → ComplexVector n × Time T → ℝ),
      LocalTrueJets P T hT.le v D H b → LocalScaledJetBounds P T gamma F v D H b →
        ∃! u : SchauderSpace P T gamma hT, schauderFun u = globalSum P T v ∧ ‖u‖ ≤ C*F := by
  obtain ⟨K,hK,hLocal⟩ := exists_uniform_localized_four_jet_budget A hg Ccut gamma hCutNonneg hγ hγone
  let C := 1+max (N : ℝ) (2*(N : ℝ)*K)
  have hC : 0 < C := by
    dsimp only [C]
    have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith [le_max_left (N : ℝ) (2*(N : ℝ)*K)]
  refine ⟨C,hC,?_⟩
  intro P hPA hPN hρone hρr hCut T hT F hF v D H b hTrue hBounds
  have hKF : 0 ≤ K*F := mul_nonneg hK.le hF
  have hLocal' := hLocal P hPA hρone hρr hCut T F hT.le hF v D H b hTrue hBounds
  let u := assembledSchauder P T gamma hT v D H b hTrue hF hKF hBounds hLocal' hγ
  have hValue : schauderFun u = globalSum P T v :=
    assembledSchauder_value P T gamma hT v D H b hTrue hF hKF hBounds hLocal' hγ
  have hNorm : ‖u‖ ≤ C*F := by
    apply (assembledSchauder_norm_le P T gamma hT v D H b hTrue hF hKF hBounds hLocal' hγ).trans
    apply max_le
    · have hNC : (N : ℝ) ≤ C := by dsimp only [C]; linarith [le_max_left (N : ℝ) (2*(N : ℝ)*K)]
      exact mul_le_mul_of_nonneg_right ((show (P.overlapBudget : ℝ) ≤ N by exact_mod_cast hPN).trans hNC) hF
    · have hNC : 2*(N : ℝ)*K ≤ C := by dsimp only [C]; linarith [le_max_right (N : ℝ) (2*(N : ℝ)*K)]
      have hCoef : 2*(P.overlapBudget : ℝ)*K ≤ 2*(N : ℝ)*K := by
        apply mul_le_mul_of_nonneg_right _ hK.le
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hPN) (by norm_num)
      have hh := mul_le_mul_of_nonneg_right (hCoef.trans hNC) hF
      simpa only [mul_assoc] using hh
  refine ⟨u,⟨hValue,hNorm⟩,?_⟩
  intro u' hu'
  exact schauderFun_injective (hu'.1.trans hValue.symm)

/-- Only the actual cutoff orders zero through three enter the assembly. -/
theorem cutoffJetBounds_of_all_orders (P : UniformChartPartition g) (B : ℕ → ℝ)
    (hB : ∀ k, 0 ≤ B k)
    (hJets : ∀ k p q z, z ∈ ball (0 : ComplexVector n) 2 →
      ‖iteratedFDeriv ℝ k (unitCutoff P p q) z‖ ≤ B k) :
    CutoffJetBounds P 2 (∑ j ∈ Finset.range 4, B j) := by
  intro p q z hz j hj
  exact (hJets j p q z hz).trans (Finset.single_le_sum (fun i _ => hB i)
    (show j ∈ Finset.range 4 from Finset.mem_range.mpr (by omega)))

end Yau.LeafProofs.L17LocalizedSchauderAux
