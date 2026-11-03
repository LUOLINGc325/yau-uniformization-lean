import Yau.Proofs.P06WeakLeviSmooth
import Yau.LeafProofs.L22Locality

noncomputable section
open Filter
open scoped Topology ContDiff ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs

/-- The literal compact-exterior hypothesis forces the upper Levi constant
to be nonnegative. The proof uses a genuine constant germ outside the
compact set and a nonzero direction in the original positive metric. -/
theorem weakLeviUpper_constantOutside_nonnegative {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (f : M.Carrier → ℝ) (C : ℝ)
    (hc : ConstantOutsideCompact f) (hw : WeakLeviUpper g.form f C) : 0 ≤ C := by
  classical
  obtain ⟨K, c, hK, hfc⟩ := hc
  have hnot : ¬ ∀ x : M.Carrier, x ∈ K := by
    intro h
    exact hK.ne_univ (Set.eq_univ_of_forall h)
  obtain ⟨x, hx⟩ := not_forall.mp hnot
  have hcenter : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hinv : ContinuousAt (chartInv x) (chartPt x x) :=
    (continuousOn_extChartAt_symm (I := ComplexModel n) x).continuousAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds (mem_extChartAt_target x))
  have houtside : ∀ᶠ z in 𝓝 (chartPt x x), chartInv x z ∉ K := by
    have hm : {y : M.Carrier | y ∉ K} ∈ 𝓝 (chartInv x (chartPt x x)) := by
      rw [hcenter]
      exact hK.isClosed.compl_mem_nhds hx
    exact hinv.tendsto.eventually hm
  have hgerm : inChart x f =ᶠ[𝓝 (chartPt x x)] (fun _ => c) := by
    filter_upwards [houtside] with z hz
    exact hfc (chartInv x z) hz
  have hnhd : {z | z ∈ chartTarget x ∧ inChart x f z = c} ∈ 𝓝 (chartPt x x) :=
    inter_mem ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_target x)) hgerm
  obtain ⟨O, hOsub, hO, hzO⟩ := mem_nhds_iff.mp hnhd
  have hfO : ContDiffOn ℝ ∞ (inChart x f) O :=
    contDiffOn_const.congr (fun z hz => (hOsub hz).2)
  have hzero : leviC (inChart x f) (chartPt x x) = 0 := by
    rw [L22Aux.leviC_congr_of_eventuallyEq hgerm]
    ext i j
    simp [leviC, leviMatrix, wirt, wirtBar]
  let i : Fin n := ⟨0, L12Aux.complexDimension_pos M⟩
  let w : Fin n → ℂ := Pi.single i 1
  have hwne : w ≠ 0 := by
    intro hw0
    have hi := congrFun hw0 i
    exact one_ne_zero (by simpa only [w, Pi.single_eq_same, Pi.zero_apply] using hi)
  have hH := L12Aux.hMat_posDef g.form x (chartPt x x) (mem_extChartAt_target x)
  have hpos : 0 < leviDirection (hMat g.form x (chartPt x x)) (WithLp.toLp 2 w) := by
    simpa [leviDirection] using hH.re_dotProduct_pos (x := w) hwne
  have h := weakLeviUpper_classical_on g f C hw x (WithLp.toLp 2 w) hO
    (fun z hz => (hOsub hz).1) hfO hzO
  rw [hzero] at h
  simp only [leviDirection, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re] at h
  exact (mul_nonneg_iff_of_pos_right hpos).mp (by simpa only [leviDirection, WithLp.ofLp_toLp] using h)

end Yau.NodeProofs.P06Aux
