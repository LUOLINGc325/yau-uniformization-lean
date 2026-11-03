import Yau.LeafProofs.L16MatrixHolder
import Yau.LeafProofs.L16ChartCoefficientGeometry

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance chartCoefficientHolder_firstGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n) := inferInstance
local instance chartCoefficientHolder_firstSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n) := inferInstance
local instance chartCoefficientHolder_secondGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance chartCoefficientHolder_secondSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance

theorem holderBound_chart_linear_coordinate {n : ℕ} {α C : ℝ} {Q : Set (Point n)}
    {L : Point n → Space n →L[ℝ] Space n} (hL : HolderBound α Q L C) (i k : Yau.RIdx n) :
    HolderBound α Q (fun p => Yau.realCoord (L p (Yau.realVec i)) k) C := by
  let A : (Space n →L[ℝ] Space n) →L[ℝ] ℝ :=
    (realCoordLinear k).comp (ContinuousLinearMap.apply ℝ (Space n) (Yau.realVec i))
  have hA (v : Space n →L[ℝ] Space n) : ‖A v‖ ≤ ‖v‖ := by
    change ‖realCoordLinear k (v (Yau.realVec i))‖ ≤ ‖v‖
    rw [realCoordLinear_apply,Real.norm_eq_abs]
    exact (realCoord_abs_le_norm _ _).trans (by simpa only [realVec_norm,mul_one] using v.le_opNorm (Yau.realVec i))
  simpa only [A,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,realCoordLinear_apply] using
    holderBound_comp_linear_contraction A hA hL

theorem holderBound_chart_second_coordinate {n : ℕ} {α C : ℝ} {Q : Set (Point n)}
    {B : Point n → Space n →L[ℝ] Space n →L[ℝ] Space n}
    (hB : HolderBound α Q B C) (i j k : Yau.RIdx n) :
    HolderBound α Q (fun p => Yau.realCoord (B p (Yau.realVec i) (Yau.realVec j)) k) C := by
  let A : (Space n →L[ℝ] Space n →L[ℝ] Space n) →L[ℝ] ℝ :=
    (realCoordLinear k).comp ((ContinuousLinearMap.apply ℝ (Space n) (Yau.realVec j)).comp
      (ContinuousLinearMap.apply ℝ (Space n →L[ℝ] Space n) (Yau.realVec i)))
  have hA (v : Space n →L[ℝ] Space n →L[ℝ] Space n) : ‖A v‖ ≤ ‖v‖ := by
    change ‖realCoordLinear k (v (Yau.realVec i) (Yau.realVec j))‖ ≤ ‖v‖
    rw [realCoordLinear_apply,Real.norm_eq_abs]
    exact (realCoord_abs_le_norm _ _).trans
      (((v (Yau.realVec i)).le_opNorm (Yau.realVec j)).trans (by
        simpa only [realVec_norm,mul_one] using v.le_opNorm (Yau.realVec i)))
  simpa only [A,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,realCoordLinear_apply] using
    holderBound_comp_linear_contraction A hA hB

/-- Genuine coefficient Holder fields and the actual finite chart jets give
    Holder control of the transformed principal matrix and full drift. -/
theorem chart_coefficient_holder_bound {n : ℕ} {α F J : ℝ} {Q : Set (Point n)}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {L : Point n → Space n →L[ℝ] Space n}
    {B : Point n → Space n →L[ℝ] Space n →L[ℝ] Space n}
    (ha : HolderBound α Q a F) (hb : ∀ i, HolderBound α Q (fun p => b p i) F)
    (hL : HolderBound α Q L J) (hB : HolderBound α Q B J) :
    HolderBound α Q (fun p => chartPrincipalMatrix (L p) (a p))
      (4*(Fintype.card (Yau.RIdx n) : ℝ)^4*F*J^2) ∧
    ∀ k, HolderBound α Q (fun p => chartDriftVector (L p) (B p) (a p) (b p) k)
      (2*((Fintype.card (Yau.RIdx n) : ℝ)^2+Fintype.card (Yau.RIdx n))*F*J) := by
  classical
  have hF : 0 ≤ F := ha.1
  have hPrincipalEach (k l : Yau.RIdx n) := holderBound_finset_sum Finset.univ
    (fun i _ => holderBound_finset_sum Finset.univ (fun j _ =>
      holderBound_mul (holderBound_mul (holderBound_matrix_entry ha i j)
        (holderBound_chart_linear_coordinate hL i k)) (holderBound_chart_linear_coordinate hL j l)))
  have hPrincipal : ∀ k l : Yau.RIdx n,
      HolderBound α Q (fun p => chartPrincipalMatrix (L p) (a p) k l)
        ((Fintype.card (Yau.RIdx n) : ℝ)^2*(4*F*J^2)) := by
    intro k l
    convert hPrincipalEach k l using 1
    · rfl
    · simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
  constructor
  · have h := holderBound_matrix_of_entries (by positivity : 0 ≤ (Fintype.card (Yau.RIdx n) : ℝ)^2*(4*F*J^2)) hPrincipal
    convert h using 1
    ring
  · intro k
    have hCurvature := holderBound_finset_sum Finset.univ (fun i _ =>
      holderBound_finset_sum Finset.univ (fun j _ => holderBound_mul (holderBound_matrix_entry ha i j)
        (holderBound_chart_second_coordinate hB i j k)))
    have hDrift := holderBound_finset_sum Finset.univ (fun i _ =>
      holderBound_mul (hb i) (holderBound_chart_linear_coordinate hL i k))
    have h := holderBound_add hCurvature hDrift
    convert h using 1
    · rfl
    · simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring

/-- Buffered smooth chart geometry controls the actual transformed Holder
    coefficients, with one constant selected before all original coefficients. -/
theorem compact_chart_transformed_coefficients_holder {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (c : OpenPartialHomeomorph (Space n) (Space n))
    (hc : ContDiffOn ℝ 3 c c.source) (hci : ContDiffOn ℝ 3 c.symm c.target)
    {K : Set (Space n)} (hK : IsCompact K) (hConv : Convex ℝ K) (hKT : K ⊆ c.target) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S X : Set (Space n)) (T M : ℝ)
      (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ),
      S ⊆ K → MapsTo c.symm S X →
      HolderBound α (cylinder X 0 T) a M →
      (∀ i, HolderBound α (cylinder X 0 T) (fun p => b p i) M) →
      HolderBound α (cylinder S 0 T) (chartTransformedPrincipal c a) (C*M) ∧
      ∀ i, HolderBound α (cylinder S 0 T) (fun p => chartTransformedDrift c a b p i) (C*M) := by
  classical
  obtain ⟨D,hD,hLip,hJets⟩ := compact_chart_coefficient_geometry_holder hα hα1 c hc hci hK hConv hKT
  let N : ℝ := Fintype.card (Yau.RIdx n)
  let W : ℝ := 1+D^α
  let A : ℝ := 4*N^4*W*D^2
  let B : ℝ := 2*(N^2+N)*W*D
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hW : 0 < W := by dsimp only [W]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨1+A+B,by positivity,?_⟩
  intro S X T M a b hSK hMap ha hb
  have hM : 0 ≤ M := ha.1
  have hSub : cylinder S 0 T ⊆ cylinder K 0 T := fun p hp => ⟨hSK hp.1,hp.2⟩
  have hActualLip : ∀ x ∈ S, ∀ y ∈ S, ‖c.symm x-c.symm y‖ ≤ D*‖x-y‖ :=
    fun x hx y hy => hLip x (hSK hx) y (hSK hy)
  have haPull := holderBound_spatial_lipschitz_pullback hα.le hD.le c.symm hMap hActualLip ha
  have hbPull (i : Yau.RIdx n) := holderBound_spatial_lipschitz_pullback hα.le hD.le c.symm hMap hActualLip (hb i)
  have h := chart_coefficient_holder_bound haPull hbPull
    (holderBound_mono (hJets T).1 hSub) (holderBound_mono (hJets T).2 hSub)
  have hBudgetA : 4*(Fintype.card (Yau.RIdx n) : ℝ)^4*(M*(1+D^α))*D^2 = A*M := by
    dsimp only [A,N,W]
    ring
  have hBudgetB : 2*((Fintype.card (Yau.RIdx n) : ℝ)^2+Fintype.card (Yau.RIdx n))*(M*(1+D^α))*D = B*M := by
    dsimp only [B,N,W]
    ring
  refine ⟨?_,?_⟩
  · have hh : HolderBound α (cylinder S 0 T) (chartTransformedPrincipal c a) (A*M) := by
      change HolderBound α (cylinder S 0 T)
        (fun p => chartPrincipalMatrix (fderiv ℝ c (c.symm p.1)) (a (c.symm p.1,p.2))) (A*M)
      simpa only [hBudgetA] using h.1
    exact holderBound_mono_const hh (mul_le_mul_of_nonneg_right (by linarith) hM)
  · intro i
    have hh : HolderBound α (cylinder S 0 T) (fun p => chartTransformedDrift c a b p i) (B*M) := by
      simpa only [chartTransformedDrift,hBudgetB] using h.2 i
    exact holderBound_mono_const hh (mul_le_mul_of_nonneg_right (by linarith) hM)

end Yau.LeafProofs.L16Aux
