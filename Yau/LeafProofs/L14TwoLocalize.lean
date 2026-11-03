import Yau.LeafProofs.L14TwoCoordinates
import Yau.LeafProofs.L14RoughChartGraph

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def compactTwoChartCoefficients (η : M.Carrier → ℝ) (W : NQForm E 2) (a : M.Carrier)
    (z : ComplexVector n) (i j : Fin n) : ComplexVector r :=
  Complex.ofReal (L18Aux.chartPullbackZero a η z) • coefficients (r := r) E W a z ![i,j]

theorem compactTwoChartCoefficients_skew (η : M.Carrier → ℝ) (W : NQForm E 2) (a : M.Carrier)
    (z : ComplexVector n) (i j : Fin n) :
    compactTwoChartCoefficients (r := r) E η W a z j i =
      -compactTwoChartCoefficients (r := r) E η W a z i j := by
  ext α
  simp only [compactTwoChartCoefficients, PiLp.smul_apply, PiLp.neg_apply,
    smul_eq_mul]
  rw [coefficients_two_skew E W a z i j α, mul_neg]

theorem compactTwoChartCoefficients_properties (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (hcη : HasCompactSupport η) (W : NQForm E 2) (hW : SmoothForm (r := r) E W)
    (a : M.Carrier) (hηa : tsupport η ⊆ bundleChartSource (r := r) E a) :
    ContDiff ℝ ∞ (compactTwoChartCoefficients (r := r) E η W a) ∧
      HasCompactSupport (compactTwoChartCoefficients (r := r) E η W a) ∧
        tsupport (compactTwoChartCoefficients (r := r) E η W a) ⊆ localDomain (r := r) E a := by
  let ψ := L18Aux.chartPullbackZero a η
  let F := compactTwoChartCoefficients (r := r) E η W a
  obtain ⟨hψ, hcψ, hsψ⟩ := bundle_chartPullbackZero_properties E a η hη hcη hηa
  have hFs : tsupport F ⊆ tsupport ψ := by
    apply closure_minimal _ (isClosed_tsupport ψ)
    intro z hz
    by_contra hn
    have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hn
    apply hz
    funext i j
    change Complex.ofReal (ψ z) • coefficients (r := r) E W a z ![i,j] = 0
    rw [hψz, Complex.ofReal_zero, zero_smul]
  have hFOn (i j : Fin n) (α : Fin r) :
      ContDiffOn ℝ ∞ (fun z => F z i j α) (localDomain (r := r) E a) := by
    change ContDiffOn ℝ ∞ (fun z => Complex.ofReal (ψ z) *
      coefficients (r := r) E W a z ![i,j] α) _
    exact ((Complex.ofRealCLM.contDiff.comp hψ).contDiffOn).mul (hW a ![i,j] α)
  refine ⟨?_, hcψ.of_isClosed_subset (isClosed_tsupport F) hFs, hFs.trans hsψ⟩
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  apply (contDiff_piLp 2).mpr
  intro α
  apply contDiff_of_contDiffOn_of_tsupport_subset (localDomain_isOpen (r := r) E a) _ (hFOn i j α)
  exact (tsupport_comp_subset (g := fun V : Fin n → Fin n → ComplexVector r => V i j α) (by rfl) F).trans
    (hFs.trans hsψ)

theorem multiplyForm_eq_twoFormPushforward (η : M.Carrier → ℝ) (W : NQForm E 2)
    (a : M.Carrier) (hηa : tsupport η ⊆ bundleChartSource (r := r) E a) :
    multiplyForm E (fun x => (η x : ℂ)) W =
      twoFormPushforward (r := r) E a (compactTwoChartCoefficients (r := r) E η W a) := by
  classical
  apply twoForm_eq_of_chart_coefficients (r := r) E _ _ a
  · intro x hx
    have hηzero : η x = 0 := by
      by_contra hn
      exact hx (hηa (subset_tsupport η hn))
    change multiplyForm E (fun x => (η x : ℂ)) W x =
      if hx : x ∈ bundleChartSource (r := r) E a then _ else _
    rw [dif_neg hx]
    apply Subtype.ext
    simp only [multiplyForm, hηzero, Complex.ofReal_zero, zero_smul]
    rfl
  · intro z hz i j α
    rw [coefficients_multiplyForm, twoFormPushforward_coefficients E a _
      (compactTwoChartCoefficients_skew E η W a) z hz]
    change _ = Complex.ofReal (L18Aux.chartPullbackZero a η z) *
      coefficients (r := r) E W a z ![i,j] α
    simp only [L18Aux.chartPullbackZero, ite_eq_left hz.1]

theorem exists_finite_compact_two_chart_decomposition (g : Yau.SmoothMetric M)
    (W : NQForm E 2) (hW : SmoothForm (r := r) E W)
    (hc : IsCompact (closure {x | W x ≠ (0 : NQForm E 2) x})) :
    ∃ s : Finset M.Carrier, ∃ F : s → ComplexVector n → Fin n → Fin n → ComplexVector r,
      (∀ i, ContDiff ℝ ∞ (F i) ∧ HasCompactSupport (F i) ∧
        tsupport (F i) ⊆ localDomain (r := r) E (i : M.Carrier)) ∧
      (∀ i z j k, F i z k j = -F i z j k) ∧
      W = ∑ i : s, twoFormPushforward (r := r) E (i : M.Carrier) (F i) := by
  classical
  obtain ⟨s, χ, hχ, hχn, hχo, hχone⟩ := exists_finite_smooth_bundle_square_partition (r := r) E g hc
  let η := fun i : s => fun x => χ i x ^ 2
  have hηs (i : s) : SmoothFn (η i) := L18Aux.smoothFn_pow (hχ i).1 2
  have hηsupport (i : s) : tsupport (η i) ⊆ tsupport (χ i) := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp only [η, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
  have hηc (i : s) : HasCompactSupport (η i) :=
    (hχ i).2.of_isClosed_subset (isClosed_tsupport _) (hηsupport i)
  have hηo (i : s) : tsupport (η i) ⊆ bundleChartSource (r := r) E (i : M.Carrier) :=
    (hηsupport i).trans (hχo i)
  let F := fun i : s => compactTwoChartCoefficients (r := r) E (η i) W (i : M.Carrier)
  refine ⟨s, F, (fun i => compactTwoChartCoefficients_properties E (η i) (hηs i) (hηc i)
    W hW (i : M.Carrier) (hηo i)), (fun i => compactTwoChartCoefficients_skew E (η i) W (i : M.Carrier)), ?_⟩
  have hsum : (∑ i, multiplyForm E (fun x => (η i x : ℂ)) W) = W := by
    apply sum_multiplyForm_eq E (fun i x => (η i x : ℂ)) W
    intro x hx
    have hreal : (∑ i, χ i x ^ 2) = 1 := (hχone x (subset_closure hx)).self_of_nhds
    exact_mod_cast hreal
  calc
    _ = ∑ i, multiplyForm E (fun x => (η i x : ℂ)) W := hsum.symm
    _ = _ := Finset.sum_congr rfl (fun i _ => multiplyForm_eq_twoFormPushforward E (η i) W
      (i : M.Carrier) (hηo i))

end Yau.LeafProofs.L14Aux
