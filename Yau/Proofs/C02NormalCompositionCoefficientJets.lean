import Yau.Proofs.C02PullbackCoefficientJets
import Yau.Proofs.C02RealBilinearPullbackJets
import Yau.Proofs.C02RealPullbackComposition
import Yau.Proofs.C02OpenCompositionJets

/-! An explicit profile controls every original complex pullback
coefficient of the corrected normal chart, on its actual open domain. -/

noncomputable section
open Set
open scoped ContDiff Manifold InnerProductSpace
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

def normalCompositionJetMajorant (a b : ℕ → ℝ) (m : ℕ) : ℝ :=
  binomialJetProduct (fun i => b (i + 1))
    (binomialJetProduct
      (fun i => (i.factorial : ℝ) * finiteJetEnvelope a i * finiteJetEnvelope b i ^ i)
      (fun i => b (i + 1))) m

theorem normal_composition_coefficient_jet_bound
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {G : ComplexVector n → ComplexVector n} (hG : ContDiffOn ℝ ∞ G O)
    (hΦ : ∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexVector n) (ComplexModel n)
      (normalRealMap g p U ∘ G) y)
    {x : ComplexVector n} (hx : x ∈ O) (a b : ℕ → ℝ) (hb0 : ∀ i, 0 ≤ b i)
    (hOuter : ∀ i, ‖iteratedFDeriv ℝ i (normalGaugeMetric g p U hU) (G x)‖ ≤ a i)
    (hInner : ∀ i, 1 ≤ i → ‖iteratedFDeriv ℝ i G x‖ ≤ b i)
    (m : ℕ) (k l : Fin n) :
    ‖iteratedFDeriv ℝ m (fun y => pullbackMat g.form (normalRealMap g p U ∘ G) y k l) x‖ ≤
      normalCompositionJetMajorant a b m := by
  let H := normalGaugeMetric g p U hU ∘ G
  let D := fderiv ℝ G
  let Q := fun y => realBilinearPullback (H y) (D y)
  have hH : ContDiffOn ℝ ∞ H O :=
    (normalGaugeMetric_smooth g p U hU).comp_contDiffOn hG
  have hD : ContDiffOn ℝ ∞ D O := hG.fderiv_of_isOpen hO (by simp)
  have hQ : ContDiffOn ℝ ∞ Q O := realBilinearPullback_smoothOn hH hD
  have hActual (y : ComplexVector n) (hy : y ∈ O) (u v : ComplexVector n) :
      Q y u v = realPullbackMetric g.form (normalRealMap g p U ∘ G) y u v := by
    exact (realPullbackMetric_normal_composition g p U hU
      ((hG.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp)) u v).symm
  apply (pullback_coefficient_jet_le_real_metric g.form hO hΦ hQ hActual hx m k l).trans
  apply norm_realBilinearPullback_jet_le hO hH hD hx m
    (fun i => (i.factorial : ℝ) * finiteJetEnvelope a i * finiteJetEnvelope b i ^ i)
    (fun i => b (i + 1))
  · intro i hi
    exact norm_iteratedFDeriv_comp_on_le hO isOpen_univ hG
      (normalGaugeMetric_smooth g p U hU).contDiffOn (fun y hy => mem_univ _) hx i a b
      (fun j hj => hOuter j) (fun j hj hji => hInner j hj)
  · intro i hi
    dsimp only [D]
    simpa only [norm_iteratedFDeriv_fderiv] using hInner (i + 1) (by omega)
  · intro i
    have ha := finiteJetEnvelope_one_le a i
    have hb := finiteJetEnvelope_one_le b i
    positivity
  · exact fun i => hb0 (i + 1)

end Yau.Blueprint.C02Proof
