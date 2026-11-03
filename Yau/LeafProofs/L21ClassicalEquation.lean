import Yau.LeafProofs.L21SmoothRepresentative

/-! The smooth representative solves the original graph equation pointwise:
weak transpose tests distinguish the actual continuous scalar outputs. -/

open MeasureTheory Filter
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem dbarWeakOn_congr_ae {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} {u v : X n → ℂ} {f : X n → Fin n → ℂ}
    (h : DbarWeakOn A u f O) (hvu : v =ᵐ[(Yau.lebesgueC n).restrict O] u) :
    DbarWeakOn A v f O := by
  intro i ψ hψ hcψ hsψ
  apply (h i ψ hψ hcψ hsψ).trans
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hO.measurableSet).mp hvu] with x hx
  by_cases hxin : x ∈ O
  · rw [hx hxin]
  · have hn : x ∉ tsupport ψ := fun hh => hxin (hsψ hh)
    have hz : transposeRow A i ψ x = 0 := by
      simp [transposeRow, image_eq_zero_of_notMem_tsupport hn, fderiv_of_notMem_tsupport ℝ hn]
    simp only [hz, mul_zero]

theorem dbarWeakOn_smooth {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {v : X n → ℂ} (hv : ContDiffOn ℝ ∞ v O) :
    DbarWeakOn A v (fun x i => dbarA A i v x) O := by
  let G := fun x a => fderiv ℝ v x (Yau.realVec a)
  have hv2 := locallyL2On_of_continuousOn hv.continuousOn
  have hG (a : Yau.RIdx n) : LocallyL2On (fun x => G x a) O :=
    locallyL2On_of_continuousOn
      (((hv.fderiv_of_isOpen hO (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).clm_apply contDiffOn_const).continuousOn)
  have hWeak (a : Yau.RIdx n) := complexWeakDerivativeOn_smooth hO hv (Yau.realVec a)
  intro i ψ hψ hcψ hsψ
  let ψC := ofRealTest ψ hψ hcψ hsψ
  have hh := weak_gradient_row_transpose_pairing hO Yau.realVec (dbarRealCoefficient A i)
    (fun a => dbarRealCoefficient_smoothOn hA i a) v G hv2 hG hWeak ψC
  have ht (x : X n) : rowTranspose Yau.realVec (dbarRealCoefficient A i) ψC x = transposeRow A i ψ x :=
    (transposeRow_eq_rowTranspose A i (hψ.differentiable (by simp)) x).symm
  have hD (x : X n) : (∑ a, dbarRealCoefficient A i a x * G x a) = dbarA A i v x :=
    (dbarA_eq_real_rows A i v x).symm
  simp only [ht, hD] at hh
  exact hh.symm

theorem smooth_representative_satisfies_dbar {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {u v : X n → ℂ} (hv : ContDiffOn ℝ ∞ v O)
    (f : X n → Fin n → ℂ) (hf : ∀ i, ContDiffOn ℝ ∞ (fun x => f x i) O)
    (heq : DbarWeakOn A u f O) (hvu : v =ᵐ[(Yau.lebesgueC n).restrict O] u) :
    ∀ x ∈ O, ∀ i, dbarA A i v x = f x i := by
  letI : (Yau.lebesgueC n).IsOpenPosMeasure := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  have h1 := dbarWeakOn_congr_ae hO heq hvu
  have h2 := dbarWeakOn_smooth hO hA hv
  have hAE (i : Fin n) : (fun x => dbarA A i v x) =ᵐ[(Yau.lebesgueC n).restrict O] (fun x => f x i) := by
    apply complex_ae_eq_of_test_integrals_eq hO
      (locallyL2On_of_continuousOn (contDiffOn_dbarA hO hA i hv).continuousOn)
      (locallyL2On_of_continuousOn (hf i).continuousOn)
    intro ψ hψ hcψ hsψ
    simpa only [mul_comm] using (h2 i ψ hψ hcψ hsψ).trans (h1 i ψ hψ hcψ hsψ).symm
  intro x hx i
  exact Measure.eqOn_open_of_ae_eq (hAE i) hO
    (contDiffOn_dbarA hO hA i hv).continuousOn (hf i).continuousOn hx

theorem exists_inner_smooth_solution {O R : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hsmall : ∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2)
    (f : X n → Fin n → ℂ) (hf : ∀ i, ContDiffOn ℝ ∞ (fun x => f x i) O)
    (u : X n → ℂ) (hu : LocallyL2On u O) (heq : DbarWeakOn A u f O)
    (hR : IsOpen R) (hcR : IsCompact (closure R)) (hRO : closure R ⊆ O) :
    ∃ v : X n → ℂ, ContDiff ℝ ∞ v ∧ v =ᵐ[(Yau.lebesgueC n).restrict R] u ∧
      ∀ x ∈ R, ∀ i, dbarA A i v x = f x i := by
  obtain ⟨v, hv, hAE⟩ := exists_inner_smooth_representative hO hA hsmall f hf u hu heq hR hcR hRO
  have hRO0 : R ⊆ O := subset_closure.trans hRO
  exact ⟨v, hv, hAE, smooth_representative_satisfies_dbar hR
    (fun i j => (hA i j).mono hRO0) hv.contDiffOn f (fun i => (hf i).mono hRO0)
    (dbarWeakOn_mono heq hRO0) hAE⟩

end Yau.LeafProofs.L21Aux
