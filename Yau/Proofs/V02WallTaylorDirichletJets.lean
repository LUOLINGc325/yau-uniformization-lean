import Yau.Proofs.V03RealDirichletDerivative

/-! Every actual real parameter jet commutes with the weighted Fourier
Hilbert trace. The seminorm bounds below concern scalar boundary functions. -/

open scoped Topology ContDiff lp
open Filter

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof

/-- Iterated directional derivatives in the parameter, with the angle fixed. -/
def realParameterJet (f : ℂ × ℝ → ℂ) : (m : ℕ) → (Fin m → ℂ) → ℂ × ℝ → ℂ
  | 0, _ => f
  | m + 1, v => realParameterDerivative (realParameterJet f m (Fin.tail v)) (v 0)

theorem realParameterJet_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (m : ℕ) (v : Fin m → ℂ) :
    ContDiffOn ℝ ∞ (realParameterJet f m v) (U ×ˢ Set.univ) := by
  induction m with
  | zero => exact hf
  | succ m ih => exact realParameterDerivative_contDiffOn hU (ih _) _

theorem realParameterJet_periodic {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (hp : ∀ z ∈ U, Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi))
    (m : ℕ) (v : Fin m → ℂ) {z : ℂ} (hz : z ∈ U) :
    Function.Periodic (fun θ => realParameterJet f m v (z, θ)) (2 * Real.pi) := by
  induction m generalizing z with
  | zero => exact hp z hz
  | succ m ih =>
    exact realParameterDerivative_periodic hU (realParameterJet_contDiffOn hU hf m _)
      (fun p hpU => ih _ hpU) hz _

theorem iteratedFDeriv_angularDirichletVector {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (hp : ∀ z ∈ U, Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi))
    (m : ℕ) (v : Fin m → ℂ) {z : ℂ} (hz : z ∈ U) :
    iteratedFDeriv ℝ m (angularDirichletVector hU hf) z v =
      angularDirichletVector hU (realParameterJet_contDiffOn hU hf m v) z := by
  induction m generalizing z with
  | zero => rfl
  | succ m ih =>
    have hd := ((angularDirichletVector_contDiffOn hU hf).contDiffAt
      (hU.mem_nhds hz)).differentiableAt_iteratedFDeriv (m := m) (by exact_mod_cast ENat.natCast_lt_top m)
    rw [hd.iteratedFDeriv_succ_apply_left']
    have he : (fun p => iteratedFDeriv ℝ m (angularDirichletVector hU hf) p (Fin.tail v)) =ᶠ[𝓝 z]
        angularDirichletVector hU (realParameterJet_contDiffOn hU hf m (Fin.tail v)) := by
      filter_upwards [hU.mem_nhds hz] with p hpU
      exact ih _ hpU
    rw [he.fderiv_eq]
    exact fderiv_realAngularDirichletVector hU (realParameterJet_contDiffOn hU hf m _)
      (fun p hpU => realParameterJet_periodic hU hf hp m _ hpU) hz _

theorem realParameterJet_eq_iteratedFDeriv {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (m : ℕ) (v : Fin m → ℂ) {z : ℂ} (hz : z ∈ U) (θ : ℝ) :
    realParameterJet f m v (z, θ) =
      iteratedFDeriv ℝ m (fun p => f (p, θ)) z v := by
  have hs : ContDiffOn ℝ ∞ (fun p => f (p, θ)) U :=
    hf.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun p hp => ⟨hp, Set.mem_univ _⟩)
  induction m generalizing z with
  | zero => rfl
  | succ m ih =>
    rw [realParameterJet, realParameterDerivative_eq_slice hU
      (realParameterJet_contDiffOn hU hf m _) hz]
    have hd := (hs.contDiffAt (hU.mem_nhds hz)).differentiableAt_iteratedFDeriv (m := m) (by exact_mod_cast ENat.natCast_lt_top m)
    rw [hd.iteratedFDeriv_succ_apply_left']
    have he : (fun p => realParameterJet f m (Fin.tail v) (p, θ)) =ᶠ[𝓝 z]
        (fun p => iteratedFDeriv ℝ m (fun y => f (y, θ)) p (Fin.tail v)) := by
      filter_upwards [hU.mem_nhds hz] with p hpU
      exact ih _ hpU
    exact congrArg (fun A : ℂ →L[ℝ] ℂ => A (v 0)) he.fderiv_eq

theorem iteratedFDeriv_angularDirichletVector_norm_sq {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (hp : ∀ z ∈ U, Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi))
    (m : ℕ) (v : Fin m → ℂ) {z : ℂ} (hz : z ∈ U) :
    ‖iteratedFDeriv ℝ m (angularDirichletVector hU hf) z v‖ ^ 2 =
      (boundaryDSq (fun θ (_ : Unit) =>
        iteratedFDeriv ℝ m (fun p => f (p, θ)) z v)).toReal := by
  rw [iteratedFDeriv_angularDirichletVector hU hf hp m v hz,
    angularDirichletVector_norm_sq hU (realParameterJet_contDiffOn hU hf m v) hz
      (realParameterJet_periodic hU hf hp m v hz)]
  congr 2
  funext θ k
  exact realParameterJet_eq_iteratedFDeriv hU hf m v hz θ

/-- Directional scalar seminorm estimates give an operator norm estimate for
the actual Hilbert-valued iterated derivative. -/
theorem norm_iteratedFDeriv_angularDirichletVector_le {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (hp : ∀ z ∈ U, Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi))
    (m : ℕ) {z : ℂ} (hz : z ∈ U) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ v : Fin m → ℂ,
      boundaryDSq (fun θ (_ : Unit) => iteratedFDeriv ℝ m (fun p => f (p, θ)) z v) ≤
        ENNReal.ofReal ((B * ∏ i, ‖v i‖) ^ 2)) :
    ‖iteratedFDeriv ℝ m (angularDirichletVector hU hf) z‖ ≤ B := by
  apply ContinuousMultilinearMap.opNorm_le_bound hB
  intro v
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb v)
  have hreal := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr (hb v)
  rw [ENNReal.toReal_ofReal (sq_nonneg _),
    ← iteratedFDeriv_angularDirichletVector_norm_sq hU hf hp m v hz] at hreal
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (Finset.prod_nonneg (fun i _ => norm_nonneg _)))).mp hreal

end Yau.Blueprint.V02WallTaylorProof
