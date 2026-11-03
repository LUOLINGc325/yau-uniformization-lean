import Yau.Proofs.V03AtlasCompact
import Yau.Proofs.V03DiscScalars
import Yau.Proofs.V03WallHessian

/-! Actual scalar pullbacks through the native spray, expressed in its
fixed induced cotangent charts. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof

variable {n b : ℕ} {M : ComplexManifold n}

def sprayCoordinate (Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M)
    (x : M.Carrier) (p : CotangentCoord n × (Fin b → ℂ)) : CotangentCoord n :=
  cotangentChart x (Ψ (NativeCotangentPoint.mk (cotangentChartInv x p.1), p.2)).val

def sprayScalar (Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M)
    (B : CotangentPoint M → ℝ) (x : M.Carrier)
    (p : CotangentCoord n × (Fin b → ℂ)) : ℝ :=
  B (cotangentChartInv x (sprayCoordinate Ψ x p))

theorem sprayScalar_contDiffOn
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    {x : M.Carrier} {S : Set (CotangentCoord n × (Fin b → ℂ))} (hS : IsOpen S)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) S)
    {B : CotangentPoint M → ℝ}
    (hB : ContDiffOn ℝ ∞ (fun u => B (cotangentChartInv x u)) (cotangentTarget x)) :
    ContDiffOn ℝ ∞ (sprayScalar Ψ B x) (S ∩ (sprayCoordinate Ψ x) ⁻¹' cotangentTarget x) := by
  exact hB.comp ((hΨ.restrict_scalars ℝ).mono Set.inter_subset_left) (fun p hp => hp.2)

theorem sprayScalar_eq_actual
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    (B : CotangentPoint M → ℝ) (x : M.Carrier)
    {p : CotangentCoord n × (Fin b → ℂ)}
    (hp : (Ψ (NativeCotangentPoint.mk (cotangentChartInv x p.1), p.2)).val ∈ cotangentSource x) :
    sprayScalar Ψ B x p =
      B (Ψ (NativeCotangentPoint.mk (cotangentChartInv x p.1), p.2)).val := by
  exact congrArg B (cotangentChart_left_inv x hp)

theorem isOpen_sprayScalar_domain
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    {x : M.Carrier} {S : Set (CotangentCoord n × (Fin b → ℂ))} (hS : IsOpen S)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) S) :
    IsOpen (S ∩ (sprayCoordinate Ψ x) ⁻¹' cotangentTarget x) :=
  hΨ.continuousOn.isOpen_inter_preimage hS
    ((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ)

theorem sprayScalar_domain_contains_closed_buffer
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    {x : M.Carrier} {a : CotangentCoord n} {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hsource : ∀ u ∈ Metric.closedBall a δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u), τ)).val ∈ cotangentSource x) :
    Metric.closedBall a δ ×ˢ Metric.closedBall 0 (R / 2) ⊆
      (Metric.ball a (2 * δ) ×ˢ Metric.ball 0 R) ∩
        (sprayCoordinate Ψ x) ⁻¹' cotangentTarget x := by
  intro p hp
  exact ⟨⟨Metric.closedBall_subset_ball (by linarith) hp.1,
    Metric.closedBall_subset_ball (by linarith) hp.2⟩,
    cotangentChart_mapsTo x (hsource _ hp.1 _ hp.2)⟩

theorem sprayScalar_zero
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    (hzero : ∀ y, Ψ (y, 0) = y) (B : CotangentPoint M → ℝ) (x : M.Carrier)
    {u : CotangentCoord n} (hu : u ∈ cotangentTarget x) :
    sprayScalar Ψ B x (u, 0) = B (cotangentChartInv x u) := by
  apply (sprayScalar_eq_actual B x (p := (u, 0)) ?_).trans
    (by rw [hzero])
  rw [hzero]
  exact cotangentChartInv_mapsTo x hu

variable {q : ℕ} {X : KahlerManifold n}

theorem deltaBase_sprayScalar_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    {x : Pt X} {S : Set (CotangentCoord n × (Fin b → ℂ))} (hS : IsOpen S)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) S) :
    ContDiffOn ℝ ∞ (sprayScalar Ψ (fun y => deltaBase d j y.1) x)
      (S ∩ (sprayCoordinate Ψ x) ⁻¹' cotangentTarget x) :=
  sprayScalar_contDiffOn hS hΨ (deltaBase_chart_contDiffOn hd j x)

theorem deltaFiber_sprayScalar_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    {x : Pt X} {S : Set (CotangentCoord n × (Fin b → ℂ))} (hS : IsOpen S)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) S) :
    ContDiffOn ℝ ∞ (sprayScalar Ψ (deltaFiber d j) x)
      (S ∩ (sprayCoordinate Ψ x) ⁻¹' cotangentTarget x) :=
  sprayScalar_contDiffOn hS hΨ (deltaFiber_chart_contDiffOn hd j x)

end Yau.Blueprint.V02WallTaylorProof
