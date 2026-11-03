import Yau.Proofs.V02AreaTaylorForms

/-! The actual spray in finite-dimensional position/coefficient variables.
Its spatial pullback bilinear kernel is independent of the chosen input disc. -/

open scoped Topology ContDiff Matrix Manifold
open Filter

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof
open Yau Yau.Blueprint V03Proof

abbrev SprayData (n b : ℕ) := CotangentCoord n × (ℂ × ComplexVector b)

variable {n q b : ℕ} {X : KahlerManifold n}

def sprayCoordinate
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (x : Pt X) (p : CotangentCoord n × (Fin b → ℂ)) : CotangentCoord n :=
  cotangentChart x (Ψ (NativeCotangentPoint.mk (cotangentChartInv x p.1), p.2)).val

def sprayInput (p : ℂ × SprayData n b) : CotangentCoord n × (Fin b → ℂ) :=
  (p.2.1, fun k => p.1 * p.2.2.1 * p.2.2.2 k)

theorem sprayInput_contDiff : ContDiff ℂ ∞ (sprayInput (n := n) (b := b)) := by
  apply ContDiff.prodMk (by fun_prop)
  apply contDiff_pi.mpr
  intro k
  have hcoord : ContDiff ℂ ∞ (fun p : ℂ × SprayData n b => p.2.2.2 k) :=
    (contDiff_piLp_apply (p := 2) (i := k)).comp (by fun_prop)
  exact (contDiff_fst.mul (by fun_prop)).mul hcoord

def localSprayMap
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (x : Pt X) (p : ℂ × SprayData n b) : CotangentCoord n :=
  sprayCoordinate Ψ x (sprayInput p)

def localSprayDomain (a : CotangentCoord n) (δ R : ℝ) : Set (ℂ × SprayData n b) :=
  sprayInput ⁻¹' (Metric.ball a (2 * δ) ×ˢ Metric.ball (0 : Fin b → ℂ) R)

def localSpatialDomain
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (x : Pt X) (a : CotangentCoord n) (δ R : ℝ) : Set (ℂ × SprayData n b) :=
  localSprayDomain a δ R ∩ localSprayMap Ψ x ⁻¹' cotangentTarget x

def localSprayDifferential
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (x : Pt X) (p : ℂ × SprayData n b) : SprayData n b →L[ℂ] CotangentCoord n :=
  (fderiv ℂ (localSprayMap Ψ x) p).comp (ContinuousLinearMap.inr ℂ ℂ (SprayData n b))

def localSpatialKernel (d : VariationData X q)
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (x : Pt X) (p : ℂ × SprayData n b) : SprayData n b →L[ℝ] SprayData n b →L[ℝ] ℝ :=
  pullbackBilinear (spatialChartBilinear d.G X.metric.form x (localSprayMap Ψ x p))
    ((localSprayDifferential Ψ x p).restrictScalars ℝ)

theorem localSprayDomain_isOpen (a : CotangentCoord n) (δ R : ℝ) :
    IsOpen (localSprayDomain (b := b) a δ R) :=
  (Metric.isOpen_ball.prod Metric.isOpen_ball).preimage sprayInput_contDiff.continuous

theorem localSprayMap_contDiffOn
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (x : Pt X) {a : CotangentCoord n} {δ R : ℝ}
    (hψ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball a (2 * δ) ×ˢ Metric.ball 0 R)) :
    ContDiffOn ℂ ∞ (localSprayMap Ψ x) (localSprayDomain a δ R) :=
  hψ.comp sprayInput_contDiff.contDiffOn (fun p hp => hp)

theorem localSpatialDomain_isOpen
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (x : Pt X) {a : CotangentCoord n} {δ R : ℝ}
    (hψ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball a (2 * δ) ×ˢ Metric.ball 0 R)) :
    IsOpen (localSpatialDomain Ψ x a δ R) :=
  (localSprayMap_contDiffOn x hψ).continuousOn.isOpen_inter_preimage
    (localSprayDomain_isOpen a δ R)
    ((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ)

theorem localSpatialKernel_contDiffOn {d : VariationData X q} (hG : CotangentImmersion d.G)
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (x : Pt X) {a : CotangentCoord n} {δ R : ℝ}
    (hψ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball a (2 * δ) ×ˢ Metric.ball 0 R)) :
    ContDiffOn ℝ ∞ (localSpatialKernel d Ψ x) (localSpatialDomain Ψ x a δ R) := by
  have hT := localSprayMap_contDiffOn x hψ
  have hD := (hT.fderiv_of_isOpen (localSprayDomain_isOpen a δ R) (m := ∞) (by simp)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℂ ℂ (SprayData n b)))
  have hDR : ContDiffOn ℝ ∞ (fun p => (localSprayDifferential Ψ x p).restrictScalars ℝ)
      (localSpatialDomain Ψ x a δ R) := by
    apply contDiffOn_clm_apply.mpr
    intro v
    exact ((hD.clm_apply (contDiffOn_const (c := v))).restrict_scalars ℝ).mono Set.inter_subset_left
  exact pullbackBilinear_contDiffOn
    ((spatialChartBilinear_contDiffOn hG x).comp (hT.restrict_scalars ℝ |>.mono Set.inter_subset_left)
      (fun p hp => hp.2)) hDR

set_option synthInstance.maxHeartbeats 100000 in
theorem localSprayDifferential_eq_slice
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (x : Pt X) {a : CotangentCoord n} {δ R : ℝ}
    (hψ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball a (2 * δ) ×ˢ Metric.ball 0 R))
    {p : ℂ × SprayData n b} (hp : p ∈ localSprayDomain a δ R) :
    localSprayDifferential Ψ x p = fderiv ℂ (fun u => localSprayMap Ψ x (p.1, u)) p.2 := by
  have hT := ((localSprayMap_contDiffOn x hψ).contDiffAt
    ((localSprayDomain_isOpen a δ R).mem_nhds hp)).differentiableAt (by simp)
  have hinc : HasFDerivAt (fun u : SprayData n b => (p.1, u))
      (ContinuousLinearMap.inr ℂ ℂ (SprayData n b)) p.2 := by
    convert ((ContinuousLinearMap.inr ℂ ℂ (SprayData n b)).hasFDerivAt
      (x := p.2)).const_add (p.1, 0) using 1 <;> simp
  exact (hT.hasFDerivAt.comp p.2 hinc).fderiv.symm

end Yau.Blueprint.V02AreaTaylorProof
