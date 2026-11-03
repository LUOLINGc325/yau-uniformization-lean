import Yau.Proofs.V02WallTaylorOrdinaryScalar
import Yau.Proofs.V02WallTaylorWithinSlice
import Yau.Proofs.V02WallTaylorPersistence
import Yau.Proofs.V02WallTaylorChartFactorSmooth

/-! Independent parameter data for the actual ordinary boundary scalar.
The physical time remains in its original closed one-sided interval. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n q b : ℕ} {X : KahlerManifold n}

abbrev OrdinaryAux (n b : ℕ) := ChartFactorAux n b × ℝ

def ordinarySprayCoordinate (d : VariationData X q) (j a : ℕ) (x : Pt X)
    (p : ℂ × OrdinaryAux n b) : CotangentCoord n × (Fin b → ℂ) :=
  (p.2.1.1, wallPower d j a (cotangentChartInv x p.2.1.1) •
    chartFactorDirection (p.1, p.2.1))

def ordinaryJetDomain (d : VariationData X q) (j a : ℕ)
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (x : Pt X) (A : CotangentCoord n) (δ R : ℝ) : Set (ℂ × OrdinaryAux n b) :=
  (Set.univ ×ˢ (Set.univ ×ˢ Set.Icc 0 d.T)) ∩
    (ordinarySprayCoordinate d j a x) ⁻¹'
      ((Metric.ball A (2 * δ) ×ˢ Metric.ball 0 R) ∩
        (sprayCoordinate Ψ x) ⁻¹' cotangentTarget x)

def ordinaryJetFunction (d : VariationData X q) (j a : ℕ)
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (x : Pt X) (p : ℂ × OrdinaryAux n b) : ℝ :=
  sprayOrdinaryScalar d j Ψ x (ordinarySprayCoordinate d j a x p, p.2.2)


theorem ordinarySprayCoordinate_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (x : Pt X) {A : CotangentCoord n} {δ : ℝ}
    (hvalid : Metric.ball A (2 * δ) ⊆ cotangentTarget x) :
    ContDiffOn ℝ ∞ (ordinarySprayCoordinate d j a x)
      {p : ℂ × OrdinaryAux n b | p.2.1.1 ∈ Metric.ball A (2 * δ)} := by
  have hU : ContDiff ℝ ∞ (fun p : ℂ × OrdinaryAux n b => p.2.1.1) :=
    contDiff_fst.comp (contDiff_fst.comp contDiff_snd)
  have hP : ContDiff ℝ ∞ (fun p : ℂ × OrdinaryAux n b => (p.1, p.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hm := ((wallPower_chart_contDiffOn hd j a x).mono hvalid).comp hU.contDiffOn (fun _ hp => hp)
  exact hU.contDiffOn.prodMk (hm.smul (chartFactorDirection_contDiff.comp hP).contDiffOn)

theorem isOpen_ordinary_spatial_domain {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (x : Pt X) {A : CotangentCoord n} {δ R : ℝ}
    (hvalid : Metric.ball A (2 * δ) ⊆ cotangentTarget x)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball A (2 * δ) ×ˢ Metric.ball 0 R)) :
    IsOpen ((ordinarySprayCoordinate d j a x) ⁻¹'
      ((Metric.ball A (2 * δ) ×ˢ Metric.ball 0 R) ∩
        (sprayCoordinate Ψ x) ⁻¹' cotangentTarget x)) := by
  apply (ordinarySprayCoordinate_contDiffOn hd j a x hvalid).continuousOn.isOpen_preimage
  · exact isOpen_ball.preimage ((continuous_fst.comp continuous_fst).comp continuous_snd)
  · intro p hp
    exact hp.1.1
  · exact isOpen_sprayScalar_domain (isOpen_ball.prod isOpen_ball) hΨ

theorem ordinaryJetDomain_uniqueDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (x : Pt X) {A : CotangentCoord n} {δ R : ℝ}
    (hvalid : Metric.ball A (2 * δ) ⊆ cotangentTarget x)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball A (2 * δ) ×ˢ Metric.ball 0 R)) :
    UniqueDiffOn ℝ (ordinaryJetDomain d j a Ψ x A δ R) :=
  (uniqueDiffOn_univ.prod (uniqueDiffOn_univ.prod (uniqueDiffOn_Icc hd.1))).inter
    (isOpen_ordinary_spatial_domain hd j a x hvalid hΨ)

theorem ordinaryJetDomain_slice {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (x : Pt X) {A : CotangentCoord n} {δ R : ℝ}
    (hvalid : Metric.ball A (2 * δ) ⊆ cotangentTarget x)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball A (2 * δ) ×ˢ Metric.ball 0 R))
    {p : ℂ × OrdinaryAux n b} (hp : p ∈ ordinaryJetDomain d j a Ψ x A δ R) :
    {z : ℂ | (z, p.2) ∈ ordinaryJetDomain d j a Ψ x A δ R} ∈ 𝓝 p.1 := by
  have hW := isOpen_ordinary_spatial_domain hd j a x hvalid hΨ
  have hh := (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hW.mem_nhds hp.2)
  filter_upwards [hh] with z hz
  exact ⟨⟨Set.mem_univ _, hp.1.2⟩, hz⟩

theorem ordinaryJetFunction_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (x : Pt X) {A : CotangentCoord n} {δ R : ℝ}
    (hvalid : Metric.ball A (2 * δ) ⊆ cotangentTarget x)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball A (2 * δ) ×ˢ Metric.ball 0 R)) :
    ContDiffOn ℝ ∞ (ordinaryJetFunction d j a Ψ x) (ordinaryJetDomain d j a Ψ x A δ R) := by
  have hcoord := (ordinarySprayCoordinate_contDiffOn hd j a x hvalid).mono
    (show ordinaryJetDomain d j a Ψ x A δ R ⊆
      {p : ℂ × OrdinaryAux n b | p.2.1.1 ∈ Metric.ball A (2 * δ)} from fun _ hp => hp.2.1.1)
  have ht : ContDiffOn ℝ ∞ (fun p : ℂ × OrdinaryAux n b => p.2.2)
      (ordinaryJetDomain d j a Ψ x A δ R) := (contDiff_snd.comp contDiff_snd).contDiffOn
  exact (sprayOrdinaryScalar_contDiffOn hd j hΨ).comp (hcoord.prodMk ht)
    (fun _ hp => ⟨hp.2, hp.1.2.2⟩)

end Yau.Blueprint.V02WallTaylorProof
