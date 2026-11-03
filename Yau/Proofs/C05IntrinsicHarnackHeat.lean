import Yau.Proofs.C05IntrinsicInverseEnergySpatialError
import Yau.Proofs.C05NormalizedHarnackTimeDerivatives

/-! The exact intrinsic heat identity of the original normalized Harnack
function, retaining the actual inverse-energy remainder and its vanishing. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
variable {n : ℕ} {M : ComplexManifold n} {ι : Type*}
set_option backward.isDefEq.respectTransparency false

def intrinsicInverseEnergyHeatRemainder (k : HermitianField M) (x : M.Carrier) : ℝ :=
  intrinsicInverseEnergyTime k x - (1/4:ℝ)*
    intrinsicInverseEnergySpatialRemainder k (scalarCurvature k) x

def intrinsicMinimizedHeat (k : HermitianField M) (κ : ℝ) (x : M.Carrier) : ℝ :=
  intrinsicScalarHarnackTime k κ x - intrinsicInverseEnergyTime k x -
    laplacian k (intrinsicHarnackMinimum k κ) x

theorem intrinsicMinimizedHeat_decomposition (k : HermitianField M)
    (hk : MetricSmooth k) (hK : KahlerClosed k) (hA : ∀ y, (ricci k y).PosDef)
    (κ : ℝ) (x : M.Carrier) :
    intrinsicMinimizedHeat k κ x =
      3*ricciLeviPairing k (scalarCurvature k) x + 2*ricciCube k x +
        κ*ricciNormSq k x - κ^2*scalarCurvature k x +
      (1/2:ℝ)*inverseEnergyHessianSquare k (scalarCurvature k) x (chartPt x x) -
        intrinsicInverseEnergyHeatRemainder k x := by
  have hs := scalarCurvature_smoothFn k hk hK
  have hs1 : SmoothFn (scalarTimeSource1 k) := scalarHarnackSource_smoothFn k hk hK 0
  have hsmul : SmoothFn (fun y => κ*scalarCurvature k y) :=
    fun c => contDiffOn_const.mul (hs c)
  have he : scalarHarnackSource k κ = (fun y => scalarTimeSource1 k y + κ*scalarCurvature k y) := by
    funext y
    simp only [scalarHarnackSource,scalarTimeSource1,zero_mul,add_zero]
  have hlap : laplacian k (scalarHarnackSource k κ) x =
      laplacian k (scalarTimeSource1 k) x + κ*laplacian k (scalarCurvature k) x := by
    rw [he,laplacian_add k _ _ hs1 hsmul,laplacian_const_mul k _ hs]
  unfold intrinsicMinimizedHeat intrinsicHarnackMinimum
  rw [laplacian_sub k _ _ (scalarHarnackSource_smoothFn k hk hK κ)
    (realRicciDifferentialEnergy_smoothFn k hk hK hA _ hs),hlap,
    realRicciDifferentialEnergy_laplacian k hk hK hA _ hs]
  dsimp only [intrinsicScalarHarnackTime,scalarTimeSource2,scalarTimeSource1,
    scalarHarnackSource,intrinsicInverseEnergyHeatRemainder,intrinsicInverseEnergySpatialRemainder]
  ring

theorem intrinsicInverseEnergyHeatRemainder_tendsto_zero
    (k : ι → HermitianField M) (hk : ∀ i, MetricSmooth (k i))
    (hK : ∀ i, KahlerClosed (k i)) (hA : ∀ i y, (ricci (k i) y).PosDef)
    (x : M.Carrier) (l : Filter ι) {CA CB CQ : ℝ}
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCQ : 0 ≤ CQ)
    (hC : ∀ᶠ i in l, ∀ j ≤ 2, ricciInverseJetNorm (k i) j x ≤ CA)
    (hB : ∀ᶠ i in l, scalarJetNorm (k i) (scalarCurvature (k i)) 2 x ≤ CB ∧
      scalarJetNorm (k i) (scalarCurvature (k i)) 3 x ≤ CB)
    (hQ : ∀ᶠ i in l, scalarJetNorm (k i) (scalarHarnackSource (k i) 0) 1 x ≤ CQ)
    (hgrad : Tendsto (fun i => scalarJetNorm (k i) (scalarCurvature (k i)) 1 x) l (𝓝 0)) :
    Tendsto (fun i => intrinsicInverseEnergyHeatRemainder (k i) x) l (𝓝 0) := by
  have hc0 := hC.mono (fun i hi => hi 0 (by norm_num))
  have ht := intrinsicInverseEnergyTime_tendsto_zero k hk hK x l hCA hCB hCQ hc0
    (hB.mono (fun _ hi => hi.1)) hQ hgrad
  have hs := intrinsicInverseEnergySpatialRemainder_tendsto_zero k hk hK hA
    (fun i => scalarCurvature (k i)) (fun i => scalarCurvature_smoothFn (k i) (hk i) (hK i))
    x l hCA hCB hC hB hgrad
  simpa only [intrinsicInverseEnergyHeatRemainder,sub_zero,mul_zero] using ht.sub (hs.const_mul (1/4:ℝ))

end Yau.Proofs.C05Aux
