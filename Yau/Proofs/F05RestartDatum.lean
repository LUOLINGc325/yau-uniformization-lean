import Yau.Proofs.F05SmoothTimeJets
import Yau.Proofs.F05SmoothSlices

/-! A real smooth restart datum: it agrees with the prescribed lateral
data and corrects exactly its initial time jet. Only a smooth spatial
extension of the actual terminal profile is needed. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05RestartDatum (τ S : ℝ) (p : M.Carrier → ℝ → ℝ) (g J : M.Carrier → ℝ) :
    M.Carrier → ℝ → ℝ := fun x s => p x (s+τ)+g x-p x τ+
      s*(J x-derivWithin (p x) (Icc τ (τ+S)) τ)

theorem F05_restart_initial (τ S : ℝ) (p : M.Carrier → ℝ → ℝ) (g J : M.Carrier → ℝ)
    (x : M.Carrier) : F05RestartDatum τ S p g J x 0 = g x := by
  simp only [F05RestartDatum,zero_add,zero_mul,add_zero]
  ring

theorem F05_restart_lateral {B : Set M.Carrier} {τ S : ℝ} (p : M.Carrier → ℝ → ℝ)
    (g J : M.Carrier → ℝ) (hTrace : EqOn g (fun x => p x τ) B)
    (hJet : EqOn J (fun x => derivWithin (p x) (Icc τ (τ+S)) τ) B)
    {x : M.Carrier} (hx : x ∈ B) (s : ℝ) :
    F05RestartDatum τ S p g J x s = p x (s+τ) := by
  simp only [F05RestartDatum,hTrace hx,hJet hx,sub_self,mul_zero,add_zero,add_sub_cancel_right]

theorem F05_restart_time_jet {τ S : ℝ} (hS : 0 < S) (p : M.Carrier → ℝ → ℝ)
    (g J : M.Carrier → ℝ) {x : M.Carrier}
    (hp : DifferentiableWithinAt ℝ (p x) (Icc τ (τ+S)) τ) :
    derivWithin (F05RestartDatum τ S p g J x) (Icc 0 S) 0 = J x := by
  have hMap : MapsTo (fun s : ℝ => s+τ) (Icc 0 S) (Icc τ (τ+S)) := by
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  have hP : HasDerivWithinAt (p x) (derivWithin (p x) (Icc τ (τ+S)) τ)
      (Icc τ (τ+S)) (0+τ) := by simpa only [zero_add] using hp.hasDerivWithinAt
  have hShift := hP.comp (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).add_const τ).hasDerivWithinAt hMap
  have hLinear := ((hasDerivAt_id (0 : ℝ)).mul_const
    (J x-derivWithin (p x) (Icc τ (τ+S)) τ)).hasDerivWithinAt (s := Icc 0 S)
  have h := (((hShift.add_const (g x)).sub_const (p x τ)).add hLinear).derivWithin
    (uniqueDiffOn_Icc hS 0 ⟨le_rfl,hS.le⟩)
  convert! h using 1 <;> simp only [zero_add,one_mul,mul_one] <;> ring

theorem F05_restart_datum_smooth {τ S : ℝ} (hS : 0 < S) (p : M.Carrier → ℝ → ℝ)
    (g J : M.Carrier → ℝ) (hp : SmoothSpaceTime p (Icc τ (τ+S)))
    (hg : SmoothFn g) (hJ : SmoothFn J) :
    SmoothSpaceTime (F05RestartDatum τ S p g J) (Icc 0 S) := by
  have hD : SmoothFn (fun x => derivWithin (p x) (Icc τ (τ+S)) τ) := by
    intro x
    have hTime := F05_joint_time_derivative_smooth
      (uniqueDiffOn_Icc (by linarith : τ < τ+S)) (hp x)
    exact hTime.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun z hz => ⟨hz,le_rfl,by linarith⟩)
  intro x
  have hShift : ContDiffOn ℝ ∞ (fun q : ComplexVector n × ℝ => p (chartInv x q.1) (q.2+τ))
      (chartTarget x ×ˢ Icc 0 S) :=
    (hp x).comp (contDiffOn_fst.prodMk (contDiffOn_snd.add contDiffOn_const))
      (fun q hq => ⟨hq.1,by linarith [hq.2.1],by linarith [hq.2.2]⟩)
  have hG : ContDiffOn ℝ ∞ (fun q : ComplexVector n × ℝ => g (chartInv x q.1))
      (chartTarget x ×ˢ Icc 0 S) := (hg x).comp contDiffOn_fst (fun q hq => hq.1)
  have hP0 : ContDiffOn ℝ ∞ (fun q : ComplexVector n × ℝ => p (chartInv x q.1) τ)
      (chartTarget x ×ˢ Icc 0 S) := (hp x).comp (contDiffOn_fst.prodMk contDiffOn_const)
    (fun q hq => ⟨hq.1,le_rfl,by linarith⟩)
  have hJs : ContDiffOn ℝ ∞ (fun q : ComplexVector n × ℝ => J (chartInv x q.1))
      (chartTarget x ×ˢ Icc 0 S) := (hJ x).comp contDiffOn_fst (fun q hq => hq.1)
  have hDs : ContDiffOn ℝ ∞ (fun q : ComplexVector n × ℝ =>
      derivWithin (p (chartInv x q.1)) (Icc τ (τ+S)) τ)
      (chartTarget x ×ˢ Icc 0 S) := (hD x).comp contDiffOn_fst (fun q hq => hq.1)
  exact ((hShift.add hG).sub hP0).add (contDiffOn_snd.mul (hJs.sub hDs))

end Yau.Proofs.F05Aux
