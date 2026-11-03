import Yau.LeafProofs.L23DistanceEnergyVariation

/-! Radial first and second jets give the true variation fields and their connection derivatives. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem mapDirection_fst_eq_deriv (Z : ℝ × ℝ → V) {r u : ℝ}
    (hZ : DifferentiableAt ℝ Z (r,u)) :
    mapDirection Z (1,0) (r,u)=deriv (fun s => Z (s,u)) r := by
  have H := hZ.hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r u))
  exact H.deriv.symm

theorem mapDirection_snd_eq_deriv (Z : ℝ × ℝ → V) {r u : ℝ}
    (hZ : DifferentiableAt ℝ Z (r,u)) :
    mapDirection Z (0,1) (r,u)=deriv (fun s => Z (r,s)) u := by
  have H := hZ.hasFDerivAt.comp_hasDerivAt u
    ((hasDerivAt_const u r).prodMk (hasDerivAt_id u))
  exact H.deriv.symm

theorem mapDirection_fst_second_eq_deriv (Z : ℝ × ℝ → V) {r u : ℝ}
    (hZ : ContDiffAt ℝ 2 Z (r,u)) :
    mapDirection (mapDirection Z (1,0)) (1,0) (r,u)=
      deriv (deriv (fun s => Z (s,u))) r := by
  have hD : DifferentiableAt ℝ (mapDirection Z (1,0)) (r,u) :=
    (mapDirection_hasFDerivAt Z hZ (1,0)).differentiableAt
  rw [mapDirection_fst_eq_deriv _ hD]
  have hnear : ∀ᶠ s in 𝓝 r, ContDiffAt ℝ 2 Z (s,u) :=
    (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hZ.eventually (by norm_num))
  have heq : (fun s => mapDirection Z (1,0) (s,u))=ᶠ[𝓝 r] deriv (fun s => Z (s,u)) :=
    hnear.mono (fun s hs => mapDirection_fst_eq_deriv Z (hs.differentiableAt (by norm_num)))
  exact heq.deriv_eq

theorem mapCovariantD_snd_zero_of_line
    (Γ : V → V →L[ℝ] V →L[ℝ] V) (Z W : ℝ × ℝ → V) {r u : ℝ}
    (hW : DifferentiableAt ℝ W (r,u)) (hzero : (fun s => W (r,s))=ᶠ[𝓝 u] (fun _ => 0)) :
    mapCovariantD Γ Z (0,1) W (r,u)=0 := by
  unfold mapCovariantD
  have hv : W (r,u)=0 := hzero.self_of_nhds
  rw [mapDirection_snd_eq_deriv W hW,hzero.deriv_eq,hv,deriv_const]
  simp

theorem mapCovariantD_linear_parallelVariation
    (Γ : V → V →L[ℝ] V →L[ℝ] V) (Z : ℝ × ℝ → V) {u : ℝ}
    (hZ : ContDiffAt ℝ 2 Z (0,u)) (P : ℝ → V)
    (hP : HasDerivAt P (-Γ (Z (0,u)) (mapDirection Z (0,1) (0,u)) (P u)) u)
    (hJ : (fun s => mapDirection Z (1,0) (0,s))=ᶠ[𝓝 u] (fun s => s • P s)) :
    mapCovariantD Γ Z (0,1) (mapDirection Z (1,0)) (0,u)=P u := by
  have hD : DifferentiableAt ℝ (mapDirection Z (1,0)) (0,u) :=
    (mapDirection_hasFDerivAt Z hZ (1,0)).differentiableAt
  have hJP : HasDerivAt (fun s => s • P s)
      (P u+u • (-Γ (Z (0,u)) (mapDirection Z (0,1) (0,u)) (P u))) u := by
    have H := (hasDerivAt_id u).smul hP
    change HasDerivAt (fun s => s • P s)
      (u • (-Γ (Z (0,u)) (mapDirection Z (0,1) (0,u)) (P u))+1 • P u) u at H
    simpa only [one_smul,add_comm] using H
  unfold mapCovariantD
  have hJval : mapDirection Z (1,0) (0,u)=u • P u := hJ.self_of_nhds
  rw [mapDirection_snd_eq_deriv _ hD,hJ.deriv_eq,hJP.deriv,hJval]
  simp only [map_smul,smul_neg]
  abel

variable {n : ℕ} {M : ComplexManifold n}
open L12Aux

theorem mapCovariantD_radialAcceleration_zero
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (Z : ℝ × ℝ → ComplexVector n) {u : ℝ} (hz : Z (0,u)∈chartTarget c)
    (hZ : ContDiffAt ℝ 3 Z (0,u))
    (hRadial : ∀ᶠ s in 𝓝 u,
      deriv (deriv (fun r => Z (r,s))) 0=
        -chartChristoffelBilin h c (Z (0,s)) (mapDirection Z (1,0) (0,s))
          (mapDirection Z (1,0) (0,s))) :
    mapCovariantD (chartChristoffelBilin h c) Z (0,1)
      (mapCovariantD (chartChristoffelBilin h c) Z (1,0) (mapDirection Z (1,0))) (0,u)=0 := by
  have hJ : ContDiffAt ℝ 2 (mapDirection Z (1,0)) (0,u) := mapDirection_contDiffAt Z 2 hZ (1,0)
  have hK : DifferentiableAt ℝ
      (mapCovariantD (chartChristoffelBilin h c) Z (1,0) (mapDirection Z (1,0))) (0,u) :=
    (mapCovariantD_contDiffAt h hh c Z _ hz 1 (hZ.of_le (by norm_num)) hJ (1,0)).differentiableAt_one
  apply mapCovariantD_snd_zero_of_line _ Z _ hK
  have hnear : ∀ᶠ s in 𝓝 u, ContDiffAt ℝ 2 Z (0,s) :=
    (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
      ((hZ.of_le (by norm_num : (2 : ℕ∞ω)≤3)).eventually (by norm_num))
  filter_upwards [hRadial,hnear] with s hs hsZ
  simp only [mapCovariantD,mapDirection_fst_second_eq_deriv Z hsZ,hs,neg_add_cancel]

end Yau.LeafProofs.L23Aux
