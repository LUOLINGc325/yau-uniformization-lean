import Yau.Proofs.V04SymplecticScalarDescent
import Yau.Proofs.V04ClockRegularity
import Yau.Proofs.V03ClearedBoundaryTensor

/-! The original symplectic Hessian scalar is continuous on every disc
circle. A fixed valid chart and the actual cleared tensor prove this;
moving-centered matrix entries are never assumed continuous. -/

open Filter
open scoped Matrix Topology ContDiff ComplexOrder Manifold
noncomputable section
namespace Yau.Blueprint.V04Proof.ClockErrorAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.Blueprint.V04Proof
open PositiveReplacementAux

variable {n q : ℕ} {X : KahlerManifold n}

theorem bivectorCost_contDiffAt {A : ℝ → CotangentMatrix n} {θ₀ : ℝ}
    (hA : ∀ i j, ContDiffAt ℝ ∞ (fun θ => A θ i j) θ₀) (J : CotangentMatrix n) :
    ContDiffAt ℝ ∞ (fun θ => bivectorCost (A θ) J) θ₀ := by
  have hs : ContDiffAt ℝ ∞ (fun θ => ∑ i, ∑ j, ∑ k, ∑ l,
      J i j * star (J k l) * A θ k i * A θ l j) θ₀ := by
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    apply ContDiffAt.sum
    intro k _
    apply ContDiffAt.sum
    intro l _
    exact (contDiffAt_const.mul (hA k i)).mul (hA l j)
  exact contDiffAt_const.mul (Complex.reCLM.contDiff.contDiffAt.comp θ₀ hs)

theorem boundarySymplectic_eq_cleared {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    (θ : ℝ) (x : X.manifold.Carrier) (hy : F.f (circlePoint θ) ∈ cotangentSource x) :
    symplecticP (boundaryHessian d j F (circlePoint θ)) =
      (wallPower d j 4 (F.f (circlePoint θ)) ^ 4)⁻¹ *
        bivectorCost (clearedBoundaryTensor d j 4 x
          ((cotangentChart x (F.f (circlePoint θ)), discTime F (circlePoint θ)), F.s))
            canonicalBivector := by
  have hz := cotangentChart_mapsTo x hy
  have hround := cotangentChart_left_inv x hy
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  have ht' : discTime F (circlePoint θ) ∈ Set.Icc 0 d.extendedT :=
    ⟨ht.1.le, ht.2.le.trans hd.2.1.le⟩
  have hp := setup_wallProfiles hd
  have hyreg := hF.2.2.2.2.2.2.2.1 θ
  have hb : deltaBase d j (cotangentChartInv x (cotangentChart x (F.f (circlePoint θ)))).1 ≠ 0 := by
    rw [hround]
    exact (deltaBase_pos hp (setup_index_bounds hd j).1 hyreg.1).ne'
  have hf : deltaFiber d j (cotangentChartInv x (cotangentChart x (F.f (circlePoint θ)))) ≠ 0 := by
    rw [hround]
    exact (deltaFiber_pos hp (setup_index_bounds hd j).2 hyreg.2).ne'
  have hcost := boundaryCost_fixed_chart_contDiffAt hd j x hz ht' F.s hb hf
  have hclear := clearedBoundaryTensor_eq hd j 4 (by norm_num) x hz ht' F.s hb hf
  rw [hround] at hclear
  rw [boundarySymplectic_fixed_chart hd hF θ x hy, hclear,
    bivectorCost_real_smul (wallPower d j 4 (F.f (circlePoint θ)) ^ 2),
    bivectorCost_canonical _ (leviMatrix_isHermitian hcost cotangentDir)]
  have hM : wallPower d j 4 (F.f (circlePoint θ)) ^ 4 ≠ 0 :=
    (pow_pos (admissible_wallPower_bounds hd hF 4 θ).1 4).ne'
  have hpow : (wallPower d j 4 (F.f (circlePoint θ)) ^ 2) ^ 2 =
      wallPower d j 4 (F.f (circlePoint θ)) ^ 4 := by ring
  rw [hpow, ← mul_assoc, inv_mul_cancel₀ hM, one_mul]

theorem boundarySymplectic_continuous {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    Continuous (fun θ => symplecticP (boundaryHessian d j F (circlePoint θ))) := by
  have hwall : ContDiff ℝ ∞ (fun θ => wallPower d j 4 (F.f (circlePoint θ))) :=
    closedDisc_real_trace_contDiff ((cotangentDisc_wallProduct_contDiffOn hd j hF.1).pow 4)
  have hinv : Continuous (fun θ => (wallPower d j 4 (F.f (circlePoint θ)) ^ 4)⁻¹) :=
    ((hwall.pow 4).inv (fun θ => (pow_pos (admissible_wallPower_bounds hd hF 4 θ).1 4).ne')).continuous
  rw [continuous_iff_continuousAt]
  intro θ₀
  let x := (F.f (circlePoint θ₀)).1
  have hself : F.f (circlePoint θ₀) ∈ cotangentSource x := mem_extChartAt_source x
  have hz := cotangentChart_mapsTo x hself
  have hcoord : ContDiffAt ℝ ∞ (fun θ => cotangentChart x (F.f (circlePoint θ))) θ₀ := by
    have hc := ((cotangentDisc_coords_contDiffWithinAt hF.1
      (circlePoint_mem_closedBall θ₀) x hself).restrict_scalars ℝ).comp θ₀
      circlePoint_contDiff.contDiffAt.contDiffWithinAt
      (fun θ (_ : θ ∈ (Set.univ : Set ℝ)) => circlePoint_mem_closedBall θ)
    exact contDiffWithinAt_univ.mp hc
  let p : ℝ → (CotangentCoord n × ℝ) × ℝ :=
    fun θ => ((cotangentChart x (F.f (circlePoint θ)), discTime F (circlePoint θ)), F.s)
  have hmap : ContDiffAt ℝ ∞ p θ₀ :=
    (hcoord.prodMk (admissible_discTime_trace_contDiff hF).contDiffAt).prodMk contDiffAt_const
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ₀)
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hdom : ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ) ∈ 𝓝 (p θ₀) :=
    prod_mem_nhds (prod_mem_nhds (hopen.mem_nhds hz)
      (Icc_mem_nhds ht.1 (ht.2.trans hd.2.1))) Filter.univ_mem
  have hA (i l : CotangentIndex n) : ContDiffAt ℝ ∞
      (fun θ => clearedBoundaryTensor d j 4 x (p θ) i l) θ₀ :=
    (((clearedBoundaryTensor_entry_contDiffOn hd j 4 x i l).contDiffAt hdom).comp θ₀ hmap)
  have hmodel := hinv.continuousAt.mul (bivectorCost_contDiffAt hA canonicalBivector).continuousAt
  have hbase : Continuous (fun θ => (F.f (circlePoint θ)).1) :=
    hF.1.1.continuousOn.comp_continuous circlePoint_contDiff.continuous circlePoint_mem_closedBall
  have hsource : ∀ᶠ θ in 𝓝 θ₀, F.f (circlePoint θ) ∈ cotangentSource x :=
    hbase.continuousAt.eventually ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hself)
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [hsource] with θ hθ
  exact boundarySymplectic_eq_cleared hd hF θ x hθ

end Yau.Blueprint.V04Proof.ClockErrorAux
