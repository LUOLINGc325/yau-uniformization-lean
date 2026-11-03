import Yau.LeafProofs.L16DeGiorgiOscillation

open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

/-- A strictly slower geometric rate than the actual oscillation contraction,
chosen before any equation fields. -/
theorem dgOsc_choose_exponent {θ : ℝ} (_hθ : 0 < θ) (hθ1 : θ < 1) (hθq : 3/4 ≤ θ) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ θ < (1/4:ℝ)^γ ∧ (1/4:ℝ)^γ < 1 ∧ 1/16 ≤ (1/4:ℝ)^γ := by
  let γ := min (1/2) ((1-θ)/4)
  let q := (1/4:ℝ)^γ
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγ1 : γ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hγθ : γ ≤ (1-θ)/4 := min_le_right _ _
  have hlog : Real.log 4 < 4 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)).trans_lt (by norm_num)
  have hqExp : q = Real.exp (-γ*Real.log 4) := by
    dsimp only [q]
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 1/4),one_div,Real.log_inv]
    congr 1
    ring
  have hLower : 1-γ*Real.log 4 ≤ q := by
    rw [hqExp]
    have hh := Real.add_one_le_exp (-γ*Real.log 4)
    linarith only [hh]
  have hmul := mul_lt_mul_of_pos_left hlog hγ
  have hθq' : θ < q := (by nlinarith only [hγθ,hmul] : θ < 1-γ*Real.log 4).trans_le hLower
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hγ
  have hq16 : (1/16:ℝ) ≤ q := by linarith only [hθq,hθq']
  exact ⟨γ,hγ,hγ1,hθq',hq1,hq16⟩

/-- Numerical widths, with the genuine squared-radius forcing series. -/
def dgOscWidth (θ B width : ℝ) : ℕ → ℝ
  | 0 => width
  | j+1 => θ*dgOscWidth θ B width j+B*(1/16:ℝ)^j

@[simp] theorem dgOscWidth_zero (θ B width : ℝ) : dgOscWidth θ B width 0 = width := rfl
@[simp] theorem dgOscWidth_succ (θ B width : ℝ) (j : ℕ) :
    dgOscWidth θ B width (j+1) = θ*dgOscWidth θ B width j+B*(1/16:ℝ)^j := rfl

theorem dgOscWidth_nonneg {θ B width : ℝ} (hθ : 0 ≤ θ) (hB : 0 ≤ B) (hw : 0 ≤ width) :
    ∀ j, 0 ≤ dgOscWidth θ B width j := by
  intro j
  induction j with
  | zero => exact hw
  | succ j ih => exact add_nonneg (mul_nonneg hθ ih) (mul_nonneg hB (pow_nonneg (by norm_num) _))

theorem dgOscWidth_geometric_bound {θ q B width : ℝ} (hθ : 0 ≤ θ) (hθq : θ < q)
    (hq16 : (1/16:ℝ) ≤ q) (hB : 0 ≤ B) (hw : 0 ≤ width) :
    ∀ j, dgOscWidth θ B width j ≤ q^j*(width+B/(q-θ)) := by
  have hd : 0 < q-θ := sub_pos.mpr hθq
  have hM : 0 ≤ B/(q-θ) := div_nonneg hB hd.le
  have hq : 0 ≤ q := (by norm_num : (0:ℝ) ≤ 1/16).trans hq16
  have hBudget : θ*(width+B/(q-θ))+B ≤ q*(width+B/(q-θ)) := by
    have he : (q-θ)*(B/(q-θ)) = B := mul_div_cancel₀ _ hd.ne'
    have hh := mul_nonneg hd.le hw
    nlinarith only [he,hh]
  intro j
  induction j with
  | zero => simpa only [dgOscWidth_zero,pow_zero,one_mul] using le_add_of_nonneg_right hM
  | succ j ih =>
    have hp : (1/16:ℝ)^j ≤ q^j := pow_le_pow_left₀ (by norm_num) hq16 j
    calc
      _ = θ*dgOscWidth θ B width j+B*(1/16:ℝ)^j := rfl
      _ ≤ θ*(q^j*(width+B/(q-θ)))+B*q^j :=
        add_le_add (mul_le_mul_of_nonneg_left ih hθ) (mul_le_mul_of_nonneg_left hp hB)
      _ = q^j*(θ*(width+B/(q-θ))+B) := by ring
      _ ≤ q^j*(q*(width+B/(q-θ))) := mul_le_mul_of_nonneg_left hBudget (pow_nonneg hq _)
      _ = _ := by rw [pow_succ]; ring

def dgOscQuarterRadius (R : ℝ) (j : ℕ) : ℝ := R*(1/4:ℝ)^j

@[simp] theorem dgOscQuarterRadius_zero (R : ℝ) : dgOscQuarterRadius R 0 = R := by simp [dgOscQuarterRadius]

theorem dgOscQuarterRadius_pos {R : ℝ} (hR : 0 < R) (j : ℕ) : 0 < dgOscQuarterRadius R j := by
  dsimp [dgOscQuarterRadius]
  positivity

theorem dgOscQuarterRadius_le {R : ℝ} (hR : 0 ≤ R) (j : ℕ) : dgOscQuarterRadius R j ≤ R := by
  have hh := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4:ℝ) ≤ 1) (n := j)
  exact (mul_le_mul_of_nonneg_left hh hR).trans_eq (mul_one _)

theorem dgOscQuarterRadius_succ (R : ℝ) (j : ℕ) :
    dgOscQuarterRadius R (j+1) = dgOscQuarterRadius R j/4 := by
  dsimp only [dgOscQuarterRadius]
  rw [pow_succ]
  ring

theorem dgOscQuarterRadius_sq (R : ℝ) (j : ℕ) :
    (dgOscQuarterRadius R j)^2 = R^2*(1/16:ℝ)^j := by
  dsimp only [dgOscQuarterRadius]
  rw [mul_pow,←pow_mul,show j*2 = 2*j by omega,pow_mul]
  norm_num


/-- Genuine interior oscillation from the proved two-measure contraction,
actual parabolic scaling and finite interval-width induction. Constants precede
all fields; arbitrary radii and the terminal time face are retained. -/
theorem dgOsc_interior_oscillation {n : ℕ} (hn : 0 < n) {ν L : ℝ} (hν : 0 < ν) (hνL : ν ≤ L) :
    ∃ γ C : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < C ∧
      ∀ D F : ℝ, 0 ≤ D → 0 ≤ F → ∀ (p₀ : Point n) (R : ℝ), 0 < R → R ≤ dgOscDriftRadius D →
      ∀ (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ),
      DGClassicalFields (dgOscCylinderOpen p₀ R) A c f u → ClassicalDivEq (dgOscCylinderOpen p₀ R) A c f u →
      DGUniformBounds (dgOscCylinderOpen p₀ R) A c f ν L D F → ContinuousOn u (dgOscCylinder p₀ R) →
      ∀ ell width : ℝ, 0 ≤ width → (∀ p ∈ dgOscCylinder p₀ R, ell ≤ u p ∧ u p ≤ ell+width) →
      ∀ r : ℝ, 0 < r → r ≤ R → ∀ p ∈ dgOscCylinder p₀ r, ∀ p' ∈ dgOscCylinder p₀ r,
      |u p-u p'| ≤ C*(r/R)^γ*(width+F*R^2) := by
  obtain ⟨θ,K,hθ,hθ1,hθq,hK,hShrink⟩ := dgOsc_interval_shrink hn hν hνL
  obtain ⟨γ,hγ,hγ1,hθγ,_hq1,hq16⟩ := dgOsc_choose_exponent hθ hθ1 hθq
  let q := (1/4:ℝ)^γ
  let M := K/(q-θ)
  let C := (4:ℝ)^γ*(1+M)
  have hd : 0 < q-θ := sub_pos.mpr hθγ
  have hM : 0 < M := div_pos hK hd
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨γ,C,hγ,hγ1,hC,?_⟩
  intro D F hD hF p₀ R hR hRs A c f u hf hpde hb hu ell width hwidth hRange r hr hrR p hp p' hp'
  let B := K*F*R^2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hW (j : ℕ) : 0 ≤ dgOscWidth θ B width j := dgOscWidth_nonneg hθ.le hB hwidth j
  have hRadPos (j : ℕ) : 0 < dgOscQuarterRadius R j := dgOscQuarterRadius_pos hR j
  have hRadLe (j : ℕ) : dgOscQuarterRadius R j ≤ R := dgOscQuarterRadius_le hR.le j
  have hRanges : ∀ j : ℕ, ∃ a : ℝ, ∀ z ∈ dgOscCylinder p₀ (dgOscQuarterRadius R j),
      a ≤ u z ∧ u z ≤ a+dgOscWidth θ B width j := by
    intro j
    induction j with
    | zero =>
      refine ⟨ell,?_⟩
      simpa only [dgOscQuarterRadius_zero,dgOscWidth_zero] using hRange
    | succ j ih =>
      obtain ⟨a,ha⟩ := ih
      have hSubOpen : dgOscCylinderOpen p₀ (dgOscQuarterRadius R j) ⊆ dgOscCylinderOpen p₀ R :=
        dgOscCylinderOpen_subset (hRadPos j).le (hRadLe j)
      have hSubClosed : dgOscCylinder p₀ (dgOscQuarterRadius R j) ⊆ dgOscCylinder p₀ R :=
        dgOscCylinder_subset (hRadPos j).le (hRadLe j)
      have hNext := hShrink D F hD hF p₀ (dgOscQuarterRadius R j) (hRadPos j) ((hRadLe j).trans hRs)
        A c f u (dgOsc_fields_mono hSubOpen hf) (fun z hz => hpde z (hSubOpen hz))
        (dgOsc_uniform_restrict hSubOpen hb) (hu.mono hSubClosed) a (dgOscWidth θ B width j) (hW j) ha
      simpa only [dgOscQuarterRadius_succ,dgOscWidth_succ,dgOscQuarterRadius_sq,B,mul_assoc] using hNext
  obtain ⟨j,hjLower,hjUpper⟩ := exists_nat_pow_near_of_lt_one (div_pos hr hR)
    ((div_le_one hR).mpr hrR) (by norm_num : (0:ℝ) < 1/4) (by norm_num : (1/4:ℝ) < 1)
  have hrj : r ≤ dgOscQuarterRadius R j := by
    have hh := (div_le_iff₀ hR).mp hjUpper
    simpa only [dgOscQuarterRadius,mul_comm] using hh
  have hNear : (1/4:ℝ)^j ≤ 4*(r/R) := by
    rw [pow_succ] at hjLower
    linarith only [hjLower]
  have hqPow : q^j = ((1/4:ℝ)^j)^γ := by
    dsimp only [q]
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 1/4) γ j,
      mul_comm γ (j:ℝ),Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 1/4) j γ]
  have hPower : q^j ≤ (4:ℝ)^γ*(r/R)^γ := by
    rw [hqPow]
    calc
      _ ≤ (4*(r/R))^γ := Real.rpow_le_rpow (pow_nonneg (by norm_num) _) hNear hγ.le
      _ = _ := Real.mul_rpow (by norm_num) (div_nonneg hr.le hR.le)
  obtain ⟨a,ha⟩ := hRanges j
  have hpr := ha p (dgOscCylinder_subset hr.le hrj hp)
  have hp'r := ha p' (dgOscCylinder_subset hr.le hrj hp')
  have hPair : |u p-u p'| ≤ dgOscWidth θ B width j := abs_le.mpr
    ⟨by linarith only [hp'r.2,hpr.1],by linarith only [hpr.2,hp'r.1]⟩
  have hAmpEq : width+B/(q-θ) = width+M*F*R^2 := by dsimp only [B,M]; ring
  have hAmp0 : 0 ≤ width+M*F*R^2 := by positivity
  have hAmp : width+M*F*R^2 ≤ (1+M)*(width+F*R^2) := by
    have hh := mul_nonneg hM.le hwidth
    have hF0 := mul_nonneg hF (sq_nonneg R)
    nlinarith only [hh,hF0]
  calc
    _ ≤ dgOscWidth θ B width j := hPair
    _ ≤ q^j*(width+B/(q-θ)) := dgOscWidth_geometric_bound hθ.le hθγ hq16 hB hwidth j
    _ = q^j*(width+M*F*R^2) := by rw [hAmpEq]
    _ ≤ ((4:ℝ)^γ*(r/R)^γ)*(width+M*F*R^2) := mul_le_mul_of_nonneg_right hPower hAmp0
    _ ≤ ((4:ℝ)^γ*(r/R)^γ)*((1+M)*(width+F*R^2)) :=
      mul_le_mul_of_nonneg_left hAmp (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (div_nonneg hr.le hR.le) _))
    _ = _ := by dsimp only [C]; ring

end Yau.LeafProofs.L16Aux
