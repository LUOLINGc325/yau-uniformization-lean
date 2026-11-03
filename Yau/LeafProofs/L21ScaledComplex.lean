import Yau.LeafProofs.L21FirstOrderCalculus
import Yau.LeafProofs.L21BoundaryWeight
import Yau.LeafProofs.L21CompactTests

/-! The degenerate first-order complex is the literal scaled graph
operator. Its smooth composition vanishes by the actual Maurer--Cartan
equations proved from the original Nijenhuis tensor. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem rowApply_const_add_mul {ι : Type*} [Fintype ι]
    (v : ι → X n) (p : ι → X n → ℂ) (c d : ℂ)
    {g : X n → ℂ} {x : X n} (hg : DifferentiableAt ℝ g x) :
    rowApply v p (fun y => c + g y * d) x = rowApply v p g x * d := by
  have hd : fderiv ℝ (fun y => c + g y * d) x = d • fderiv ℝ g x := by
    simpa only [zero_add] using
      ((hasFDerivAt_const c x).fun_add (hg.hasFDerivAt.mul_const d)).fderiv
  simp only [rowApply, hd, _root_.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem dbarA_coefficient_row
    (A : X n → Matrix (Fin n) (Fin n) ℂ) {x : X n}
    (hA : ∀ i k, DifferentiableAt ℝ (fun y => A y i k) x)
    (i j : Fin n) (b : Yau.RIdx n) :
    rowApply Yau.realVec (dbarRealCoefficient A i) (dbarRealCoefficient A j b) x =
      dbarA A i (fun y => A y j b.1) x * wirtRealCoefficient b.2 := by
  change rowApply Yau.realVec (dbarRealCoefficient A i)
    (fun y => (if b.1 = j then wirtBarRealCoefficient b.2 else 0) +
      A y j b.1 * wirtRealCoefficient b.2) x = _
  rw [rowApply_const_add_mul Yau.realVec (dbarRealCoefficient A i)
    (if b.1 = j then wirtBarRealCoefficient b.2 else 0) (wirtRealCoefficient b.2) (hA j b.1)]
  congr 1
  exact (dbarA_eq_real_rows A i (fun y => A y j b.1) x).symm

theorem dbarA_commutes_of_maurerCartan {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hMC : CommutesOn A O) {f : X n → ℂ} {x : X n} (hx : x ∈ O)
    (hf : ContDiffAt ℝ ∞ f x) (i j : Fin n) :
    dbarA A i (dbarA A j f) x = dbarA A j (dbarA A i f) x := by
  have hdA (r k : Fin n) := ((hA r k).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hdP (r : Fin n) (b : Yau.RIdx n) :=
    ((dbarRealCoefficient_smoothOn hA r b).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hc (b : Yau.RIdx n) :
      rowApply Yau.realVec (dbarRealCoefficient A i) (dbarRealCoefficient A j b) x -
        rowApply Yau.realVec (dbarRealCoefficient A j) (dbarRealCoefficient A i b) x = 0 := by
    rw [dbarA_coefficient_row A hdA, dbarA_coefficient_row A hdA, hMC x hx i j b.1, sub_self]
  have hh := rowApply_commutator Yau.realVec (dbarRealCoefficient A i) (dbarRealCoefficient A j)
    (hdP i) (hdP j) hf
  simp only [hc, zero_mul, Finset.sum_const_zero] at hh
  have he (r : Fin n) (g : X n → ℂ) : rowApply Yau.realVec (dbarRealCoefficient A r) g = dbarA A r g := by
    funext y
    exact (dbarA_eq_real_rows A r g y).symm
  simp only [he] at hh
  exact sub_eq_zero.mp hh

def scaledGraphD (s : X n → ℂ) (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (f : X n → ℂ) (x : X n) (i : Fin n) : ℂ :=
  s x * dbarA A i f x

def scaledGraphCurl (s : X n → ℂ) (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (v : X n → Fin n → ℂ) (x : X n) (i j : Fin n) : ℂ :=
  s x * (dbarA A i (fun y => v y j) x - dbarA A j (fun y => v y i) x) -
    dbarA A i s x * v x j + dbarA A j s x * v x i

theorem scaledGraphCurl_scaledGraphD {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {s f : X n → ℂ} (hs : ContDiffOn ℝ ∞ s O) (hf : ContDiffOn ℝ ∞ f O)
    {x : X n} (hx : x ∈ O) (i j : Fin n) :
    scaledGraphCurl s A (scaledGraphD s A f) x i j =
      s x ^ 2 * (dbarA A i (dbarA A j f) x - dbarA A j (dbarA A i f) x) := by
  have hds := (hs.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hdD (r : Fin n) :=
    ((contDiffOn_dbarA hO hA r hf).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  simp only [scaledGraphCurl, scaledGraphD, dbarA_mul A i hds (hdD j),
    dbarA_mul A j hds (hdD i)]
  ring

def degenerateT (A : X n → Matrix (Fin n) (Fin n) ℂ) (f : X n → ℂ) :=
  scaledGraphD (fun x => (rho x : ℂ)) A f

def degenerateS (A : X n → Matrix (Fin n) (Fin n) ℂ) (v : X n → Fin n → ℂ) :=
  scaledGraphCurl (fun x => (rho x : ℂ)) A v

theorem degenerateS_degenerateT_eq_zero {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hMC : CommutesOn A O) {f : X n → ℂ} (hf : ContDiffOn ℝ ∞ f O)
    {x : X n} (hx : x ∈ O) (i j : Fin n) :
    degenerateS A (degenerateT A f) x i j = 0 := by
  have hs : ContDiffOn ℝ ∞ (fun x : X n => (rho x : ℂ)) O :=
    (Complex.ofRealCLM.contDiff.comp contDiff_rho).contDiffOn
  rw [degenerateS, degenerateT, scaledGraphCurl_scaledGraphD hO hA hs hf hx i j,
    dbarA_commutes_of_maurerCartan hO hA hMC hx (hf.contDiffAt (hO.mem_nhds hx)),
    sub_self, mul_zero]

end Yau.LeafProofs.L21Aux
