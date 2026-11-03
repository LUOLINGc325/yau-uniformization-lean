import Yau.LeafProofs.L05PerturbationVariableHolder

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbBaseData {n : ℕ} (ell L : ℝ)
    (Phi : Sym n → Point n → ℝ) (f u : Point n → ℝ) : Prop :=
  ContinuousOn (fun z : Sym n × Point n => Phi z.1 z.2) (univ ×ˢ backward 1) ∧
  (∀ p∈backward 1, globalElliptic (fun H => Phi H p) ell L) ∧
  (∀ p∈backward 1, ConcaveOn ℝ univ (fun H => Phi H p)) ∧
  Phi 0 (0,0)=0 ∧ f (0,0)=0 ∧ C2 (backward 1) u ∧
  (∀ p∈backward 1, |u p| ≤ 1) ∧
  (∀ p∈backward 1, timeD (backward 1) u p-Phi (hessian u p) p=f p)

def perturbSmallData {n : ℕ} (ell L delta : ℝ)
    (Phi : Sym n → Point n → ℝ) (f u : Point n → ℝ) : Prop :=
  perturbBaseData ell L Phi f u ∧
  (∀ H : Sym n, ∀ p∈backward 1, |Phi H p-Phi H (0,0)| ≤ delta*(1+‖H‖)) ∧
  (∀ p∈backward 1, |f p| ≤ delta)

def perturbHolderData {n : ℕ} (ell L alpha beta mu af : ℝ)
    (Phi : Sym n → Point n → ℝ) (f u : Point n → ℝ) : Prop :=
  perturbBaseData ell L Phi f u ∧
  (∀ H : Sym n, ∀ p∈backward 1, ∀ q∈backward 1,
    |Phi H p-Phi H q| ≤ mu*(1+‖H‖)*holderWeight beta p q) ∧
  (∀ p∈backward 1, ∀ q∈backward 1, |f p-f q| ≤ af*holderWeight alpha p q)

theorem perturb_small_data_holder {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ kappa : ℝ, 0 < kappa ∧ kappa < 1 ∧ ∀ delta : ℝ, 0 ≤ delta → delta ≤ 1 →
      ∀ (Phi : Sym n → Point n → ℝ) (f u : Point n → ℝ),
      perturbSmallData ell L delta Phi f u →
      HolderBound kappa (perturbClosed (0 : Space n) (1/2) 0) u 100 := by
  obtain ⟨kappa,hk0,hk1,hHolder⟩ := perturb_variable_equation_holder hn hell hL
  refine ⟨kappa,hk0,hk1,?_⟩
  intro delta hd0 hd1 Phi f u hData
  rcases hData with ⟨⟨_,hE,_,hPhi0,_,hu,hSup,hPDE⟩,hCoeff,hf⟩
  exact hHolder delta hd0 hd1 Phi hE hPhi0 hCoeff u f hu hSup hf hPDE

end Yau.LeafProofs.L05Aux
