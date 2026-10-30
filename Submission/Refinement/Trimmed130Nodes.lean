module

public import Submission.Refinement.InverseImageWeights
public import Submission.Refinement.Trimmed130Branches
public import Submission.Refinement.Trimmed130Support
public import Submission.Refinement.Trimmed130PolynomialCap
public import Submission.Refinement.Trimmed130Scalars
public import Submission.Refinement.Sharp130Circle
public import Submission.CatalanMeasure.GenD.D58.OddProfile

@[expose] public section

namespace CatalanMeasure.GenD.Refinement.Trimmed130

open Analytic Set OAI.InternalCatalan CatalanMeasure.Improvement.Fields
open CatalanMeasure.Refinement.Trimmed130

noncomputable def tau (N : ℕ) : Fin ((D58.Odd.design.n0 - D58.Odd.design.g0) * N) → ℝ :=
  inverseQuadratureNodes D58.Odd.design branchCertificate (by decide) N

theorem tau_injective (N : ℕ) : Function.Injective (tau N) :=
  inverseQuadratureNodes_injective D58.Odd.design branchCertificate (by decide) N

theorem tau_mem (N : ℕ) (i : Fin ((D58.Odd.design.n0 - D58.Odd.design.g0) * N)) :
    tau N i ∈ Ioo (-1 : ℝ) 1 :=
  (inverseQuadratureNodes_support D58.Odd.design branchCertificate (by decide) N i).1

theorem tau_ne_zero (N : ℕ) (i : Fin ((D58.Odd.design.n0 - D58.Odd.design.g0) * N)) :
    tau N i ≠ 0 :=
  (inverseQuadratureNodes_support D58.Odd.design branchCertificate (by decide) N i).2.1

theorem tau_support (N : ℕ) (i : Fin ((D58.Odd.design.n0 - D58.Odd.design.g0) * N)) :
    trimmedResidualSupport (realCoordinate (tau N i)) :=
  coordinate_mem_trimmedSupport (tau_mem N i)
    (inverseQuadratureNodes_support D58.Odd.design branchCertificate (by decide) N i).2.2

theorem tau_weights : GapWeightBounds D58.Odd.design tau weight := by
  apply inverseImage_weight_bounds D58.Odd.design (by decide) (by decide)
    branchCertificate realP_natDegree (by decide)
    (radius := (radius : ℝ)) (C := polynomialCap) (wc := weightCap)
    (by norm_num [radius]) (by norm_num [radius]) weight_margin polynomialCap_bound
  intro z hz
  have h := Sharp.circle_bound z hz
  simpa [D58.Odd.design, weightCap, Sharp.sharpWeightCap] using h

end CatalanMeasure.GenD.Refinement.Trimmed130
